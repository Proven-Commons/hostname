#!/usr/bin/env python3
"""Differential tests: the Lean host name matcher against a model of
the specification and three implementations in wide use.

The tool answers `match`, `ref`, `presented` and `verify` requests (see
the header of Main.lean). Its answers are checked two ways.

1. Against `spec_model`, a Python reading of SPEC.md written with
   regular expressions, apart from the Lean code. Every answer must
   agree.

2. For `match`, against three oracles:

   - Go: `crypto/x509`'s `Certificate.VerifyHostname`, through the
     program in tests/oracles/go, built here with the `go` on PATH;
   - OpenSSL: `X509_check_host` from the system libcrypto, through
     ctypes, with `X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS` and
     `X509_CHECK_FLAG_NEVER_CHECK_SUBJECT`;
   - pyca/cryptography: its X.509 verifier, with a certificate whose
     only subject alternative name is the presented identifier, signed
     by a test root, and the reference identifier as the server name.

   Each oracle gets the presented identifier as the one DNS name in a
   certificate. On a pair where both identifiers are well formed and
   the reference has no trailing dot, every oracle must give the
   tool's answer. Elsewhere the oracles differ from RFC 9525 and from
   each other in known ways, so a disagreement is counted under the
   first property of the pair that explains it (an underscore, a
   trailing dot, a wildcard over one label, ...). A disagreement on a
   pair with none of those properties is a failure, and so is a match
   that no oracle gives.

Inputs come from a recorded seed, after fixed sets:

- the examples of RFC 9525 and RFC 6125, and the name checks of the
  x509-limbo suite, at the commit named in LIMBO_COMMIT;
- characters that Unicode case folding or lookalikes could slip past
  an ASCII check: the Kelvin sign, the long s, dotless and dotted i,
  fullwidth and Cyrillic letters;
- every pair of strings of up to three characters over `a`, `A`, `1`,
  `-`, `.`, `*` and `_`;
- every string of up to five characters over the same alphabet, as a
  reference and as a presented identifier;
- well formed reference identifiers with presented identifiers built
  from them: the same name in another case, a wildcard in place of the
  first label, a label more or less, a label or character changed;
- mutations of those: an underscore, a trailing or doubled dot, a
  hyphen at the edge of a label, an all-digit last label, a label of
  64 characters or a name of 254, characters outside ASCII, spaces and
  NULs, a `*` anywhere, partial wildcards, and a wildcard over one
  label;
- `verify` requests on random lists;
- malformed requests, which the tool must answer with `error`.

Every seventh request ends in CR LF.

When this Python lacks the pinned pyca/cryptography, the script
creates a virtual environment in `.lake/oracle-venv`, installs it
there, checked against the hashes in `tests/oracle-requirements.txt`,
and runs itself again with it.

    python3 tests/run_tests.py [--seed N] [--count N]

`--count` is the number of random pairs after the fixed sets. The
script builds the executable and the Go oracle first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
"""

import argparse
import ctypes
import ctypes.util
import datetime
import itertools
import os
import platform
import random
import re
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "hostname"
GO_SRC = ROOT / "tests" / "oracles" / "go"
GO_EXE = ROOT / ".lake" / "oracle-go" / "go-oracle"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
REQUIREMENTS = ROOT / "tests" / "oracle-requirements.txt"
VENV = ROOT / ".lake" / "oracle-venv"
PIN = "50.0.1"
TIMEOUT = 3600
BUILD_TIMEOUT = 3600
LIMBO_COMMIT = "1080e565f26e544bbe9cf99953be8a57c08e7e20"
# Certificates and verifiers kept for reuse, at most, per oracle.
CACHE = 4096


def oracle_ready():
    """Whether the pinned pyca/cryptography imports."""
    try:
        import cryptography
    except ImportError:
        return False
    return cryptography.__version__ == PIN


def ensure_oracle():
    """Import pyca/cryptography. When this Python lacks the pinned
    version, install it, checked against the hashes in
    tests/oracle-requirements.txt, into a virtual environment and run
    again with it."""
    if oracle_ready():
        return
    if os.environ.get("HOSTNAME_ORACLE_VENV"):
        sys.exit(f"pyca/cryptography {PIN} is not usable even in .lake/oracle-venv")
    python = VENV / "bin" / "python"
    if not python.exists():
        subprocess.run([sys.executable, "-m", "venv", str(VENV)], check=True)
    subprocess.run([str(python), "-m", "pip", "install", "--quiet", "--require-hashes",
                    "-r", str(REQUIREMENTS)], check=True)
    env = dict(os.environ, HOSTNAME_ORACLE_VENV="1")
    os.execve(str(python), [str(python), *sys.argv], env)


ensure_oracle()

import cryptography  # noqa: E402
from cryptography import x509  # noqa: E402
from cryptography.hazmat.primitives import hashes  # noqa: E402
from cryptography.hazmat.primitives.asymmetric import ec  # noqa: E402
from cryptography.x509.oid import ExtendedKeyUsageOID, ExtensionOID, NameOID  # noqa: E402
from cryptography.x509.verification import PolicyBuilder, Store  # noqa: E402


# ---------------------------------------------------------------------
# The model of the specification, from SPEC.md.

LABEL = r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?"
NAME = re.compile(rf"{LABEL}(?:\.{LABEL})*")
ASCII_LOWER = str.maketrans("ABCDEFGHIJKLMNOPQRSTUVWXYZ", "abcdefghijklmnopqrstuvwxyz")


def host_name(s):
    """A host name: labels of RFC 1034 and RFC 1123 joined by dots, at
    most 253 characters, the last label not all digits."""
    return (len(s) <= 253 and NAME.fullmatch(s) is not None
            and not s.rsplit(".", 1)[-1].isdigit())


def model_reference(r):
    """The host name a reference identifier gives, or None."""
    name = r[:-1] if r.endswith(".") else r
    return name if host_name(name) else None


def model_presented(p):
    """("wild", suffix) or ("exact", name) for a well formed presented
    identifier, or None."""
    if p.startswith("*."):
        s = p[2:]
        return ("wild", s) if len(p) <= 253 and host_name(s) and "." in s else None
    return ("exact", p) if host_name(p) else None


def spec_model(r, p):
    name, form = model_reference(r), model_presented(p)
    if name is None or form is None:
        return False
    kind, s = form
    if kind == "exact":
        return name.translate(ASCII_LOWER) == s.translate(ASCII_LOWER)
    if "." not in name:
        return False
    return name.split(".", 1)[1].translate(ASCII_LOWER) == s.translate(ASCII_LOWER)


# ---------------------------------------------------------------------
# What sets a pair outside the domain where every oracle should follow
# RFC 9525, in the order a disagreement is counted under.

def labels_of(s):
    return s.split(".")


def outside_reasons(r, p):
    reasons = []
    if r == "" or p == "":
        reasons.append("an empty string")
    if r.endswith(".") and r != ".":
        reasons.append("a trailing dot on the reference")
    if p.endswith(".") and p != ".":
        reasons.append("a trailing dot on the presented name")
    if any(ord(c) > 127 for c in r + p):
        reasons.append("a character outside ASCII")
    if "_" in r + p:
        reasons.append("an underscore")
    if any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-.*_"
           and ord(c) <= 127 for c in r + p):
        reasons.append("another character outside names, such as a space or NUL")
    if "*" in r:
        reasons.append("a * in the reference")
    if "*" in p and not (p.startswith("*.") and "*" not in p[2:]):
        reasons.append("a * other than as the whole left-most label")
    rn = r[:-1] if r.endswith(".") else r
    pn = p[2:] if p.startswith("*.") else p
    pn = pn[:-1] if pn.endswith(".") else pn
    if any(x == "" for x in labels_of(rn) + labels_of(pn)):
        reasons.append("an empty label")
    if p.startswith("*.") and "*" not in p[2:] and "." not in p[2:]:
        reasons.append("a wildcard over one label")
    if any(x.startswith("-") or x.endswith("-") for x in labels_of(rn) + labels_of(pn)):
        reasons.append("a hyphen at the edge of a label")
    if any(len(x) > 63 for x in labels_of(rn) + labels_of(pn)):
        reasons.append("a label over 63 characters")
    if len(rn) > 253 or len(p) > 253:
        reasons.append("a name over 253 characters")
    if labels_of(rn)[-1].isdigit() or labels_of(pn)[-1].isdigit():
        reasons.append("an all-digit last label")
    return reasons


# ---------------------------------------------------------------------
# The oracles.

def build_go():
    GO_EXE.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, GOFLAGS="-mod=mod", CGO_ENABLED="0")
    subprocess.run(["go", "build", "-o", str(GO_EXE), "."], cwd=GO_SRC, check=True, env=env,
                   timeout=BUILD_TIMEOUT)


def go_version():
    out = subprocess.run(["go", "version"], capture_output=True, text=True)
    return out.stdout.strip()


def run_lines(cmd, lines, timeout=TIMEOUT):
    """Send `lines` to `cmd`, one per line, and return its answer
    lines and a note on how the run failed, or None."""
    raw = "".join(lines).encode("utf-8")
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf):
        while chunk := stream.read1(1 << 16):
            buf += chunk

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out)),
               threading.Thread(target=drain, args=(proc.stderr, err))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    return answers, problem


class OpenSSL:
    """X509_check_host on a certificate whose only subject alternative
    name is the presented identifier, as a dNSName."""
    GEN_DNS = 2
    NID_SUBJECT_ALT_NAME = 85
    FLAGS = 0x4 | 0x20  # NO_PARTIAL_WILDCARDS | NEVER_CHECK_SUBJECT

    def __init__(self):
        path = ctypes.util.find_library("crypto")
        if path is None:
            raise OSError("no libcrypto")
        lib = ctypes.CDLL(path)
        vp = ctypes.c_void_p
        lib.X509_new.restype = vp
        lib.X509_free.argtypes = [vp]
        lib.GENERAL_NAME_new.restype = vp
        lib.GENERAL_NAME_set0_value.argtypes = [vp, ctypes.c_int, vp]
        lib.ASN1_IA5STRING_new.restype = vp
        lib.ASN1_STRING_set.argtypes = [vp, ctypes.c_char_p, ctypes.c_int]
        lib.OPENSSL_sk_new_null.restype = vp
        lib.OPENSSL_sk_push.argtypes = [vp, vp]
        lib.OPENSSL_sk_pop_free.argtypes = [vp, vp]
        lib.GENERAL_NAME_free.argtypes = [vp]
        lib.X509_add1_ext_i2d.argtypes = [vp, ctypes.c_int, vp, ctypes.c_int, ctypes.c_ulong]
        lib.X509_check_host.argtypes = [vp, ctypes.c_char_p, ctypes.c_size_t, ctypes.c_uint,
                                        vp]
        lib.OpenSSL_version.restype = ctypes.c_char_p
        lib.OpenSSL_version.argtypes = [ctypes.c_int]
        self.lib = lib
        self.version = lib.OpenSSL_version(0).decode()
        self.certs = {}

    def cert(self, p):
        x = self.certs.get(p)
        if x is None:
            lib = self.lib
            if len(self.certs) >= CACHE:
                for old in self.certs.values():
                    lib.X509_free(old)
                self.certs.clear()
            x = lib.X509_new()
            gens = lib.OPENSSL_sk_new_null()
            gen = lib.GENERAL_NAME_new()
            ia5 = lib.ASN1_IA5STRING_new()
            if lib.ASN1_STRING_set(ia5, p, len(p)) != 1:
                raise RuntimeError("ASN1_STRING_set")
            lib.GENERAL_NAME_set0_value(gen, self.GEN_DNS, ia5)
            lib.OPENSSL_sk_push(gens, gen)
            if lib.X509_add1_ext_i2d(x, self.NID_SUBJECT_ALT_NAME, gens, 0, 0) != 1:
                raise RuntimeError("X509_add1_ext_i2d")
            lib.OPENSSL_sk_pop_free(gens, ctypes.cast(lib.GENERAL_NAME_free, ctypes.c_void_p))
            self.certs[p] = x
        return x

    def match(self, r, p):
        rb, pb = r.encode("utf-8"), p.encode("utf-8")
        return self.lib.X509_check_host(self.cert(pb), rb, len(rb), self.FLAGS, None) == 1


def der_length(n):
    if n < 128:
        return bytes([n])
    b = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(b)]) + b


class Pyca:
    """pyca/cryptography's verifier: a chain of one certificate, whose
    only subject alternative name is the presented identifier as a
    dNSName (written byte for byte), under a test root."""

    def __init__(self):
        self.now = datetime.datetime(2026, 1, 1, tzinfo=datetime.timezone.utc)
        # Fixed keys: the answers do not depend on them, and fixed keys
        # keep the run repeatable.
        self.ca_key = ec.derive_private_key(20261026, ec.SECP256R1())
        self.leaf_key = ec.derive_private_key(20261027, ec.SECP256R1())
        self.ca_name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, "oracle root")])
        day = datetime.timedelta(days=1)
        ca = (x509.CertificateBuilder()
              .subject_name(self.ca_name).issuer_name(self.ca_name)
              .public_key(self.ca_key.public_key()).serial_number(1)
              .not_valid_before(self.now - day).not_valid_after(self.now + 3650 * day)
              .add_extension(x509.BasicConstraints(ca=True, path_length=None), critical=True)
              .add_extension(x509.KeyUsage(False, False, False, False, False, True, True, False,
                                           False), critical=True)
              .add_extension(x509.SubjectKeyIdentifier.from_public_key(
                  self.ca_key.public_key()), critical=False)
              .sign(self.ca_key, hashes.SHA256()))
        self.store = Store([ca])
        self.certs = {}
        self.verifiers = {}
        self.serial = 1

    def cert(self, p):
        c = self.certs.get(p)
        if c is None:
            if len(self.certs) >= CACHE:
                self.certs.clear()
            pb = p.encode("utf-8")
            name = b"\x82" + der_length(len(pb)) + pb
            san = b"\x30" + der_length(len(name)) + name
            self.serial += 1
            day = datetime.timedelta(days=1)
            c = (x509.CertificateBuilder()
                 .subject_name(x509.Name([])).issuer_name(self.ca_name)
                 .public_key(self.leaf_key.public_key()).serial_number(self.serial)
                 .not_valid_before(self.now - day).not_valid_after(self.now + 90 * day)
                 .add_extension(x509.UnrecognizedExtension(
                     ExtensionOID.SUBJECT_ALTERNATIVE_NAME, san), critical=True)
                 .add_extension(x509.ExtendedKeyUsage([ExtendedKeyUsageOID.SERVER_AUTH]),
                                critical=False)
                 .add_extension(x509.AuthorityKeyIdentifier.from_issuer_public_key(
                     self.ca_key.public_key()), critical=False)
                 .sign(self.ca_key, hashes.SHA256()))
            self.certs[p] = c
        return c

    def verifier(self, r):
        if r not in self.verifiers:
            if len(self.verifiers) >= CACHE:
                self.verifiers.clear()
            try:
                v = (PolicyBuilder().store(self.store).time(self.now)
                     .build_server_verifier(x509.DNSName(r)))
            except ValueError:
                v = None  # pyca refuses the reference identifier
            self.verifiers[r] = v
        return self.verifiers[r]

    def match(self, r, p):
        v = self.verifier(r)
        if v is None:
            return False
        try:
            v.verify(self.cert(p), [])
            return True
        except Exception:  # VerificationError, or a SAN pyca cannot read
            return False


# ---------------------------------------------------------------------
# The fixed sets.

# RFC 9525: sections 6.1.2, 6.3 and 7.1. RFC 6125: section 6.4.3.
RFC_PAIRS = [
    ("www.bigcompany.example", "WWW.BigCompany.Example"),
    ("WWW.BigCompany.Example", "www.bigcompany.example"),
    ("www.bigcompany.example", "web.bigcompany.example"),
    ("mail.isp.example", "mail.isp.example"),
    ("isp.example", "mail.isp.example"),
    ("messenger.example", "messenger.example"),
    ("foo.bigcompany.example", "*.bigcompany.example"),
    ("foo.bar.bigcompany.example", "*.*.bigcompany.example"),
    ("foo.bar.bigcompany.example", "*.bigcompany.example"),
    ("foo.example.com", "*.example.com"),
    ("bar.foo.example.com", "*.example.com"),
    ("example.com", "*.example.com"),
    ("baz1.example.net", "baz*.example.net"),
    ("foobaz.example.net", "*baz.example.net"),
    ("buzz.example.net", "b*z.example.net"),
]

# x509-limbo, at LIMBO_COMMIT: the name checks of groups webpki::san and
# rfc5280::san, as (case id, reference, presented, expected).
LIMBO = [
    ("webpki::san::exact-dns-san", "example.com", "example.com", True),
    ("webpki::san::mismatch-domain-san", "example2.com", "example.com", False),
    ("webpki::san::mismatch-subdomain-san", "def.example.com", "abc.example.com", False),
    ("webpki::san::mismatch-subdomain-apex-san", "abc.example.com", "example.com", False),
    ("webpki::san::mismatch-apex-subdomain-san", "example.com", "abc.example.com", False),
    ("webpki::san::public-suffix-wildcard-san", "example.com", "*.com", False),
    ("webpki::san::public-suffix-multi-label-wildcard-san", "example.co.uk", "*.co.uk", False),
    ("webpki::san::public-suffix-private-namespace-wildcard-san", "example.s3.amazonaws.com",
     "*.s3.amazonaws.com", False),
    ("webpki::san::leftmost-wildcard-san", "foo.example.com", "*.example.com", True),
    ("webpki::san::wildcard-embedded-leftmost-san", "baz.example.com", "ba*.example.com",
     False),
    ("webpki::san::wildcard-not-in-leftmost-san", "foo.bar.example.com", "foo.*.example.com",
     False),
    ("webpki::san::wildcard-match-across-labels-san", "foo.bar.example.com", "*.example.com",
     False),
    ("webpki::san::wildcard-embedded-ulabel-san", "xn--bliss-1b3c148a.example.com",
     "xn--*-1b3c148a.example.com", False),
    ("webpki::san::unicode-emoji-san", "xn--628h.example.com", "\U0001f61c.example.com", False),
    ("webpki::san::san-wildcard-only", "example.com", "*", False),
    ("webpki::san::san-wildcard-only-tld", "com", "*", False),
    ("rfc5280::san::underscore-dns", "foo_bar.example.com", "foo_bar.example.com", False),
    ("rfc5280::san::ip-in-dns", "8.8.8.8", "8.8.8.8", False),
]
# The two limbo cases that need the Public Suffix List, which this
# library does not hold (README, "What is not proved").
LIMBO_PSL = {"webpki::san::public-suffix-multi-label-wildcard-san",
             "webpki::san::public-suffix-private-namespace-wildcard-san"}

# Characters that case folding or a careless check could take for
# ASCII letters, each with the ASCII letter it looks like.
TRAPS = [("K", "k"), ("ſ", "s"), ("ı", "i"), ("İ", "i"),
         ("ｋ", "k"), ("к", "k"), ("а", "a"), ("ß", "ss"),
         ("ɡ", "g"), ("‐", "-"), ("․", "."), ("．", "."),
         ("。", "."), ("́", "")]


def trap_pairs():
    for bad, good in TRAPS:
        for name in ["key.example", "store.example", "id.example", "sky.example",
                     "a-b.example", "a.example.com", "ssl.example", "go.example"]:
            if good and good in name:
                lookalike = name.replace(good, bad, 1)
                yield name, lookalike
                yield lookalike, name
                yield lookalike, lookalike
                yield name, "*." + lookalike.split(".", 1)[1] if "." in lookalike else name
                yield lookalike, "*." + name.split(".", 1)[1]
        yield "a" + bad + ".example", "a" + bad + ".example"


def name_of_length(n, first="c"):
    """A name of exactly `n` characters, of labels of 63 characters
    and a shorter one first, starting with `first`."""
    labels = []
    while n > 63:
        labels.append("a" * 63)
        n -= 64
    if n <= 0:  # the dot before the last label used up the length
        labels[-1] = "a" * (63 + n - 1)
        n = 1
    return ".".join([first + "b" * (n - 1)] + labels) if n >= 1 else ".".join(labels)


def boundary_pairs():
    """Names at both sides of the length limits: labels of 62 to 64
    characters, names of 251 to 255, and wildcard names of 252 to
    255."""
    for k in [1, 62, 63, 64]:
        name = "q" * k + ".example"
        yield name, name
        yield name, name.upper()
        yield "x." + name, "*." + name
    for n in range(250, 257):
        name = name_of_length(n)
        yield name, name
        yield name.upper(), name
        yield name + ".", name
        suffix = name_of_length(n - 2)
        yield "w." + suffix, "*." + suffix
        yield "W." + suffix, "*." + suffix.upper()


GRID_ALPHABET = "aA1-.*_"


def grid(n):
    for k in range(n + 1):
        for t in itertools.product(GRID_ALPHABET, repeat=k):
            yield "".join(t)


# ---------------------------------------------------------------------
# Random names.

LETDIG = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"


def random_label(rng):
    r = rng.random()
    if r < 0.05:
        n = rng.choice([62, 63])
    elif r < 0.1:
        return "xn--" + "".join(rng.choice("abcdefghijklmnopqrstuvwxyz0123456789")
                                for _ in range(rng.randint(2, 12)))
    else:
        n = rng.choice([1, 1, 2, 3, 3, 4, 5, 6, 7, 8, 10, 12, 16])
    if n == 1:
        return rng.choice(LETDIG)
    mid = "".join(rng.choice(LETDIG + "--") for _ in range(n - 2))
    return rng.choice(LETDIG) + mid + rng.choice(LETDIG)


def random_name(rng, min_labels=1):
    k = max(min_labels, rng.choice([1, 2, 2, 3, 3, 3, 4, 4, 5, 6, 8]))
    labels = [random_label(rng) for _ in range(k)]
    if labels[-1].isdigit():
        labels[-1] = labels[-1] + rng.choice("abcxyz")
    while len(".".join(labels)) > 253 and len(labels) > min_labels:
        labels.pop(0)
    name = ".".join(labels)
    if len(name) > 253:
        return random_name(rng, min_labels)
    if rng.random() < 0.03:  # fill up to the length limit
        while True:
            longer = random_label(rng) + "." + name
            if len(longer) > 253:
                break
            name = longer
    return name


def recase(rng, s):
    r = rng.random()
    if r < 0.4:
        return s
    if r < 0.6:
        return s.upper()
    if r < 0.7:
        return s.lower()
    return "".join(c.upper() if rng.random() < 0.5 else c.lower() for c in s)


def change_char(rng, s):
    i = rng.randrange(len(s))
    if s[i] == ".":
        return s
    alphabet = LETDIG if i == 0 or i == len(s) - 1 or s[i - 1] == "." or s[i + 1] == "." \
        else LETDIG + "-"
    return s[:i] + rng.choice(alphabet) + s[i + 1:]


def derive(rng, r):
    """A presented identifier built from the reference name `r`."""
    labels = r.split(".")
    choice = rng.randrange(10)
    if choice == 0:
        return recase(rng, r)
    if choice == 1 and len(labels) >= 3:
        return "*." + recase(rng, ".".join(labels[1:]))
    if choice == 2 and len(labels) >= 2:
        return "*." + recase(rng, r)
    if choice == 3 and len(labels) >= 4:
        return "*." + recase(rng, ".".join(labels[2:]))
    if choice == 4:
        i = rng.randrange(len(labels))
        new = labels[:i] + [random_label(rng)] + labels[i + 1:]
        if new[-1].isdigit():
            new[-1] += "q"
        return recase(rng, ".".join(new))
    if choice == 5:
        return recase(rng, change_char(rng, r))
    if choice == 6:
        return recase(rng, random_label(rng) + "." + r)
    if choice == 7 and len(labels) >= 2:
        return recase(rng, ".".join(labels[1:]))
    if choice == 8:
        return random_name(rng)
    return "*." + random_name(rng, 2)


MUTATIONS = [
    lambda rng, s: s[:rng.randint(0, len(s))] + "_" + s[rng.randint(0, len(s)):]
    if s else "_",
    lambda rng, s: s + ".",
    lambda rng, s: "." + s,
    lambda rng, s: s.replace(".", "..", 1),
    lambda rng, s: "-" + s,
    lambda rng, s: s.replace(".", "-.", 1),
    lambda rng, s: s.replace(".", ".-", 1),
    lambda rng, s: s.rsplit(".", 1)[0] + "." + str(rng.randint(0, 999)) if "." in s
    else str(rng.randint(0, 999)),
    lambda rng, s: "a" * 64 + "." + s,
    lambda rng, s: ("b" * 63 + ".") * 4 + s,
    lambda rng, s: s.replace(rng.choice(TRAPS)[1] or "a", rng.choice(TRAPS)[0], 1),
    lambda rng, s: s[:len(s) // 2] + rng.choice([" ", "\t", "\x00", "\n", "/", ":", "@"])
    + s[len(s) // 2:],
    lambda rng, s: s[:rng.randint(0, len(s))] + "*" + s[rng.randint(0, len(s)):]
    if s else "*",
    lambda rng, s: rng.choice(["f*", "*f", "f*o", "**", "*-", "xn--*"]) + "."
    + s.split(".", 1)[-1],
    lambda rng, s: "*." + s.rsplit(".", 1)[-1],
    lambda rng, s: "*",
    lambda rng, s: "",
    lambda rng, s: ".".join(str(rng.randint(0, 255)) for _ in range(4)),
    lambda rng, s: s.replace(".", "", 1),
]


def mutate(rng, s):
    return MUTATIONS[rng.randrange(len(MUTATIONS))](rng, s)


# ---------------------------------------------------------------------
# The requests.

def hexs(s):
    return s.encode("utf-8").hex()


def match_case(label, r, p):
    return (label, f"match {hexs(r)} {hexs(p)}", "1" if spec_model(r, p) else "0", (r, p))


MALFORMED = [
    "match 0g 61", "match 616 61", "match 61", "ref", "presented 61 62", "verify -",
    "verify 6g -", "MATCH 61 61", "ref ff", "ref c0af", "ref eda080", "",
    "match  61 61", "ref 4A", "verify -,- -", "presented",
]

# A last line sent with no LF, or with CR LF, and the answer due.
AT_EOF = [(f"ref {hexs('example.com')}", "1"), (f"match {hexs('a.b')} {hexs('*.b')}\r\n", "0"),
          (f"presented {hexs('*.example.com')}\r\n", "1")]


def cases(seed, count):
    for req in MALFORMED:
        yield ("error", req, "error", None)
    for r, p in RFC_PAIRS:
        yield match_case("rfc", r, p)
    for _, r, p, _ in LIMBO:
        yield match_case("limbo", r, p)
    for r, p in trap_pairs():
        yield match_case("lookalike", r, p)
    for r, p in boundary_pairs():
        yield match_case("length", r, p)
        yield ("length ref", f"ref {hexs(r)}", "1" if model_reference(r) is not None else "0",
               None)
        yield ("length presented", f"presented {hexs(p)}",
               "1" if model_presented(p) is not None else "0", None)
    short = list(grid(3))
    for r in short:
        for p in short:
            yield match_case("grid pair", r, p)
    for s in grid(5):
        yield ("grid ref", f"ref {hexs(s)}", "1" if model_reference(s) is not None else "0",
               None)
        yield ("grid presented", f"presented {hexs(s)}",
               "1" if model_presented(s) is not None else "0", None)
    rng = random.Random(seed)
    pool = []
    for _ in range(count):
        r = random_name(rng)
        p = derive(rng, r)
        if model_presented(p) is None:
            p = recase(rng, r)
        roll = rng.random()
        if roll < 0.55:
            yield match_case("random", recase(rng, r), p)
        elif roll < 0.75:
            yield match_case("mutated", mutate(rng, recase(rng, r)), p)
        elif roll < 0.95:
            yield match_case("mutated", recase(rng, r), mutate(rng, p))
        else:
            yield ("random ref", f"ref {hexs(r)}", "1", None)
            m = mutate(rng, p)
            yield ("mutated presented", f"presented {hexs(m)}",
                   "1" if model_presented(m) is not None else "0", None)
        if len(pool) < 400:
            pool.append(r)
            pool.append(p)
    for _ in range(max(1, count // 20)):
        rs = [rng.choice(pool) for _ in range(rng.randint(0, 4))]
        ps = [rng.choice(pool) if rng.random() < 0.7 else mutate(rng, rng.choice(pool))
              for _ in range(rng.randint(0, 4))]
        if rs and rng.random() < 0.5:
            ps.insert(rng.randint(0, len(ps)), derive(rng, rng.choice(rs).lower()))
        want = any(spec_model(r, p) for r in rs for p in ps)
        hl = lambda xs: ",".join(hexs(x) for x in xs) if xs else "-"
        yield ("verify", f"verify {hl(rs)} {hl(ps)}", "1" if want else "0", None)


# ---------------------------------------------------------------------

def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261026)
    ap.add_argument("--count", type=count, default=300_000)
    args = ap.parse_args()

    def give_up(why):
        write(["# Test results", "", "- Oracle: none ran", f"- Seed: {args.seed}", "- Inputs: 0",
               f"- Failures: 1 ({why})", ""])
        sys.exit(why)

    try:
        build = subprocess.run(["lake", "build", "hostname"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        if build.returncode != 0:
            print(build.stdout + build.stderr)
            give_up("`lake build hostname` failed")
    except (OSError, subprocess.TimeoutExpired) as e:
        give_up(f"`lake build hostname` failed: {e}")
    try:
        build_go()
    except (OSError, subprocess.SubprocessError) as e:
        give_up(f"the Go oracle did not build: {e}")
    try:
        openssl = OpenSSL()
    except (OSError, AttributeError) as e:
        give_up(f"libcrypto could not be loaded: {e}")
    pyca = Pyca()

    items = list(cases(args.seed, args.count))
    # Every seventh request ends in CR LF, which the tool must take as LF.
    out, problem = run_lines([str(EXE), "serve"],
                             [req + ("\r\n" if i % 7 == 6 else "\n")
                              for i, (_, req, _, _) in enumerate(items)])
    failures = [("(whole run)", "a clean run", problem)] if problem else []
    for item, got in itertools.zip_longest(items, out):
        if item is None:
            failures.append(("(no request)", "nothing", got))
        elif got != item[2]:
            failures.append((item[1], item[2], "(no answer)" if got is None else got))
    eof_right = 0
    for req, want in AT_EOF:
        got, problem = run_lines([str(EXE), "serve"], [req], timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    # The oracles, on every match pair.
    pairs = [(item[3], item[2] == "1", item[0]) for item in items if item[3] is not None]
    go_out, problem = run_lines([str(GO_EXE)],
                                [f"{r.encode().hex()} {p.encode().hex()}\n"
                                 for (r, p), _, _ in pairs])
    if problem or len(go_out) != len(pairs):
        failures.append(("(Go oracle run)", "a clean run",
                         problem or f"{len(go_out)} answers for {len(pairs)} pairs"))
        go_out = ["?"] * len(pairs)
    oracles = ["Go", "OpenSSL", "pyca/cryptography"]
    strict = 0
    strict_matches = 0
    agree = {o: 0 for o in oracles}
    named = {o: {} for o in oracles}
    for ((r, p), lean, label), g in zip(pairs, go_out):
        answers = {"Go": g == "1", "OpenSSL": openssl.match(r, p),
                   "pyca/cryptography": pyca.match(r, p)}
        reasons = outside_reasons(r, p)
        if not reasons:
            strict += 1
            strict_matches += lean
        if lean and not any(answers.values()):
            failures.append((f"match {r!r} {p!r}", "a match some oracle gives too",
                             "a match no oracle gives"))
        for o in oracles:
            if g == "?" and o == "Go":
                continue
            if answers[o] == lean:
                agree[o] += 1
            elif not reasons:
                failures.append((f"match {r!r} {p!r}", f"{o} answers {int(answers[o])}",
                                 f"the tool answers {int(lean)}"))
            else:
                key = (reasons[0], "the oracle matches" if answers[o] else "the tool matches")
                named[o][key] = named[o].get(key, 0) + 1
    limbo_right = sum(1 for cid, r, p, want in LIMBO if spec_model(r, p) == want)
    limbo_psl = sorted(cid for cid, r, p, want in LIMBO if spec_model(r, p) != want)
    if set(limbo_psl) != LIMBO_PSL:
        failures.append(("x509-limbo", f"only {sorted(LIMBO_PSL)} differ", str(limbo_psl)))

    by_label = {}
    for label, _, _, _ in items:
        by_label[label] = by_label.get(label, 0) + 1
    matches = sum(1 for _, lean, _ in pairs if lean)
    malformed = [got for item, got in zip(items, out) if item[0] == "error"]

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Lean: {lean_version()}",
        "- Oracle: the model of the specification, `spec_model` in `tests/run_tests.py`, "
        "and Go, OpenSSL and pyca/cryptography, as below",
        f"- Go oracle: `crypto/x509` `Certificate.VerifyHostname`, {go_version()}",
        f"- OpenSSL oracle: `X509_check_host`, {openssl.version}, with "
        "`X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS` and `X509_CHECK_FLAG_NEVER_CHECK_SUBJECT`",
        f"- pyca/cryptography oracle: its X.509 verifier, version {cryptography.__version__}, "
        f"on Python {platform.python_version()}",
        f"- x509-limbo: commit {LIMBO_COMMIT}",
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Answers that differ from the model of the specification: "
        f"{sum(1 for item, got in zip(items, out) if got != item[2])}",
        f"- Pairs checked: {len(pairs)}, of which {matches} match and "
        f"{len(pairs) - matches} do not",
        f"- Pairs of two well formed names, the reference without a trailing dot: {strict}, "
        f"of which {strict_matches} match. Every oracle must agree on each.",
        "- Agreement with each oracle over all pairs: "
        + ", ".join(f"{o} {agree[o]} of {len(pairs)}" for o in oracles),
        f"- x509-limbo name checks the tool answers as the suite expects: {limbo_right} of "
        f"{len(LIMBO)}. The others need the Public Suffix List: {', '.join(limbo_psl)}",
        f"- Malformed requests answered `error`: {malformed.count('error')} of "
        f"{by_label.get('error', 0)}",
        f"- Requests ending in CR LF: every seventh, {len(items) // 7}",
        f"- Last lines sent alone, with no LF or with CR LF, answered right: {eof_right} of "
        f"{len(AT_EOF)}",
        f"- Failures: {len(failures)}",
        "",
        "## Where the oracles differ",
        "",
        "Outside the well formed pairs, each disagreement is counted under the first property "
        "of the pair that sets it outside, and by which side matches.",
        "",
    ]
    for o in oracles:
        lines.append(f"### {o}")
        lines.append("")
        if not named[o]:
            lines.append("No disagreement.")
        for (reason, side), n in sorted(named[o].items(), key=lambda kv: -kv[1]):
            lines.append(f"- {reason}, {side}: {n}")
        lines.append("")
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- `{req[:160]!r}`: expected `{want[:120]!r}`, got `{got[:120]!r}`"
                  for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    print(f"{len(items)} requests, {len(pairs)} pairs checked against three oracles, "
          f"{len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
