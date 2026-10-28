# hostname: TLS host name matching, proved

A TLS client must check that the server's certificate is for the host it meant to reach. This library makes the core of that check in Lean: whether a DNS name from a certificate matches the name the client connected to, by RFC 9525, section 6.3. Machine-checked proofs show four things:

- It matches exactly the pairs that rule allows. Labels are compared in order with ASCII case ignored, and a wildcard `*` stands for exactly one label.
- A wildcard anywhere but as the whole left-most label, two wildcards, and partial wildcards such as `f*.example.com` match nothing.
- ASCII case is the only difference ignored. Characters outside ASCII never match, so the Kelvin sign `K` is not `k`.
- A name that is not well formed, such as `a..example`, `foo_bar.example`, `-a.example` or `192.0.2.1`, matches nothing.

The tests compare it with Go's `crypto/x509`, OpenSSL's `X509_check_host`, and pyca/cryptography. On 177,360 pairs of well formed names, all three give the same answers as this library. `tests/TEST-RESULTS.md` has the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean:

- `Hostname.matchName : String → String → Bool`: does a presented identifier (second) match a reference identifier (first)?
- `Hostname.verify : List String → List String → Bool`: does any presented identifier match any reference identifier?
- `Hostname.validReference`, `Hostname.validPresented : String → Bool`: is an identifier well formed?

`SPEC.md` says what each one does.

## What is proved

The statements are in `Spec.lean`, the definitions they use in `Spec/Defs.lean`, and the proofs in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| `matchName r p` is true exactly when `r` and `p` are well formed and `p` matches by RFC 9525, section 6.3. Without a wildcard, `p` is the reference name with ASCII case ignored. With one, the reference name is one label, a dot, and the rest of `p` with ASCII case ignored. | `Spec.matchName_iff` |
| `validReference` accepts exactly the host names of RFC 1034 and RFC 1123, with or without a trailing dot. `validPresented` accepts exactly the host names, and `*.` before a host name of two or more labels. | `Spec.validReference_iff`, `Spec.validPresented_iff` |
| `verify` succeeds exactly when some presented identifier matches some reference identifier. | `Spec.verify_iff` |
| A presented identifier holding `*` matches only when it starts with `*.` and holds no other `*`. | `Spec.wildcard_leftmost_only` |
| A wildcard stands for exactly one label, never zero or two. | `Spec.wildcard_one_label` |
| A wildcard over one label, such as `*.com`, matches nothing. | `Spec.wildcard_two_labels` |
| Changing the ASCII case of either identifier changes no answer. | `Spec.matchName_case_left`, `Spec.matchName_case_right` |
| An identifier holding a character outside ASCII matches nothing. | `Spec.matchName_ascii_left`, `Spec.matchName_ascii_right` |
| Without a wildcard, matching is sameness with ASCII case ignored. It is reflexive, symmetric and transitive on such names. | `Spec.matchName_exact`, `Spec.matchName_refl`, `Spec.matchName_symm`, `Spec.matchName_trans` |
| The examples of RFC 9525 and RFC 6125. The name checks of the x509-limbo suite. Malformed names, the length limits, and pairs loose matchers get wrong. | `Spec.rfc9525_examples`, `Spec.rfc6125_examples`, `Spec.limbo_vectors`, `Spec.reject_vectors`, `Spec.accept_vectors`, `Spec.length_vectors` |
| The limit below, stated as a theorem: `*.co.uk` matches `example.co.uk`. | `Spec.public_suffix_limit` |

The command-line tool in `Main.lean` answers requests with these functions directly.

## What is not proved

- **Wildcards over a public suffix of two or more labels.** `*.co.uk` and `*.s3.amazonaws.com` match names under them. A wildcard needs two labels after it, which stops `*.com`, but catching `*.co.uk` needs the Public Suffix List, which changes over time. RFC 9525, section 7.1, leaves this out of its scope. A caller that needs it must check the list itself. x509-limbo expects both of these to fail, and they are its only two name checks this library does not pass.
- **What comes before and after.** The names are passed in by the caller. Reading them from a certificate, checking the certificate chain, and building the reference identifier from what the user asked for all lie outside this library. RFC 9525, section 6.1, warns that the reference identifier must come from the user's input and not from DNS.
- **IP addresses, SRV-IDs, URI-IDs, and the common name.** Section 6.4 matches an IP address by its bytes. That is not done here, and an IPv4 address is not a host name, so it matches nothing.
- **U-labels and Punycode.** A name with characters outside ASCII matches nothing. The client must turn it into A-labels first. An A-label is not checked for valid Punycode.
- **Reading requests and printing answers in `Main.lean`.** That code covers the hex parsing, the request format and the lists `verify` takes. The differential tests cover it, with malformed requests and CR LF line endings.
- **Speed.** The code works on lists of characters, which suits the proofs. A pair of names takes time in proportion to their length, which is at most 253 characters for any name that can match.

## Where other implementations differ

The tests count every disagreement with Go, OpenSSL and pyca/cryptography, with the property of the pair that explains it. On pairs of well formed names whose reference has no trailing dot, there are none. Elsewhere:

- **Go's `crypto/x509`** accepts underscores, hyphens at the end of a label, and an all-digit last label unless the whole name is an IP address. It sets no length limits. It matches a wildcard over one label, so `*.com` matches `example.com`. When either name is not a valid host name, it compares the two strings with ASCII case ignored. So `a..example` matches `a..example`, and `*.example.com` as a reference matches itself.
- **OpenSSL's `X509_check_host`** compares a name without a wildcard as a string, with ASCII case ignored and no check of its syntax. So underscores, empty labels and all-digit last labels match themselves. It does not drop the trailing dot of an absolute reference. Its wildcard rules agree with these, with partial wildcards turned off, except that they set no length limit and allow an all-digit last label.
- **pyca/cryptography** checks names as this library does. It differs on three points:
  - it refuses a reference with a trailing dot;
  - it matches a wildcard over one label;
  - it allows an all-digit last label, so the DNS name `8.8.8.8` matches the reference `8.8.8.8`, which RFC 5280 forbids and x509-limbo tests.

Each of these is a choice this library makes on purpose, in `SPEC.md`.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about, such as the conversion between strings and lists.
- The operating system and hardware it runs on.
- For the tests only: Go, OpenSSL and pyca/cryptography as oracles, and the model of the specification in `tests/run_tests.py`. The record names their versions.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), Python 3, Go, and OpenSSL's libcrypto.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script builds the tool and the Go oracle, and loads libcrypto. When Python lacks the pinned pyca/cryptography, it installs it into `.lake/oracle-venv`, checked against the hashes in `tests/oracle-requirements.txt`. It runs these inputs:

- the RFC examples, the x509-limbo name checks, and lookalike characters from outside ASCII;
- every pair of strings of up to three characters over `a`, `A`, `1`, `-`, `.`, `*` and `_`;
- random well formed names, with presented names built from them, and mutations of both, from a recorded seed.

It then rewrites `tests/TEST-RESULTS.md`.

`python3 tests/plant_bugs.py` checks the tests themselves. It plants ten bugs in a copy of the code, one at a time, such as a label allowed to end in a hyphen or a wildcard allowed to stand for no label. It records how many failures the tests report for each in `tests/PLANTED-BUGS.md`. Every bug must be caught. Each of them also breaks a proof.

## Layout

- `Hostname/Basic.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the RFCs.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
- `tests/oracles/go/`: the Go oracle.
- `tests/plant_bugs.py` and `tests/PLANTED-BUGS.md`: the planted bugs, and the record that the tests catch each one.
- `tests/oracle-requirements.txt`: the pyca/cryptography oracle's version, pinned by hash.
