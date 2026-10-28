# Specification: hostname

A TLS client connects to a server it names, such as `www.example.com`, and the server shows a certificate listing the DNS names it may answer for. The client must check that one of those names covers the one it meant. This library makes that check, as RFC 9525, section 6.3, sets it out (https://www.rfc-editor.org/rfc/rfc9525#section-6.3). RFC 9525 replaced RFC 6125 in 2023.

The name the client meant is the *reference identifier*. A name in the certificate is a *presented identifier*. A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, and the other files `bar.toml` lists.

## Names

Both kinds of identifier are made of *labels* joined by dots.

- A label is 1 to 63 ASCII letters, digits and hyphens. It starts and ends with a letter or digit. This is `<label>` of RFC 1034, section 3.5, with a digit allowed first, as RFC 1123, section 2.1, allows.
- A host name is one or more labels joined by dots, at most 253 characters in all. RFC 1034, section 3.1, limits a name to 255 octets in the form DNS sends, which is 253 characters written out.
- The last label of a host name is not all digits. RFC 1123, section 2.1, notes this of every valid host name. It keeps an IPv4 address such as `192.0.2.1` from passing as a host name. RFC 9525 matches addresses separately, in section 6.4.
- An A-label, such as `xn--bcher-kva`, is a label like any other here. Whether it is valid Punycode is not checked. A U-label, such as `bücher`, holds characters outside ASCII, so it is not a label. RFC 9525 has the client turn U-labels into A-labels before matching.

A **reference identifier** is a host name. It may end with one more dot, the trailing dot of an absolute name (`example.com.`). That dot is dropped before matching. RFC 9525 does not mention the trailing dot. Dropping it follows the DNS, where `example.com.` and `example.com` are the same name.

A **presented identifier** is either:

- a host name; or
- a *wildcard name*: the label `*`, a dot, and a host name of at least two labels, at most 253 characters in all.

Section 6.3 allows one wildcard character, and only as the whole left-most label. A presented identifier that breaks those rules is invalid, and section 6.3 says it MUST be ignored, so it matches nothing. That covers `*.*.example.com`, `f*.example.com`, `*oo.example.com`, `foo.*.example.com` and a bare `*`. A presented identifier with a trailing dot is not in the preferred name syntax that RFC 5280, section 4.2.1.6, requires of a certificate's DNS names, so it is invalid too.

**Wildcards over one label.** A wildcard name needs at least two labels after the `*`, so `*.com` matches nothing. RFC 9525, section 7.1, puts protection against wildcards over a public suffix, such as `*.com` or `*.co.uk`, outside its scope. The two-label rule is a partial guard, the one OpenSSL applies. It catches `*.com` but not `*.co.uk`, which needs the Public Suffix List. That list changes over time and is not part of this library.

## Matching

Two names are compared label by label, with ASCII case ignored (RFC 4343, section 3), and nothing else ignored. An upper case letter `A` to `Z` equals its lower case `a` to `z`. No other character equals any character but itself, so Unicode case folding never applies: the Kelvin sign `K` (U+212A) is not `k`.

`matchName reference presented` is true exactly when both identifiers are well formed and one of these holds:

1. The presented identifier is a host name, and it is the reference name with ASCII case ignored.
2. The presented identifier is `*.` followed by a suffix. The reference name is one label, a dot, and then that suffix with ASCII case ignored. So the wildcard stands for exactly one label: `*.example.com` matches `foo.example.com`, but not `example.com` or `a.b.example.com`.

`verify references presented` is true when some presented identifier matches some reference identifier. That is the search of RFC 9525, section 6.2.

`validReference` and `validPresented` say whether an identifier is well formed.

Nothing here can fail. Every function returns `true` or `false` for every pair of strings.

## Out of scope

- Reading names out of a certificate, which needs a DER reader. The caller passes the names.
- IP addresses (RFC 9525, section 6.4), SRV-IDs, URI-IDs, and the application service type of section 6.5.
- Turning U-labels into A-labels, and checking that an A-label is valid Punycode.
- The common name of the certificate's subject, which RFC 9525 forbids as an identifier.
- Name constraints, which an issuing certificate can place on these names (RFC 5280, section 4.2.1.10).

## The command-line tool

The command-line tool in `Main.lean` has two modes:

- `hostname check REFERENCE PRESENTED...` prints `match` or `no match` for each presented identifier. It exits with 0 when one matches, and with 1 when none does.
- `hostname serve` answers requests from the differential tests, one per line. Each string is sent as the hex digits of its UTF-8 bytes. The header comment of `Main.lean` gives the protocol.

Every answer comes from `matchName`, `validReference`, `validPresented` and `verify`.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given. The definitions the statements use are in `Spec/Defs.lean`. They are written from the RFCs, separately from the code.

| Property | Theorem |
|----------|---------|
| `matchName` is true exactly when the rules above say the names match, as `Spec.Matches` states them. | `Spec.matchName_iff` |
| `validReference` and `validPresented` accept exactly the well formed identifiers. | `Spec.validReference_iff`, `Spec.validPresented_iff` |
| `verify` is true exactly when some presented identifier matches some reference identifier. | `Spec.verify_iff` |
| A presented identifier holding `*` matches only when it starts with `*.` and holds no other `*`. | `Spec.wildcard_leftmost_only` |
| A wildcard stands for exactly one label. | `Spec.wildcard_one_label` |
| A wildcard over one label, such as `*.com`, matches nothing. | `Spec.wildcard_two_labels` |
| Changing the ASCII case of either identifier changes no answer. | `Spec.matchName_case_left`, `Spec.matchName_case_right` |
| An identifier holding a character outside ASCII matches nothing. | `Spec.matchName_ascii_left`, `Spec.matchName_ascii_right` |
| Without a wildcard, matching is sameness with ASCII case ignored. | `Spec.matchName_exact` |
| Every host name matches itself. Matching is symmetric for names with no wildcard or trailing dot, and it chains. | `Spec.matchName_refl`, `Spec.matchName_symm`, `Spec.matchName_trans` |
| The examples of RFC 9525 and RFC 6125. | `Spec.rfc9525_examples`, `Spec.rfc6125_examples` |
| The name checks of x509-limbo, with the answers the suite expects. | `Spec.limbo_vectors` |
| The two x509-limbo cases this library does not catch: wildcards over a public suffix of two labels. | `Spec.public_suffix_limit` |
| Malformed names and pairs that must not match, and pairs that must. | `Spec.reject_vectors`, `Spec.accept_vectors` |
| The length limits: 63 characters to a label, 253 to a name. | `Spec.length_vectors` |

Together, these fix every output. `matchName` is fixed for every pair of strings by `Spec.matchName_iff`, and the validity checks and `verify` are fixed by their own theorems. The other statements follow from those. They state, in the plainest words, the properties a reader will look for.

## Oracles

The differential tests compare the tool with three implementations in wide use:

- Go's `crypto/x509`;
- OpenSSL's `X509_check_host`, with partial wildcards turned off;
- pyca/cryptography's verifier.

They also compare it with a model of this specification written in Python. The tool must agree with the model on every input. On pairs of well formed names whose reference has no trailing dot, it must agree with every implementation. Elsewhere the implementations differ from RFC 9525 and from each other in known ways, listed in `README.md`. The tests count each such difference under the property of the input that explains it. A difference they cannot explain is a failure.
