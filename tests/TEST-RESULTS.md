# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Model of the specification: `spec_model` in `tests/run_tests.py`
- Go oracle: `crypto/x509` `Certificate.VerifyHostname`, go version go1.24.7 linux/amd64
- OpenSSL oracle: `X509_check_host`, OpenSSL 3.0.13 30 Jan 2024, with `X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS` and `X509_CHECK_FLAG_NEVER_CHECK_SUBJECT`
- pyca/cryptography oracle: its X.509 verifier, version 50.0.1, on Python 3.13.17
- x509-limbo: commit 1080e565f26e544bbe9cf99953be8a57c08e7e20
- Seed: 20261026
- Inputs: 529723
- By kind: error 16, grid pair 160000, grid presented 19608, grid ref 19608, length 47, length presented 47, length ref 47, limbo 18, lookalike 244, mutated 119709, mutated presented 15073, random 165218, random ref 15073, rfc 15, verify 15000
- Answers that differ from the model of the specification: 0
- Pairs checked: 445251, of which 33222 match and 412029 do not
- Pairs of two well formed names, the reference without a trailing dot: 177360, of which 32625 match. Every oracle must agree on each.
- Agreement with each oracle over all pairs: Go 443674 of 445251, OpenSSL 442568 of 445251, pyca/cryptography 444334 of 445251
- x509-limbo name checks the tool answers as the suite expects: 16 of 18. The others need the Public Suffix List: webpki::san::public-suffix-multi-label-wildcard-san, webpki::san::public-suffix-private-namespace-wildcard-san
- Malformed requests answered `error`: 16 of 16
- Requests ending in CR LF: every seventh, 75674
- Last lines sent alone, with no LF or with CR LF, answered right: 3 of 3
- Failures: 0

## Where the oracles differ

Outside the well formed pairs, each disagreement is counted under the first property of the pair that sets it outside, and by which side matches.

### Go

- a hyphen at the edge of a label, the oracle matches: 326
- a wildcard over one label, the oracle matches: 311
- a label over 63 characters, the oracle matches: 277
- an underscore, the oracle matches: 253
- a * in the reference, the oracle matches: 169
- a trailing dot on the reference, the oracle matches: 113
- a character outside ASCII, the oracle matches: 60
- an empty label, the oracle matches: 48
- a name over 253 characters, the oracle matches: 12
- an all-digit last label, the oracle matches: 8

### OpenSSL

- an empty label, the oracle matches: 677
- a trailing dot on the reference, the tool matches: 597
- a hyphen at the edge of a label, the oracle matches: 547
- a label over 63 characters, the oracle matches: 277
- an underscore, the oracle matches: 232
- a * in the reference, the oracle matches: 175
- a trailing dot on the reference, the oracle matches: 97
- a character outside ASCII, the oracle matches: 60
- a name over 253 characters, the oracle matches: 12
- an all-digit last label, the oracle matches: 9

### pyca/cryptography

- a trailing dot on the reference, the tool matches: 597
- a wildcard over one label, the oracle matches: 311
- an all-digit last label, the oracle matches: 9
