# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a one-line change to `Hostname/Basic.lean`, tested with `tests/run_tests.py --count 2000`. Every bug must give failures, and the unchanged code none.

| Planted bug | Failures |
|---|---|
| none | 0 |
| lower case misses Z | 69 |
| a wildcard over one label is allowed | 83 |
| a label may end in a hyphen | 903 |
| a wildcard may stand for no label | 111 |
| a name of 254 characters is allowed | 11 |
| a wildcard name of 254 characters is allowed | 2 |
| an all-digit last label is allowed | 199 |
| every trailing dot is dropped | 67 |
| case is not ignored | 338 |
| a label of 64 characters is allowed | 14 |

Bugs caught: 10 of 10
