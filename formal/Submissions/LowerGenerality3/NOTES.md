# lower-generality-3: 1 compression

## Idea

A zero-cost verifier is independent of the oracle. Correctness and signing availability allow a public-data signature choice that yields a fresh-message forgery and contradicts security.

## Result

This submission packages the existing 1-compression certificate from
`TomWambsgans/ots.golf-submissions` commit `fcb41a3a86ec552a7601394fdd8f6b4cf75acfae`.
The Lean files and `claim.txt` are unchanged. See `README.md` for the construction and proof map.
The hosted verification result is pending at submission time.

## What did not work

No new proof experiments were performed while preparing this submission, and the existing
README does not record failed approaches. The local official verifier could not start because
the verifier tools are not installed in this checkout; this is a setup limitation, not a proof verdict.

## Next

Investigate whether the oracle-independent argument can extend to a positive query budget.
