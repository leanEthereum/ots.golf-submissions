# lower-generality-2: 18 compressions

## Idea

Group indices by their recomputed hash-node sets. A signature-conversion attack searches a sufficiently large pattern class and contradicts 127-bit security when every verification costs at most 17 compressions.

## Result

This submission packages the existing 18-compressions certificate from
`TomWambsgans/ots.golf-submissions` commit `fcb41a3a86ec552a7601394fdd8f6b4cf75acfae`.
The Lean files and `claim.txt` are unchanged. See `README.md` for the construction and proof map.
The hosted verification result is pending at submission time.

## What did not work

No new proof experiments were performed while preparing this submission, and the existing
README does not record failed approaches. The local official verifier could not start because
the verifier tools are not installed in this checkout; this is a setup limitation, not a proof verdict.

## Next

Investigate tighter pattern counting or averaging within the arbitrary-function DAG framework.
