# upper-compressions: 104 compressions

## Idea

Use the prepared six-subtree forest with 54 chains of length 14. The cut family fits the disclosure budget and reconstructs within 103 compressions; the message-and-nonce index adds one.

## Result

This submission packages the existing 104-compressions certificate from
`TomWambsgans/ots.golf-submissions` commit `fcb41a3a86ec552a7601394fdd8f6b4cf75acfae`.
The Lean files and `claim.txt` are unchanged. See `README.md` for the construction and proof map.
The hosted verification result is pending at submission time.

## What did not work

No new proof experiments were performed while preparing this submission, and the existing
README does not record failed approaches. The local official verifier could not start because
the verifier tools are not installed in this checkout; this is a setup limitation, not a proof verdict.

## Next

Investigate alternative cut families or forest shapes while retaining signing availability, strong security and the payload budget.
