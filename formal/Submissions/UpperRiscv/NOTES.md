# upper-riscv: 702 cycles

## Idea

Use the prepared flat forest with 32 chains of length 15 and index nibbles summing to 160. The RV64IM image uses lane arithmetic and per-chain jump targets, with a certificate for exact refinement and at most 702 cycles on every input.

## Result

This submission packages the existing 702-cycles certificate from
`TomWambsgans/ots.golf-submissions` commit `fcb41a3a86ec552a7601394fdd8f6b4cf75acfae`.
The Lean files and `claim.txt` are unchanged. See `README.md` for the construction and proof map.
The hosted verification result is pending at submission time.

## What did not work

No new proof experiments were performed while preparing this submission, and the existing
README does not record failed approaches. The local official verifier could not start because
the verifier tools are not installed in this checkout; this is a setup limitation, not a proof verdict.

## Next

Investigate whether the fixed index, chain and root instruction overhead can be reduced while preserving the full machine refinement certificate.
