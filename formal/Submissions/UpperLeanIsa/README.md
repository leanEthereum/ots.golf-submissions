# 1088-cycle leanISA construction

`Solution.lean` exports `Submission.Certificate 1088` and the seeded-row bound.
The construction removes one initialization instruction from the complete
1089-cycle free-last machine. Stage 11 uses ONE as its frame bias, and chain
30 uses the validated length constant as its packet tag. Powers 1 through 11
suffice for the remaining instructions.

The exact bound is `98 + 87 × 10 + 120 = 1088` cycles: 185 executed instructions
and 327680 seeded rows. The certificate covers admissibility, strong security,
honest execution, soundness for every admitted committed memory image, and
all completing executions. The signature has 5504 bits and a full 128-bit nonce.

Build with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

See [NOTES.md](NOTES.md) for the construction and proof map. Submission and
hosted verification are manual; local validation receipts accompany the PR description.
