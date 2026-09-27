# 1110-cycle leanISA construction

`Solution.lean` exports the complete `Submission.Certificate 1110`. Affine frames
remove fourteen entry JUMPs from the previous 1124-cycle verifier. The score is
`110 + 88 × 10 + 120 = 1110`, with 198 executed instructions and 327680 seeded rows.
The full 128-bit nonce fits the 5504-bit signature budget.

The certificate covers admissibility, 127-bit strong security, bytecode validity,
honest-prover equivalence, soundness against arbitrary committed images, and all
completing executions. See [NOTES.md](NOTES.md) for the construction, validation,
credits and research history. No hosted 1110 verdict is claimed.

Build with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

`claim.txt` contains the score. Previous complete certificates remain in Git:
b5063a0 (1124), fb0489b (1125), and 191ba69 (1138).
