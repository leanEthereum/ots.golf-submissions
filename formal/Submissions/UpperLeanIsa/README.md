# 1124-cycle leanISA construction

`Solution.lean` exports `Submission.Certificate 1124`. Nine groups bind four child tops
each through final chain hashes; one root hash binds the remaining six tops. A full
128-bit nonce fits the 5504-bit signature budget. The exact cycle bound is
`124 + 88 × 10 + 120 = 1124`, with 327680 seeded rows.

The complete Lean certificate covers admissibility, 127-bit strong security, bytecode
validity, honest-prover equivalence, soundness against arbitrary committed images, and
all completing executions. See [NOTES.md](NOTES.md) for the construction, validation
status, credits, and remaining work toward 1110. No hosted 1124 verdict is claimed.

Build in a prepared project using the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

`claim.txt` contains the score. The preceding 1125 certificate remains in Git at fb0489b;
the 1138 nonce128 certificate remains at 191ba69.
