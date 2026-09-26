# 1138-cycle leanISA construction

This root exports `Submission.Certificate 1138`. Six groups use final chain hashes to bind
30 dependency tops. A light seventh group binds top 7 through the final steps of chains
39, 40 and 41, leaving two root hashes. The complete proof covers admissibility,
127-bit strong security, bytecode validity, honest-prover equivalence, soundness against any
committed image, and the cycle bound. The score is `128 + 89 × 10 + 120 = 1138`.

See [NOTES.md](NOTES.md) for the construction, validation status, and credits.

Build in a prepared project with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

`Solution.lean` is the competition entry point and `claim.txt` contains the score.
The root keeps the 1149 revision's consolidated length certificates and adjacent ordering
checks. Clean-build timing and a hosted run for 1138 remain to be measured.
