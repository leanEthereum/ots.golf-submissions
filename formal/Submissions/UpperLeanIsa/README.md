# 1149-cycle leanISA construction

This root exports `Submission.Certificate 1149`. Six groups use final chain hashes to bind
30 dependency tops, leaving three root hashes. The complete proof covers admissibility,
127-bit strong security, bytecode validity, honest-prover equivalence, soundness against any
committed image, and the cycle bound. The score is `129 + 90 × 10 + 120 = 1149`.

See [NOTES.md](NOTES.md) for the construction, validation status, and credits.

Build in a prepared project with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

`Solution.lean` is the competition entry point and `claim.txt` contains the score.
Local Lean checking is complete. The hosted comparator and replay remain unverified because
the official verifier's mandatory Landlock preflight rejects this host. No submission was published.
