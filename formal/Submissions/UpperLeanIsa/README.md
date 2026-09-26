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
The original PR #47 check timed out after compilation. This revision consolidates the
length certificates and replaces the quadratic ordering check with adjacent checks.
The clean build, exported-statement comparison, axiom checks and fresh kernel replay pass
locally. The 1149-cycle program is unchanged; hosted timing remains to be confirmed.
