# 1125-cycle leanISA construction

This root exports `Submission.Certificate 1125`. Nine groups use final chain hashes to bind
dependency tops: five with five-dep packets and four with three-dep packets. One root hash
remains. The complete proof covers admissibility, 127-bit strong security, bytecode validity,
honest-prover equivalence, soundness against any committed image, and the cycle bound. The
score is `125 + 88 × 10 + 120 = 1125`.

See [NOTES.md](NOTES.md) for the construction, validation status, and credits.

Build in a prepared project with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

`Solution.lean` is the competition entry point and `claim.txt` contains the score.
