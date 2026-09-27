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
This local revision expands the nonce to 128 bits and relocates the length gate's alias
cells without adding cycles. Its complete certificate passes local compilation, exact
export comparison, axiom auditing and fresh kernel replay;
the hosted 1138 record used the preceding 127-bit nonce revision. See the notes for
the proof changes and research still needed for 1110.
