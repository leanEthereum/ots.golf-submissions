# 1095-cycle leanISA construction

`Solution.lean` exports the complete `Submission.Certificate 1095` and its
seeded-row bound. The score is `105 + 87 × 10 + 120 = 1095`, with 192 executed
instructions and 327680 seeded rows. The full 128-bit nonce remains within the
5504-bit signature budget.

Split alias multiplicities, mixed four- and five-child binding packets, four
internal child chains, and a linear security potential support layer 85.
All 440 security tiers are connected to exact counts of the actual codec.
Unit 11 ties its index field through its landing hint `g ^ e`: its blocks are
placed at slots whose power of `g` carries the field value, and the index is
decoded through the bijection `unmask`. This removes one ordinary instruction
from every path of the 1096 construction.

The certificate covers admissibility, 127-bit strong security, bytecode validity,
honest-prover equivalence, soundness against arbitrary committed images and all
completing executions. See [NOTES.md](NOTES.md) for the proof map and credits.

The proof builds locally and uses only the permitted axioms. Hosted timing and
acceptance remain unverified. No optimality claim is made.

Build with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```
