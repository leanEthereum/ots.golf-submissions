# 1096-cycle leanISA construction

`Solution.lean` exports the complete `Submission.Certificate 1096` and its
seeded-row bound. The score is `106 + 87 × 10 + 120 = 1096`, with 193 executed
instructions and 327680 seeded rows. The full 128-bit nonce remains within the
5504-bit signature budget.

Split alias multiplicities, mixed four- and five-child binding packets, four
internal child chains, and a linear security potential support layer 85.
All 440 security tiers are connected to exact counts of the actual codec.

The certificate covers admissibility, 127-bit strong security, bytecode validity,
honest-prover equivalence, soundness against arbitrary committed images and all
completing executions. See [NOTES.md](NOTES.md) for the proof map and credits.

The complete proof passes a clean local build, exact challenge comparison,
permitted-axiom checks and fresh Lean kernel replay. The measured build/export/
check stages total about 19 minutes 47 seconds, close to the 20-minute limit;
hosted timing and acceptance remain unverified. No optimality claim is made.

Build with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

The 1110-cycle fallback remains at commit `0c066e7`.
