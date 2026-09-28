# 1095-cycle leanISA construction

`Solution.lean` exports the complete `Submission.Certificate 1095` and its
seeded-row bound. The score is `105 + 87 × 10 + 120 = 1095`, with 192 executed
instructions and 327680 seeded rows. The full 128-bit nonce remains within the
5504-bit signature budget.

Split alias multiplicities, mixed four- and five-child binding packets, four
internal child chains, and a linear security potential support layer 85.
All 440 security tiers are connected to exact counts of the actual codec.

The certificate covers admissibility, 127-bit strong security, bytecode validity,
honest-prover equivalence, soundness against arbitrary committed images and all
completing executions. See [NOTES.md](NOTES.md) for the proof map and credits.

The additional cycle is saved by centering the checksum, using a fixed free-stage
frame, and reusing initialized hash constants. Exactly one SET is removed;
padding remains counted. Clean build, exact challenge comparison, allowed-axiom
audit and fresh kernel replay all pass. The measured local build/export/check
stages total 534.3 seconds (clean build 273.2 s; comparison/replay 241.8 s).
The official runner fails closed here because Landlock is unavailable; hosted
timing and acceptance remain unverified. No optimality claim is made.

Build with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

The 1096-cycle fallback remains at commit `055dfe9`; the 1110 ancestor is `0c066e7`.
