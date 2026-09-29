# 1089-cycle leanISA construction

`Solution.lean` exports the complete `Submission.Certificate 1089` and the
seeded-row bound. Three landing hints and a free-last execution order reduce
the completed 1093 construction by four ordinary instructions.

The bound is `99 + 87 × 10 + 120 = 1089` cycles: 186 executed instructions and
327680 seeded rows. The certificate includes scheme admissibility and security,
honest execution, soundness for every admissible committed memory image, and
the universal execution cost. The signature has 5504 bits and a full 128-bit nonce.

Clean build, exact challenge comparison, permitted-axiom audit and fresh Lean
kernel replay pass with Lean 4.33.1. The measured stages total 1158.334 seconds.
Receipts are in `leanisa-sub1090-evidence/certificate1089/`. Hosted verification
remains pending: the official local runner requires Landlock, which is unavailable.
See [NOTES.md](NOTES.md) for the construction, proof map and continuation notes.

Build with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```
