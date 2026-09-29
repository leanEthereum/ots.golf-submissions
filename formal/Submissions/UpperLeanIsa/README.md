# 1093-cycle leanISA construction

This revision removes one more constant initialization from the proved 1094
construction. The final group uses the already validated 5504-bit length as its
frame bias; the free stage uses ONE. All other groups retain distinct powers.
The proved bound is `103 + 87 × 10 + 120 = 1093` cycles, with 190 executed instructions
and 327680 seeded rows.

The index classes, 440 security tiers, signing schedule, 5504-bit signature and
full 128-bit nonce are unchanged. Domain labels are relabeled to use powers
through twelve. The full arbitrary-memory guard includes exact field checks for
both fixed biases and every possible first operand below 2^16.

`Solution.lean` exports `Submission.Certificate 1093` and the seeded-row bound.
Clean build, exact challenge comparison, permitted-axiom audit, twelve arithmetic
regression tests, and fresh Lean kernel replay pass locally. The measured
build/export/check stages total 907.680 seconds, with peak sampled process-tree
PSS of 12.383 GiB. Hosted verification remains pending: the official local
runner fails closed because Landlock is unavailable.
See [NOTES.md](NOTES.md) for the proof structure, attribution and further research.

Build with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```
