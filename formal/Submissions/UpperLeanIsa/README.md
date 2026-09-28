# 1094-cycle leanISA construction

This construction combines two independent one-cycle savings from the 1096 machine:
our centered checksum removes a constant initialization; Luc's unit-11 landing-hint
tie removes an index-pattern initialization. The proved score is
`104 + 87 × 10 + 120 = 1094` cycles, with 191 instructions and 327680 seeded rows.

A bijective index unmasking preserves the exact 440 security tiers. The signature
remains 5504 bits, including the full 128-bit nonce. The competition's security,
memory-size and resource requirements are unchanged.

`Solution.lean` exports the full `Submission.Certificate 1094` and seeded-row bound.
It covers admissibility, strong security, bytecode validity, honest-prover
equivalence, arbitrary committed images and all completing executions.
Clean build, exact challenge comparison, allowed-axiom checking, six arithmetic
regressions and fresh Lean kernel replay all pass. The measured build/export/check
stages total 524.759 seconds locally. The official runner fails closed here
because Landlock is unavailable; hosted verification remains pending.
No optimality claim is made. See [NOTES.md](NOTES.md) for details and full credits.

Build with the pinned dependencies:

```sh
lake build Submissions.UpperLeanIsa.Solution
```
