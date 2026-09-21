# leanISA baseline — work in progress

This is an unfinished candidate, not a certified competition entry. There is no cycle
claim, `Solution.lean`, or exported `Submission.Certificate` yet.

The candidate uses 34 Winternitz chains: 32 base-256 message digits and two checksum
digits. Each chain value has 128 bits, giving a 4,352-bit signature. Every chain step
includes its chain number and position in an explicit 896-bit oracle query. Root
absorption uses a separate metadata value and a full 256-bit chaining state.

Checked in Lean against core `2d900ae486930689af01a6963d58c574cf17e5f7`:

- Distinct messages have incomparable checksum encodings.
- Signatures have exactly 4,352 bits; oversized raw signatures are rejected.
- Signing never fails, and verification is deterministic.
- Key generation and verification each cost at most 17,408 compressions; signing
  costs at most 17,340. All three fit the current 2²⁰ budgets on every oracle path.

The compression bounds are algorithm bounds, **not leanISA cycle scores**.

Still required:

- Perfect correctness under the cached random oracle, including wire decoding.
- The contract's strong-unforgeability theorem. Its 127-bit target has not yet been proved
  for this construction; the parameters remain provisional until that proof is complete.
- Concrete leanISA bytecode and an honest memory-filling strategy.
- Machine faithfulness, soundness, a universal cycle bound, and the seeded-row bound.
- The exact competition exports and a successful official verifier run.

Build the current modules with the updated trusted core's Lean project and this root
available at `formal/Submissions/UpperLeanIsa`:

```sh
lake build Submissions.UpperLeanIsa.BasicProperties
```

`Checksum.lean` adapts the namespace and module header of VCVio's
[`HashSig/SLHDSA/WotsChecksum.lean`](https://github.com/Verified-zkEVM/VCVio/blob/25f26bfee60d6700644eb1a69f091091948f15da/HashSig/SLHDSA/WotsChecksum.lean),
by Vitalik Buterin, Nicolas Consigny, and Alexander Hicks. Its Apache-2.0 copyright
notice is retained; the repository's `LICENSE` contains the license. The remaining
files were prepared with assistance from Codex.
