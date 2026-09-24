# leanISA — 33843 cycles (RT-MX)

This root descends from RT (nconsigny, PR #35, 85343) and RT-128 (PR #36, 49335). It uses all 43
signature words:
- 41 message fields of 7 and 6 bits, aligned to the two message cells;
- two 6-bit checksum digits.

A 6-bit field `d` is stored as the chain digit `e = 64 + d`, so every chain keeps 127 steps. The
security proofs therefore change only by constants. `NOTES.md` has the design, the cost bound,
the executable model and next steps.

- Scheme (`Encoding`): the field layout (`fieldWidth`, `fieldOff`, `digitOff`), injectivity via
  contiguous fields, and a new `digits_incomparable` for the offset checksum digits. Every other
  scheme and security file is RT-128 with 43 chains and 5504-bit signatures.
- Bytecode (`MachineProgram`): `logSize = 16`, `memLog = 16`. It uses:
  - Rice(1) `JUMP` trees on the leaf index (128 or 64 leaves);
  - a 50-node unary `c_hi` tree;
  - aligned ties;
  - a constant zero pair;
  - the checksum identity `Σ E + 64·(E 41 − 64) + E 42 = 5271`, checked in the exponent.
- Cycles (`MachineCycles`): `totalCost E ≤ 33723` on every completing run. The exact worst case
  is 33722 (the all-zero message: 3319 `BLAKE2S`).
- Soundness and faithfulness (`ConstraintMath`, `MachineSound`, `MachineProver`, `MachineHonest`,
  `MachineFaithful`): as in RT-128, with mixed-width packing lemmas for the ties.

Build with `lake build Submissions.UpperLeanIsa.Solution`.

`Checksum.lean` adapts VCVio's
[`HashSig/SLHDSA/WotsChecksum.lean`](https://github.com/Verified-zkEVM/VCVio/blob/25f26bfee60d6700644eb1a69f091091948f15da/HashSig/SLHDSA/WotsChecksum.lean)
(Apache-2.0; Vitalik Buterin, Nicolas Consigny, Alexander Hicks). The scheme, security and
machine proofs derive from the leanISA records of scaraven (PR #31), nconsigny (PR #35) and
lucemans (PR #36), which in turn adapt RISC-V proofs by Tom Wambsgans (PR #5) and Holindauer
(PR #15).
