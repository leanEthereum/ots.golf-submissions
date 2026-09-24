# leanISA — 49335 cycles (RT-128)

This root ports the 85343-cycle RT record (PR #35) from base-256 to base-128 Winternitz. There are
39 chains of 127 steps and 4992-bit signatures. The proof architecture and the forced-dispatch
bytecode design are unchanged. `NOTES.md` has the design, the cost bound and next steps.

- Scheme (`Encoding`, `Algorithms`, `Wire`, `Resources`, `Correctness`, `Security` and its
  dependencies, `KeygenBridge`): RT's scheme and proofs with base-128 constants.
- Bytecode (`MachineProgram`): `logSize = 16`, `memLog = 16`, Rice(1) `JUMP` trees, a unary
  `c_hi` tree, a straddling tie for digit 18, and the checksum in the exponent.
- Cycles (`MachineCycles`): `totalCost E ≤ 49215` on every completing run. The exact worst case
  is 49214 (the all-zero message: 4865 `BLAKE2S`).
- Soundness and faithfulness (`ConstraintMath`, `MachineSound`, `MachineProver`, `MachineHonest`,
  `MachineFaithful`): as in RT, with generalized bit-packing lemmas for the 7-bit tie.

Build with `lake build Submissions.UpperLeanIsa.Solution`.

`Checksum.lean` adapts VCVio's
[`HashSig/SLHDSA/WotsChecksum.lean`](https://github.com/Verified-zkEVM/VCVio/blob/25f26bfee60d6700644eb1a69f091091948f15da/HashSig/SLHDSA/WotsChecksum.lean)
(Apache-2.0; Vitalik Buterin, Nicolas Consigny, Alexander Hicks). The scheme, security and
machine proofs derive from the leanISA records of scaraven (PR #31) and nconsigny (PR #35), which
in turn adapt RISC-V proofs by Tom Wambsgans (PR #5) and Holindauer (PR #15).
