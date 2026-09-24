# leanISA — 1598 cycles (HL-FLAT-A)

Replaces the 85343-cycle Winternitz record with a one-layer hypercube scheme and a
straight-line bytecode whose every completing run costs exactly
`308 + 10·117 + 120 = 1598` cycles (425 instructions, 117 `BLAKE2S`).

- **Scheme** (`SchemeFlat`, `Layer*`): 42 chains of 128-bit words, widths 3 (chains 0..39,
  length 8) and 4 (chains 40, 41, length 16). A fresh uniform 128-bit nonce is ground until
  the 128-bit index `H(m, pk, η)` has digits on layer 106; the signature is 42 words plus the
  nonce, 5504 bits. Chain steps, the index and the 10 root calls are separated by metadata and
  tags. Keygen 640, sign `2^20`, verify 234 compressions.
- **Security** (`Records` … `Security`, `FlatHyp`, `FlatSecurity`): generic in `P : Params`
  under `P.Hyp`; `Pr ≤ B/2^128 < B/2^127`. The index-grinding analysis is ported from UpperRiscv.
- **Bytecode** (`MachineProgram`): `logSize = 18`, `memLog = 16`, hinted-landing dispatch with
  digit-independent block costs, so `steps = 425` is constant.
- **Machine proofs**: `MachineRun`/`MachinePath` (every completing run is one path),
  `MachineCycles` (exponent identity `Σ s = 106`), `MachineSound`, `MachineProver`,
  `MachineHonest`, `MachineFaithful`. `seededRows = 2^18 + 2^16 < 2^20`.

Build with `lake build Submissions.UpperLeanIsa.Solution`. Design, model and credits: `NOTES.md`.
