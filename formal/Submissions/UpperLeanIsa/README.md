# leanISA — 1439 cycles (HL-TRI)

This root keeps HL-FLAT-A's scheme and security proofs unchanged (42 chains of 3-bit and 4-bit
digits, nonce-ground index on layer 106, 10-call tagged root). It replaces the bytecode so that
three chains share one landing:
- 14 groups, one frame and one dispatch per group;
- one tie word per group into the index accumulator;
- one layer factor `g^σ` per group, with `g^2..g^7` precomputed.

Every completing run executes 266 instructions (117 `BLAKE2S`):
`149 + 10·117 + 120 = 1439` cycles.

- `MachineProgram`: `logSize = 18`, `memLog = 16`. Entries `BASE g + SP g · rank`. Frame-entry
  `I0` jumps pin every landing, and bodies run in frame 1.
- `MachineRun`, `MachinePath`: every completing run is the forced walk of one layer vector.
- `MachineCycles`: the tie gives `acc_13 = idx` and the layer product gives `Σ s = 106`, both
  hash-free. The run is exactly 266 steps and 1319 cycles.
- `MachineSound`, `MachineProver`, `MachineHonest`, `MachineFaithful`: as HL-FLAT-A, per group.

Design, the rejected entry-assertion variant, the model and next steps are in `NOTES.md`. The
scheme, security, layer-count and index-grinding proofs are HL-FLAT-A's (credits in `NOTES.md` section 7). The grouped bytecode and machine proofs were prepared with
Claude Opus 5.5.

Build with `lake build Submissions.UpperLeanIsa.Solution`.
