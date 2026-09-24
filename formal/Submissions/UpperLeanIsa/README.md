# leanISA — 1422 cycles (HL-TRI-R9)

This root keeps HL-FLAT-A's security proof structure (42 chains of 3-bit and 4-bit digits,
nonce-ground index on layer 106) with a 9-call tagged root: call 0 hashes tops 0..5, calls
1..7 take the cv pair `(top (5r+1), top (5r+2))` and absorb the low half of the previous state
and three tops, and call 8 takes the full state and top 41. The chains `0, 6, 11, …, 36` keep
the high half of their last step's answer (`Params.hiTop`), so that each cv pair sits in two
adjacent cells. The bytecode lets three chains share one landing:
- 14 groups, one frame and one dispatch per group;
- one tie word per group into the index accumulator;
- one layer factor `g^σ` per group, with `g^2..g^7` precomputed.

Every completing run executes 258 instructions (116 `BLAKE2S`):
`142 + 10·116 + 120 = 1422` cycles. Key generation costs 638 compressions, verification 232.
The tag symbols and root metadata reuse existing constant cells.

- `MachineProgram`: `logSize = 18`, `memLog = 16`. Entries `BASE g + SP g · rank`. Frame-entry
  `I0` jumps pin every landing, and bodies run in frame 1.
- `MachineRun`, `MachinePath`: every completing run is the forced walk of one layer vector.
- `MachineCycles`: the tie gives `acc_13 = idx` and the layer product gives `Σ s = 106`, both
  hash-free. The run is exactly 258 steps and 1302 cycles.
- `MachineSound`, `MachineProver`, `MachineHonest`, `MachineFaithful`: as HL-FLAT-A, per group.

Design, the rejected entry-assertion variant, the model and next steps are in `NOTES.md`. The
scheme, security, layer-count and index-grinding proofs are HL-FLAT-A's (credits in `NOTES.md` section 7). The grouped bytecode and machine proofs were prepared with
Claude Opus 5.5.

Build with `lake build Submissions.UpperLeanIsa.Solution`.
