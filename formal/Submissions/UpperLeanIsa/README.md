# leanISA — 1390 cycles (HL-TRI-1390)

This root keeps HL-FLAT-A's security proof structure (42 Winternitz chains, nonce-ground index)
with a 127-bit index: bits `1 … 127` of the low half of the index answer, 41 three-bit digits
and one four-bit digit, on layer 103. Every leanISA query costs two compressions, so the
security constant is `κ' = (19/20)·2^-127` per compression and `κ'·B < B/2^127` still holds
(`NOTES.md` section 0). The 9-call tagged root is unchanged: call 0 hashes tops 0..5, calls
1..7 take the cv pair `(top (5r+1), top (5r+2))` and absorb the low half of the previous state
and three tops, and call 8 takes the full state and top 41. The chains `0, 6, 11, …, 36` keep
the high half of their last step's answer (`Params.hiTop`), so that each cv pair sits in two
adjacent cells. The bytecode lets three chains share one landing:
- 14 groups, one frame and one dispatch per group;
- one tie word per group into the index accumulator; bit 0 of the index cell (the junk bit) is
  a radix-2 digit of group 0, which has 1024 blocks and sets the accumulator to its word;
- one layer factor `g^σ` per group, with `g^2..g^7` precomputed.

Every completing run executes 253 instructions (113 `BLAKE2S`):
`140 + 10·113 + 120 = 1390` cycles. Key generation costs 622 compressions, verification 226.
The tag symbols, the index metadata and the root metadata reuse existing constant cells.

- `MachineProgram`: `logSize = 18`, `memLog = 16`. Entries `BASE g + SP g · rank`. Frame-entry
  `I0` jumps pin every landing, and bodies run in frame 1.
- `MachineRun`, `MachinePath`: every completing run is the forced walk of one layer vector.
- `MachineCycles`: the tie gives `acc_13 = Σ T_g = idx` (group 0's word carries the junk bit),
  and the layer product gives `Σ s = 103`, all hash-free. The run is exactly 253 steps and 1270
  cycles.
- `MachineSound`, `MachineProver`, `MachineHonest`, `MachineFaithful`: as HL-FLAT-A, per group;
  the honest junk digit is bit 0 of the index cell.

Design, the rejected entry-assertion variant, the model and next steps are in `NOTES.md`. The
scheme, security, layer-count and index-grinding proofs are HL-FLAT-A's (credits in `NOTES.md`
section 7). The grouped bytecode and machine proofs were prepared with Claude Opus 5.5.

Build with `lake build Submissions.UpperLeanIsa.Solution`.
