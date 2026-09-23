# Ascending cell grid: 364-cycle candidate

This extends the officially verified 372-cycle dense-dispatch submission (PR #27,
commit 9fe2362), which builds on Alexander Hicks's 377-cycle mixed-width image and
dhsorens's paired dispatch.

Assisted by: Claude Fable 5.1

## What changes

The 372 image expands 24 of its 32 chains: a chain whose wire value is not already
in its 24-byte working cell pays one `ADDI x10, x12, 8` after its first hash. Only
the eight 192-bit chains at the bottom of the payload sit on the cell grid, because
the wide chains run upwards from the payload base while the narrow chains are
relocated downwards from the top, and the two families meet at a 16-byte junction
that costs two full 256-bit root slices.

Here every chain runs in the same direction. The 32 cells are `0x3FFFE0 + 24k` in
execution order, each hash writing its 32 bytes at `0x3FFFD8 + 24k`, eight bytes
below the state. A chain needs no expansion exactly when its wire value starts at
its own cell, and a wire block survives until it is read exactly when it lies at or
above its own cell's state address: the writes of the chains processed so far cover
`[0x3FFFD8, 0x3FFFE0 + 24k)`, and every later block is above that. So the payload
can be permuted freely as long as `wireSlot k ≥ slot k` for every chain.

The signature budget is 672 bytes = 28 cells of 24 bytes. A group of consecutive wire
blocks whose lengths sum to a multiple of 24 places one chain on the grid. With the
152-bit (19-byte) minimum state, only one-chain groups (a 192-bit chain) and
five-chain groups (four 152-bit chains and one 160-bit chain, 96 bytes) pay off, and
12 + 4 such groups fill the budget exactly: sixteen chains on the grid, sixteen
relocated, against eight and twenty-four before.

- Chains 0–3 carry 160-bit states, 4–19 carry 152-bit states, 20–31 carry 192-bit
  states (5376 bits, signature 5504 bits as before).
- The wire holds four 96-byte blocks with chains `4b+4` (on the grid), `b`,
  `4b+5`, `4b+6`, `4b+7`, then chains 20–31 in place. `Payload.index`/`coindex`
  are the two directions of this permutation, checked inverse by kernel decision;
  the verifier applies `permute`, the signer `unpermute`.
- The root reads the low 192 bits of every cell, 768 contiguous bytes from
  `0x3FFFD8`: 6144 bits, twelve compression blocks instead of thirteen.
- The dispatch halfwords move from `0x3FFFE0` (now cell 0) to `0x4002E0`, the first
  bytes after the signature buffer.
- `x11` starts at 160, becomes 152 at pair 2 and 192 at pair 10: two width changes,
  both on pair boundaries.

Rows are `[12,1,8] / [13,9,4] / [14,10,6] / [11,0,15] / [3,5,2] / [7]`, still 16 rows of
128 instructions per group with bodies at offsets 0, 40 and 80. The four pairs whose
left chain is on the grid and whose right chain is relocated need 41 instructions and
take the 48-instruction third slot, as does pair 15 with the root and decision (47).
Pairs 12–15 share a row with pairs 8–11 at displacements −320, −160, −160 and +320
bytes, so the fourth dispatch word again reuses the third word's base constants.
Chain 0 is now relocated, so the first prologue is six instructions and the copies
start at instruction 52.

The proved accounting is:

- Index phase: 40 cycles.
- Chains: 189 hashes + 64 pointer instructions + 16 redirects + 32 dispatch
  instructions + two width changes = 303 cycles.
- Root hash (12 blocks) and decision: 21 cycles.
- Total: 364 cycles; 12340 instructions + 104 data bytes = 49464 bytes.

## Security and availability at 152 bits

The bad-record weight is `δ = 2 · 1025² · 2⁻¹⁵²`, about `0.125 · 2⁻¹²⁸`, and the
signing-failure allowance is `2⁻¹²⁸` in total. The 372 proof spent `0.882 · 2⁻¹²⁸` of it
on the availability term through the bound `numValid ≥ 712 · 2¹⁰⁵`; the true count at
sum 157 is `751.03 · 2¹⁰⁵`, so `Valid.numValid_avail` now certifies `750 · 2¹⁰⁵` and the
miss term becomes `(1 − 750/2²³)^(2²⁰) ≤ 0.482¹²⁸ < 0.74 · 2⁻¹²⁸`, leaving `0.26 · 2⁻¹²⁸`
for `δ ≤ 2⁻¹³⁰`. Strong unforgeability keeps its margin: `2δ < 1036 κ` with the
keygen cost now 1036 (1024 chain hashes and a 12-block root), and verification costs
202 compressions. Chain states of 144 bits would put `δ` near `32 · 2⁻¹²⁸` and are not
admissible under this proof, which is why the narrow width is 152.

## Validation status

`lake build Submissions.UpperRiscv.Solution` passes with the pinned toolchain, and the
exported submission, certificate and image-size theorem use only `propext`,
`Classical.choice` and `Quot.sound`. The layout was first checked by a small model of
the image (block sizes, row capacities, landing addresses below 65536, the
`wireSlot ≥ slot` and commit-disjointness invariants); the Lean image reproduces its
12340-instruction length and the same invariants by decision.

## Rejected directions

- 144-bit states (sixteen wide, sixteen narrow, one width change) fail the
  signing-failure budget as described above.
- A twelve-block root with the record's two-directional layout is impossible: the
  junction between an upward and a downward family always needs two 256-bit slices.
- With the grid but the wire in execution order, on-grid chains must form a suffix
  of the payload and at most twelve fit (368 cycles); the sixteenth on-grid chain
  needs the block permutation.
- Two widths only ({152, 192}) cannot fill 672 bytes with sixteen on-grid chains:
  the relocated deficit of 96 bytes is not a multiple of 5.
- Fewer chains (30 or 31) save expansions and a root block but raise the accepted
  digit sum by more than they save.
