# RISC-V upper bound: 362 cycles with in-place chains

This candidate extends the 372-cycle dense-dispatch record (PR #27, by alexanderlhicks,
itself building on dhsorens's paired-dispatch construction). Index processing, dispatch,
digits and security argument are those of the 372 record; what changes is where the chains
are hashed. **362 = 40 index + 299 chains + 23 root and decision**, on every accepting run
and as the proved bound on every run.

## The idea: hash most chains inside the signature

The scheme is a WOTS-style one-time signature: 32 hash chains, 24 with 160-bit (20-byte)
states and 8 with 192-bit (24-byte) states, one 4-bit digit per chain, accepted digit sum
157. A chain hash reads the state at `x10` and writes a 256-bit (32-byte) answer to the
8-byte aligned buffer at `x12`; the next state is a slice of the answer, and the final
answers of all chains form the root input `R`, whose hash must match the public key.

In the 372 record every 20-byte narrow value sits at a 20-byte stride in the signature,
where no 8-aligned 32-byte buffer can hold it in place, so each narrow chain first
*expands* its value into a separate 24-byte tile and then needs a "redirect"
(`ADDI x10, x12, 8`): 24 redirects in all.

Here the wire order of the signature interleaves narrow and wide values so that most chains
are hashed **in place**, with no expansion and no redirect:

- An in-place chain with wire value at `w` uses the buffer `x12 = w - j` (8-aligned) and
  its next state is answer bytes `[j, j + width)`, which is `w` again, so every hash
  reads and overwrites the same bytes (`Forest.truncOff k = 8 j`). The buffer's other
  `32 - width` bytes (`j` below, the rest above) must be *dead* when the chain runs:
  already-read signature values of earlier chains, the consumed nonce tail, or free memory.
- The repeating 64-byte unit of the signature is `gap (20) | narrow (j = 12) | wide
  (j = 0)`: the "gap" holds the value of a chain that is expanded (and so read) earlier;
  the in-place narrow chain extends 12 bytes down into it and the wide chain 8 bytes up
  into the next unit's gap, so their extensions overwrite exactly the stale gap bytes.
  11 narrow chains (13-23 in execution order; `j` is 12, 4, 0 or 8) and all 8 wide
  chains (24-31) run in place.
- The 13 other narrow chains (0-12) are expanded as before: 11 tiles are stacked above
  the signature at a 24-byte stride and processed top-down, and two tiles sit *in span*
  over the three-value gap `[472, 532)` of their own wire values (chain 11 runs first,
  then chain 12's tile overwrites chain 11's already-read value).
- The bottom wide chain (wire `[0, 24)`, `x12 = -8` relative to the end of the nonce)
  runs **last**. Its buffer spills into the consumed nonce tail and its state ends at the
  start of `R`, so after it `x10` already points at the root input: the root needs
  no `ADDI x10` (one cycle).

Offsets are relative to `0x400040`, the first byte after the 16-byte nonce. `R` is
`[0, 928)`: the 32-byte final answers of the 20 chains whose buffers lie inside it and the
top 24 bytes of the other 12, contiguous and identical for every digit vector. It is 7424
bits, 15 compressions (the record's `R` was 784 bytes, 13 compressions): two root
blocks are the price of the in-place extensions.

**Accounting (every accepted input):** index 40; chains 189 hashes + 64 pointer ADDIs +
**13** redirects + 32 dispatch (LHU + JALR per pair) + 1 width change = 299; root
`ADDI x11, x13, 1920` + 15-cycle ECALL = 16; decision 7. Total 40 + 299 + 23 = 362
(record: 40 + 310 + 22 = 372: -11 redirects, -1 root ADDI, +2 root blocks). The image has
12340 instructions and 104 data bytes (49464 bytes); the record's row groups
`[0,1,2] [3] [8,4,12] [9,5,13] [10,6,14] [11,7,15]` are unchanged, the largest landing
address is 53324.

## What changed in the proof

- **Labelling.** DAG chain `k` is the `k`-th executed chain (narrow chains 0-23, then wide
  chains 24-31) and pair `q` = chains `2q, 2q+1` still reads index lane `q`, so the index,
  digit and dispatch proofs are untouched. The graph cost of the root is 15 (keygen 1039,
  reconstruction 204, verification 205 compressions).
- **Wire order.** `Payload` maps graph-order bits to wire bits through a permutation of
  32-bit units (`unitMap`/`unitUnmap`, inverse laws by `decide +kernel`), since every value
  is 5 or 6 units long.
- **Per-chain tables** over `Fin 32`, all checked by `decide +kernel`: `outAddr` (buffer),
  `wireSlot` (wire value), `expands`, `work` (input address), `truncOff`,
  `work k = outAddr k + truncOff k / 8`, no hash clobbers an unread wire value
  (`unread_disjoint'`) or an earlier chain's committed root slice (`completed_disjoint'`).
- **Root.** `Forest.rootCat` is a table-driven concatenation of the kept answer slices in
  memory order (`rootChain`, `rootStart`, `rootOff`). One generic lemma,
  `Forest.rootCat_extract`, shows that `rootCat c` determines the high 192 bits of every
  chain top; the security proof (`Events.rootCat_slice_inj`, `Values.card_updHash_rc_le`)
  only uses that fact. The machine side assembles `R` piece by piece
  (`MixedRootMemory.completed_part`) and `MixedRoot` drops the pointer update.

**Validation status:** checked by our private CI mirror of the verifier (a GitHub Actions
build of `Submissions.UpperRiscv.Solution` against the pinned contract, the stub-statement
and axiom check, and the pinned comparator); **not yet** by the hosted ots.golf verifier.
Before any Lean was written, a Python emulator of this exact image measured 362 =
40/299/23 on every accepted input (213 accepting runs, including forced extreme digit
vectors) and at most 362 on every reject; a byte-tag replay found no clobbered unread
input, one `R` map for all digit vectors, and at least 24 committed bytes per chain.

The in-place layout was found with Claude Fable 5.1 and implemented in Lean with
Claude Opus 5.5 (Anthropic).

---

## The 372-cycle base construction (text by its authors)

The candidate extends the verified 377-cycle mixed-width construction. It uses
thirty-two four-bit index digits with accepted sum 157, executes 189 chain hashes,
and packs up to three pair bodies into a 128-instruction dispatch row. The signature
still occupies 5504 bits, including a 128-bit nonce, eight 192-bit chain states and
twenty-four 160-bit states.

The coarse digit still selects a row with a 512-byte stride. Bodies start at row
offsets 0, 40 and 80 instructions; the final body may occupy 48 instructions. This
reduces code size enough to use the all-four-bit digit profile with halfword loads
and signed-immediate JALR dispatch. A shared digit mask removes one load, and the
bounded fine/coarse sums permit a single mask after the shifted addition, removing
one AND. REMU 65535 still performs the horizontal sum.

The proved bound is 40 cycles for index processing, 310 for all chain blocks and 22
for the root and decision. The image contains 12338 instructions and 104 data bytes:
49456 bytes. Hash work is 203 compressions; ordinary instructions contribute 169 cycles.

**Validation:** the full exported 372-cycle certificate and image-size theorem pass
the pinned Lean build (8900 jobs), with only the three permitted axioms. Independent
tests cover 6706 transcript cases, seven pinned-machine fixtures and exact image
equality. The PR requests official hosted validation; see `NOTES.md` for the local
production-wrapper infrastructure limitation.

The proof remains in the `Mixed*.lean` modules, with security and availability in the
shared graph/wire modules. `MixedProgram` defines the image; `MixedLanes` proves the
single-mask fold; `MixedCode` locates the packed bodies; `MixedVerifier`, `Candidate`
and `Solution` connect execution to the certified wire algorithm and export the claim.

See `NOTES.md` for layout details, validation and attribution.
Rules: [ots.golf/rules](https://ots.golf/rules).
