# Work in progress: 377-cycle mixed-width candidate

This branch extends dhsorens's 394-cycle construction and the verified 393-cycle
submission by Alexander Hicks, assisted by GPT-6. It is **not ready for submission**.

The 64-bit-nonce, 375-cycle proposal was rejected after identifying a chosen-message
collision attack violating the challenge's quantitative security bound. This branch
retains a 128-bit nonce. It uses 32 chains (eight 192-bit, twenty-four 160-bit),
a 5/3, 5/3, then fourteen 4/4 digit layout with accepted sum 160, reverse processing
of packed narrow states, and a REMU horizontal sum. The wire signature remains 5504 bits.

Checked so far: Wire.certificate proves generic admissibility, 127-bit strong
unforgeability, and a 206-compression bound. ForestVerifier.directVerify_eq proves
the sequential specification matches the wire verifier. MixedProgram proves its
15,412 instructions are admitted and its 61,752-byte image fits the image limit.
The Lean image matches the independently tested Python generator instruction for
instruction and byte for byte. Axiom checks use only propext, Classical.choice,
and Quot.sound.

Still required: universal machine refinement and the 377-cycle bound. Candidate,
Solution, claim.txt, and the old Riscv2Program machine proofs are inherited from
the 393-cycle baseline and have NOT been ported to the mixed construction. Their
presence is not a complete certificate for this branch. Do not submit this snapshot.

The preserved notes below describe the previously verified 393-cycle baseline.

---

# upper-riscv: 393-cycle candidate — mask after folding

This extends dhsorens's 394-cycle paired-dispatch construction and its Lean proof.
The scheme, hash queries, signature format, digit profile, and security argument
are unchanged. The fold becomes `SRLI; ADD; AND` instead of
`SRLI; AND; AND; ADD`, using broadcast mask `0x03fc` instead of `0x01fc`.

For fine sums s<128 and coarse sums t<48, write the packed input as P=4N,
where N's bytes alternate the s and t values. Dividing P+P/256 by four gives
N+N/256. Adjacent byte sums are below 256, so selecting alternating bytes
recovers s+t with no interfering carry. `fold_fields` and `fold_toNat` establish
this in Lean. Index cost falls 43 to 42; total becomes 42+331+20=393.
The image has 12493 instructions and 104 data bytes, totaling 50076 bytes.

Development checks: the standalone arithmetic lemma compiles with only propext
and Quot.sound. A Python instruction interpreter agrees with a separate verifier
on complete oracle transcripts and decisions for 5626 cases, including each invalid
length through 5505 and an oversized input. It also checks 786432 local carry
cases and 100000 random packed words. The candidate image generated in Python
matches all instructions and data exported from the Lean Program definition.
These tests do not replace the full certificate or comparator replay.

The official verifier could not start locally: no configured bounded work
filesystem, and this host has systemd 255 rather than the documented >=257.
The complete local build of Submissions.UpperRiscv.Solution passed, including
the certificate axiom guard (propext, Classical.choice, Quot.sound), and the
source-policy check passed. Comparator replay and the production resource/isolation
check remain outstanding. Do not interpret this infrastructure failure as a proof rejection.

What did not work: omega alone on the full expanded modulo expression was not
sufficient; expressing the sum as base-256 digits exposes the no-carry invariant.
Lowering target 215 to 214 also fails the current availability count.
Next: wider/dense dispatch and cheaper pointer management, with their full setup
costs counted. The historical notes below describe the inherited construction.

Assisted by: GPT-6

---

# upper-riscv: 394 cycles — paired dispatch

## Idea

The 426-cycle image pays five fixed cycles per chain: a four-instruction prologue (advance the
input pointer, point the answer buffer, load the dispatch halfword, jump) and the `+1` hash that
the memory layout forces. The prologue exists because each chain's disclosed position is a
separate jump. Two chains can share one jump if the code the jump lands in already knows *both*
positions — and it can, if the code is replicated: one copy of the block per value of the second
chain's digit.

So block `q < 12` serves the pair of chains `2q` (a five-bit digit `dA`) and `2q + 1` (a four-bit
digit `dB`). The two digits sit in one 16-bit lane of the index answer, at lane bits `2 … 6` and
`10 … 13`, so a single mask leaves `4 · dA + 1024 · dB` in the lane and the stored halfword
`base − 4 dA − 1024 dB` is a complete dispatch address: `1024 dB` selects one of sixteen
64-instruction *copies* of the pair's block (laid out with `dB` decreasing), `4 dA` selects the
hash step inside the copy's 32-step table for chain `2q`. A copy is

```
32 × ECALL            chain 2q, entered at step 31 − dA        dA + 1 cycles
ADDI x10, 24; ADDI x12, x10, −8   move to chain 2q + 1          2
(dB + 1) × ECALL      chain 2q + 1, all of it                   dB + 1
prologue (q + 1)      the next block's prologue, replicated     4
(25 − dB) × nop       padding to 64 instructions                —
```

so a pair costs `8 + dA + dB` cycles against `10 + dA + dB` for two single blocks. The four
copies of a lane word's four pairs are interleaved at 256-instruction strides, which is what makes
the *same* broadcast base serve all four lanes of the word: lane `l` of lane word `g` lands at
`copyStart (4g + l) dB + 4 · (31 − dA) = laneBaseOf g − (4 dA + 1024 dB) + jumpImm q`. The
twelve four-bit digits of the `16 × 5 + 12 × 4` profile are exactly the twelve coarse digits;
the remaining four five-bit chains `24 … 27` keep single 32-step tables (blocks `12 … 15`).

The index phase shrinks as well: four lane words (one per answer word, mask `0x3C7C` for the
three pair words, `0x7C` for the singles word) instead of seven, and one 4-instruction *fold*
`(a &&& m) + ((a >>> 8) &&& m)` with `m = 0x1FC` broadcast, which adds the coarse sums (lane bits
`10 …`, each `< 48`) onto the fine sums (lane bits `2 …`, each `< 128`) so that every lane holds
`4 · (Σ dA + Σ dB)` and the one-`MUL` top-lane sum check is unchanged.

- **Chains 355 → 331.** Twelve pairs at `6 + (dA + 1) + (dB + 1)`, four singles at `4 + (d + 1)`:
  `72 + 16 + 243`.
- **Index 51 → 43.** Loads 7 → 11 (four words, two masks, the fold mask, the `MUL` constant,
  three bases), lanes 31 → 15, fold +4.
- Root and decision 20, unchanged. `43 + 331 + 20 = 394`.

## Proof

- `Valid.lean`: `wid k` is 5 for even `k < 24` and for `24 … 27`, 4 for odd `k < 24`; `jw k`
  places digit `2p` at lane bit 2 and digit `2p + 1` at lane bit 10 of lane `p % 4` of word
  `p / 4`, and digit `24 + l` at lane bit 2 of lane `l` of word 3 (`fieldPos_fine`,
  `fieldPos_coarse`). `numValid_avail` is re-decided for the new digit order; the count is a
  permutation of the 426 profile's, so the availability bound is the same.
- `Program.lean`: the layout (`copyStart`, `singleTableStart`, `landing0`, `laneBaseOf`,
  `jumpImm`), `laneWord g` with `baseReg g`, `fold`, `prologue q`, `switch`, `copyCode q dB`,
  `groupCode`, `pairsCode`, `singleBlock`; 12494 instructions and a 104-byte data image.
- `Lanes.lean`: the mask arithmetic lane by lane (`and_maskPair`, `and_maskSingle`,
  `and_maskFold`) and `fold_toNat`. One `omega` over all eight fields of a word does not
  terminate in useful time; the per-field lemmas `lane*_fine`/`lane*_coarse`/`lane*_fold` and a
  `ring` finish do.
- `IndexLanes.lean`, `IndexArith.lean`: `lanesUpTo 4`, `foldValue`, `top_fold_answer`,
  `lane_halfword` (a lane of `broadcast B − laneWord` is `B − (4 dA + 1024 dB)`), `fine_word`/
  `coarse_word` identifying the lane fields with `fieldDigit`.
- `IndexPhase.lean`: eleven loads, `mainBlock = loadWords ++ lanes ++ fold ++ sumOps` (33
  instructions), `afterIndex_lanes` giving `Ctx.lanes` for the 16 blocks, `indexPhase.length = 49`,
  refinement at 43 cycles.
- `ChainContext.lean`: `dispatch index q = 4 · digit (firstChain q) + 1024 · coarseDigit index q`;
  `Ctx` now also carries the location of the whole image (`Ctx.code`), since a pair block has
  to find its copy in `pairsCode` from the disclosed digits rather than from the code it was
  entered on.
- `ChainPrologue.lean`: `jump_target` for the sixteen blocks, with the `JALR` immediates decided
  in range.
- `ChainBlock.lean`: `copy_located`/`single_located` peel the selected copy or table out of
  `verifier` with `drop_flatMap_fixed` (dropping whole 64-, 256- and 4096-instruction blocks of
  the nested `flatMap`s); `table_refines` runs a chain from its landing step; `pair_refines` is
  prologue, chain `2q`, `switch_refines`, chain `2q + 1`; `single_refines` is prologue and chain.
- `ChainPhase.lean`: induction over the 16 blocks; `blocksCost 0 = 331` through
  `stepsFrom 0 = 243` (`fixedPositions_sum`).
- `Verifier.lean`: `cycleBound = 394`, `verifier.length = 12494` and admissibility by
  `decide +kernel` (about ten seconds). `Solution.lean`: `image_size` is `4 · 12494 + 104 = 50080`.
- `WireAdapter.lean`, `Wire.lean`: core `1bd23e5` added `Admissible.verifyCost`, verification
  within `verifyBudget = 2 ^ 20` compressions (it stops an expensive verifier from inflating the
  budget `B` that `Secure` quantifies over). `WireAdapter.admissible` now takes the typed
  scheme's verification-cost bound and weakens it with `VerifyCostAtMost.mono`; `Wire.lean`
  passes the forest's `255` and `by decide`. A root without the field is rejected with
  `Fields missing: verifyCost` in `WireAdapter.lean` — the error names the adapter, not the
  scheme, because that is where the structure is built.

## Cost

`43 (index) + 331 (chains) + 20 (root and decision) = 394`, image length 12494 (50080 bytes).

## What did not work

- **Pairs of two five-bit digits.** The second digit needs one copy per value: 32 copies of a
  64-instruction block for each of 14 pairs is 28672 instructions, and the dispatch halfword is
  16 bits: every landing address must be below `2^16 + 2047`, so the copies of all pairs have to
  fit in about 64 KB of code. Sixteen copies for twelve pairs (12288 instructions, 48 KB) fit;
  32 copies for fourteen do not. The `16 × 5 + 12 × 4` profile happens to have exactly twelve
  four-bit digits, one coarse digit per pair.
- **Fourteen pairs of `5 + 4`** (a 126-bit index) would remove the four single blocks, but the
  profile fails the availability count at target 215 and the targets that would still win.
- **Three chains per block** needs copies indexed by two digits (`2^9` copies at least): far
  beyond the halfword's reach.
- **192-bit chain values and 28 chains are pinned by alignment.** The HASH output pointer must be
  8-byte aligned and a chain's answer is written eight bytes below its slot, so slots are 24 bytes
  apart and the 5504-bit signature (`128 + 28 · 192`) is what the memory layout can hold; a
  different value width would need a different slot geometry and re-doing the spill argument of
  the 426 notes.
- **The switch (2 cycles per pair) stays.** The second chain's input pointer and answer buffer
  both move by 24 bytes; no single instruction moves both, and the hash call reads them from
  `x10`/`x12` only.

## What is left

- 81 − 8 = 73 fixed cycles outside the chains: prefix 5, index hash 1, length check 2, loads 11,
  lanes 15, fold 4, sum check 4, setup 1, root 2 + 11, decision 7; plus 8 per pair and 4 per single.
- The image is at 48 KB of a 64 KB dispatch window. A denser copy layout (the 25 − dB nops are
  dead) would leave room for two more coarse bits on a few pairs, but the chain profile is pinned by
  the availability count.

---

# upper-riscv: 426 cycles — three fields per lane

## Idea

The 436-cycle image spends 61 cycles on the index phase, 39 of them on eight lane words: for
every lane word one shift, one mask, one accumulation, one subtraction from the broadcast jump
base and one store, because each field is the low bits of one *byte* of the answer and has to be
moved to bits `2 … 6` of a 16-bit lane (`SLLI 2` for the even bytes, `SRLI 6` for the odd ones)
before the mask can leave `4 · field` there.

The fields are the scheme's to place. Put them where the mask wants them: two five-bit fields per
16-bit lane of answer words 0 and 1, at lane bits `2` and `7`, and three four-bit fields per lane
of word 2, at lane bits `2`, `6` and `10`. Then the first extraction pass of every word is a bare
`AND` (its fields already sit at bit 2), and the other passes are one `SRLI` each (by 5, or by 4
and 8) followed by the `AND`. The 28 fields fill seven lane words instead of eight, and the third
mask and the fourth index word are not loaded.

- **Lanes 39 → 31.** Seven lane words: extraction `1 + 2 + 1 + 2 + 1 + 2 + 2 = 11` (was 16),
  seven `SUB`, seven `SD`, six `ADD` (each −1).
- **Loads 9 → 7.** Three index words and two masks (−2).
- Nothing else moves: the chains (355), the root and the decision (20), the prefix, the length
  check, the sum check and the setup are the 436 image's. `61 − 10 = 51`.

The scheme's index is still the 128-bit packing of the 28 digits and the acceptance is still
`Σ digit = 215`; only `pack`'s reading of the answer changes, so the security proof, the
availability table and the chain graph are untouched.

## Proof

- `Valid.lean`: `fieldPos k` gives the bit of digit `k` in the answer through a cell
  decomposition — 29 cells in bit order, each some unread bits (`jw k`) below digit `k` — and
  `fieldDigit` replaces `byteDigit`. `pack`, `pack_lt`, `digit_pack` keep their statements.
- `PackFiber.lean`: the fibre bijection `y ↦ (pack y, junk y)` is the byte proof with the cell
  widths `cw = jw + wid` in place of 8 and the digit on top of the junk instead of below it; the
  cell arithmetic is `Nat.mod_mul_right_div_self`. `PackCount.lean` is unchanged but for two
  argument lists.
- `Program.lean`: `laneWord g` for `g < 7` (`wordIdx`, `shiftOf`, `widthOf`, the two mask
  registers), seven loads, and chain `k`'s halfword at `laneOfChain k`/`laneIdx k`.
- `Lanes.lean`, `IndexLanes.lean`, `IndexArith.lean`: the lane arithmetic over lane words `g`
  rather than pairs `(w, i)`; `laneFld_word` identifies lane `laneIdx k` of lane word
  `laneOfChain k` with `fieldDigit answer k` by `fieldPos_eq`/`wid_eq` (28 kernel-decided
  cases), and `field_sum` reindexes the 7 × 4 lane fields to the 28 digits by expansion.
- `IndexPhase.lean`: the load effect on seven registers, `lanesUpTo 7`, `afterIndex_lanes`
  through `laneFld_word`, `indexPhase.length = 57`, `mainBlock.length = 41`, refinement at 51.
- `ChainContext.lean`, `ChainPrologue.lean`: `laneHalf k ≤ 54`, the lane area is 56 bytes.
- `Solution.lean`: the new export `image_size : submission.image.byteSize < 1048576` (core
  `b38f3c5` requires it; `4 · 886 + 80 = 3624`). A root without it is rejected at the export
  step with `Child exited with 139`, which is the exporter failing on the missing constant, not
  a proof error.
- `Verifier.lean`: `cycleBound = 426`, image length 886; `jumpBase = 6088` still puts every
  `JALR` immediate in range (feasible window `[5537, 6512]` for the shorter code).

## Cost

`51 (index) + 355 (chains) + 20 (root and decision) = 426`, image length 886.

## What did not work

- **The `+1` hash per chain (28 cycles) is forced by the layout, not by security.** Every chain
  writes its 256-bit answer at `slot − 8`, so 64 bits spill into the previous slot's tail, and
  the 5440-bit root input deliberately reads those spill bytes. A chain with digit 0 that made no
  hash would leave its spill bytes holding whatever its neighbour left — the previous top's high
  64 bits, or payload — so the root input would depend on the neighbour's digit, which a fixed
  DAG cannot express. Every chain must hash at least once. The way out, 32-byte slots hashed in
  place (`x10 = x12`, no spill), caps the payload at 21 chains, and 21 chains need target 460:
  `4 · 21 + 460 = 544` chain cycles against 355. Dead.
- **No width profile beats `5n + target = 355`.** Over all `n ≤ 28` and all splits of the 128
  index bits (exhaustive two-value profiles and 20 000 random profiles), the minimal admissible
  `5n + target` is 355, attained only by `16 × 5 + 12 × 4` at target 215; 214 fails at
  `657 · 2^105 < 712 · 2^105`. Fewer chains do not pay for themselves even after crediting a
  smaller root and fewer lane words: `n = 27` needs target 232 (438 in all), `n = 26` target 249 (449).
  The threshold is `p ≥ 1 − exp(−(128 ln 2 − ln(1 − 2⁻⁷)) / 2²⁰) ≈ 8.4617 · 10⁻⁵`.
- **The `SUB` per lane word stays.** The halfword must carry the jump base: `JALR`'s immediate
  reaches `±2048` and the tables sit above `0x1000`, so `x28` has to be `base − 4 · field`, and
  no single RV64IM instruction both masks the junk bits and adds a base. Flipping the digit
  convention to store `4 · (31 − field)` does not help for the same reason.
- **Summing the digits without the `ADD`s** (masking the raw words and folding bytes with one
  `MUL`) costs the same 11 cycles as the accumulation plus the sum check.

## What is left

- The 81 cycles outside the chains: prefix 5, index hash 1, length check 2, loads 7, lanes 31,
  sum check 4, setup 1, root 2 + 11, decision 7. The two cycles of the length check need the
  verifier specified on odd-length queries (see the 437 notes).
- A lane word is `≥ 3` cycles (mask, subtract, store) plus the shift and the accumulation; seven
  are needed for 28 halfwords. Four `LHU` targets per stored word is the ceiling of this dispatch.

---

# upper-riscv: 436 cycles — the public key in the index query

## Idea

The loader places the public key at `0x400000`, the message right after it and the signature
(whose first 128 bits are the nonce) after that, and `x10` starts as the public-key pointer.
Hashing the 512 bits `pk ‖ message ‖ nonce` from that pointer, instead of the 384 bits
`message ‖ nonce` from the message pointer, drops the one instruction that moved `x10`; the
query is still one block. The scheme's index query becomes `H(η ‖ m ‖ pk)`.

## Proof

The index-side security argument (`Rows`, `SignRho`, `RowPotential`, `EncCharges`,
`Potentials`, `StageB`) never looked inside the message: it only used that the encoding inputs
`m ‖ η` are injective in `(m, η)` and that encoding queries are told apart from hash-node queries
by their length. So the message of that argument is now the *extended message* `m ‖ pk`
(`EMessage`, `emsg m pk` in `GScheme.lean`); `swapHalves` is generalised to any message width,
and every row, potential and charge lemma is unchanged up to the type. The bridges are
`GScheme.signLoop`/`verify` (which form `emsg m (publicKey x)` and `emsg m pk`), `sign_eq_map`,
`Potentials.sign_eq`, `Assembly.rest₂_eq_signIdx` (the public key of a record in a fibre is the
fibre's) and the forgery support in `StageB.stB_support`/`events_stB`, where a forgery with the
same encoding input as the signature has the same message because `emsg` is injective.
`Values.len_hashParent_ne_enc` now separates 512 from 192 and 5440. On the machine side the
prefix is five instructions, `prefix_memBits` reads the three loader regions as one 512-bit
value, and chain 0's prologue starts from the public-key pointer (`ADDI x10, x10, 64`).

## Cost

`61 (index) + 355 (chains) + 20 (root and decision) = 436`, image length 896.

---

# upper-riscv: 437 cycles — the same scheme, eight cycles of layout

## Idea

The 445-cycle image is the bare-chain scheme; nothing in the scheme graph or the security
argument moves here except one constant. The eight cycles come from the machine layout and the
availability threshold.

- **Target 215 instead of 216 (−1).** The sum of the 28 fields is the number of chain hash
  steps, and the availability bound is what fixes it. `compW wid 28 215 ≥ 712 · 2^105` indices
  are accepted, so a fresh index misses with probability at most `1 − 712/2^23`, and the block
  bound `miss^8192 ≤ 0.4995` gives `miss^(2^20) ≤ 0.882 · 2^-128` — with `δ ≤ 2^-135` this is
  still under the `2^-128` failure allowance. (The bound is tight in the sense that 214 fails:
  `compW wid 28 214` is about `657 · 2^105` and the true failure probability is near `2^-118`.)
  The check `numValid_le_half`/`two_numValid_le` is the only place the count enters the security
  side; `paperRowHyp` takes the availability count as a hypothesis, so the potential files are
  untouched.
- **Hash the index query in place (−3).** The loader places the message at `0x400010` and the
  signature, whose first 128 bits are the nonce, right after it at `0x400030`, so the 384 bits
  `message ‖ nonce` are already contiguous. The scheme's index query is
  `H(swapHalves (m ‖ η))` where `swapHalves` moves the message to the low half; it is a
  bijection with explicit inverse (`swapBack`), which is all `SignIdx`/`Reconstruct` need. The
  prefix is now seven instructions — no copy of the nonce and message to the data area — and
  `x10` keeps pointing at the message through the index phase.
- **Lanes below the signature, addressed from the message pointer (−0, but frees `x29`).** The
  eight lane words are stored at `0x3FFFF8 + 8j` with `SD` relative to `x10 = 0x400010`; the
  chain prologue then loads its jump halfword relative to its own answer buffer
  `x12 = slot − 8` (`LHU x28, x12, lane − out`), so no register has to hold the data base and
  the `ADDI x29` of the old setup is gone (−1).
- **Chain 0 starts from the message pointer (−1).** After the index phase `x10 = 0x400010`; the
  slot of chain 0 is `0x400040`, so chain 0's prologue is `ADDI x10, x10, 48` and the old
  `ADDI x10, x9, −24` of the setup disappears. The prologue immediates are `48` for chain 0 and
  `24` otherwise (`prevInput k`).
- **The root answer goes where chain 27 left `x12` (−1).** The root only needs `x10` (region)
  and `x11` (5440); `x12` still points eight bytes below the last slot, which is a valid, aligned
  output range that overlaps only the region already read. The decision reads the answer from
  there. `rootLin` is two instructions.
- **No payload register (−1).** The root pointer `sig + 8` is 656 bytes below the last slot,
  where `x10` stands after chain 27, so `ADDI x10, x10, −656` replaces `ADDI x10, x9, −8` and
  the prefix no longer sets `x9`.
- **Cost.** `62 (index) + Σ_k (4 + field_k + 1) + 20 (root) = 62 + 112 + 243 + 20 = 437`.
  Image length 897.

## Proof changes

`Valid.lean` (target 215, `numValid_avail : 712 · 2^105 ≤ numValid`), `Availability.lean`
(the sharper Bernoulli block bound and the `0.882 · 2^-128 + 2^-135 ≤ 2^-128` arithmetic),
`GScheme.lean`/`SignIdx.lean`/`Reconstruct.lean`/`Correctness.lean` (`swapHalves`, its inverse
and injectivity, the index query in the new order), `Program.lean`, `IndexLanes.lean` (lane
stores relative to `x10`), `IndexPhase.lean` (in-place index hash: `prefix_memBits` reads
`swapHalves (m ++ nonce)` straight from the loader's layout; one-instruction setup; the frame
now excludes the 64 lane bytes below the signature), `ChainContext.lean` (`Ctx` without the data
register; `prevInput`), `ChainPrologue.lean` (`prologue_step0` for the two immediates,
`lane_offset` relative to the answer buffer), `ChainBlock.lean` (`ChainsInv.out` carries the
last answer buffer to the root), `RootPhase.lean` (`rootOut = slotAddr 27 − 8`, the root pointer from `ChainsInv.input`),
`Verifier.lean` (`cycleBound = 437`).

## What is left

- Prologue 4 × 28 = 112: both pointer moves are needed (the hash reads `x10` and writes `x12`,
  and the two must differ by eight), the `LHU` and the `JALR` are the dispatch. A layout where the
  same `x12` serves two chains would need the answer of chain `k` to be chain `k+1`'s input
  buffer, which the payload order forbids.
- Lanes 39: eight words × (shift, mask, add, sub, store) minus one; the `SUB` from the broadcast
  jump base is what makes the halfword a `JALR` target, so it cannot be merged into the mask.
- Root 11 blocks and 7 decision cycles are fixed by the 5440-bit root and the two-word compare.
- Target 215 is the floor for this index distribution; a differently shaped index (non-uniform
  field widths) changes `compW` and might allow 214 with the same 5504-bit signature.
- Two more cycles are conceivable but need the scheme's verifier to be specified on signatures
  of every length: if the index length were `x13 ^ 5888` and the root length `x13 ^ 192`, the
  length check (`LD` + `BEQ`) could go, but the Lean verifier would then have to make the same
  odd-length queries on wrong-length inputs, and the security proof would have to charge
  root-preimage events for every query length.

---

# upper-riscv: 445 cycles — bare chains

## Idea

The previous submissions (693, then 687 under the expanded keygen budget) spent two cycles per
hash step: a `SH` writing a level tag into the chain input's header, then the `ECALL`. The tag
existed only for the security proof, which mapped every 192-bit chain query to a unique node
`(k, t)` through `decodeHdr` and charged one target per query. The earlier notes estimated that
dropping the tag would need "a genuinely sharper argument" because the per-query bound had no
slack. It does not: the slack comes from the *width* of the values, not from the analysis.

- **Widen the chain values from 128 to 192 bits and drop headers and tags entirely.** A chain
  input is now the bare 192-bit value; the chain step keeps the high 192 bits of the 256-bit
  answer. A fresh 192-bit query is a candidate second preimage for *all* 896 chain hash nodes,
  but each is matched on 192 bits, so the union bound costs `896 · 2^-192 ≈ 2^-182 ≪ 2^-128`
  (`spr_charge`). The old zero-slack bound charged `ε = 2^-128` per query for a single target;
  the same `ε` now covers all targets with room to spare. Nothing about the potential argument
  changes: `Potentials`, `RowPotential`, `StageB` and `Assembly` are the old files.
- **What the proof loses without tags is uniqueness, not probability.** Two things in the old
  proof silently used that distinct keygen points had distinct tags: `pointOf_inj_left` (the
  keygen cache is a function of the point) and `not_spr_kc` (an honest output never sits at a
  foreign point). Both are now *events* about the honest record — `DistinctRec` and
  `NoOutCollision`, packaged as `GoodRec` — bounded by resampling one coordinate at a time
  (`GoodRec.lean`): `δ = 2 · 897² · 2^-192 ≈ 2^-171`. Key generation is analysed as a real
  cache-reusing run (`E_run_keygen_le` adds an indicator for non-distinct points), and the bad
  records are given up at once in `Assembly.main_bound`: `probTrue ≤ 2ε(B − 907) + 2δ`, which is
  below `B/2^127` because `2δ < 907 · 2^-127` with ~50 bits to spare.
- **The cut nodes are the chain inputs, not the values above them**, so the exposed-cache
  coupling (`fExp`) had to be made canonical (a chosen exposed node per point) to stay
  resampling-invariant on records that are not good; on good records it is the keygen cache.
- **Byte fields instead of nibbles.** With 192-bit values a signature holds 28 values
  (`28 · 192 + 128 = 5504`, the maximum). The index reads its field `k` as the low 5 (k < 16) or
  4 (16 ≤ k < 28) bits of byte `k` of the answer, packed into a 128-bit index; a field is
  extracted into a 16-bit lane with one shift and one mask (`0x7C`/`0x3C` broadcast, `0x003C003C`
  for the last word), so the eight lane words cost 39 instructions. Target 216 gives
  `compW wid 28 216 ≥ 729 · 2^105` accepted indices, the same availability threshold as before;
  the block bound was sharpened to `miss^8192 ≤ 0.493` so that `miss^(2^20) ≤ 2^-129` leaves room
  for `δ`.
- **In-place hashing is impossible, hashing eight bytes below is free.** Hashing a 24-byte slot
  with the 32-byte answer written *on* it spills eight bytes into the next slot, which still holds
  an undisclosed value if chains run upward, while the reader (node order = payload order) forces
  chains to run upward. Writing the answer at `slot − 8` instead spills only into the tail of the
  previous chain's final answer: its high 192 bits (the next input) land exactly on the slot, and
  the root then reads the 680 bytes from `sig + 8` — the low 192 bits of every top and the full
  top of chain 27 — with no copy. `x12 = x10 − 8` is one `ADDI` in the prologue, which otherwise
  only advances `x10` by 24 and loads the jump target. Chain 0's spill lands on the second half of
  the nonce, already consumed.
- **Cost.** `68 (index) + Σ_k (4 + field_k + 1) + 21 (root) = 68 + 112 + 244 + 21 = 445`. The
  root hash is 5440 bits, eleven compressions (down from twelve).

## What is left

- The chain prologue (4 cycles × 28 = 112) is now a quarter of the total. Chains with more levels
  would trade prologues for hash steps one for one, so the optimum is where `4 + (field + 1)`
  per chain is balanced against the number of chains a 5504-bit signature can hold; with 192-bit
  values that is 28 chains, fixed by the signature cap.
- The index phase (68) is dominated by the eight lane words (39). A fused mask that keeps two
  fields per lane, or a single 64-bit multiply-and-shift field sum, could shave a dozen cycles.
- The keygen budget is now `2^20`; nothing here uses it (907 compressions).

---

# upper-riscv: 687 cycles

## Idea

The 693-cycle image spends 70 cycles on the index phase, `9 + 2 · nibble` per chain (602) and 21
on the root and decision. Each chain step is `SH x12, tag, -2; ECALL`: the store puts a 16-bit
level tag into the top halfword of the chain header, so that the 192-bit chain input
`header ‖ value` names its node `(chain, level)`. The fifteen tags must be pairwise distinct, and
eight of them were values that happen to sit in registers after the index phase; the other seven
cost one `ADDI` each in `levelSetup`.

**Widen the tag field.** A `SW x12, tag, -4` costs the same cycle as the `SH`, but a 32-bit tag is
the low 32 bits of the register, and many more registers have pairwise distinct known low words:

| register | low 32 bits | why it is known |
|---|---|---|
| `x0` | 0 | zero (last level, so the final header is the root's) |
| `x5` | 1 | HASH call number |
| `x11` | 192 | chain input length |
| `x9` | `0x400040` | payload cursor |
| `x13` | 4224 | checked signature length |
| `x22` | `0x00780078` | lane mask `0x0078007800780078` |
| `x23` | `0x00010001` | lane-sum multiplier (distinct from `x5` only at 32 bits) |
| `x24`, `x25` | `0x16621662`, `0x20222022` | broadcast jump bases |
| `x2` | `0x01000000` | the loader's stack top, never written by the image |
| `x1` | 1256 | the sum comparator `8 · 157` (see below) |
| `x12`, `x10` | `slotAddr k`, `slotAddr k - 8` | the chain's own HASH pointers |
| `x14` | `4412 + 156 k` | the prologue's `JALR x14, x28, imm` return address |
| `x3` | 2 | the one remaining `ADDI` |

Three tags depend on the chain (`x12`, `x10`, `x14`); the header is
`slotAddr k + levVal k t · 2^32` and `hdrNat_injective` still recovers `(k, t)`: the low 32 bits
give the chain, the high 32 bits the level within it. The `JALR` return address is free because
the prologue's jump already exists; its `rd` was `x0`.

**Let the sum comparator be a tag.** The sum check was `MUL; SRLI 48; XORI 1256; BEQ x27, x0`.
Loading the comparator instead, `ADDI x1, x0, 1256; MUL; SRLI 48; BEQ x27, x1`, costs the same
four cycles but leaves 1256 in `x1` for the rest of the run, which is one tag fewer to set up.

## Result

`levelSetup` shrinks from eight instructions to two (`ADDI x3, x0, 2; ADDI x11, x0, 192`): the
index phase costs **64** cycles, the total **687** (`64 + 602 + 21`), image length 1331. Nothing
else changed: same scheme graph, same 32 chains × 15, same target 157, same 4224-bit signature,
same root input. The security proof only reads the header through `Flat.hdrNat`, `hdrNat_lt` and
`hdrNat_injective`, whose statements are unchanged, so `Names/Values/Events/Resample/StageB` were
rebuilt but not edited. The machine proof changes are in `Constants`, `Program`,
`ChainContext` (`Ctx.levels` covers only the twelve fixed registers), `ChainSteps` (`StepInv`
carries `x14`; `StepInv.tag` assembles all fifteen tags), `ChainBlock` (`JALR` with `rd = x14`),
`IndexPhase`, `MachineFacts` (word-store lemmas) and `BlockExecution` (`SW` is straight-line).

Official verifier: `python3 .contract/verifier/verify.py upper-riscv --source .`. This
WSL2 development host cannot start the judge's systemd/Landlock sandbox (systemd 249, no
securityfs), so the same `verify.py` pipeline was run through comparator's development shim, as
on macOS: policy checks, staging over the trusted tree, warm `.lake` clone, stub rendering,
comparator with statement comparison, axiom audit and kernel replay →
`verified: track=upper-riscv claim=687`, comparator exit 0, in 1642 s unsandboxed on a machine
about three times slower than the hosted judge (whose run of the 693 root took 388 s).

## What did not work, and what is left

- **A fifteenth free tag.** Everything else with a known low word is a duplicate: `x6` (the
  loaded 4224 equals `x13`), `x27` after the check (equals `x1`), the zero registers, and
  `x26`/`x28`/`x20`/`x21`/`x30`/`x31` are input-dependent. A tag must be a function of `(k, t)`
  only, so the nibble-dependent jump target `x28` is out.
- **The index phase is otherwise tight for this dispatch.** The copy of the nonce is forced by the
  protected index `H(m ++ η)` (nonce in the low bits, i.e. below the message in memory). The
  eight lane words (shift, mask, subtract, store) are the cheapest way found to give 32 chains a
  16-bit `jumpBase - 8·nibble` each, and their seven `ADD`s are the cheapest nibble sum given
  that the masked words exist anyway; SWAR byte-lane sums cost more once the 16-bit fold and
  masks are counted. Two jump bases are forced by the 4992-byte span of the chain tables.
- **The prologue stays at nine.** The HASH ABI needs `x10 = x12 - 8` for in-place chaining, so two
  pointer updates; the disclosed word must be copied because the signature stride (16) leaves no
  room for the 32-byte output and the header; a constant-scratch variant saves the pointer updates
  but pays four to move the top into the root input. Using the `JALR` return address as the slot
  pointer would put the slots at the 156-byte code stride and inflate the root input.
- **Next single cycle: the root's `ADDI x10`.** After chain 31 the input pointer sits at the top
  of the slot region while the root input starts at the bottom. Taking the chain value from the
  *high* half of the hash output, processing slots downward and reading the root input as
  `value ‖ header` pairs (6144 bits, still 12 compressions) would leave `x10` already at the root
  input; it needs the low-half `trunc` replaced throughout `Values/Events` and a new root format,
  for one cycle.
- **The big prizes are unchanged** from the previous notes: dropping the per-step tag store
  (about 157 cycles) needs the security potential re-derived with a level-split second-preimage
  charge; wide chain states (about 70) need a full redesign.


## Expanded key-generation budget

Revalidation under the `2^20` key-generation limit. Only the key-generation
admissibility bound changes; the construction and verification score are unchanged.
