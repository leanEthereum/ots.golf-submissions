# Field-rescaled Group3 with an 8-call root and a landing exit

Claim **1281** cycles: `111` non-hash instructions `+ 105 × 10 + 120`, `steps = 216`.
This is the 1283-cycle design with two trims. TRIM16 (1282): the 55 cost-17 entries of each of
the six (3,10) tables become *dummy* field values that are never accepted, so the machine has no
blocks for them and the prologue no longer sets `C_17`; the first (alias) table regains its
origin. FREE-Z (1281): the free top moves from call 0's cv into call 1's message, so the free
block drops its copy; the first group gets a second block region in a fifteenth frame for the
free digit 0 (see *Root and memory layout*). The
1283 design is the 1291-cycle design with an 8-call root (ROOT8): the last root call carries the
low half of the state after call 6 as its metadata instead of a constant tag, which frees the
ninth call. Chain lengths, the 655 positions, tags, keygen and chain numbering are unchanged
from 1291. The previous records are 1282, 1283, 1291 (rehomed root), 1294, 1295, 1319, 1332, 1598 and
85343.
The contract is pinned at `da1418bfec2a599ac36d035f3a1ec551e73d73a0`, Lean 4.33.1.

## Scheme and raw table interface

The raw hash-index word has 128 bits. The scheme drops its least significant bit and uses
127 effective bits. The first machine table duplicates each effective tuple at adjacent raw
indices; the XOR tie still checks the entire raw index. `IndexBits` proves the exact fibers
of this projection. `MachineTable` proves that the machine digits agree with the effective
scheme digits, while scheme injectivity is stated only over effective indices.

The effective widths are `[9,9,9,9,9,11,11,10,10,10,10,10,10]`; raw widths increase the first
to 10. The base shapes are `(3,9)` without the origin (shape 0, now unused), `(3,9)`,
`(4,11)`, and `(3,10)`; every group uses shape 1, 2 or 3. A (3,10) field value `v ≥ 969` (the
cost-17 band) is a *dummy*; an index with a dummy field (`Group3.dummy`) has free digit
`[gsum = 96]`, so its digit sum `gsum + [gsum = 96]` is never 96. Otherwise the free digit is
`96 - gsum`. Acceptance is exactly: no dummy field and `33 ≤ gsum ≤ 96` (`accepted_iff`). The
bound and injectivity of the digits do not depend on the free digit. The machine has `VF u`
blocks per group (969 for the (3,10) groups), 13312 − 330 raw group entries in all.

There are exactly **30698186487542081244787668213344876** accepted effective indices
(`189.19 × 2^107`, counted with the (3,10) profiles cut at cost 16), at least `188 × 2^107`. Signing draws fresh untried 127-bit nonces for at most `2^19` trials.
The availability proof bounds signing failure by `2^-128`: with `θ = 188`,
`(1 − 188/2^20)^512 ≤ 512/559`, `(512/559)^32 ≤ 0.061` and `0.061^32 · 559/512 ≤ 2^-128`. The signature contains 42
128-bit words and a 127-bit nonce; the loader supplies the nonce cell's zero high bit.

The chain lengths have 655 steps in total. Every accepted verification performs 96 chain
hashes, one index hash, and eight root hashes. Each hash costs two abstract compressions,
giving keygen 1326 and verification 210; signing costs at most `2^20` compressions.

## Security at the effective-index width

The 128-bit chain words retain the original collision bounds. The index-query rate is
`κ = 2^-127`. `StageA` maintains `2 * encCount + budget ≤ 2^127`: every newly cached index
query spends two compressions. `StageB` charges the corresponding adaptive row potential.

The last root call's metadata is a random word, so location separation is no longer syntactic.
A record is *separated* (`Record.Sep`) when the low half of its call-6 answer is none of the
nine constant tags (chain, index, root calls 0..6), and *good* (`Record.Good`) when moreover no
keygen answer other than the last call's has the public key as its low half. `KeygenBridge`
shows key generation is a uniform record up to the records that are not separated (their last
call may repeat a cached query; they are bounded by one). `Security` drops the records that are
not good: their weight is `badW ≤ (9 + 663) / 2^128` (`badW_le`, by resampling one answer).

The targets gain two `extraTargets` sets: the public key's low half at every 896-bit non-index
query other than the honest last call (a candidate last call), and the index metadata at every
query shaped like root call 6 (so a forged last call is never an index query; `root_binding`).
Non-index queries pay at most one hidden charge and three target charges, `4 · 2^-129 = κ` per
compression; index queries are unchanged. The exposed points of a good record hit no target.

`CostPrefix` proves that key generation consumes a fixed positive prefix `K = 1326` of the
experiment budget. `Security.main_bound` bounds success by `badW + (B - K) / 2^127` for
`B ≤ 2^127`, and `badW < K / 2^127` supplies the strict inequality required by the contract.
Larger budgets use the bound of one on every success probability. Signing failure is bounded
by `miss^(2^19 - 1) ≤ 2^-128`, since the keygen cache holds at most one index-shaped entry.
`Group3Security` instantiates the proof and admissibility.

## Field constants and the landing exit

Let `Q = 2^60`, `M = 2^64 - 1`, and `C_c = g^(Q*c)` in the ISA's GF(2^64) subfield.
Because `16*Q ≡ 1 mod M`, `C_16 = g` and `(C_c)^16 = g^c`.
`FieldRescale` proves these identities and injectivity over all costs through 300.

The fifteen landing frames reuse `C_1..C_15` (frames are separated by `Q = 2^60`, and
`15 Q + 2^33 < M`). The 21-slot prologue pins ONE, length, g and
`C_1 … C_15` (`C_16 = g`; no block multiplies by `C_17`), then computes the index and
dispatches (slot 20); slot 21 is a pad.
The frame proofs cover all admitted memory sizes through `2^32` cells.

The free block seeds `g^262143 / C_96 * C_s`; each group multiplies by its own `C_cost`, so the
last product is `GP_13 = g^seedExp t` with `t = s + sum costs ≤ 63 + 13·16` and
`seedExp t = (262137 + Q t) mod M` (`initialProduct_mul`, since `96 Q ≡ 6`). The exit is
`JUMP(ONE, GP_13, ONE)`. The exit table (`MachinePath.seed_table`, `decide +kernel` over
`t ≤ 284`) shows `seedExp t` is the sentinel `262143` only at `t = 96`; the totals `96 − 16j`
(`j = 1 … 6`) land on the pads `262143 − j`, and every other total lands past the bytecode
(`exit_forced`). So a completing run has `s + sum costs = 96`, without any hash-binding
assumption, and the sentinel cell `SET` of the 1295 prologue is saved.

Group regions run from slot 22 through 232544; the first group's frame-14 copy follows at
`232545 … 248360` (`zOff = 232523`). Free blocks start at `255615 + 68*s`, `s<64`. Their
occupied lengths are `s+4`. Total occupied slots are 250632; code capacity is 262144.
The honest memory has 65536 cells, giving 327680 seeded rows.

## Root and memory layout

Call 0 uses cv `(top 38, top 41)` (cells 150/151; `rootInit = top41 ++ top38`) and message
tops 3..6, tag `C_1`. Call 1 uses cv `(top 37, lo(state 0))` (cells 236/237, top 37 directly
below `stCell 0`) and message `[top 0, top 1, top 2, top 7]`, tag `C_2`. Calls `r=2..6` use cv `(top (5r+2), top (5r+3))` and
`[lo(previous), top (5r+4), top (5r+5), top (5r+6)]`, tag `C_(r+1)`. Call 7 uses cv
`(top 39, top 40)`, message tops 8..11, and metadata `lo(state 6)` (the `stCell 6` operand).
The public key is the low half of the last state. `Events.root_binding` walks back from the
public key (the low half of state 0 is now in call 1's cv, `lo_eq_of_rootInput`);
`Events.tops_eq_of_rootInputs` covers the new top placement. The same 15 chains are exported and
the targets are unchanged, so `badW ≤ 672/2^128` as before.

The free top is read by call 1 in group 0's block. It is the signature cell `wCell 0` when the
free digit `s` is 0 and the free chain's output cell `tfCell` otherwise; the block cannot know
`s`, so group 0 has two variants (`body T u v z`, `rt`): `z = false` in frame 1 and `z = true` in
frame 14 (landing hints `hCell 14 = 183`, `h1Cell 14 = 184`, frame constant `C_15`). The free
block of digit `s` ends with `MUL(H_F, g, H'_F)` and `JUMP(ONE, H_F, F_F)` for `F = frG0 s`
(14 if `s = 0`, else 1), so frame isolation forces the variant. The forced walk visits unit `j`
in frame `frU s j`; both variants have the same length and cost.

Group 0 (the alias table, chains 1, 2, 7) is the home of call 1 and runs before group 5
executes call 0: the image is committed, and `MachineSound.root_step` locates each call by
membership, not by execution order. Groups 1..4 and 12 export the cv words
(`exported = {12,13,17,18,…,37,38,39,40,41}`); groups 5 and 6 (the quads) are the homes of calls
0 and 7, groups 7..11 those of calls 2..6. The uniform counts are
`CU = [5,8,8,8,8,6,6,6,6,6,6,6,8]` (sum 87); the free block's count is 4.

Chains `[1,7,12,17,22,27,32,37,38,39]` retain the high half only on their final step. Their
output pairs are positioned so the selected tops share adjacent cv cells with the next chain;
chains 39 and 40 keep their former home cells 231..234, top 38 is written to `(149, 150)` beside
top 41 at 151, and top 37 to `(235, 236)` below `stCell 0`.
Chains 1, 2, 7, 8 keep their cells 156, 157, 160, 161 as in-block home cells (`xhCell`), without
zero-digit copies; only exported tops are copied explicitly. The honest image assigns both halves
of each output, including unused halves, and all eight root states.

`MachineProgram` proves block lengths, uniform costs, and frame isolation. `MachinePath`
extracts the forced path; a landing names a live block (`x < VF u`), so the tie shows the index
has no dummy field (`Compat.digit_free` needs exactly that, and `Compat.live` gives it for the
honest accepted index). `MachineCycles` proves 216 instructions and 1161 execution cycles,
plus the 120-cycle boundary charge. `MachineSound`, `MachineProver`, `MachineHonest`, and
`MachineHonestPath` connect these instructions to the verifier for every fixed oracle table.
`MachineFaithful` proves the contract's honest-execution equivalence. `MachineGroup3` and
`Solution` assemble the concrete clauses.

## Validation and status

The complete local `Solution` build passes from a clean submission build directory. Exported
`certificate`, `seeded_rows` and `submission` depend only on `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `admit` or `native_decide` is used. The local policy checker
(`verifier/check_submission.py upper-leanisa`) accepts the root.

Executable model: `leanisa-frontier/group3/model1281` (`run_model.py --trunc16 --origin
--freecopy`, `budget_1281.py --freecopy`): score 1281, 111 non-hash, 105 BLAKE2S, 216
instructions; support `{(1161, 216)}`; groups end 248361 as in Lean (`zEnd`); 40/40 off-layer
vectors rejected. Without `--freecopy` it gives the 1282 stage (groups end 232545). The 1283 model is `model1283`
(`run_model.py`, `budget_1283.py`):
score 1283, 113 non-hash, 105 BLAKE2S, 218 instructions; support `(cost, steps) =
{(1163, 218)}`; 40/40 off-layer vectors rejected; adversarial completions all accepted by
verify; exit pads `262137 … 262142`. With `--rootb` it reproduces 1291. By default the model
places the (3,10) exporter before the quads; `--lean` uses the Lean group order (the exporter is
group 12, `CU = [5,8,8,8,8,6,6,6,6,6,6,6,8]`) with the same score, support and groups end. The
Lean layout keeps the 1291 chain numbering.

## Credits

- The user's 1332-cycle Group3 baseline, developed with Claude Opus 5.5, supplies the grouped
  tables, hinted-landing architecture, and most machine proof structure. It builds on the
  1598-cycle HL-FLAT-A and earlier 85343-cycle leanISA records.
- The R9 generic scheme and security-proof structure were adapted from the public submission
  at [d2dcc9edda216eec46943eab4b5752a670674554](https://github.com/leanEthereum/ots.golf-submissions/tree/d2dcc9edda216eec46943eab4b5752a670674554/formal/Submissions/UpperLeanIsa),
  with rotated chain numbering, ONE padding, and the effective-index budget proof added here.
- `Cache`, `IUB`, `Master`, counting/availability lemmas, and adaptive index-grinding proofs
  inherit the earlier UpperRiscv and leanISA authors' work, including Tom Wambsgans (PR #5)
  and Holindauer with Claude Fable 5.1 (PR #15), as credited in the preserved baseline.
- The field-rescaling model and 1295 plan are retained in `leanisa-frontier/field-opt`.
  The 1295 implementation and proof adaptation were completed with Codex.
- The landing exit (hash-free exit table, pads below the sentinel) is from the 1319-cycle
  record, prepared with Claude Opus 5.5; its port onto the 1295 machine (1294) was prepared
  with Claude Opus 5.5.
- The root rehoming (1291) was prepared with Claude Opus 5.5.
- The 8-call root with a state-word tag (1283), its good-record security argument and the
  one-entry signing bound were prepared with Claude Opus 5.5.
- TRIM16 (dummy cost-17 entries, 1282) and FREE-Z (the free top in call 1 with a frame-14 variant
  of the first group, 1281) were prepared with Claude Opus 5.5.
