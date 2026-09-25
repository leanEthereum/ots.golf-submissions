# Local 1208-cycle continuation

The full local Lean certificate compiles for 1208 cycles and 206 instructions.
A single checked-length DEREF replaces the separate ONE and signature-length SETs.
The rarest-cut scheme and tables of the verified 1209 source are unchanged.
This local continuation has not been submitted. Original 1209 notes follow.

# Field-rescaled Group3 with rarest-cut signing, aliased tables and a landing exit

Claim **1209** cycles: `109` non-hash instructions `+ 98 × 10 + 120`, `steps = 207`.
This is the 9-call root of the 1289 design (ROOT9, every root call has a constant tag) with two
changes. The signer keeps the *rarest* accepted class of all `2^19` trials (rarest-cut), and the
security proof charges index queries and signing through a certified tier schedule. The group
tables alias the cheap (3,10) tuples at several field values, which raises the accepted mass
enough to lower the layer from 96 to 88: eight fewer chain hashes per verification (−80). The
machine layout, the 9-call root, the frame-14 copy of the first group and the landing exit are
those of the 1289 design. The previous records are 1281, 1282, 1283, 1291 (rehomed root), 1294,
1295, 1319, 1332, 1598 and 85343.
The contract is pinned at `da1418bfec2a599ac36d035f3a1ec551e73d73a0`, Lean 4.33.1.

## Scheme and raw table interface

The raw hash-index word has 128 bits. The scheme drops its least significant bit and uses
127 effective bits. The first machine table duplicates each effective tuple at adjacent raw
indices; the XOR tie still checks the entire raw index. `IndexBits` proves the exact fibers
of this projection. `MachineTable` proves that the machine digits agree with the effective
scheme digits.

The effective widths are `[9,9,9,9,9,11,11,10,10,10,10,10,10]`; raw widths increase the first
to 10. The shapes (`SchemeGroup3`) are `(3,9)` for the first group, `(4,11)` for the quads
(groups 5, 6), `(3,10)` for groups 7..12 and plain `(3,9)` for the exporters (groups 1..4). A
table lists, per cost `c`, the first `nT s c` lex tuples of digit sum `c`, each at `muT s c`
adjacent field values (its *aliases*). The (3,10) tables have multiplicities 2, 8, 2 at costs 1,
2, 3 and multiplicity 1 elsewhere; every other table has multiplicity 1. The last value of each
(3,10) table is a *dummy*; an index with a dummy field gets free digit `[gsum = 88]`, so its digit
sum is never 88. Otherwise the free digit is `88 - gsum`. Acceptance is exactly: no dummy field
and `25 ≤ gsum ≤ 88` (`accepted_iff`). The machine has `VF u` blocks per group,
`[1024, 512, 512, 512, 512, 2048, 2048, 1023 × 6]`, one block per live field value.

A *class* is the digit vector of an accepted index; its *weight* is the number of accepted
indices with that digit vector, the product of the field multiplicities (`weight_eq`). There are
**35402584949483527480931065832952447** accepted effective indices (`218.19 × 2^107`, accepted
mass `A ≈ 2^-12.23`) in 18 tiers of weights `1, 2, 4, …, 2^16, 2^18`
(`TierSchedule.tierA`, `tierN`).

The signature contains 42 128-bit words and a 127-bit nonce; the loader supplies the nonce
cell's zero high bit. The chain lengths have 625 steps in total. Every accepted verification
performs 88 chain hashes, one index hash, and nine root hashes. Each hash costs two abstract
compressions, giving keygen 1268 and verification 196; signing costs exactly `2^20`
compressions.

## Rarest-cut signing

`LayerScheme.signLoop` makes all `2^19` trials at fresh untried nonces (no early stop) and keeps
the accepted trial of least weight; a trial replaces the best only if it is strictly lighter, so
the earliest trial of the minimum tier wins. Signing fails only when no trial is accepted.
`LayerAvailability` bounds the failure by `(1 − A)^(2^19 − 1) ≤ 2^-128` (the keygen cache holds
at most one index-shaped entry); in floating point the value is `2^-157.4`.

## Security argument

The proof follows `.tmp/rarest/tier-proof.md` (conditions §10 with `I = 2^127`, `CR = 1/2`,
non-index rate `2^-128` per compression), generic in the tier schedule:

- `TierCodec`: the class codec and `TierHyp` (the class weights and counts per tier of the
  scheme match a schedule `Sched`, `K = 127`). `Records.Hyp` carries
  `tier : ∃ S, S.Valid ∧ P.TierHyp S` in place of the old `numValid` bounds and `digit_inj`.
- `TierNumeric`: `Sched.Valid`, the exact rational conditions: tier masses, `ȳ_t^(2^19)`
  bounds, the collision slope `H' ≤ hp`, the linear slope `κ₁ ≥ κ_post, SC_f/(2L)`, the knee
  `b0`, `κ_max ≤ 2^-127`, availability and `A ≤ 2^-10`.
- `TierSchedule`: the layer-88 schedule `g1281Sched` (`hp = 1.18976·2^-127`,
  `κ₁ = hp/2 = 0.59488·2^-127`, `b0 = 1`, so `κ_max ≈ 0.892·2^-127`), `ȳ` powers by 19
  outward-rounded squarings at precision `2^256`, and `Group3.tierHyp`, a kernel-evaluated
  count of the accepted field tuples by total cost and multiplicity code.
- `TierRow`, `TierKernel`, `TierSign`: the signer as `signTier` on extended messages, one-trial
  bounds under RowGood (`η₀ = (2^66 + 2^19)/(2^127 − 2^19)`), the winner law by value-function
  induction, and the kernel bounds K1–K5 (fresh and cached winners, self-collision, tail, and
  the average post-sign rate `κ_B = 2^-128 + (p − 2^-127)^+/2 = max(2^-128, p/2)`).
- `TierPotential`: the pre-sign potential `Pre = (1 + b/I)·G + Z + Y` with its charge on a fresh
  index query, and the quadratic budget term `K(b) = κ₁ b + H'/(4I)·((b − b0)^+)^2` with
  `K(b) ≤ b/2^127` for `b ≤ 2^127` (`Kb_le`).
- `TierPsi`: the RowGood supermartingale `Ψ` (exponent `2^-56`, deviation `2^66`), normalized
  so that it starts below `2^-500` and is at least 1 whenever a row with `u ≤ 2^126` fails
  RowGood.
- `TierLoss`: the loss of signing is at most `G + Z + Y + SC_f` (P1).
- `StageA`: `ΦA = hidden + second-preimage + sumW·(Pre + Ψ + K(b))`, its charges, the
  continuation through signing, and the master bound. `StageB`: `ΦB` with the class-dependent
  rate `κ_B` and the `IdxPost` charge `p(c)` per index query. `IdxCharges` gives the index-query
  charge per class. `IdxRho`, `IdxRows`, `RowPotential` and `RowIneq` of the 1281 root are
  removed.
- `Security.main_bound`: `probTrue ≤ 2^-500 + (B − keygenCost)/2^127` for `B ≤ 2^127`;
  `keygenCost = 1268 > 0` gives the strict bound `< B/2^127` (`κ_mul_sub_lt`). Larger budgets use
  the bound of one. `Group3Security` instantiates the proof and admissibility.

The generic `Events`, `Transcript`, `Exposure`, `Targets`, `KeygenBridge`, `CostPrefix` and
`Correctness` are those of the 1289 root, with the index type replaced by classes and the new
signing loop.

## Field constants and the landing exit

Let `Q = 2^60`, `M = 2^64 - 1`, and `C_c = g^(Q*c)` in the ISA's GF(2^64) subfield.
Because `16*Q ≡ 1 mod M`, `C_16 = g` and `(C_c)^16 = g^c`.
`FieldRescale` proves these identities and injectivity over all costs through 300.

The fifteen landing frames reuse `C_1..C_15` (frames are separated by `Q = 2^60`, and
`15 Q + 2^33 < M`). The 21-slot prologue pins ONE, length, g and `C_1 … C_15` (`C_16 = g`;
the costs used are 0 … 16), then computes the index and dispatches (slot 20); slot 21 is a pad.
The frame proofs cover all admitted memory sizes through `2^32` cells.

The free block seeds `g^262143 / C_88 * C_s`; each group multiplies by its own `C_cost`, so the
last product is `GP_13 = g^seedExp t` with `t = s + sum costs` and
`seedExp t = (262143 + Q (t − 88)) mod M`. The exit is `JUMP(ONE, GP_13, ONE)`. The exit table
(`MachinePath.seed_table`, `decide +kernel` over `t ≤ 284`) shows `seedExp t` is the sentinel
`262143` only at `t = 88`; the totals `88 − 16j` (`j = 1 … 5`) land on the pads `262143 − j`,
and every other total lands past the bytecode (`exit_forced`). So a completing run has
`s + sum costs = 88`, without any hash-binding assumption.

Group regions run from slot 22 through 234653 (`gEnd = 234654`); the first group's frame-14
copy follows at `234654 … 250525` (`zOff = 234632`, `zEnd = 250526`). Free blocks start at
`255615 + 68*s`, `s < 64`. Code capacity is 262144. The honest memory has 65536 cells, giving
327680 seeded rows.

## Root and memory layout

Call 0 uses cv `(top 38, top 37)` (cells 150/151; `rootInit = top37 ++ top38`) and message
tops 3..6, tag `C_1`. Call 1 uses the state after call 0 as its cv (`stCell 0`) and message
`[top 0, top 1, top 2, top 7]`, tag `C_2`. Calls `r=2..6` use cv `(top (5r+2), top (5r+3))` and
`[lo(previous), top (5r+4), top (5r+5), top (5r+6)]`, tag `C_(r+1)`. Call 7 uses the state after
call 6 as its cv and message tops 8..11, tag `C_8`; call 8 the state after call 7 as its cv and
message `[lo(state 7), top 39, top 40, top 41]`, tag `C_9`. The public key is the low half of the
last state (`copy (stCell 8) pkCell` ends the last group). `Events.root_binding` walks back from
the public key (`lo_eq_of_rootInput`); `Events.tops_eq_of_rootInputs` covers the top placement.

The free top is read by call 1 in group 0's block. It is the signature cell `wCell 0` when the
free digit `s` is 0 and the free chain's output cell `tfCell` otherwise; the block cannot know
`s`, so group 0 has two variants (`body T u v z`, `rt`): `z = false` in frame 1 and `z = true` in
frame 14 (landing hints `hCell 14 = 183`, `h1Cell 14 = 184`, frame constant `C_15`). The free
block of digit `s` ends with `MUL(H_F, g, H'_F)` and `JUMP(ONE, H_F, F_F)` for `F = frG0 s`
(14 if `s = 0`, else 1), so frame isolation forces the variant. The forced walk visits unit `j`
in frame `frU s j`; both variants have the same length and cost.

Group 0 (the alias table, chains 1, 2, 7) is the home of call 1 and runs before group 5
executes call 0: the image is committed, and `MachineSound.root_step` locates each call by
membership, not by execution order. Groups 1..4 export the cv words; groups 5 and 6 (the quads)
are the homes of calls 0 and 7, groups 7..11 those of calls 2..6, and group 12 that of call 8.
The uniform counts are `CU = [5,8,8,8,8,6,6,6,6,6,6,6,6]` (sum 85); the free block's count is 4.

`MachineProgram` proves block lengths, uniform costs, and frame isolation. `MachinePath`
extracts the forced path; a landing names a live block (`x < VF u`), so the tie shows the index
has no dummy field. `MachineCycles` proves 207 instructions and 1089 execution cycles, plus the
120-cycle boundary charge. `MachineSound`, `MachineProver`, `MachineHonest`, and
`MachineHonestPath` connect these instructions to the verifier for every fixed oracle table.
`MachineFaithful` proves the contract's honest-execution equivalence. `MachineGroup3` and
`Solution` assemble the concrete clauses.

## Validation and status

The local `Solution` build passes (`lake build Submissions.UpperLeanIsa.Solution`, about 75 s
wall for all `UpperLeanIsa` modules on 16 threads). Exported `certificate`, `seeded_rows` and
`submission` depend only on `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `admit`
or `native_decide` is used. The policy checker (`verifier/check_submission.py upper-leanisa`)
has not been re-run on this root.

Executable models: `.tmp/t1281/model/tables/machine.py` (layout, regions, exit pads and the
claim `109 + 10·98 + 120 = 1209` for the layer-88 tables) and
`.tmp/t1281/model/tables/numeric.py` (the tier schedule).

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
- The 9-call root with constant tags on the 1281 machine (1289) was prepared with Claude Opus 5.5.
- Rarest-cut signing (the tier proof, the `Tier*` files and the rewired stage proofs), the
  aliased layer-88 tables with their tier-schedule certificate, and the 1209 machine were
  prepared with Claude Opus 5.5.
