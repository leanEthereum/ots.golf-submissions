# Fused chain binding at 1126 cycles

Claim **1126 cycles**: **126 ordinary instructions + 88 BLAKE2S × 10 + 120 boundary cycles**.
Every completing path executes 214 instructions. The 88 hashes are 86 chain steps, one index,
and one root call. This improves the 1209 reference by 83 cycles (6.87%), the 1149 fused
record by 23 cycles, and the 1138 root, from which this root descends, by 12 cycles.

The reference is the verified submission by lucemans at
`6363c32ead978b927a23860bfb863dff4ba9987e`:
https://ots.golf/submissions/ae54a7a1c4f0d7c6f00e42030c96e468.
The local 1198 continuation is preserved separately. This construction retains its rarest-cut
signer and much of the machine framework, and proves a new fused dependency DAG and security
reduction. `Fusion*.lean` contains the active construction. Older modules provide shared lemmas
and preserve the earlier proof development.

## Fusing chain and root work

A chain's final hash can include other chain tops in its packet. A chain hash that
reconstruction needs anyway then authenticates those dependency tops. Nine groups work this
way. Five groups use **five-dep** packets: two dependency tops as cv words and three alongside
the current chain word as message words, with metadata that identifies the parent chain.
Four groups use **three-dep** packets: three dependency tops in message words 1–3.

| Unit | Kind | Parent chains | Dependency tops |
| --- | --- | --- | --- |
| 5 | five-dep | 3, 4, 5, 6 | 7, 8, 9, 10, 11 |
| 0 | five-dep | 1, 2, 7 | 14, 15, 16, 19, 20 |
| 7 | five-dep | 14, 15, 16 | 26, 29, 30, 31, 34 |
| 8 | five-dep | 19, 20, 21 | 35, 36, 39, 40, 41 |
| 9 | five-dep | 24, 25, 26 | 12, 13, 0, 17, 18 |
| 6 | three-dep | 8, 9, 10, 11 | 21, 24, 25 |
| 10 | three-dep | 29, 30, 31 | 22, 23, 27 |
| 11 | three-dep | 34, 35, 36 | 28, 32, 33 |
| 12 | three-dep | 39, 40, 41 | 37, 38 (38 twice) |

The first two dependency tops of a five-dep group are its cv pair. Their cells are adjacent:
(289, 290), (269, 270), (285, 286), (277, 278) and (257, 258).

A three-dep final step has the message `[x, d0, d1, d2]`, the cv pair `(C_a, C_(a+1))` at
cells `(50 + a, 51 + a)` and the metadata `ONE`. Each three-dep chain has its own `a`: chains
8..11 use 1..4, 29..31 use 5..7, 34..36 use 8..10 and 39..41 use 11..13. The cv word
`C_a ≠ ONE` separates these steps from ordinary chain steps, the metadata `ONE` separates them
from index, fused and root queries, and distinct `a` separate the three-dep parents from each
other. The three-dep step replaces a hash that the chain executes anyway, so it adds no
instruction.

Each binding group's all-zero tuple is excluded, so every accepted signature reconstructs
at least one final binding hash in that group. The acyclic dependency order makes key
generation and reconstruction coherent. Domain-separation proofs cover ordinary chain steps,
five-dep and three-dep endpoints, index queries, and the root query with their exact bit
strings.

The root is a single hash in group 5. It takes tops 1 and 2 as cv (cells 281, 282), tops 3–6
as message, and `C_1` (cell 51) as metadata. Its output pair is at cells 302 and 303, and its
low half is the public key. Binding propagates through the DAG to all 42 tops.

## Tables, signing, and exact probability bounds

The signature is 42 complete 128-bit words and a 127-bit nonce, totaling 5503 bits. The signer
tries `2^19` nonces and keeps the accepted class of least weight, breaking ties by earliest
trial. A class's weight counts its effective 127-bit indices. Thirteen group tables encode
41 chain digits; the free chain digit completes the total to **86**. The group cost lies in
`[23,86]`, so the free digit lies in `[0,63]`.

Alias multiplicities vary by group and cost band. Every raw field value is live: the field
lengths are `[1024,512,512,512,512,2048,2048,1024,1024,1024,1024,1024,1024]`. Units 8, 9, 10
and 12 have a cost-17 band (digits stay at most 16). An exporter can run the all-zero tuple only
at raw field value 0, so every exporter table has at most one raw value of cost 0.
`FusionCodec` specifies the exact tuples and aliases; `FusionTier` and `FusionNumeric` prove
their counts and numerical bounds.

There are 17 dyadic class weights `1,2,...,2^16`. The schedule uses
`hp = 1455152844958 / 2^40 / 2^127`, `k1 = 727576585389 / 2^40 / 2^127`, and
`b0 = 38095929638710986492724218760267`.
Independent numerical estimates give about 132.81 bits of signing availability and a
normalized security slope of 0.992590. The Lean proof uses exact integer counts and
outward-rounded rational certificates, proving signing failure at most `2^-128` and
127-bit strong unforgeability for the actual adaptive cached-oracle experiment.
Key generation uses at most 1252 abstract compressions; verification uses at most 176.

The security proof normalizes each chain query to the reconstruction's final dependency
context, proves hidden-input and matching-output bounds for the five-dep and three-dep
packets, and extracts a forgery event through the dependency DAG. It covers both successful and
failed signing.

## Addresses, constants, and execution

The memory layout places selected high and low hash halves in adjacent cv cells. Ordinary
position tags use the existing cost constants. Five-dep endpoint tags additionally reuse the
checked signature-length cell (5503) and the forced terminal landing product. Their exact
bits are proved distinct and are matched to the abstract scheme's metadata. The root and all
metadata come from the pool `g, C_1 … C_15`, 5503 and the landing product, so the prologue sets
no extra constant.

The prologue has 19 straight instructions (init, `g`, `C_1 … C_15`, the index hash and
`MUL H'_0`) and dispatches at slot 19; slots 20 to 26 are never-executed pads. The free block
always materializes its top. Group 0 blocks have `7 + c` slots, group 5 blocks `7 + c` (with the
root call), group 6 blocks `9 + c` (group 6 exports its tops and can copy three zero-digit
tops), and the other groups `8 + c`. Group regions run from slot 27 through 243257. Free blocks
begin at 255615 with stride 68; the sentinel is 262143. The code and memory tables have
`2^18` and `2^16` rows, respectively, for **327680 seeded rows**.

The cycle accounting is 19 prologue and exit, and 107 block non-hash instructions (126), one
index hash, 86 chain hashes and one root hash (88), and the 120-cycle boundary charge:
`126 + 88 × 10 + 120 = 1126`.

The landing products multiply `C_cost` per group, except on units 8, 9, 10 and 12. These units
have no cost-0 tuple, so they multiply `C_(cost − 1)` and the product never needs `C_17`. The
landing seed is `initialProduct(82,s)`. Since `initialProduct(82,s) · C_p =
initialProduct(86,s) · C_(p+4)`, the final exponent is
`(11529215046068731897 + 2^60 * (s + sum(group costs))) mod (2^64 - 1)`.
Only total 86 reaches the sentinel; every other total in the range 0..284 lands on a pad or
beyond the program. Frame guards also reject entry into a block's middle.
The universal cycle theorem quantifies over every admitted memory size, image, and step count.

The machine executes groups in unit order, but order does not matter to the proof: committed
memory lets an instruction assert a relation involving values checked later. Soundness
reconstructs those relations in mathematical dependency order. The honest prover first
reconstructs all tops, then collects the complete output pairs and the root state; repeated
oracle queries share cached answers.

## Validation status

The 1149 parent was submitted as
[PR #47](https://github.com/leanEthereum/ots.golf-submissions/pull/47).
[Its hosted check](https://ots.golf/submissions/f9ecc2114da4705241500bb9b239941d)
timed out after 1232 seconds; every submission module had compiled successfully.
Its revision then cut proof-checking work, and this root keeps those changes:

- The 88 chained length-certificate fragments are consolidated into `LengthPowers`,
  `LengthLogValues`, and `LengthBounds`, with sequential elaboration.
- `Earlier` is proved transitive and `locationOrder` checks only adjacent pairs.
  `List.isChain_iff_pairwise` then gives the pairwise ordering theorem, replacing the direct
  check of 196878 pairs.

The 1149 revision measured a clean submission build of 250.279 seconds and a fresh kernel
replay of the exported proof of 278.563 seconds. The 1126 root has one tier fewer than 1149
and one root call. Its local check is `lake build Submissions.UpperLeanIsa.Solution` with
`#print axioms` on `certificate` and `seeded_rows`, which report only `propext`,
`Classical.choice` and `Quot.sound`. Clean-build timing and exported-proof replay for 1126
still have to be measured, and a hosted run has to confirm the wall-clock limit.

Executable research checks on the 1149 parent exercised accepted indices with both free-digit
extremes, three complete signing runs, middle-block landings, incorrect layer totals, and
modified memory cells. Six negative controls showed why allowing an all-zero binding tuple
would leave a dependency unauthenticated. Those tests used a deterministic test oracle; the
Lean proof is the security and universal-correctness evidence.

## Failed directions and remaining obstacles

Allowing zero-cost binding tuples improves the table distribution but breaks binding: a group
can disclose all its parent tops without executing any hash that authenticates its children.
The negative controls reproduce this problem. The current tables exclude all nine origins.

Without the cost-17 band, nine binding tables fail the exact gate (slope 1.000959). Setting
`C_17` in the prologue instead of shifting the landing seed costs one cycle (1127). Eight
binding tables with costs at most 16 give 1128. Two root calls with three-dep packets give
1133. Designs without a root call force an always-active chain and lose about one layer; with
layer 87 they reach at best 1127. Layer 85 fails for every design searched, with a best slope
of 1.293. That is search evidence, not an impossibility proof.

The current score still spends 126 cycles on initialization, index ties, copies, hints, frame
transitions, and landing products. Some uniform padding is part of the constant path bound.
Further work can optimize those operations jointly with table shapes, or search below layer 86
while maintaining the exact availability and strong-security inequalities. The search and this
certificate establish an upper bound, not an optimality lower bound near 1010 or any other value.

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

- This layer-87 table search, regenerated tier certificates, and fused length-guard port were prepared with Codex.

- The six-group fused construction, exact layer-86 search, dependency-aware security proof,
  new address layout, and complete 1149-cycle machine certificate were prepared with Codex.

- The light seventh binding group on chains 39, 40, 41, the two-call root, the (C_1, C_2) light
  cv, and the 1138-cycle machine certificate were prepared with Claude Opus 5.5.

- The single-call root, the nine binding groups with three-dep packets, the cost-17 band with
  `C_(cost − 1)` landing factors and the shifted seed, the retuned tables and tier certificate,
  and the 1126-cycle machine certificate were prepared with Claude Opus 5.5.
