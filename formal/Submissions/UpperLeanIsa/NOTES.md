# Fused chain binding at 1115 cycles

Claim **1115 cycles**: **125 ordinary instructions + 87 BLAKE2S × 10 + 120 boundary cycles**.
Every completing path executes 212 instructions. The 87 hashes are 85 chain steps, one index,
and one root call. This improves the 1209 reference by 94 cycles (7.78%), the 1149 fused
record by 34 cycles, the recorded 1138 root by 23 cycles, and the unsubmitted 1125 root, from
which this root descends, by 10 cycles. The step from 1125 is one chain hash: the layer drops
from 86 to 85, and a new pre-sign potential keeps the security slope below 1 at layer 85.

The reference is the verified submission by lucemans at
`6363c32ead978b927a23860bfb863dff4ba9987e`:
https://ots.golf/submissions/ae54a7a1c4f0d7c6f00e42030c96e468.
All modules of this root are part of the certificate's import closure.

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
cells `(50 + a, 51 + a)` and the metadata `ONE`. Chains 8..11 use `a = 1..4`, 29..31 use 5..7,
34..36 use 8..10 and 39..41 use 11..13. The cv word `C_a ≠ ONE` separates these steps from
ordinary chain steps, the metadata `ONE` separates them from fused and root queries, the cv
word `C_a ≠ C_14` separates them from the index, and distinct `a` separate the three-dep
parents from each other.

Each binding group's all-zero tuple is excluded, so every accepted signature reconstructs
at least one final binding hash in that group. The acyclic dependency order makes key
generation and reconstruction coherent.

The root is a single hash in group 5. It takes tops 1 and 2 as cv (cells 281, 282), tops 3–6
as message, and `C_1` (cell 51) as metadata. Its output pair is at cells 302 and 303, and its
low half is the public key. Binding propagates through the DAG to all 42 tops.

## Tables, signing, and exact probability bounds

The signature is 42 complete 128-bit words and a 127-bit nonce, totaling 5503 bits. The signer
tries `2^19` nonces and keeps the accepted class of least weight, breaking ties by earliest
trial. A class's weight counts its effective 127-bit indices. Thirteen group tables encode
41 chain digits; the free chain digit completes the total to **85**. The group cost lies in
`[22,85]`, so the free digit lies in `[0,63]`.

The field lengths are `[1024,512,512,512,512,2048,2048,1024,1024,1024,1024,1024,1024]`. Unit 7
has 1020 live values; its last 4 field values are dummies, which no accepted index uses. Units
from 7 on enumerate digits at most 15. Units 8, 9 and 10 have a cost-17 band. An exporter can
run the all-zero tuple only at raw field value 0. `FusionCodec` specifies the exact tuples
and aliases; `FusionTier` and `FusionNumeric` prove their counts and numerical bounds.

There are 21 dyadic class weights `1,2,...,2^20`. The schedule uses
`hp = 2014953938675 / 2^40 / 2^127`, `k1 = 1007477734885 / 2^40 / 2^127`,
`h1 = 568695663674 / 2^40 / 2^127` and `b0 = 916139622403514217087474011998551`. The
normalized security slope is 0.980948 and the signing availability is about 129.9 bits.

The pre-sign potential is `G + Z + Y + (b / 2I) · G₁`, where `G₁` is the `G` mass of the held
classes of weight 1. A fresh index answer whose class is already held does not raise `G`, and
this saving pays for the `Z` increase of every class of weight at least 2. Only the weight-1 tier
keeps a budget term, with the coefficient `h1 / 8`. The slope is
`k1 + (h1 / 8) · max(0, 1 − 2 (2 k1 − hp) / h1)²` in units of `2^-127`, where `h1` bounds the
weight-1 part of `H̄`. The Lean proof uses exact integer counts and
outward-rounded rational certificates, proving signing failure at most `2^-128` and 127-bit
strong unforgeability for the actual adaptive cached-oracle experiment.

## Addresses, constants, and execution

The prologue has 18 straight instructions: the length gate (which also forces `ONE`), `g`,
`C_1 … C_14`, the index hash and `MUL H'_0`. It dispatches at slot 18; slots 19 to 26 are
never-executed pads. The prologue sets no `C_15`:

- The landing product of a block multiplies by `C_p` for its product exponent `p`. When
  `p = 15`, the block multiplies by `C_14` into a scratch cell and then by `C_1`. This occurs
  only at cost 16 of the five shifted units, whose digits are at most 15, so such a block has
  at most one zero digit and the second multiplication takes a padding slot.
- The index hash uses the cv pair `(C_14, GP_13)` at cells 64 and 65 and the metadata `ONE`.
  `GP_13` is the exit target, forced to `g^262143` on every completing run. The cv word `C_14`
  separates the index from ordinary and three-dep steps. This frees `g` as the tag of
  five-dep chain 4, so the 17 tags `C_1 … C_14`, `g`, 5503 and `GP_13` need no extra constant.

Group 0 blocks have `7 + c` slots, group 5 blocks `7 + c` (with the root call), group 6 blocks
`9 + c`, and the other groups `8 + c`. Group regions run from slot 27 through 241721. Free
blocks begin at 255615 with stride 68; the sentinel is 262143. The code and memory tables have
`2^18` and `2^16` rows, respectively, for **327680 seeded rows**.

The cycle accounting is 18 prologue and exit, and 107 block non-hash instructions (125), one
index hash, 85 chain hashes and one root hash (87), and the 120-cycle boundary charge:
`125 + 87 × 10 + 120 = 1115`.

Units 7, 8, 9, 10 and 12 have no cost-0 tuple and multiply `C_(cost − 1)`. The landing seed
is `initialProduct(80,s)`, and `initialProduct(80,s) · C_p = initialProduct(85,s) · C_(p+5)`.
The final exponent is `(12682136550675578873 + 2^60 * (s + sum(group costs))) mod (2^64 - 1)`.
Only total 85 reaches the sentinel; every other total in the range 0..284 lands on a pad or
beyond the program. Frame guards (frames 0 to 13, constants `C_1 … C_14`) reject entry into a
block's middle. The universal cycle theorem quantifies over every admitted memory size, image,
and step count.

The machine executes groups in unit order, but committed memory lets an instruction assert a
relation involving values checked later. Soundness reconstructs those relations in dependency
order. The honest prover first reconstructs all tops, then collects the output pairs and the
root state; repeated oracle queries share cached answers.

## Validation status

`lake build Submissions.UpperLeanIsa.Solution` succeeds, and `#print axioms` on `certificate`
and `seeded_rows` reports only `propext`, `Classical.choice` and `Quot.sound`. The 1149 parent's
hosted check timed out after 1232 seconds; its revision consolidated the length certificates
into `LengthPowers`, `LengthLogValues` and `LengthBounds` and checks the location order through
adjacent pairs. This root keeps those changes. A hosted run still has to confirm the wall-clock
limit.

## Failed directions

- Allowing zero-cost binding tuples breaks binding: a group can disclose all its parent tops
  without executing a hash that authenticates its children.
- Without the cost-17 band, nine binding tables fail the exact gate (slope 1.000959).
- Binding top 11 inside group 6 (so group 6 copies at most two zero tops) needs the tuples
  `(0,0,0,c)` excluded; the exact gate fails (slope 1.0088). Relaxing the binding of group 12
  would pay for it, but the packets then lack two dependency slots.
- Dropping `C_15` by leaving holes in the cost bands fails the gate (slope 1.0186).
- Layer 85 fails the earlier potential `(1 + b/I) · G + Z + Y` for every design searched
  (slope 1.374 on these tables).
- Layer 84 stays out of reach with the new potential: its slope is at least `hp / 2`, and that
  is at least 1.056 for the best layer-84 design found. That is search evidence, not an impossibility
  proof.

## Credits

- The user's 1332-cycle Group3 baseline, developed with Claude Opus 5.5, supplies the grouped
  tables, hinted-landing architecture, and most machine proof structure. It builds on the
  1598-cycle HL-FLAT-A and earlier 85343-cycle leanISA records.
- The R9 generic scheme and security-proof structure were adapted from the public submission
  at [d2dcc9edda216eec46943eab4b5752a670674554](https://github.com/leanEthereum/ots.golf-submissions/tree/d2dcc9edda216eec46943eab4b5752a670674554/formal/Submissions/UpperLeanIsa),
  with rotated chain numbering, ONE padding, and the effective-index budget proof added here.
- `Cache`, `IUB`, `Master`, counting/availability lemmas, and adaptive index-grinding proofs
  inherit the earlier UpperRiscv and leanISA authors' work, including Tom Wambsgans (PR #5)
  and Holindauer with Claude Fable 5.1 (PR #15).
- The field-rescaling model and 1295 plan are retained in `leanisa-frontier/field-opt`.
  The 1295 implementation and proof adaptation were completed with Codex.
- The landing exit is from the 1319-cycle record, prepared with Claude Opus 5.5; its port onto
  the 1295 machine (1294), the root rehoming (1291), the 8-call root (1283), TRIM16 (1282),
  FREE-Z (1281), the 9-call root (1289), rarest-cut signing with the `Tier*` proofs, and the
  1209 machine were prepared with Claude Opus 5.5.
- The layer-87 table search, regenerated tier certificates, fused length-guard port, the
  six-group fused construction, exact layer-86 search, dependency-aware security proof and the
  1149-cycle machine certificate were prepared with Codex.
- The light seventh binding group, the two-call root and the 1138-cycle machine certificate
  were prepared with Claude Opus 5.5.
- The single-call root, the nine binding groups with three-dep packets, the cost-17 band with
  `C_(cost − 1)` landing factors and the 1126-cycle machine certificate were prepared with
  Claude Opus 5.5.
- The removal of `C_15` (split product, index cv `(C_14, GP_13)`), the digit bound 15 with
  the retuned tier certificate, the 1125-cycle machine certificate and the removal of the
  pre-fusion modules were prepared with Claude Opus 5.5.
- The pre-sign potential with the weight-1 budget term, the layer-85 tables and the 1115-cycle
  machine certificate were prepared with Claude Opus 5.5.
