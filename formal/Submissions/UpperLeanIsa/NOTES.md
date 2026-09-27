# Fused chain binding at 1138 cycles

## Local research toward 1110 (2026-09-27)

`Solution.lean` and `claim.txt` still describe the upstream 1138-cycle construction.
There is no 1110-cycle certificate in this checkout. Two independent research helpers
have been compiled with the pinned Lean toolchain:

- `LightRootShape.lean` proves packet-location separation, three-child packet binding,
  acyclic evaluation, and conditional coverage of all 42 chains from one six-word root.
  Twelve groups must each have a positive parent. Constant CV pairs distinguish parent
  coordinates, and metadata distinguishes groups; only existing constants C_1 through
  C_16 are needed. Availability, security, and a concrete machine remain to be proved.
- `Nonce128Budget.lean` proves the budget charging and bounding algebra with a 2^128
  nonce row. At attack budgets at most 2^127, setting the linear slope to hp/2 gives
  an upper slope of 5*hp/8, compared with 3*hp/4 in the current numeric schedule.
  This is not a security theorem. The current nonce is still 127 bits; the proposed
  128-bit nonce fits exactly in the 5504-bit signature limit, but needs a new encoding,
  length gate, signing-row analysis, numeric certificate, and machine proof.

Numerical searches tried 128-bit effective indices, varied field widths, and mixed alias
multiplicities within a cost band. None produced a candidate meeting every security,
availability, and code-size condition. Search scores are floating-point diagnostics.
A weighted acceptance condition accounting for zero-digit copies also needs an efficient
machine checksum: its extra cost-factor initialization cannot be omitted from a cycle claim.

The following notes describe the unchanged certified 1138 construction.

Claim **1138 cycles**: **128 ordinary instructions + 89 BLAKE2S × 10 + 120 boundary cycles**.
Every completing path executes 217 instructions. The 89 hashes are 86 chain steps, one index,
and two root calls. This improves the 1209 reference by 71 cycles (5.87%) and the 1149 fused
record, from which this root descends, by 11 cycles.

The reference is the verified submission by lucemans at
`6363c32ead978b927a23860bfb863dff4ba9987e`:
https://ots.golf/submissions/ae54a7a1c4f0d7c6f00e42030c96e468.
The local 1198 continuation is preserved separately. This construction retains its rarest-cut
signer and much of the machine framework, and proves a new fused dependency DAG and security
reduction. `Fusion*.lean` contains the active construction. Older modules provide shared lemmas
and preserve the earlier proof development.

## Fusing chain and root work

A binding chain's final hash includes five other chain tops in the packet: two as cv words
and three alongside the current chain word as message words. The metadata identifies the
parent chain. A chain hash that reconstruction needs anyway thus authenticates five
dependency tops. Six groups work this way:

| Group | Binding chains | Dependency tops |
| --- | --- | --- |
| 0 | 1, 2, 7 | 14, 15, 16, 19, 20 |
| 1 | 3, 4, 5, 6 | 21, 24, 25, 31, 34 |
| 2 | 8, 9, 10, 11 | 35, 36, 39, 40, 41 |
| 3 | 14, 15, 16 | 12, 13, 0, 17, 18 |
| 4 | 19, 20, 21 | 22, 23, 27, 28, 32 |
| 5 | 24, 25, 26 | 33, 37, 38, 29, 30 |
| 6 (light) | 39, 40, 41 | 7 |

The light group 6 binds top 7, which the 1149 root hashed in a third root call. The final
step of each chain 39, 40, 41 keeps its ordinary shape except for two words. Message word 1
carries top 7 in place of the low tag digit, and the cv pair is `(C_1, C_2)` (cells 51, 52)
in place of `(ONE, g)`. The message is `[x, t7, B, C]` with the metadata `ONE`. The cv word
`C_1 ≠ ONE` separates these steps from ordinary chain steps. The tag digits `(B, C)` at the
final positions 592, 608, 624 are `(2,7)`, `(4,7)` and `(6,7)`, which separates the three
light parents from each other. Top 7 is always materialized at cell 289, because group 0
copies the revealed word there when its digit is zero. The light step replaces a hash that
the chain executes anyway, so it adds no instruction.

Each binding group's all-zero tuple is excluded, so every accepted signature reconstructs
at least one final binding hash in that group. For the light group this is unit 12, whose
table lost its single cost-0 tuple. The acyclic dependency order makes key generation and
reconstruction coherent: it evaluates top 7 before chains 39..41, and those before 8..11.
Domain-separation proofs cover ordinary chain steps, fused endpoints, light endpoints, index
queries, and root queries with their exact bit strings.

The final root uses two hashes. Root 0 takes tops 1 and 2 as cv, and tops 3–6 as message.
Root 1 takes top 26 and the low half of root 0 as cv, and tops 8–11 as message.
Its low half is the public key. Binding propagates through the DAG to all 42 tops.

## Tables, signing, and exact probability bounds

The signature is 42 complete 128-bit words and a 127-bit nonce, totaling 5503 bits. The signer
tries `2^19` nonces and keeps the accepted class of least weight, breaking ties by earliest
trial. A class's weight counts its effective 127-bit indices. Thirteen group tables encode
41 chain digits; the free chain digit completes the total to **86**. The group cost lies in
`[23,86]`, so the free digit lies in `[0,63]`.

Alias multiplicities vary by group and cost band. Live raw field prefixes have lengths
`[1022,512,512,512,512,2047,2047,1023,995,974,969,1024,968]`.
Unused field values reject. The tables are the 1149 tables except that unit 12 drops its
cost-0 tuple. `FusionCodec` specifies the exact tuples and aliases;
`FusionTier` and `FusionNumeric` prove their counts and numerical bounds.

There are 18 dyadic class weights `1,2,...,2^17`. The schedule uses
`hp = 1415907530965 / 2^40 / 2^127`, `k1 = hp/2`, and `b0 = 1`.
Independent numerical estimates give about 133.145 bits of signing availability and a
normalized security slope of 0.9658203. The Lean proof uses exact integer counts and
outward-rounded rational certificates, proving signing failure at most `2^-128` and
127-bit strong unforgeability for the actual adaptive cached-oracle experiment.
Key generation uses at most 1254 abstract compressions; verification uses at most 178.

The security proof normalizes each chain query to the reconstruction's final dependency
context, proves hidden-input and matching-output bounds for the fused and light packets, and
extracts a forgery event through the dependency DAG. It covers both successful and failed
signing.

## Addresses, constants, and execution

The memory layout places selected high and low hash halves in adjacent cv cells. Ordinary
position tags use the existing cost constants. Fused endpoint tags additionally reuse the
checked signature-length cell (5503) and the forced terminal landing product. Their exact
bits are proved distinct and are matched to the abstract scheme's metadata.

The prologue has 24 straight instructions and dispatches at slot 24; slots 25 and 26 are
never-executed pads. The 1149 prologue also set `C_22` for root 2; that constant is gone.
The free block always materializes its top. Group 0 blocks have `7 + c` slots, since the
group no longer hosts a root call. Group regions run from slot 27 through 234288. Free blocks
begin at 255615 with stride 68; the sentinel is 262143. The code and memory tables have
`2^18` and `2^16` rows, respectively, for **327680 seeded rows**.

The cycle accounting is 24 prologue and 104 block non-hash instructions (128), one index hash,
86 chain hashes and two root hashes (89), and the 120-cycle boundary charge:
`128 + 89 × 10 + 120 = 1138`.

The landing seed is `initialProduct(86,s)`. The final exponent is
`(11529215046068731897 + 2^60 * (s + sum(group costs))) mod (2^64 - 1)`.
Only total 86 reaches the sentinel; every other total in the conservative range 0..284
lands on a pad or beyond the program. Frame guards also reject entry into a block's middle.
The universal cycle theorem quantifies over every admitted memory size, image, and step count.

The machine executes group 0 before the light steps of group 12 that read top 7, but order
does not matter to the proof: committed memory lets an instruction assert a relation involving
values checked later. Soundness reconstructs those relations in mathematical dependency order.
The honest prover first reconstructs all tops, then collects the complete output pairs and
root states; repeated oracle queries share cached answers.

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
replay of the exported proof of 278.563 seconds. The 1138 root has the same certificate sizes
and one root call and one adjacent-order pair fewer. Its local check is
`lake build Submissions.UpperLeanIsa.Solution` with `#print axioms` on `certificate`,
`seeded_rows` and `submission`, which report only `propext`, `Classical.choice` and
`Quot.sound`. Clean-build timing and exported-proof replay for 1138 still have to be measured,
and a hosted run has to confirm the wall-clock limit.

Executable research checks on the 1149 parent exercised accepted indices with both free-digit
extremes, three complete signing runs, middle-block landings, incorrect layer totals, and
modified memory cells. Six negative controls showed why allowing an all-zero binding tuple
would leave a dependency unauthenticated. Those tests used a deterministic test oracle; the
Lean proof is the security and universal-correctness evidence.

## Failed directions and remaining obstacles

Allowing zero-cost binding tuples improves the table distribution but breaks binding: a group
can disclose all its parent tops without executing any hash that authenticates its children.
The negative controls reproduce this problem. The current tables exclude all seven origins.

A single light parent does not work. One chain with its own metadata forces that coordinate
to be nonzero, and the exact gate then gives a slope of at least 1.289 at layer 86. Unit 10 is
an equivalent choice of light parents at layer 86. Layer 85 fails for every table searched,
with a best slope of 1.2988. That is search evidence, not an impossibility proof.

The current score still spends 128 cycles on initialization, index ties, copies, hints, frame
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
