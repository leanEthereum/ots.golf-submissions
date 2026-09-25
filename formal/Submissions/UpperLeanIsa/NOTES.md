# Fused chain binding at 1149 cycles

Claim **1149 cycles**: **129 ordinary instructions + 90 BLAKE2S × 10 + 120 boundary cycles**.
Every completing path executes 219 instructions. The 90 hashes are 86 chain steps, one index,
and three root calls. This improves the 1209 reference by 60 cycles (4.96%).

The reference is the verified submission by lucemans at
`6363c32ead978b927a23860bfb863dff4ba9987e`:
https://ots.golf/submissions/ae54a7a1c4f0d7c6f00e42030c96e468.
The local 1198 continuation is preserved separately. This construction retains its rarest-cut
signer and much of the machine framework, and proves a new fused dependency DAG and security
reduction. `Fusion*.lean` contains the active construction; older modules provide shared lemmas
and preserve the earlier proof development.

## Fusing chain and root work

A binding chain's final hash includes five other chain tops in the packet: two as cv words
and three alongside the current chain word as message words. The metadata identifies the
parent chain. Thus a chain hash already required for reconstruction also authenticates five
dependency tops. The six groups are:

| Binding chains | Dependency tops |
| --- | --- |
| 1, 2, 7 | 14, 15, 16, 19, 20 |
| 3, 4, 5, 6 | 21, 24, 25, 31, 34 |
| 8, 9, 10, 11 | 35, 36, 39, 40, 41 |
| 14, 15, 16 | 12, 13, 0, 17, 18 |
| 19, 20, 21 | 22, 23, 27, 28, 32 |
| 24, 25, 26 | 33, 37, 38, 29, 30 |

Each binding group's all-zero tuple is excluded, so every accepted signature reconstructs
at least one final binding hash in that group. The acyclic dependency order ensures coherent
key generation and reconstruction. Domain-separation proofs cover ordinary chain steps,
fused endpoints, index queries, and root queries with their exact bit strings.

The final root uses three hashes. Root 0 takes tops 1 and 2 as cv, and tops 3–6 as message.
Root 1 takes top 26 and the low half of root 0 as cv, and tops 8–11 as message.
Root 2 takes top 7 and the low half of root 1 as cv, with four ONE message words.
Its low half is the public key. Binding propagates through the DAG to all 42 tops.

## Tables, signing, and exact probability bounds

The signature is 42 complete 128-bit words and a 127-bit nonce, totaling 5503 bits. The signer
tries `2^19` nonces and keeps the accepted class of least weight, breaking ties by earliest
trial. A class's weight counts its effective 127-bit indices. Thirteen group tables encode
41 chain digits; the free chain digit completes the total to **86**. The group cost lies in
`[23,86]`, so the free digit lies in `[0,63]`.

Alias multiplicities vary by group and cost band. Live raw field prefixes have lengths
`[1022,512,512,512,512,2047,2047,1023,995,974,969,1024,969]`.
Unused field values reject. `FusionCodec` specifies the exact tuples and aliases;
`FusionTier` and `FusionNumeric` prove their counts and numerical bounds.

There are 18 dyadic class weights `1,2,...,2^17`. The schedule uses
`hp = 1393370080481 / 2^40 / 2^127`, `k1 = hp/2`, and `b0 = 1`.
Independent numerical estimates give about 135.139 bits of signing availability and a
normalized security slope of 0.950447. The Lean proof uses exact integer counts and
outward-rounded rational certificates, proving signing failure at most `2^-128` and
127-bit strong unforgeability for the actual adaptive cached-oracle experiment.
Key generation uses at most 1256 abstract compressions; verification uses at most 180.

The new security proof normalizes each chain query to the reconstruction's final dependency
context, proves hidden-input and matching-output bounds for the fused packets, and extracts
a forgery event through the dependency DAG. It covers both successful and failed signing.

## Addresses, constants, and execution

The memory layout places selected high and low hash halves in adjacent cv cells. Ordinary
position tags use the existing cost constants. Fused endpoint tags additionally reuse the
checked signature-length cell (5503) and the forced terminal landing product. Their exact
bits are proved distinct and are matched to the abstract scheme's metadata.

The prologue has 25 straight instructions and dispatches at slot 25; slot 26 is a pad.
The free block always materializes its top, removing the former zero-digit frame variant.
Group regions run from slot 27 through 235318. Free blocks begin at 255615 with stride 68;
the sentinel is 262143. The code and memory tables have `2^18` and `2^16` rows, respectively,
for **327680 seeded rows**.

The landing seed is `initialProduct(86,s)`. The final exponent is
`(11529215046068731897 + 2^60 * (s + sum(group costs))) mod (2^64 - 1)`.
Only total 86 reaches the sentinel; every other total in the conservative range 0..284
lands on a pad or beyond the program. Frame guards also reject entry into a block's middle.
The universal cycle theorem quantifies over every admitted memory size, image, and step count.

The machine checks root 2 before roots 0 and 1: committed memory lets an instruction assert
a relation involving values checked later. Soundness therefore reconstructs those relations
in mathematical dependency order. The honest prover first reconstructs all tops, then collects
the complete output pairs and root states; repeated oracle queries share cached answers.

## Validation status

The complete local `Solution` certificate compiles for **1149**, including all six clauses
and the seeded-row bound. A clean rebuild with pinned dependencies prebuilt took **451.757
seconds** and emitted **30549 bytes**. The exported submission, certificate, seeded-row bound,
admissibility, security, faithfulness, soundness, and cycle theorem depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The source-policy checker accepts all 189 files.

Largest child peak RSS was 15591036 KiB. Summed process RSS overcounted shared pages and reached
52.94 GiB; the kernel's whole-environment cgroup lifetime peak was **21089607680 bytes
(19.64 GiB)**, below 24 GiB, with no OOM events. That counter includes other work and cached
files and was not reset. It is not an isolated or enforced verifier resource verdict.
Detailed build, axiom, source-policy, source-hash, and memory evidence is retained in the sibling
`leanisa-1150-evidence` directory. These checks are distinct from the official comparator and replay.

The official verifier cannot start on this host because its mandatory preflight reports:
`Landlock is not enabled on this kernel: refusing to build untrusted code`.
The sandbox was not bypassed. This work has not published a competition submission.

Executable research checks exercised accepted indices with both free-digit extremes, three
complete signing runs, middle-block landings, incorrect layer totals, and modified memory
cells. Six negative controls demonstrate why allowing an all-zero binding tuple would leave
a dependency unauthenticated. Those tests used a deterministic test oracle; the Lean proof
is the security and universal-correctness evidence.

## Failed directions and remaining obstacles

Allowing zero-cost binding tuples improves the table distribution but breaks binding: a group
can disclose all its parent tops without executing any hash that authenticates its children.
The negative controls reproduce this problem. The current tables exclude all six origins.

Reducing root hashes requires a new dependency-aware security proof; replacing only the root
code does not establish unforgeability. Dynamic metadata derived from mutable root outputs
also complicates domain separation. Fixed tags with proved cell values avoid that obligation.

The current score still spends 129 cycles on initialization, index ties, copies, hints, frame
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
