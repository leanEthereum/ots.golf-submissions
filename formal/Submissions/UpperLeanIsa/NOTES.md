# Layer-87 rarest-cut tables with fused length initialization

Claim **1198 cycles**: `108 + 97 × 10 + 120`, with **205 executed instructions**.
This continues the verified 1209 submission by lucemans at
`6363c32ead978b927a23860bfb863dff4ba9987e`:
https://ots.golf/submissions/ae54a7a1c4f0d7c6f00e42030c96e468.

The underlying rarest-cut signer, nine-call root, and generic security reduction are inherited
from that source. The changes are a new concrete table distribution and one initialization
instruction saved with the checked-length DEREF from the local 1280 continuation.

## Construction and score

The signer still tries all `2^19` fresh nonces and keeps the accepted class of least weight,
with ties resolved in favor of the earliest trial. A class is a chain-digit vector; its weight
is the number of effective indices that decode to it. The effective index remains 127 bits,
and signatures remain 42 words plus a 127-bit nonce, totaling 5503 bits.

The first (3,9) table and both (4,11) tables now contain the cheapest distinct bounded tuples
that fill their fields. In each (3,10) table, cost-1 tuples have multiplicity 2 and cost-3 tuples
have multiplicity 8; all other included tuples have multiplicity 1. Previously the
multiplicities at costs 1, 2, 3 were 2, 8, 2. The cost-16 band is truncated to 135 tuples.
All four table shapes now fill their entire field; there are no dummy field values.

Acceptance uses the layer **87**, down from 88: the 13 group costs must sum to a value in
`[24,87]`, and the free digit completes their sum to 87. This removes one chain hash.
All existing chain lengths and tags are retained: 625 chain steps at key generation,
1268 key-generation compressions, and at most 194 verification compressions.

The prologue uses one DEREF to check the 5503-bit length and pin ONE, replacing the two
separate SET instructions. It computes the index and dispatches at slot 19; slots 20 and 21
are pads. `LengthGate` proves the guard for every loader length through 5505 and every
admitted memory size through log 32 using kernel-checked GF(2^64) logarithm certificates.

Every completing path therefore has 108 ordinary instructions and 97 BLAKE2S instructions
(87 chains, one index, nine roots), plus the fixed 120-cycle boundary charge.

## Security and availability

The exact accepted effective-index count is

`32866494248757430662161494135648372`, approximately `202.5554094 × 2^107`.

The 18 class weights remain `1,2,4,...,2^16,2^18`. `TierSchedule` contains regenerated class
counts and staged two-dimensional recurrence checkpoints, all evaluated by `decide +kernel`.
It proves `Group3.tierHyp` and all conditions of `Tier.Sched.Valid` against the actual tables.
The dyadic security constants are

* `hp = 1291862767788 / 2^40 / 2^127`;
* `k1 = hp / 2`;
* `b0 = 1`.

The resulting maximum security slope is approximately `0.881207 × 2^-127`. Availability uses
at least `2^19 - 1` fresh trials and proves failure at most `2^-128`; an independent estimate
is about `2^-146.13`. The numerical certificates use outward-rounded squaring at precision
`2^256`, retaining the verified source's public-key-dependent availability and strong-security
arguments. No cryptographic assumption or additional axiom is introduced.

## Layout

Group regions end at slot **233438**. The first group's frame-14 copy has offset **233416**
and ends at **249254**. Free blocks still start at **255615**. The code table has `2^18` slots;
the honest memory has `2^16` cells, giving **327680 seeded rows**. The raw full-index XOR tie,
frame isolation, adjacent high/low hash output cells, and nine constant root tags are retained.

The layer exit now seeds the product for 87. Its exponent base is
`10376293541461884921 = (262143 - 87 × 2^60) mod (2^64 - 1)`.
Only total 87 reaches the sentinel; other conservative totals through 284 reach pads or lie
outside the code table. The original all-memory proof structure checks this new exit table.

## Validation

The complete local `Solution` build passes for **1198 cycles**. A clean rebuild of all 145
submission Lean modules with the pinned dependencies prebuilt took **408.672 seconds** and
produced **25515 bytes** of compiler output. Largest child peak RSS was **8005856 KiB**;
this is not aggregate process-tree memory or an official resource verdict.

The exported `submission`, `certificate`, and `seeded_rows`, plus the tier schedule, table
counting, length guard, instruction semantics, and cycle theorem, depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The audit checks the complete certificate type,
205 steps, layer 87, 327680 seeded rows, 5503 signature bits and 1268 keygen compressions.
All 145 final Lean sources regenerate byte for byte from the 1208 checkpoint. There are no
`sorry`, `admit`, or `native_decide` uses in the Lean sources.

This is a complete local certificate, not a hosted verifier verdict. Production replay
requires a host with the mandatory Landlock sandbox, unavailable in this workspace.
No 1198 submission has been published by this work.

## Search and next steps

The unchanged 1209 tables fail at layer 87: their availability estimate is only 120.43 bits
and their normalized security slope is about 1.00988. Restoring omitted cheap distinct tuples
improves the security distribution; relocating the eightfold aliases supplies the remaining
availability. The selected configuration passed independent exact rational checks before its
Lean certificates were generated.

The searches covered 255 assignments of multiplicities 1/2/4/8 at costs 0..3 and 324 pairs of
aliased costs chosen from 0..8. No layer-86 configuration passed both bounds in those searches.
This is a limit of that search family, not a lower bound. Broader alias distributions, table
width allocations, or a separately proved root reduction are possible next directions.

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
