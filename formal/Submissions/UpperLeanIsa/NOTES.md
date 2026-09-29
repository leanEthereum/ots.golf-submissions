# 1089 research continuation; certified baseline remains 1093

The 2026-09-29 continuation in `autoresearch/leanisa-sub1090` constructs a new
1089-cycle candidate from the completed 1093 checkpoint `40a9697f`. This root
still exports `Submission.Certificate 1093`: **no 1089 certificate is claimed**.
The original `Solution.lean`, claim, scheme and certified machine are unchanged.

The new candidate combines partial landing-hint ties for 56 group-8 raw codes
and 59 group-9 raw codes, the existing group-11 hint, and the corrected
free-last/ZVAR' design recovered from the earlier Claude research. The execution
order is `[0,2,3,4,5,6,7,8,9,10,11,12,1]`. Group 1 has normal and zero-free-chain
twins; duplicating a hinted group would change its tie pattern. The group budgets
sum to 82. Both intended paths have 99 ordinary instructions and 87 hashes:
186 instructions, 969 execution cycles, 1089 with the boundary charge.

`TriangularHints`, `PartialHintData`, `PartialHintIndex`, `PartialHintLabels`
and `PartialHintCodec` supply the complete reversible raw-index encoding and
the exact `2^129` oracle-output fiber factor. Selector positions are group 11:
28..36; group 8: 37..42 plus 64..67; group 9: 0..9. Masks must be removed in
that order. Full class-count/security integration remains to be done.

`FreeLastBlocks`, `FreeLastLayout`, `FreeLastLayoutData`, `FreeLastProgram`,
`FreeLastCompile` and `FreeLastPathCost` define the actual candidate instruction
lists, balanced layout decoder and complete bytecode parameterized by its field
base. They prove block budgets, contiguous layout coverage, special hint entry
checks, bytecode/seeded-row validity, compiler weights and the intended-path
counts. The layout has 14820 normal group blocks, 512 Z twins and 63 positive
free blocks; groups 11 and 12 retain their old addresses. The compact free tail
occupies `[260064,262143)` and there are 999 unused slots immediately before it.

`FreeLastNoRepeat` proves that completing executions cannot revisit registers,
including under the uncached support semantics. `FreeLastVariant` proves the
last group's raw-code tie is injective and the N-to-Z checksum contradiction.
`FreeLastExitData` checks all 1024 new frame-1 exit guards for the length-biased
group. `FreeLastResearch` proves the centered product invariant, a weighted
nonroot lemma, and the arithmetic root bound
`11006439705738751537 < 2^64`. That arithmetic is not yet connected to complete
polynomial families or a selected safe base. `FreeLastChecks` imports the new
component proofs for auditing; it is separate from the submission exports.

The 21 selected component theorems pass trusted primitive comparison and the
dependency-axiom audit, using only `propext`, `Classical.choice` and `Quot.sound`.
Fresh kernel replay of their 30806 exported declarations passes in 177.112
seconds. An initial audit caught a native-solver axiom from `bv_decide`; all
seven uses were replaced by ordinary BitVec lemmas before the passing replay.
This is a component audit, not an exact 1089 challenge comparison or a hosted
submission verdict.

Remaining work: instantiate/prove the signed-frame and exit-landing families;
prove exact entry inversion and every completing path, including re-entry and
N/Z switching; connect the new accumulator/codec to the scheme; port the honest
image, faithful and arbitrary-memory soundness proofs. Only then can the claim
change to 1089 and undergo full challenge comparison and replay. The imported
old `IndexBits` helpers must be factored before installing the new decoder, to
avoid an import cycle.

The local design, generators and validation receipts are saved in
`/projects/golf/leanisa-sub1090-evidence/`, especially `DESIGN_1089.md` and
`RESULT.md`. Independent arithmetic checked all layout entries and budgets,
67,108,864 selector/context roundtrips, and 4096 complete accumulators. The
universal Lean inverse covers every raw word, beyond those finite tests.

The construction preserves the baseline tuples, alias multiplicities, layer 85,
signing schedule, domains, nonce and signature sizes. No claim of optimality is
made. The older layer-84/root-fusion candidates failed security and are not reused.

## Preserved report for the completed 1093 checkpoint

The validation measurements and historical credits below refer to `40a9697f`,
before the separate research components above were added.

This revision by Nicolas Consigny and Codex extends the locally proved 1094
construction, which combines our centered checksum with Luc's verified PR #66
landing-hint tie (assisted by Claude Opus 5.5). The rules and trusted contract are
unchanged. Complete local validation passes; hosted verification remains pending.

## The additional saving

The proved bound is `103 + 87 * 10 + 120 = 1093` cycles: 190 instructions and
973 execution cycles before the fixed public-boundary surcharge. Twelve SETs
initialize C1 through C12. The length assertion, index hash, initial hint XOR,
and dispatch follow. All body locations are unchanged from 1094.

Stage 12 (the final charged group) uses the validated length bit pattern 5504
as its affine bias, replacing C13. Stage 13 (the free chain) keeps ONE. Stages
0 through 11 use distinct positive powers of the selected field base. Removing
C13 also requires relabeling inactive metadata 13 to 12, and chain 31's packet
tag 13 to 0. `SplitDomains` rechecks packet kind and location separation.
Ordinary position tags need only C0 through C8; the centered checksum needs
C0 through C10. No other executed instruction needs C13.

The same 42 disclosed words and full 128-bit nonce occupy 5504 signature bits.
There are 2^18 code slots and 2^16 memory cells, totaling 327680 seeded rows.
The bytecode and memory caps, raw-input obligations, signing and verification
budgets, and strong-unforgeability definition remain unchanged.

## Arbitrary committed memory

Reusing a constant requires a new control-flow proof. Treating length as an
independent power, or simply reusing ONE for both stages, would not suffice.

`FixedBiasPolys` proves nonzero collision polynomials whenever at least one
stage has a positive exponent. `AffineSelect` chooses a base avoiding all those
roots, as well as the existing checksum, halt and domain constraints.

For two fixed stages, `LengthFrameChecks`, `LengthFrameScan`, and
`LengthFrameData0` through `LengthFrameData16` certify every offset of all
1024 final-group blocks and 64 free blocks. The scans check 41810 exact field
identities. Only a matching stage at its declared entry is exempt from an
address-exclusion check. There are 40722 wrong body landings, including all
1088 attempts to use the other fixed stage's bias at a valid entry. An additional
53 nonzero initial frames are checked. The ONE-biased zero frame fails its read.
The length frame is nonzero at all 262144 slots, and both halt guards hold.

For each wrong landing, the certified ratio is `g^delta` where
`2^32 ≤ delta ≤ (2^64 - 1) - 2^16`. Multiplying by any first operand `g^c`,
`c < 2^16`, cannot address any memory row `g^j`, `j < 2^32`. Thus the proof covers
all prover-chosen images at every admitted memory size, including malicious
images and wrong cross-stage jumps. `AffineDecode.layout_fixed` connects the
finite block geometry to actual compiled instruction descriptors.

`ByteWindowCore` and `ByteWindow` certify radix-256 exponentiation tables and
provide ordinary kernel computation of each field relation. Each block has its
own small proof; three import chains limit simultaneous expensive checks.
No native evaluator axiom, external arithmetic result, or proof placeholder is
used. External discrete logarithms only supply witnesses checked by Lean.

## Preserved index and security argument

The centered checksum, unit-11 landing hint, reversible raw-index decoding,
accepted cost window 22 through 85, split alias multiplicities, exact class counts,
and 440-tier signing schedule are unchanged. The pure oracle domain labels are
reinstantiated with the relabeled constants and their separation proof.

The normalized linear security coefficient remains
`1094562261779 / 2^40`, approximately 0.995499. The signing schedule uses 2^19
trials and exact outward-rounded rational bounds. The research failure bound is
approximately 0.587825 times 2^-128; the certificate proves the required bound.
There is no change to the 127-bit security target or whole-experiment budget.

`AffinePath` and `AffineCycles` cover every completing execution. `AffineValues`
and `AffineSound` establish soundness for arbitrary committed images.
`AffineHonest`, `AffineHonestPath` and `AffineFaithful` use the loaded length
word to construct the matching honest execution on every raw input.

## Validation

The isolated clean build passes with 8985 jobs in 452.448 seconds. Exact
challenge and primitive comparison, exported dependency-axiom checking, and
fresh Lean kernel replay pass in 436.628 seconds, including 392.925 seconds
inside kernel replay. The solution exports 64803 declarations; the standard
three built-in Quot entries are removed from the map before replay. Only
`propext`, `Classical.choice`, and `Quot.sound` occur in the exported axiom
closure. The named certificate, seeded-row, cycle, faithful and soundness audits
agree.

The five measured build, challenge-compilation, export and check stages total
907.680 seconds locally. Peak sampled process-tree PSS is 12.383 GiB, and clean
build output is 35653 bytes. These are standalone development measurements,
not hosted cgroup measurements or a hosted runtime guarantee. The official
local runner fails closed because Landlock is unavailable; no sandbox gate
was bypassed.

All twelve arithmetic regressions pass. They reconstruct the actual layout
from source, cover all 512 existing hint placements and 14820 block budgets,
check every finite log and ratio, and reject tampered, duplicate or missing
rows. Tests supplement the universal Lean proof. Lean source hashes remained
unchanged through clean build, export and replay; documentation was finalized
afterwards. Only this admitted submission root changes.

## Further gains and rejected shortcuts

A second partial landing hint remains a candidate for 1092. Group 8 has only
56 raw codes whose unpadded body needs seven ordinary operations; the others fit
six. Replacing the pattern SET+XOR by a hint XOR for those 56 codes would lower
the group's maximum by one. A researched layout interleaves those blocks with
group 0, preserves all group-12 and free-stage addresses, and uses a finite label
permutation plus a triangular two-mask bijection. Its arithmetic placement and
generic inverse are checked, but its full index/layout/machine proof is not
ported here. No 1092 certificate is claimed.

Simply deleting padding does not lower the current worst case: actual accepted
layer-85 tuples saturate all group budgets even when the free digit is zero.
Forbidding free digit zero or pruning a single saturated group fails the tested
security/availability bounds. Global rare-path exclusion has numerical room,
but needs actual machine enforcement. A pure-verifier filter alone is invalid.
Pointing the final root hash directly at the public-key cell would also bind its
second output word to the pinned message cell, so it does not remove the final
copy under the current memory layout. No optimality claim is made.

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

- The full-nonce revision and the four-child single-root construction, exact codec/tier
  proofs, address layout, security proof and 1125-cycle machine certificate were prepared with Codex.
- The validated-length frame and shifted checksum, reducing the machine to 1124 cycles,
  were prepared with Codex.
- The affine-frame candidate and its polynomial avoidance, secure codec, instruction
  semantics, length check, universal 1110-cycle proof, soundness, honest prover and complete certificate were prepared with Codex.

- The mixed-packet split-alias layer-85 construction, linear security argument, exact multiplicative counting, and 1096 proof port were prepared with Codex using parallel agents.
- The centered-checksum and fixed-free-frame 1095 revision, exact landing certificates,
  and full machine proof port were prepared with Codex using parallel agents.

- Luc (`lucemans`), assisted by Claude Opus 5.5, contributed the unit-11 landing-hint
  tie, its placement and index unmasking in verified [PR #66](https://github.com/leanEthereum/ots.golf-submissions/pull/66),
  checked commit `ac71030479e8eced8c762d4d6c0891a00c1a31c8`.
- The composition of the two independent 1095 improvements into this 1094 construction
  was prepared with Codex using parallel agents.
- The validated-length second fixed frame, exact cross-stage certificates, byte-window
  checking, and complete 1093-cycle proof port were prepared with Codex.
