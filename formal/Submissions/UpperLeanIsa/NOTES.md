# 1124-cycle four-child leanISA construction

The complete certificate in `Solution.lean` targets 1124 cycles. This research branch
continues toward a fully certified result at most 1110; it has not reached that goal.

## Construction

The signature has 42 disclosed 128-bit chain words and a full 128-bit nonce, totaling
5504 bits. The message/public-key/nonce index supplies 127 effective bits. The signer
chooses its rarest accepted cut among 2^19 trials. The concrete tables have 21 alias-weight
tiers and their exact schedule bounds the normalized security slope by
0.9101406258355382. `FourChildTier` links the enumerated tables to the exact counts;
`FourSecurity` and `FourAdmissible` prove strong unforgeability and full admissibility.

Nine binding groups each have at least one positive parent digit. Their final chain
queries bind four child tops using the packet
`[child0, child1, current, child2, child3, tag, metadata]`.
A tag/metadata pair identifies each binding parent. All needed domain words come from
C1 through C13, ordinary and index metadata remain C0 and C16, and root metadata is C4.
The single root binds tops 3,4,5,6,8,9. The graph is acyclic and its root plus nine binding
packets cover all 42 tops. The codec rejects each all-zero binding tuple.

Thirteen constants C1 through C13 are pinned before the full-nonce length gate.
C1,C2,C3,C4 occupy cells 105,106,47,107 to reject its otherwise possible long-length
aliases. The remaining aliases lie in loader-padded cells. After the gate establishes
length 5504, that loaded word supplies frame 1; frame 0 uses C1 and frames 2–13 use
C2–C13. Their field exponents remain separated by more than 2^33. This removes the C14
initializer. Each of the nine positive binding-group costs contributes `cost - 1` to
the product; the free block targets 77 instead of 86. The exact sum identity restores
all nine hashes at the exit, so the hash count and signature scheme are unchanged.

ONE and g remain adjacent at 48 and 49. The four-child CV pairs and root CV pair have
disjoint physical answer pairs; ten chains take the high half of their final hash so
the selected tops are adjacent.

Group 5 supplies the four root message words directly from the signature for zero digits;
all other groups materialize their tops. The group ordinary-instruction allowances are
`[7,8,8,8,8,6,9,8,8,8,8,8,8]`, totaling 102. Including the free block and prologue/exit gives
124 ordinary cycles. There are 86 chain hashes, one index hash and one root hash:

`124 + 88 * 10 + 120 = 1124`.

Every completing execution has 212 instructions. The bytecode has 2^18 slots, the group
prefix ends at slot 243173, and the free blocks start at 255615. Memory has 2^16 cells,
so the seeded-row total is 327680, strictly below 2^20. The public execution witnesses
cannot reduce the cycle bound: `FourMachineCycles` quantifies over all admitted memory
sizes, committed images, and completing step counts. `FourMachineSound` excludes completing
images for rejected signatures; `FourMachineFaithful` proves the honest prover equivalence.
Key generation uses 720 oracle queries (1440 charged compressions), and verification uses
at most 176 charged compressions in the abstract oracle model.

## Validation

The complete 1124-cycle solution built with the pinned Lean version (8919 jobs). Its
256,820,865-byte export contains 55,400 declarations and passed exact statement/primitive
comparison, the axiom audit, and a fresh unchanged Lean kernel replay. Replay took
319.726 seconds; all local export checks took 360.680 seconds, with sampled peak PSS of
5,204,140,032 bytes. Only propext, Classical.choice and Quot.sound were used.
The official Linux sandbox cannot run here because Landlock is unavailable;
standalone local checks do not constitute a hosted verdict. No 1124 submission has been pushed.

The preceding 1125-cycle checkpoint fb0489b passed exact statement/primitive comparison,
axiom audit and a fresh unchanged Lean kernel replay. Its 256,735,416-byte export contained
55,390 declarations. Kernel replay took 398.423 seconds; all export checks took 440.173 seconds
with 4,221,604,864 bytes of sampled peak PSS. It used only propext, Classical.choice and Quot.sound.
That complete checkpoint is retained in Git.

The preceding full nonce128 certificate at commit 191ba69 proved 1138 cycles. Its exact
export comparison, axiom audit and fresh kernel replay passed in 355.328 seconds, with
peak PSS of 5,205,716,992 bytes. That checkpoint is retained in Git.
The earlier 1149 timeout fix, commit 3c87a7b, passed the hosted verifier:
[official transcript](https://ots.golf/submissions/ad10465b7c22e33d9c89c82d6e85d57b/log).
The original d8e29b3 timeout on PR47 is a different revision.

A closed field-power reduction initially made the new root-domain compatibility proof
expensive. A general symbolic `tagWord_eq_cell` lemma avoids that reduction; the concrete
table module then compiled in about four seconds. The older timeout fixes are retained:
consolidated length certificates and adjacent-pair checks for the transitive location order.

## Remaining work toward 1110

The target is still at most 1110, not a lower-bound claim. The next improvement must save
ordinary instructions, reduce the number of chain hashes while maintaining the exact
security and availability inequalities, or both. The previous nonce128 layer-85 and full
128-bit-index searches did not pass every constraint. The four-child layer-85 searches
also failed the security bound; they do not prove that layer impossible.

New twelve-group screens with eight triples, three quadruples and a quintuple did not
pass the security/code-size constraints at layer85. A proposed eight-group hybrid with
four five-child packets and four four-child packets can fit its domain constants into
C1..C14; its first layer84 screen also failed (best-loss normalized slope about1.806).
That hybrid is only a research model and has no Lean scheme or machine certificate.

`TierKnee.lean` proves the largest legal integer knee for a positive collision slope,
and proves that it never increases the quadratic budget term. It is a standalone
research helper; the exported 1124 certificate still uses its original schedule.
Further screens with heterogeneous aliases, wider cost bands, and conditional binary
projections did not produce a passing 1110 candidate. These screens are not proofs.

Do not omit zero-digit copies or the hint-times-g checks when estimating a new machine.
The latter prevent jumps into block interiors. Removing zero-binding exclusions leaves
children unauthenticated. Weighted-rank ideas require an explicit implementation and a
budget for all extra field constants. The suggested 1010 figure is not a proved lower bound.

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
