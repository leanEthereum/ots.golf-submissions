# 1110-cycle affine-frame leanISA construction

`Solution.lean` exports the complete `Submission.Certificate 1110`, together with
its seeded-row bound. The score is `110 + 88 * 10 + 120 = 1110`. Every completing
execution has 198 instructions. The certificate covers full admissibility,
127-bit strong security, bytecode validity, honest-prover equivalence, soundness
against arbitrary committed images, and the universal cycle bound.

## The fourteen-cycle saving

The preceding complete certificate at b5063a0 costs 1124 cycles. It uses two
JUMPs per stage: a dispatch and an entry that restores frame one. This construction
removes all fourteen entry JUMPs by keeping a different frame throughout each block.
The former hint MUL becomes an XOR, so no operation is added.

For execution stage f=0 use exponent 14; for f=1..13 use exponent f. If the hinted
block entry is e, the preceding XOR checks `H1 = H + a^exponent`, where `H = g^e`.
One JUMP enters e with frame `H1`. Every cell c in that block is encoded as
`g^c / (g^e + a^exponent)`. Straight instructions keep this nonzero frame. The
final exit resets the frame to one. The address generator remains the pinned g.

The fixed a is chosen by a finite polynomial-avoidance argument. For each wrong
stage, wrong target slot, first operand, and potential memory cell, a successful
read would give a nonzero polynomial equation. The sum of all polynomial degree
bounds is strictly less than the field size 2^64, so a common nonroot exists.
Additional polynomial constraints keep every frame nonzero, prevent a dispatch
from halting, separate powers 0..300, and force a checksum landing in the program
to be its intended sentinel. The layout and a depend only on the fixed table,
never on the input, committed image, or oracle. This is a noncomputable fixed
bytecode definition permitted by the contract; the proof does not select a
base separately for each execution.

The checksum guard matters independently of the entry guards. Without it, a
wrong checksum could re-enter the prologue after the final JUMP resets the frame
to one. `AffineExit.checksum_landing_exact` rules out every such program target.
`AffinePath.run_full` then extracts all fourteen blocks from every completing
execution, with the exact step count and cost. This argument covers every
admitted memory size and cache-free oracle-answer path.

## Scheme and layout

The signature contains 42 disclosed 128-bit chain words and the full 128-bit
nonce, totaling 5504 bits. The index supplies 127 effective bits. The signer
uses rarest-cut signing over 2^19 trials. The existing layer-86 tables and
21-tier exact schedule remain in use; their normalized security slope is
0.9101406258355382.

Nine binding groups have at least one positive parent digit. The final step of
each parent binds four child tops with two domain words. One root binds the
remaining six tops. The graph is acyclic and its root and binding packets cover
all 42 tops. The all-zero tuple of each binding group is excluded. Verification
performs 86 chain hashes, one index hash, and one root hash.

The thirteen C1..C13 initializers now pin a^1..a^13. Cell 49 pins a^14; ONE stays
at cell 48. These supply all fourteen stage biases without another initializer.
C1,C2,C3,C4 occupy cells 105,106,47,107, which reject the nonzero aliases of the
single-instruction length gate. `AffineLength` proves the gate still enforces
length 5504 and ONE with the new powers.

The ordinary hash CV is (ONE,a^14), ordinary metadata is ONE, and index metadata
is a^14. Binding tags use powers 1..13, binding metadata powers 1,2,3 (6 for unused
parents), and the actual root metadata is power 4. Codec-only root metadata uses
powers 15..23. `AffineCodec` proves the domain separation, full admissibility and
strong security of this codec. `AffineCompat`, `AffineValues`, and `AffineSound`
connect these exact words and queries to the bytecode.

Nine guaranteed binding hashes are deducted from the group checksum costs.
The free seed is `g^sentinel / a^77 * a^s`, and each group multiplies by
`a^(cost-deduction)`. The exit restores the nine deductions and forces the full
layer to be 86. `AffineProver` fills the affine hints and products along with
the chain and root answers. `AffineReplay` and `AffineHonestPath` prove that
accepted signatures complete; `AffineFaithful` handles both verifier decisions.

The bytecode has 2^18 slots and memory 2^16 cells, for 327680 seeded rows, below
2^20. The group prefix ends at 243173; free blocks begin at 255615. Entries and
strides are unchanged from 1124; bodies and controls shift one slot earlier,
and removed entry slots become trailing padding. Hash, signature, nonce, and
top cells retain their addresses. Group 5 reads zero-digit root words directly
from the signature; other groups still materialize the required tops.

## Validation

The complete 1110 solution builds with the pinned Lean toolchain (8941 jobs).
Its 313,845,556-byte export contains 61,781 declarations. Exact statement and
primitive comparison, the export axiom check, and a fresh unchanged Lean kernel
replay all passed. Kernel replay took 373.987 seconds; the complete comparison
process took 419.224 seconds with sampled peak PSS 5,247,025,152 bytes. A separate
audit of 19 main declarations found only propext, Classical.choice and Quot.sound.
The source-policy check passed, and checked Lean-source hashes were preserved.

Evidence is recorded in `leanisa-1110-evidence`, including the replay transcript,
profiles, export hashes and source hashes. No hosted 1110 verdict is claimed,
and this branch has not been pushed. The official Linux sandbox cannot run in
this workspace because Landlock is unavailable; standalone local checks are
not a hosted verdict.

The preceding complete 1124 certificate at b5063a0 passed exact statement and
primitive comparison, its axiom audit, and fresh unchanged Lean kernel replay.
Its export was 256,820,865 bytes and 55,400 declarations; replay took 319.726 seconds.
Older complete checkpoints are fb0489b (1125) and 191ba69 (1138).

The 1149-cycle timeout fix at 3c87a7b passed the hosted verifier:
[official transcript](https://ots.golf/submissions/ad10465b7c22e33d9c89c82d6e85d57b/log).
The original d8e29b3 timeout on PR47 was a different revision. Consolidated
length certificates and adjacent-pair order checks retain those timeout fixes.

## Research history and next directions

Nonce128 layer-85, full-index, twelve-group and five-child screens did not pass
all security, availability and code-size bounds. These failures do not prove
that those layers are impossible. Rotating binding packets does not supply free
domain separation: different rotations can coincide on attacker-chosen children.
A 1010-cycle lower bound has not been proved.

`TierKnee` and `ImplicitNonce` are independent research helpers. An omitted nonce
flag model gave a conditional 1116 estimate, but its generalized security theorem
and machine proof were not completed. Those experiments are superseded for this
goal by the complete affine construction. They remain available for later research.

Further improvement requires fewer ordinary assertions or fewer hashes with the
exact security and availability inequalities preserved. Keep initialization,
zero-digit copies, checks on jump targets, the length gate, the row bound, and
the public-boundary charge in every estimate. The present saving comes entirely
from entry-jump removal, not from dropping a binding or verification check.

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
