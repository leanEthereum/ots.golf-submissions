# Hinted RISC-V upper bound: 315 cycles

A mask preserves both the view-length bank and the free-chain displacement.
Pair 0's single prologue links its jump into `x1`, which gives the root length,
so no constant load is needed. The chain bodies are packed around reserved
rejection targets for every other bank.

The full Lean certificate proves **315 cycles on every accepting execution**,
127-bit strong unforgeability, honest expansion and faithfulness, and soundness
for arbitrary views. Signatures are 5504 bits; honest views are 7360 to 7420 bits.
The image is 1,043,408 bytes, 5,168 bytes below the limit. The root remains
884 bytes (14 compression blocks).

Independent execution of the Lean-exported image passes 17,079 cases, including
5,697 accepting executions with exact ordered oracle transcripts and 315 cycles.
The certificate uses only `propext`, `Classical.choice` and `Quot.sound`.
Hosted verification is pending.

See `NOTES.md` for the link, layout, cost accounting, validation and lineage.
This extends the 316-cycle version and lucemans's
[320-cycle submission](https://ots.golf/submissions/0380117cf0362ee8535e725c194cf03a),
source `3bfb3022de749d253c8faa5b5068c72b91e5bb06` (PR 53).

Rules: [ots.golf/rules](https://ots.golf/rules).
