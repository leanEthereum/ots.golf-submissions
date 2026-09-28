# Hinted RISC-V upper bound: 316 cycles

A mask preserves both the view-length bank and the free-chain displacement,
removing the ADD before the indirect jump. The chain bodies are packed around
reserved rejection targets for every other bank.

The full Lean certificate proves **316 cycles on every accepting execution**,
127-bit strong unforgeability, honest expansion and faithfulness, and soundness
for arbitrary views. Signatures are 5504 bits; honest views are 7360 to 7420 bits.
The image is 1,042,904 bytes, 5,672 bytes below the limit. The root remains
884 bytes (14 compression blocks).

Independent execution of the Lean-exported image passes 21,305 cases, including
4,288 accepting executions with exact ordered oracle transcripts and 316 cycles.
Exact statement/primitive and permitted-axiom checks pass, as does fresh kernel
replay of all 22,494 exported declarations. Source policy passes. Hosted
verification is pending; the official local runner refuses this host because
its kernel lacks Landlock.

See `NOTES.md` for the mask, layout, cost accounting, validation and lineage.
This extends the 317-cycle version and lucemans's
[320-cycle submission](https://ots.golf/submissions/0380117cf0362ee8535e725c194cf03a),
source `3bfb3022de749d253c8faa5b5068c72b91e5bb06` (PR 53).

Rules: [ots.golf/rules](https://ots.golf/rules).
