# Hinted RISC-V upper bound: 317 cycles

Two 144-bit caps at opposite ends of the root save two hashes from the published
320-cycle free-chain construction. Encoding the free count in the view length
then removes one byte-load instruction.

The full Lean certificate proves **317 cycles on every accepting execution**,
127-bit strong unforgeability, honest expansion and faithfulness, and soundness
for arbitrary views. Signatures are 5504 bits; honest views are 7360 to 7420 bits.
The image is 63,064 bytes and the root is 884 bytes (14 compression blocks).

Exported statement/primitive comparison and the permitted-axiom check pass.
A fresh Lean kernel replay passes all 22,423 exported declarations; comparison
and replay take 98.03 seconds wall clock, with sampled peak PSS of 5.05 GiB. Independent execution matches
768 accepting oracle transcripts, with additional view-length and raw-form tests.
Hosted verification is pending; the official local runner refuses this host
because its kernel lacks Landlock.

See `NOTES.md` for the layout, cost accounting, validation and lineage. This
builds on lucemans's [320-cycle submission](https://ots.golf/submissions/0380117cf0362ee8535e725c194cf03a),
source `3bfb3022de749d253c8faa5b5068c72b91e5bb06` (PR 53), and its predecessors.

Rules: [ots.golf/rules](https://ots.golf/rules).
