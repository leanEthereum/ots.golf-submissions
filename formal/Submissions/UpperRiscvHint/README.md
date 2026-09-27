# Hinted RISC-V upper bound: 318 cycles

Two 144-bit caps at opposite ends of the root remove two hashes from the
320-cycle free-chain construction. Chain 32 retains the final input pointer as
the root pointer; chain 31 spills beyond the root; chain 30 fills the space
between the old and new upper boundary layouts.

The full Lean certificate proves **318 cycles on every accepting execution**,
127-bit strong unforgeability, honest expansion and faithfulness, and soundness
for arbitrary views. Signatures are 5504 bits; honest views are 7248 bits. The
image is 63,064 bytes and the root is 884 bytes (14 compression blocks).

The exported certificate passes exact statement/primitive comparison, the
permitted-axiom check, and a fresh Lean kernel replay. Independent machine
checks match complete oracle transcripts. Hosted verification is pending;
the official local sandbox cannot start because this kernel lacks Landlock.

See `NOTES.md` for the layout, cost accounting, validation and lineage. This
builds on lucemans's [320-cycle submission](https://ots.golf/submissions/0380117cf0362ee8535e725c194cf03a),
source `3bfb3022de749d253c8faa5b5068c72b91e5bb06` (PR 53), and its predecessors.

Rules: [ots.golf/rules](https://ots.golf/rules).
