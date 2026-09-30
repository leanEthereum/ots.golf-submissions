# Hinted RISC-V upper bound: 311 cycles

This builds on the weighted-pair 312 and changes only the encoding and dispatch
of the six cap pairs (pairs 0–5, whose two chains may both hash zero times).
When a cap pair's right chain hashes zero times, its two pointer writes do
nothing; that row replaces them by one checksum `ADDI`, and the next prologue's
first pointer move is rebased because `x10` still holds the left chain's state.
Redirected points of that kind drop the pointer pair and fold the unit into the
correction they already carry. Each cap pair's rank is its executed cost, so
every accepting execution costs at most 311 cycles.

`Solution.certificate` proves 127-bit strong unforgeability, admissibility,
soundness for arbitrary views, honest expansion and faithfulness, and the
311-cycle accepting bound. The complete certificate compiles with Lean 4.33.1
and passed exact-statement comparison, permitted-axiom checks and fresh kernel
replay of all 22,784 exported declarations. The graph, chain widths, 128-bit nonce and packed
index, 5,504-bit signature and 884-byte root are unchanged from the 312 and
the 315 record; no new chain-value security assumption is introduced.

The image is 1,043,408 bytes, with 260,838 instructions and 56 data bytes. The
Lean-exported image matches the independently tested 311 prototype exactly. The VM suite passes
4,699 accepting executions (every landing of every pair, all free counts, 276
skip-row cases, random cuts), all at 311 cycles against one fixed-key root, and
rejects every one of the 5,504 signature-bit flips.

See `NOTES.md` for the alphabet, counting, security and machine-proof changes.
Local validation reports are in
`golf/riscv-innovation-evidence/claude311skip-port/README.md` in the project
workspace. Official sandbox verification is unavailable on this host because
it lacks Landlock; no hosted result is claimed.

Base: the locally certified weighted-pair 312 (itself built on the 315 source
`df3ac8e8d0781da8e8c61bac1b5d116f2687e142` and the certified 314 modulo-257
port). Earlier lineage includes lucemans's
[320-cycle submission](https://ots.golf/submissions/0380117cf0362ee8535e725c194cf03a),
source `3bfb3022de749d253c8faa5b5068c72b91e5bb06` (PR 53).
Pinned contract: `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c`.
Rules: [ots.golf/rules](https://ots.golf/rules).
