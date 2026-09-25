# leanISA — 1281 cycles

Field-rescaled Group3 with a 127-bit effective index, an eight-call root whose last call is
tagged by the chaining state, and a landing exit (the exit jumps to the last landing product; a
hash-free exit table forces the layer). The cost-17 entries of the six (3,10) tables are dummy
indices that are never accepted, so the prologue drops the `C_17` constant. The free chain's top
is a message word of root call 1, read by a second, frame-isolated copy of the first group's
blocks when the free digit is 0, so the free block needs no copy.
Every completing execution takes **1281 cycles**:
`111 + 105 × 10 + 120`, with exactly **216 instructions**.

- 42 chains; 96 continuation hashes per accepted signature.
- 127-bit nonce; 5503-bit signature.
- 1326 key-generation compressions; at most 2^20 signing compressions; 210 verification compressions.
- Strict 127-bit strong security, including the adaptive index-grinding proof.
- Program log-size 18; honest memory log-size 16; 327680 seeded rows.
- Soundness and cycle bounds cover every admitted prover-selected memory size, image, and step count.

`Solution.lean` exports `submission`, `certificate : submission.Certificate 1281`, and `seeded_rows`.
Build with `lake build Submissions.UpperLeanIsa.Solution` in the pinned contract project.

Local Lean compilation succeeds. The official verifier requires a Linux host with Landlock
and its documented resource-isolation setup; it cannot run on the current development host.
See `NOTES.md` for the construction, proof changes, and credits.
