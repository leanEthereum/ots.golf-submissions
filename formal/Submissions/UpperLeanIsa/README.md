# leanISA — 1209 cycles

Field-rescaled Group3 with a 127-bit effective index, rarest-cut signing, aliased group tables
on the layer 88, a nine-call root with constant tags, and a landing exit (the exit jumps to the
last landing product; a hash-free exit table forces the layer). The signer makes all `2^19`
trials and keeps the accepted class with the fewest accepted indices; the security proof pays
for index queries and signing with a certified 18-tier schedule. The (3,10) tables place their
cheap tuples at several field values, which raises the accepted mass and lowers the layer. The
free chain's top is a message word of root call 1, read by a second, frame-isolated copy of the
first group's blocks when the free digit is 0.
Every completing execution takes **1209 cycles**:
`109 + 98 × 10 + 120`, with exactly **207 instructions**.

- 42 chains; 88 continuation hashes per accepted signature.
- 127-bit nonce; 5503-bit signature.
- 1268 key-generation compressions; exactly 2^20 signing compressions; 196 verification compressions.
- Strict 127-bit strong security, including the adaptive index-grinding proof for the
  rarest-cut signer.
- Program log-size 18; honest memory log-size 16; 327680 seeded rows.
- Soundness and cycle bounds cover every admitted prover-selected memory size, image, and step count.

`Solution.lean` exports `submission`, `certificate : submission.Certificate 1209`, and `seeded_rows`.
Build with `lake build Submissions.UpperLeanIsa.Solution` in the pinned contract project.

Local Lean compilation succeeds. The official verifier requires a Linux host with Landlock
and its documented resource-isolation setup; it cannot run on the current development host.
See `NOTES.md` for the construction, proof changes, and credits.
