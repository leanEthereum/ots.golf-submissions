# RISC-V upper bound: 364-cycle ascending-grid candidate

The candidate extends the verified 372-cycle dense-dispatch construction. It keeps
thirty-two four-bit index digits with accepted sum 157, 189 chain hashes, paired
dispatch and three bodies per 128-instruction row, and changes the memory layout:
all thirty-two chains work in 24-byte cells laid out in execution order from
`0x3FFFE0`, and the wire payload is permuted so that sixteen chain values already
sit in their cells. The signature still occupies 5504 bits: a 128-bit nonce, four
160-bit, sixteen 152-bit and twelve 192-bit chain states.

Eight fewer chains need the expansion instruction, and the root now reads the low
192 bits of every cell as one 768-byte region, twelve compression blocks instead of
thirteen. The narrower 152-bit states are admissible because the availability bound
is tightened to the true accepted-index count. Two width changes remain.

The proved bound is 40 cycles for index processing, 303 for all chain blocks and 21
for the root and decision. The image contains 12340 instructions and 104 data bytes:
49464 bytes. Hash work is 202 compressions.

**Validation:** the full exported 364-cycle certificate and image-size theorem pass
the pinned Lean build with only the three permitted axioms, and the official
verifier script was run locally (see the PR). See `NOTES.md` for the layout, the
security accounting at 152 bits and the rejected directions.

The proof remains in the `Mixed*.lean` modules, with security and availability in the
shared graph/wire modules. `MixedProgram` defines the image and `MixedLayout` the
cell/wire geometry; `Payload` holds the wire permutation and its inverse;
`MixedCode` locates the packed bodies; `MixedVerifier`, `Candidate` and `Solution`
connect execution to the certified wire algorithm and export the claim.

Rules: [ots.golf/rules](https://ots.golf/rules).
