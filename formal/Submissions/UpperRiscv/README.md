# RISC-V upper bound: 360 cycles, four more chains hashed in place

This candidate extends dhsorens's 364-cycle ascending cell grid (PR #28), which builds on the
372-cycle dense dispatch, Alexander Hicks's mixed-width image and dhsorens's paired dispatch.
It changes one thing: four 152-bit chains no longer pay an expansion hash and a redirect.
**360 = 40 index + 299 chains + 21 root and decision**, on every accepting run and as the
bound on every run.

## In-place chains above the cell

The scheme is a WOTS-style one-time signature with 32 hash chains and one 4-bit digit per chain.
The verifier hashes each chain inside memory: a hash reads the state (`x11` bits at `x10`) and
writes its 256-bit answer at `x12`, and the next state is a fixed slice of that answer. In the 364
layout chain `k` (in execution order) writes every answer to the 32-byte buffer
`[cell_k - 8, cell_k + 24)`, with `cell_k = 0x3FFFE0 + 24k`. A chain whose disclosed wire value
starts exactly at `cell_k` is hashed in place: its state is answer bytes `[8, 8 + w)`. Every other
chain first hashes its wire value, then points `x10` at `cell_k` (the redirect `ADDI x10, x12, 8`).
That costs 16 redirects.

A wire value of width `w` bytes that starts at `p` with `cell_k <= p <= cell_k + 24 - w` also lies
inside chain `k`'s buffer. It can be hashed in place with `x10 = p`, taking the next state from
answer bytes `[j, j + w)`, `j = p - cell_k + 8`. The buffer bytes below the value are dead: they
hold the previous chain's top 8 answer bytes, which the root does not read, and wire bytes of
chains that have already run. In the 364 wire, the last 152-bit value of each 96-byte group
(chains 7, 11, 15 and 19) starts five bytes above its cell, so `j = 13`, and the value ends exactly
at the buffer's end. Those four chains now keep `x10` at their wire value and take their state
from answer bits `[104, 256)`. They drop the expansion hash and the redirect, and their copy
bodies use a plain 16-hash ladder.

Everything else is the 364 image: the cells and buffers, the root region (the low 192 bits of
every buffer, 768 bytes, 12 compression blocks), the wire permutation, the execution order, the
rows and the dispatch. As for the 364's other 152-bit chains, the root commits to a fixed 192-bit
slice of each chain's top. That slice need not contain the state slice. Security only needs the
state slice to fix at least 152 of the 256 answer bits, and `card_filter_trunc_le'` now proves
this for a window at any offset.

Accounting: 189 chain hashes, 64 pointer instructions, **12** redirects, 32 dispatch instructions
and two width changes give 299 cycles for the chains. The index phase (40) and the root and
decision (21) are unchanged. The image is still 12340 instructions and 104 data bytes (49464
bytes). Only four copy-body families and four prologue immediates differ.

In the proof, `expands k` marks the twelve chains that still expand, and `work k` is a chain's
input address while it hashes. `Forest.truncOff k` (64, or 104 for chains 7, 11, 15, 19) is the
bit offset of the next state, and `trunc` takes the slice at `min (truncOff k) (w - chainBits k)`.
`MixedLayout.work_eq'` (`work k = outAddr k + truncOff k / 8`) is checked by kernel decision, and
the general counting lemma `Values.card_filter_extract_le` bounds the security events at either
offset.

Credit: the ascending cell grid, wire permutation and 152-bit accounting are dhsorens's (PR #28),
and they rest on the constructions credited below. The in-place observation was found with
Claude Fable 5.1 and implemented with Claude Opus 5.5.

**Validation:** `lake build Submissions.UpperRiscv.Solution`, the stub-statement and axiom check
and the pinned comparator pass on a CI mirror of the verifier (GitHub Actions, pinned `.contract`).
The hosted ots.golf verifier has not checked it yet.

---

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
