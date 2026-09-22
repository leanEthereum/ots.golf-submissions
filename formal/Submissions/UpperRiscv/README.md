# RISC-V upper bound: 372-cycle dense-dispatch candidate

The candidate extends the verified 377-cycle mixed-width construction. It uses
thirty-two four-bit index digits with accepted sum 157, executes 189 chain hashes,
and packs up to three pair bodies into a 128-instruction dispatch row. The signature
still occupies 5504 bits, including a 128-bit nonce, eight 192-bit chain states and
twenty-four 160-bit states.

The coarse digit still selects a row with a 512-byte stride. Bodies start at row
offsets 0, 40 and 80 instructions; the final body may occupy 48 instructions. This
reduces code size enough to use the all-four-bit digit profile with halfword loads
and signed-immediate JALR dispatch. A shared digit mask removes one load, and the
bounded fine/coarse sums permit a single mask after the shifted addition, removing
one AND. REMU 65535 still performs the horizontal sum.

The proved bound is 40 cycles for index processing, 310 for all chain blocks and 22
for the root and decision. The image contains 12338 instructions and 104 data bytes:
49456 bytes. Hash work is 203 compressions; ordinary instructions contribute 169 cycles.

**Validation:** the full exported 372-cycle certificate and image-size theorem pass
the pinned Lean build (8900 jobs), with only the three permitted axioms. Independent
tests cover 6706 transcript cases, seven pinned-machine fixtures and exact image
equality. The PR requests official hosted validation; see `NOTES.md` for the local
production-wrapper infrastructure limitation.

The proof remains in the `Mixed*.lean` modules, with security and availability in the
shared graph/wire modules. `MixedProgram` defines the image; `MixedLanes` proves the
single-mask fold; `MixedCode` locates the packed bodies; `MixedVerifier`, `Candidate`
and `Solution` connect execution to the certified wire algorithm and export the claim.

See `NOTES.md` for layout details, validation and attribution.
Rules: [ots.golf/rules](https://ots.golf/rules).
