# Hinted RISC-V upper bound: 320 cycles with a free chain

A 33rd chain, the free chain, completes the index digit sum `S` to 145. Its count `c = 145 - S`
is not in the signature. The honest view carries it as byte `v = 4 c` at view byte 64, a dead
byte of normal chain 13's buffer. The machine subtracts `v & 0xFC` from the checksum sum, so the
residue in `x5` is the HASH call number exactly when `S + c = 145` modulo 255. The free dispatch
jumps `c` cells before pair 0's prologue; a count of 16 or more lands on a jump to a rejection
stub, and this is also the raw-form flag. The accepted set is every digit vector with all
sixteen pair sums at most 24 and `S` in `[130, 145]`.

The chain that hashes last, normal chain 32, sits at the bottom of the 888-byte root region with
its answer buffer eight bytes lower, in the nonce's high word, and its top is answer bits
`[64, 256)`. After its last hash `x10` already points at the root input, so the root setup is one
instruction: `ADDI x11 x1 960` with `x1` the free base 6144.

Proved accounting: every accepting path costs **320 = 34 index + 4 free dispatch + 145 digit
units + 137 for the pairs' overhead, the root (14 blocks) and the decision** cycles. The image is
15,751 instructions and 64 data bytes, 63,068 bytes. The signature is 5504 bits; the honest view
is 7248 bits.

The Lean image equals the independent generator, and 13,299 transcript cases pass. See
`NOTES.md` for the layout, the proof, the validation and the lineage of this entry (321, 324,
337, and the deterministic 349 → 364 records it builds on).

Rules: [ots.golf/rules](https://ots.golf/rules).
