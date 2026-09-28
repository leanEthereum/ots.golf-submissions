# RISC-V upper bound: 341 cycles

The signature carries no count tag. The lane sum of the index phase, reduced
modulo 1020, is already four times the free digit `(146 - S) mod 255`, so the
remainder feeds the free-chain jump directly and the free table rejects every
digit of 16 or more. This removes the tag load, the tag subtraction and the
checksum branch from the 344-cycle image.

The certificate covers every accepting and rejecting raw-input execution.
Full-length acceptance costs 192 hash compressions and 149 ordinary
instructions. The signature is 5456 bits and the image is 62,552 bytes.

The full Lean build and the permitted-axiom check pass. The Lean-exported
image equals an independent generator and passes 16,330 exact
oracle-transcript executions. These are local development checks, not a
hosted verdict.

See [NOTES.md](NOTES.md) for the construction, validation and research history.
