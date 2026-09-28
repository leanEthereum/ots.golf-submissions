# RISC-V upper bound: 344 cycles

The final count tag stores `4*v`, so the verifier can load the free-chain jump
width directly. A modulo-1020 checksum verifies both alignment and the digit
sum, removing one instruction from the 345-cycle image.

The certificate covers every accepting and rejecting raw-input execution.
Full-length acceptance costs 192 hash compressions and 152 ordinary
instructions. The signature is 5464 bits and the image is 62,552 bytes.

The full Lean build, exact statement/primitive comparison, permitted-axiom
check and fresh kernel replay of 22,253 declarations pass. The exported image
also passes 16,480 independent exact oracle-transcript executions.
The official runner stops at Landlock preflight on this host; these are
local development checks, not a hosted verdict.

See [NOTES.md](NOTES.md) for the construction, validation and research history.
