# Development notes

## Construction

Use a conservative Winternitz encoding before optimizing cycles. The 256-bit message
is represented by 32 bytes. Append the two-byte checksum `sum(255 - byte)`; it fits
because its maximum is 8,160. Signing reveals position `digit` of each of 34 chains;
verification advances it through positions `digit .. 254` to the endpoint.

Each chain query uses the leanISA input format: a zero chaining value, a 512-bit block
containing the 128-bit value, chain identifier, position and a zero cell, and metadata
1. Its low 128 output bits become the next value. Root absorption folds the 34
endpoints with metadata 2 and retains the full 256-bit state between calls, finally
truncating to the 128-bit public key. Every call costs two model compressions.

## Checked results

`Encoding.lean` proves message-encoding injectivity and checksum incomparability.
`Resources.lean` proves all three pathwise algorithm budgets, including the newly
required verification cap. `BasicProperties.lean` proves the signature-size bound,
oversized rejection, zero signing failure and deterministic verification.

## Remaining proof work

Do not infer a security certificate from the checksum theorem. It excludes simple
chain-advancing attacks but does not bound oracle attacks. A full proof must account
for guessing hidden chain inputs, matching chain outputs, root collisions, adaptive
message choice, and strong forgeries on the already signed message. Only that proof
can justify the tentative 128-bit chain values under the exact cost-normalized target.

For the bytecode, prefer bounded control flow with every hint constrained. The
protected cycle bound quantifies over all committed images and uncached answer
paths; hash binding cannot be used to justify a loop bound. Include the mandatory
120-cycle boundary charge. No bytecode or cycle estimate is certified here yet.

## Why existing entries were not copied

Existing RISC-V entries query the oracle on lengths that leanISA's fixed 896-bit
interface cannot issue. Merkle–Damgård hashing is a different oracle program and
needs its own proof; substituting it does not preserve the old certificate.

The local leanVM checkout's current branch is RISC-V work. Its older `origin/main`
contains leanISA signature code, but the XMSS instance has different key/signature
sizes and budgets. It is implementation inspiration, not a ready competition proof.
