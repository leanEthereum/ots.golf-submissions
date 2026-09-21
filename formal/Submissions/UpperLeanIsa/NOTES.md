# Development notes

## Construction

Use a conservative Winternitz encoding before optimizing cycles. The 256-bit message
is represented by 32 bytes. Append the two-byte checksum `sum(255 - byte)`; it fits
because its maximum is 8,160. Signing reveals position `digit` of each of 34 chains;
verification advances it through positions `digit .. 254` to the endpoint.

Each chain query uses the leanISA input format: a zero chaining value, a 512-bit block
containing the 128-bit value, chain identifier, position and a zero cell, and metadata
1. Its low 128 output bits become the next value. Root absorption folds the 34
endpoints with distinct metadata 35 down to 2 and retains the full 256-bit state between calls, finally
truncating to the 128-bit public key. Every call costs two model compressions.

## Checked results

`Encoding.lean` proves message-encoding injectivity and checksum incomparability.
`Resources.lean` proves all three pathwise algorithm budgets, including the newly
required verification cap. `BasicProperties.lean` proves the signature-size bound,
oversized rejection, zero signing failure and deterministic verification.

`Wire.lean` proves both serialization round trips. `Correctness.lean` first proves
correctness for every fixed oracle answer table, then uses VCVio's cached-oracle
support characterization to transfer it to the protected random-oracle experiment.
This proves perfect correctness even when the message depends on the public key,
and completes `scheme.Admissible`. The fixed-table lemmas also characterize
verification on arbitrary raw inputs, not just signatures produced by the signer.

`ForgeryStructure.lean` extracts chain second preimages or an honest word before
the signed cut, conditional on reconstruction matching the honest endpoint vector.
`RootBinding.lean` removes that condition by extracting a root second preimage when
the vectors differ. Its internal comparisons use all 256 hash-output bits; only
the final root comparison uses the 128 public-key bits. The combined theorem is
`accepted_forgery_event`. It covers a different signature at the same message too.
The second-preimage inputs are restricted to the actual reconstructed paths:
existence of a collision somewhere in the entire oracle table would not give a
useful probability bound.

`QueryLayout.lean` proves that equal honest query inputs have the same position,
even across different records. `Records.lean` gives independent coordinates for
sources and full hash outputs, together with the programmed cache.
`RecordSemantics.lean` proves that any table respecting this cache reproduces
all chain values, signed words, endpoints, and the public key.

`TargetBound.lean` derives adaptive target-output bounds from a cache potential.
`SecondPreimages.lean` specializes this to the tagged chain/root queries. A query
matches at most one position; its target set has at most 2^128 full answers and
it costs two compressions. The resulting rate is 2^-129 per compression.

`Resampling.lean` partitions records by the information at a signing cut. It
exposes all root answers, each cut word, and subsequent chain answers; this may
reveal extra data, which is safe for an upper bound on adversarial success.
`Exposure.lean` proves that this information determines the exposed oracle cache
and that the remaining hidden cache is disjoint. `HiddenCharges.lean` resamples
one hidden input coordinate to bound a fixed query, without a union factor over
chain positions. `HiddenBound.lean` lifts this to adaptive computations using the
same 2^-129 per-compression rate. `Coupling.lean` combines that bound with identical-
until-bad to replace hidden programmed answers by fresh answers for a whole public
fiber and any bounded payoff.

`Replay.lean` proves exact cached executions for the chains and signing. It allows
any cache extending the honest record, including one extended by adversarial queries.
Signing produces the recorded cut signature and leaves the cache unchanged. The
signature is also proved to depend only on the post-signing public data.

These are checked ingredients, not yet the full security theorem.

## Remaining proof work

Do not infer a security certificate from the checksum theorem. It excludes simple
chain-advancing attacks but does not bound oracle attacks. A full proof must account
for guessing hidden chain inputs, matching chain outputs, root collisions, adaptive
message choice, and strong forgeries on the already signed message. Only that proof
can justify the tentative 128-bit chain values under the exact cost-normalized target.

The remaining gap is probabilistic, not checksum arithmetic. In particular:

1. Relate the real cached experiment to independently sampled chain records,
   preserving the adversary's views before and after its adaptive signing request.
   Distinct chain/root position tags now guarantee pairwise distinct honest inputs
   for every record. No bad-record collision allowance is needed for this step.
2. Translate the structural witnesses into queries on the real experiment's
   transcript. The fixed-table support characterization proves correctness; it
   does not preserve the probability weights needed for security.
3. Bound hidden-word hits and targeted second preimages, including prior queries,
   cache hits, root compression, and the final verifier's queries. Charge them to
   `CostAtMost (experiment scheme adversary) B`, then establish the strict
   `B / 2^127` inequality.

VCVio's `RandomOracle.ProbeEps` supplies a single-hidden-target hit bound, and
`RandomOracle.DeferredSampling` supplies probability manipulations. Neither is
an instantiated WOTS reduction. The pinned `HashSig.SLHDSA.Security` explicitly
packages primitives without a complete unforgeability theorem; do not replace
the missing competition proof with an assumed primitive-security hypothesis.

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

## Elaboration notes

Use explicit classical deciders for existential searches over the finite record
space. An inferred executable decider may enumerate a function space of astronomical
size while Lean checks definitional equality. Keep finite-set membership lemmas
generic in the element type before specializing them to records (`finiteFiber`).
Do not unfold a concrete `Finset.univ` of records or 256-bit words to prove a counting
identity. Normalize scalar exponents separately from finite-set expressions.

The prospective final accounting can allow separate hidden-input and output-match
charges before and after signing: four charges at 2^-129 on the remaining budget.
To obtain the required strict 127-bit bound, prove and subtract the positive cost
already spent on key generation. This is a proposed assembly strategy, not a checked
experiment bound. The stage transitions must still preserve the relevant cache and
public-data invariants, including queries made before the signing request.
