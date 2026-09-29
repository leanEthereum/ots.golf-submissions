# Candidate 87: larger shared DAGs with the record's signing schedule

This submission proves a worst-case bound of **87 compressions** for the
generic upper-bound track, including every rejecting input and every oracle-answer
path. It extends the verified 88-compression construction by replacing each of its
three 20-node hash blocks with a searched 35-node block. The 160-tier signing
schedule, 86-bit nonce, 129-bit disclosed values, and security target are unchanged.

## Construction

Each of three identical blocks contains fourteen independent length-18 chains
`c0` through `c13` and the following thirty-five ternary hash nodes. An `h` input
refers to the low 129 bits of that hash's output; a `c` input is a chain endpoint.
Each node's exclusive child is in its last (low) input slot.

| Node | Children, in input order | Exclusive child |
|---|---|---|
| h0 | c2, c3, c8 | c8 |
| h1 | c4, c0, h0 | h0 |
| h2 | c0, c2, c1 | c1 |
| h3 | c3, h1, h2 | h2 |
| h4 | c3, c0, c7 | c7 |
| h5 | c0, h1, c6 | c6 |
| h6 | c4, c3, h5 | h5 |
| h7 | c2, h1, c13 | c13 |
| h8 | c2, c0, h7 | h7 |
| h9 | c0, c3, c9 | c9 |
| h10 | c3, c0, c10 | c10 |
| h11 | h1, c3, h10 | h10 |
| h12 | c4, c2, h11 | h11 |
| h13 | h6, c2, c12 | c12 |
| h14 | c4, h1, h13 | h13 |
| h15 | c0, c3, h14 | h14 |
| h16 | h6, h15, h12 | h12 |
| h17 | h15, c3, h8 | h8 |
| h18 | c4, h6, h17 | h17 |
| h19 | h16, h18, h9 | h9 |
| h20 | h6, h1, h19 | h19 |
| h21 | h15, c2, h20 | h20 |
| h22 | c0, c3, c11 | c11 |
| h23 | h1, c2, h22 | h22 |
| h24 | h6, h15, h4 | h4 |
| h25 | h18, h16, h24 | h24 |
| h26 | c2, h1, h25 | h25 |
| h27 | h6, c4, c5 | c5 |
| h28 | h15, c2, h27 | h27 |
| h29 | h1, c0, h28 | h28 |
| h30 | h16, h18, h29 | h29 |
| h31 | h15, h6, h3 | h3 |
| h32 | h18, h16, h31 | h31 |
| h33 | h6, h15, h23 | h23 |
| h34 | h18, h16, h33 | h33 |

The five block tops, in root-slot order, are `h32, h21, h30, h34, h26`.
They have no user within the block. The root hashes a 16-bit tag and the fifteen
block tops: `16 + 15 * 129 = 1951` bits, costing four compressions. Chain queries
are 145 bits and ternary queries are 403 bits, each costing one compression.
All node tags are distinct 16-bit values. The public key is the root's low 128 bits.

Key generation costs `3 * (14 * 18 + 35) + 4 = 865` compressions. The graph has
2627 named nodes including sources, concatenations, hashes, and truncations.

## Exact cut count and verification cost

There are exactly **2,800,958** valid expansion sets per block. Each discloses at
most fourteen 129-bit values. A needed chain is disclosed once at a position in
`0..18`, even when several parents use it. A needed unexpanded hash is disclosed;
an expanded hash is evaluated once and shared by every parent that needs it.

The supported family has graph reconstruction cost exactly **86**:
four root compressions plus a total of 82 chain and internal-node compressions
across the three blocks. Its exact cardinality is

`678547358015097091041046109088624`.

This exceeds the existing schedule's required

`676013856769711926075368867014708`

classes by about **0.3748%**. The scheme selects an injectively indexed subfamily
of exactly the required size; the security schedule's probabilities are unchanged.

`LongChain91Geometry.lean` proves the graph conditions, bounds disclosures, and
counts this family. The weighted frontier recurrence merges equivalent states
and reaches at most 255 states at a level. The kernel evaluates a base-`2^320`
generating number and extracts digit 82 of its cube. The larger digit base bounds
the entire tuple population and prevents carries from invalidating coefficient
extraction. A separate base-`2^36` generating number proves the fourteen-word bound.

A signature occupies at most `86 + 42 * 129 = 5504` bits. The message/nonce query
is 342 bits, distinct from every graph query length, and costs one compression.
Thus the total verification bound is **1 + 86 = 87**. The raw wire adapter also
rejects oversized inputs and preserves strong unforgeability.

## Search and independent arithmetic checks

The search first reproduced the published 88-compression count exactly. At a
total cost of 87, the record's original graph supplies only about 67.26% of the
required classes. Extending its chains even to saturation raises this only to
67.49%. Rewiring the original twenty-node blocks improved this to about 82.5%
in the tested runs, still short of the target.

Allowing additional ternary nodes found a forty-four-node block with about
101.50% of the required capacity. Greedy removal of exclusive nodes reduced it
to the present thirty-five-node block while preserving the needed count.

The numerical search used a saddle-point estimate to rank large graphs. Its
estimates were never used as proof certificates. Exact integer frontier evaluation
checked the candidate, and a separate exhaustive enumeration of all 2,800,958
expansion sets, followed by integer polynomial convolution, reproduced its
cardinality and word bound. Lean then checks its own exact finite certificates.

## Exact 160-tier schedule

`CompactSchedule91.lean` contains literal lists of 160 class populations,
160 per-class alias multiplicities, and 160 upward-rounded winner-kernel
numerators.

The class populations sum to the subfamily cardinality above. They run
from

- tier 0: `165731999761240428825280379636982` classes;
- tier 159: `6273147585895` classes.

The per-class alias multiplicities are strictly increasing, from

- tier 0: `374796160129614344588800418032272040264`;
- tier 159:
  `9901842140742959321105762597502091375939212910554127043776`.

The multiplicity-weighted total is exactly

`9938514739378411853906048441678916651529596919925356639434040636883783447`

accepted 256-bit answers. The decoder identifies this accepted prefix with the
schedule's alias type and proves every class and tier fiber exactly.

Signing performs `L = 2^20` 86-bit nonce trials with replacement and retains
the earliest occurrence in the minimum accepted tier. The certificate scales
kernel witnesses by `2^80`; twenty outward-rounded squarings at `2^512`
precision bound the true first-minimum kernels.

The checked schedule envelopes include

- reference mean `< (967/1000) * κ`;
- kernel maximum `< (4/5) * L`;
- per-class winner weight `< (17/40) * L * κ`;
- diagonal term `< (13/40) * L^2 * κ`;
- post-sign positive part `< 47/100`;

where `κ = 2^-127`.

Nonce reuse is included in the availability calculation. The resulting honest
signing failure is at most `2^-129`, within the required `2^-128` bound.

## Authentication and actual-cache security

Every supported cut has equal reconstruction cost, and every hash node costs at
least one compression. If no value of a cut `c` is computed during the
reconstruction of a cut `c'`, then the expanded set of `c'` is contained in
the expanded set of `c`; equal cost makes them equal. So reconstruction from
the forged cut evaluates a value disclosed by the signed cut.

A DAG needs one more rule: every non-expanded hash node has a kid outside the
needed set. Without it, a disclosed node whose kids are all needed can be
expanded for free at equal cost. In this graph the rule is structural: a node's
exclusive kid is needed exactly when the node is expanded. For distinct cuts,
take a node `u` expanded by the forged cut and not by the signed cut. Its
exclusive kid is hidden under the signed cut. Descending from the root along
the forged expansion, each step gives a 129-bit (root: 128-bit) second
preimage or equal inputs. At `u` the equal input contains the hidden kid, so
the query is a hidden key-generation point. This supplies the concrete
cross-cut authentication event.

The 16-bit tag names at most one node, whose hidden kid is a free uniform
129-bit coordinate, so a hidden hit has probability at most `2^-129`. The root
binding rate `2 * 2^-129` is below `2^-129` times the root's block cost 4, so
every query is still covered at `2^-128` per compression.

The replay proof keeps the actual shared memoized cache. It separately tracks

- all exposed 342-bit index inputs;
- the selected message's 86-bit nonce row;
- repeated decodings of the same class;
- paid non-index queries;
- the post-sign remaining budget.

For each message row, the good event has 162 coordinates: 160 prefix deficits,
the reference score, and the literal post-sign excess score. Direct Freedman
bounds give a simultaneous empirical failure at most `2^-512`. Completion of
all message rows contributes at most `2^-760`, and the simultaneous class
occupancy cap fails with probability at most `2^-334`.

For `B <= 2^86/64`, stopped first and second moments give the coefficient

`6235189 / 6272000`.

For `2^86/64 <= B <= 2^127`, an equality-collision martingale, global diagonal
clock, and occupancy cap give four `2^-244` tails plus the `2^-334` occupancy
tail and coefficient

`2423 / 2450`.

Both coefficients are strictly below one. Above `2^127`, the universal
probability bound closes the security inequality directly.

## What required care

Treating the `2^20` nonce draws as fresh would be unsound: duplicate nonces
reuse the same memoized answer. Availability explicitly includes the
`L / 2^86` collision term, and the security proof retains private nonwinning
queries and charges their later public exposure.

A `1/100` allowance for the completed-row excess does not close the large
scalar inequality:

`1/2 + (99/98)*(48/100) > (99/98)*(968/1000)`.

The final proof controls the excess score directly at `1/1000`, producing the
`471/1000` completed-row bound.

The completion-table good event cannot be assumed pointwise after an adaptive
transcript. Its failure is averaged through the actual preceding computation.

## Validation

The development build and a clean build pass on the pinned Lean 4.33.1 contract.
The clean build completes 8,851 jobs in 104.298 seconds. The required endpoints
are `scheme`, `admissible`, `secure`, and `cost : scheme.VerifyCostAtMost 87`.

The exact exported challenge statements and primitive definitions match. Exported
axiom checking passes with only `propext`, `Quot.sound`, and `Classical.choice`.
All 29,705 exported solution declarations replay successfully in a fresh Lean
kernel environment: 109.522 seconds for replay, about 132.2 seconds for the entire
parse/compare/axiom/replay stage. Source policy and protected-file checks also pass.

Reproduce the official check from the repository root:

```sh
python3 .contract/verifier/verify.py upper-compressions --source .
```

Local numerical evidence, build logs, and standalone comparator/kernel replay
are kept outside the admitted proof root. The local official sandbox refuses
to start because this host's kernel does not enable Landlock; no sandbox check
or protected definition was weakened. Public verified status requires the hosted
verifier's durable verdict.

## What to try next

An 86-compression construction under the unchanged schedule needs at least
`676013856769711926075368867014708` cuts at graph reconstruction cost 85.
This submitted graph has only `450123217072147955044066685848890` such cuts,
about 66.58% of the requirement. The searches here do not prove optimality.
Different numbers of block tops, differently sized blocks, and sharing between
blocks remain candidates for further work. Any change must retain the exclusive
hidden-child argument, or replace it with a new authentication proof.

## Credits

- The 88-compression record by `lucemans`, assisted by Claude Opus 5.5, supplies
  the shared-DAG proof architecture: PR #58, checked commit
  `ee2e551ad841bc25a2daa2be643061162cffe809`.
- The 91-compression record, PR #19, supplies the chain-18 compact schedule,
  collision-aware replay, actual-cache security, and equal-cost cross-cut argument.
- This 87-compression graph search, exact checking, proof adaptation, and validation
  were developed with Codex.
