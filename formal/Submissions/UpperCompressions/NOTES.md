# Candidate 89: fused shared-DAG blocks with collision-aware replay

This root claims a worst-case verification bound of 89 compressions for the
generic upper-bound track. It exports the canonical raw bit-string scheme,
including deterministic verification, oversized-input rejection, admissibility,
and 127-bit strong security.

## Construction

The DAG consists of seven identical blocks under one root. Each block has

- 8 chains `c0, c4, c6, c7, c11, c13, c17, c20`, each with 18 one-compression
  steps;
- 13 hash nodes, two binary and eleven ternary, each costing one compression
  (kids in input order, high word first; the last kid is the low word):

| node | kids | exclusive kid |
|---|---|---|
| h5 | c4, c0 | c0 |
| h8 | c4, h5, c7 | c7 |
| h9 | c4, h8 | h8 |
| h10 | h5, h9, c6 | c6 |
| h12 | h5, h10, c11 | c11 |
| h14 | h10, h9, c13 | c13 |
| h15 | c4, h5, h14 | h14 |
| h16 | h9, h15, h12 | h12 |
| h18 | h9, c4, c17 | c17 |
| h19 | h15, h10, h18 | h18 |
| h21 | h9, h15, c20 | c20 |
| h22 | h5, h10, h21 | h21 |
| h23 (block top) | h16, h19, h22 | all |

The root hashes a 16-bit tweak and the seven block tops (`16 + 7 * 129 = 919`
bits, two compressions). All disclosed graph values are 129 bits; the public
key is the low 128 bits of the root output. Input lengths are 145 (chain step),
274 (binary node), 403 (ternary node) and 919 (root). None equals the 342-bit
index query.

The graph is a DAG, not a tree. The hub chain `c4` and the nodes `h5, h9, h10,
h15` have several parents, so one disclosure or one expanded node serves
several parents. The other seven chains are private: each is the exclusive kid
of one node. Every hash node has an exclusive kid, which is a kid with no other
parent, and it sits in the last (low) input slot.

Key generation costs

`7 * (8 * 18 + 13) + 2 = 1101`

compressions.

## Cuts

A cut expands a set `E` of hash nodes in each block. The needed values are the
root inputs and the kids of expanded nodes. A needed hash node outside `E` is
disclosed. A needed chain is disclosed once at one position `t` in `[0, 18]`,
whatever its number of parents, and costs `18 - t` steps. Each block has 873
valid expanded sets.

A cut is supported if its graph reconstruction cost is exactly 88 and it
discloses at most 42 words. There are exactly

`789639520673168360830123672680154`

supported cuts (`1.168` times the schedule cardinality). The count is the
seventh power of the per-block generating number, read off in base `2^330`.
The scheme uses a subfamily of exactly

`676013856769711926075368867014708`

cuts, the cardinality of the record's schedule, so the schedule and all its
probability certificates are unchanged. Distinct scheduled classes are mapped
injectively to this subfamily.

## Signature and verification cost

A signature contains an 86-bit nonce and at most 42 disclosed 129-bit values:

`86 + 42 * 129 = 5504` bits.

Verification reconstructs the selected cut in 88 compressions. Its
256-bit-message/86-bit-nonce query has length 342 and costs one compression,
so the worst-case total is 89 on arbitrary raw inputs and oracle-answer paths.

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
binding rate `2 * 2^-129` equals `2^-129` times the root's block cost 2; the
inequality is tight and still covers every query at `2^-128` per compression.

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

Run from the repository root:

`python3 .contract/verifier/verify.py upper-compressions --source .`

The exported endpoint and each newly introduced proof layer were also compiled
with Lean 4.33.1 while developing this submission. Public verified status
begins only with the hosted durable verdict.

## What to try next

The smaller numerical margin is the small-budget coefficient
`6235189/6272000`. Possible gains are a tighter stopped factor than `65/64`, a
smaller empirical multiplier than `99/98`, or a schedule with a lower reference
mean while preserving the collision moments.

An 88-compression candidate needs graph reconstruction cost 87 with at least
`676013856769711926075368867014708` supported cuts under the same 42-word
disclosure bound.

## Credits

- The 91-compression record (PR #19) supplies the chain-18 compact schedule,
  the collision-aware replay and actual-cache security proof, and the
  equal-cost cross-cut argument.
- The fused shared-DAG blocks were prepared with Claude Opus 5.5.
