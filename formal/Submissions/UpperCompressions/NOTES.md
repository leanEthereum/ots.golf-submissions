# Candidate 85: a seven-top graph under a two-compression root

This candidate proves a worst-case verification bound of **85 compressions**,
including rejecting inputs: 1 index query + 82 in-graph compressions + a
2-compression root. It is the checked 86 construction (PR #68) with a different
graph. The 160-tier signing schedule, 86-bit nonce, 129-bit values, class count
and the whole security argument are unchanged.

## Idea: count cuts as reachable compositions

A graph of this family is 42 "long chains". A long chain is either a plain
hash chain, or a spine of ternary nodes ending in a private hash chain: each
spine node has its exclusive kid (the next spine node, or the private chain)
and up to two shared inputs, which are heads of other long chains. The proof
already sees the graph this way (`privatePathLen`, `privatePathAt`).

A cut is then a vector `a` with one entry per long chain, `a_i` being the
compressions spent on it (expanded spine nodes plus walked chain steps), and
the in-graph cost is the sum. A vector is a cut exactly when every long chain
with `a_i > 0` is reachable: the tops are always present, and an expanded spine
node makes its shared targets present. Hence

    cuts of in-graph cost r = C(r + 41, 41) * P[a uniform composition of r into 42 parts is reachable].

A Monte Carlo estimate of this probability agrees with the exact counter on
the 86 graph and on the new one. Two consequences drive the design:

- A spine helps a target only through its shallowest reference to it. A
  second, deeper reference from the same spine adds nothing.
- An entry is at least `d` with probability about `(2/3)^d` at `r = 82`, so a
  reference at depth `d` of a present spine fires with that probability. The
  targets just below the tops have the fewest possible referrers and decide
  most of the loss.

The 86 graph keeps 88.60% of `C(123, 41)`. Most of its loss comes from seven
long chains high in the order: each is positive but unreachable in 2 to 4% of
compositions, against 0.2 to 0.5% for the others.

## Construction

Order the 42 long chains and let references point only downwards. Fill the
targets from the top of the order down. Each target takes the strongest free
reference slots above it, at most one per spine, until its estimated
unreachability drops below a threshold (0.003 here). Then delete the three
nodes whose removal costs least, which gives exactly 213 nodes, so most
constants of the 86 proof stay as they are.

The result has 41 spines and one plain chain. Spine lengths are 6 (28 spines),
5 (5), 4, 3, 2 and 1 (2 each). Seven spines of 6 nodes are the tops. 207 nodes
have two shared inputs and 6 have one. Every non-top long chain is referenced
by 6 to 19 nodes.

Exact count at in-graph cost 82:

`705154647346183708283501533499397`

The schedule needs `676013856769711926075368867014708`. The candidate has
**4.311%** more, which is 92.32% of `C(123, 41)`. Every cut discloses at most
42 words, by the same structural proof.

The root reads seven tops: `16 + 7*129 = 919` bits, two compressions. Key
generation costs `42*24 + 213 + 2 = 1223`. Total `1 + 82 + 2 = 85`.

Greedy designs of the same kind, exact counts relative to the schedule's need
at in-graph cost 82:

| Tops | Nodes | Count / need |
|---|---|---|
| 7 | 185 | 1.0297 |
| 7 | 216 | 1.0411 |
| 7 | 272 | 1.0641 |
| 5 | 272 | 1.0391 |
| 4 | 272 | 1.0149 |
| 3 | 320 | 0.9814 |

## Proof changes

Only data and constants tied to the root change. Every proof script is kept
except one line.

- `LongChain91Geometry.lean`: the tables (`kid`, `top`, `privateOwner`,
  `kidIsTop`, `topSet`, `kidsH`, `kidsC`, the mask and list lookup trees,
  the private paths), `topMask`, the path population bound, the generating
  number and the exact count. Root arity 11 becomes 7, root cost 3 becomes 2,
  reconstruction cost 85 becomes 84. A script regenerates the file from the 86
  file and the graph, and checks every `decide +kernel` side condition first.
- `LongChain91CutBridge.lean`: root charge 2, reconstruction cost 84, key
  generation 1223.
- `LongChain91Auth.lean`: the root's exclusive kid is `top 6`; root input
  919 bits. In `sprRate_le_query_cost` the root case is now an equality,
  `ε + ε ≤ ε * 2`, since the root still binds 128 bits and costs two blocks.
- Key generation cost 1224 becomes 1223 in the six files that carry the
  experiment budget. Claim 86 becomes 85 in `LongChain91Scheme.lean` and
  `Solution.lean`.
- The 14 `ProofBundle` files and the schedule files are untouched.

The counting certificate is much smaller. The memoised recurrence has 2260
states against 72680 for the 86 graph, because the layered references leave
few distinct needed-sets. `LongChain91Geometry.lean` builds in 61 seconds
against 165 for the 86 file on the same machine.

## Validation

The required exports are `scheme`, `admissible`, `secure` and
`cost : scheme.VerifyCostAtMost 85`.

- The official pipeline, run locally from the repository root against contract
  `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c` with Lean 4.33.1, reports
  `verified` at claim 85: policy checks, exact statement comparison, the
  permitted-axiom check and a fresh kernel replay all pass ("Lean default
  kernel accepts the solution"). The run took 336.5 seconds with a peak
  resident size of 8.2 GB. The 86 record took 1036.7 seconds on the same
  machine, although other jobs were running during that measurement.
- The local run was on macOS, where the verifier is not sandboxed. It is
  development evidence and not a hosted verdict.
- The cut counter used for the search reproduces the 86 graph's exact count
  `676752439849646922507063152752853` and its 72680 recurrence states. Two
  independent implementations, one with the proof's radix `2^111` recurrence
  and one tracking disclosed words, agree on the new count, and no cut
  discloses more than 42 words.

Reproduce:

```sh
python3 .contract/verifier/verify.py upper-compressions --source .
```

## What is left

- **84 needs a one-compression root**, so at most three tops (`16 + 3*129 =
  403` bits). The greedy three-top design reaches 98.1% of the needed count
  and a short hill-climb on the exact count reaches 98.6%. Four tops reach
  101.5% but need two root blocks.
- A one-block root also fails `sprRate_le_query_cost` as stated. The root
  binds 128 bits, so its second-preimage rate is `2ε` while one block is
  charged `ε`. A different charge for root queries would be needed.
- In-graph cost 81 is out of reach for this family with any schedule:
  `C(122, 41)` is 78% of `4 * 2^107`, the floor for best-of-`2^20` signing. So
  84 is the floor for this approach.

## Credits

- The 86 record by `nconsigny` (PR #68) supplies the whole proof used here:
  the shared-DAG architecture with exclusive kids, the memoised counting
  certificate, the cut bridge and the authentication argument.
- The 88 record by `lucemans` (PR #58) introduced the shared-DAG blocks, and
  the 91 record (PR #19) the compact schedule, the collision-aware replay and
  the equal-cost cut argument.
