# Candidate 86: one shared graph with the existing signing schedule

The candidate proves a worst-case verification bound of **86 compressions**,
including rejecting inputs. Local proof checks pass; resource measurement and
hosted verification remain pending.
It uses a single graph across 42 independent chains, replacing the three
separate blocks in the checked 87 construction. The 160-tier signing schedule,
86-bit nonce, 129-bit values and security target are unchanged.

## Construction and exact count

There are 42 chains of length 24 and 214 hash nodes. Eleven top values feed
the root. The exact ordered inputs appear in `LongChain91Geometry.lean`.
Unary and binary nodes are padded by repeating an existing input, giving
403-bit internal queries with their 16-bit tags. Each node's last input is
private to that consuming node; the same value may occur in another slot of
that node. Chain queries have 145 bits. Both query types cost one compression.

The root input contains `16 + 11*129 = 1435` bits and costs three compressions.
All tags are distinct. The public key is the low 128 bits of the root output.
Key generation costs `42*24 + 214 + 3 = 1225` compressions. There are 3710 named
nodes, including concatenations and truncations.

A cut discloses each needed chain once and each needed unexpanded hash once.
Expanded hashes are evaluated once and shared by all their consumers. The
supported family fixes chain-plus-internal cost 82, giving reconstruction
cost 85 after the root. Its exact class count is

`676745322862130083544291330002029`.

The existing schedule needs

`676013856769711926075368867014708`

classes. The candidate has **0.108203%** more and selects an injectively
indexed subfamily of exactly the required size.

The disclosure bound has a structural proof. Unexpanded hashes have distinct
private children, and those children are unneeded. Their injection into the
unneeded values bounds the number of needed values minus expanded hashes by
42. Thus every cut discloses at most 42 words. A signature uses at most
`86 + 42*129 = 5504` bits. The 342-bit message-and-nonce index query costs one
compression, giving a total of `1 + 82 + 3 = 86`.

The exact cost counter uses the same weighted recurrence as the cut-counting
proof. Private-child paths inject canonical choices into a product of 42
finite intervals. A path with `a` hashes has at most `a + 25` codes: its
expanded prefix length plus its walked chain suffix. The proved population
bound is `95265665839134290490590838458312294400000000000000000000000000`.
Radix `2^206` exceeds this bound, so coefficient extraction has no carries.
The computation is reduced modulo `radix^83` before extracting digit 82.

The certificate memoizes individual recurrence states, skips hash
variables whose need bit is absent, and proves each numerical step with Lean's
ordinary kernel. It does not use a native-evaluation axiom. The graph has
83063 distinct nontrivial recurrence states. Checked balanced lookup tables
supply the graph masks and their prefix unions. The complete construction,
admissibility, security, and cost proofs pass a clean Lean build.

Proof representation matters for this computation. The pinned toolchain's
default natural-number hash uses only the low 64 bits. The tactic's state
cache therefore mixes all four words of its hash mask. Its large polynomial
values all have constant coefficient one, so their low bits coincide too.
Each coefficient is represented by a literal with a distinct temporary low
word, followed by a right shift that removes that word. State masks use their
four-word hash in the same way. Lean's kernel checks the resulting arithmetic
equalities, and a proved congruence lemma aligns the initial mask with the
goal. These temporary words occur only in the certificate; the signature
scheme is unchanged. This representation also improves the distribution of
hashes in the exporter's expression table.

The original list counter reached 5272 frontier states and 340847 state visits
on this graph. Earlier graphs and list-counter implementations exceeded the
memory limit. The memoized certificate addresses that proof-engineering
obstruction without changing the signing schedule or security assumptions.

Independent research checks reproduce coefficients for scores 84 through 88
using GMP coefficient arrays and sliding-window chain convolutions. The search
used floating-point estimates only for ranking; those estimates overstate the
final capacity slightly and are not proof certificates.

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
binding rate `2 * 2^-129` is below `2^-129` times the root's block cost 3, so
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

## Further search

A private-child path decomposition gives the proved injective encoding used
above. Adding a cost-sum identity would bound a cost-r layer by
`binomial(r + 41, 41)`. At r = 81 this is
`509210537125015289581387223531062`, below the unchanged schedule's target.
The layer bound is not formalized here and is specific to this graph family.
It suggests exploring a smaller root, a different family, or a different
signing schedule when pursuing 85.

A first experiment sampled 100 ways to turn six of the eleven tops into two
new ternary nodes, leaving seven root inputs and a two-compression root.
The best tested merge has exactly `328174229109783911312517805967435`
classes at total score 85, only 48.5455% of the required count. These simple
root merges are insufficient; a seven-top graph would need further redesign.

## Validation status

The required exports are `scheme`, `admissible`, `secure`, and
`cost : scheme.VerifyCostAtMost 86`. The complete candidate passes a clean
Lean build in 379.547 seconds, with 10.319 GiB sampled peak PSS. All four
exports use only `propext`, `Quot.sound`, and `Classical.choice` in their axiom
closures. Solution export completed in 444.226 seconds. Exact exported
statement and primitive comparison pass, and all 112830 solution declarations
pass fresh Lean kernel replay. The initial interpreted check took 544.421
seconds, including 346.753 seconds of replay. Its pipeline total exceeds the
20-minute limit. A compiled local checker, matching the official comparator's
execution mode, is being measured before drawing a resource conclusion.

The previously checked 87 submission remains on its own branch. Its clean
build and fresh kernel replay do not certify this new candidate.

Reproduce the official check from the repository root:

```sh
python3 .contract/verifier/verify.py upper-compressions --source .
```

Research artifacts and numerical cross-checks are kept outside the admitted
root. This environment's official verifier fails closed because Landlock is
unavailable; no sandbox requirement was changed. A public record requires the
hosted verifier's durable verdict.

## Credits

- The 88-compression record by `lucemans`, assisted by Claude Opus 5.5,
  supplies the shared-DAG proof architecture: PR #58, checked commit
  `ee2e551ad841bc25a2daa2be643061162cffe809`.
- The 91-compression record, PR #19, supplies the compact schedule,
  collision-aware replay, actual-cache security and equal-cost cut argument.
- The 87 and subsequent 86 graph research and proof adaptations were developed
  with Codex. The global sharing search and the counter reductions are recorded
  in the accompanying research directory.
