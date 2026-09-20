# Upper-compressions research and 102-compression certificate

This submission exports a complete 102-compression certificate;
`README.md` describes the construction and proof map. Its bit-string admissibility,
127-bit strong security and all-input cost theorems pass pinned Lean 4.33.1 with
only the permitted axioms. Final local replay evidence is recorded below. The
hosted verification verdict is still outstanding. The research chronology below
records the local work that preceded this initial submission.

## The technique

This submission lowers the upper-compressions claim from **104 to 102** with a complete certificate of admissibility and 127-bit strong unforgeability. The verification bound covers every input and oracle-answer path, including rejection.

The technique combines two changes: **remove the intermediate subtree layer, and choose the number of accepted indices to meet the signing-failure requirement.** The smaller family makes it possible to disclose cuts that take one fewer compression to reconstruct.

### A shallower forest

Start with 54 independent 128-bit seeds. Extend each through 18 tagged hash steps, combine each triple of chain tips into a group digest, then hash all 18 group digests directly into the public key. Each digest retains the low 128 bits of the 256-bit oracle answer.

```text
54 independent seeds
        │  18 hash steps per chain
54 chain tips
        │  3 tips per group
18 group digests
        │  one tagged root hash
128-bit public key
```

Every hash input includes a 16-bit node tag. The chain, group, and root inputs are 144, 400, and 2,320 bits, so their actual compression costs are 1, 1, and 5. The tags are charged in the same shared random oracle as every other query.

A signature reveals six group digests and one value on each of the 36 chains in the remaining twelve groups. Choose those chain positions so their remaining hash costs sum to 84.

| Work or space | Exact accounting |
|---|---:|
| Key generation | `54 × 18 + 18 + 5 = 995` compressions |
| Disclosures | `6 + 36 = 42` words, or 5,376 bits |
| Full signature | `128 + 5,376 = 5,504` bits |
| Reconstruction | `84 + 12 + 5 = 101` compressions |
| Verification | `1` index query `+ 101 = 102` compressions |

### Enough indices, with a proof of availability

The certified number of distinct cuts is

$$
\binom{18}{6}\,[x^{84}](1+x+\cdots+x^{18})^{36}
=29{,}487{,}481{,}484{,}631{,}239{,}862{,}222{,}768{,}351{,}166{,}608.
$$

This is smaller than the previous `2^115` index family. It is still large enough for **`M = 45 × 2^109` distinct indices**, which meets the required signing-failure bound.

Signing samples nonces without replacement and hashes the message with each fresh 128-bit nonce, accepting when the resulting 128-bit index is below M. Each fresh trial succeeds with probability

$$p=M/2^{128}=45/524288.$$

The availability proof groups the `2^20` trials into 128 blocks of 8,192. The first four binomial terms prove `(1 + 45/524243)^8192 ≥ 2`. Since `1 + 45/524243 = 1/(1-p)`, each block fails with probability at most one half, hence

$$(1-p)^{2^{20}}\le(1/2)^{128}=2^{-128}.$$

The proof establishes freshness for the actual signing computation, including messages chosen as a function of the public key: key generation uses input lengths 144, 400, and 2,320, while indexing uses 384 bits. Distinct signing nonces then give distinct fresh index queries.

For comparison, the same shallow forest with chain cost 85 supplies enough cuts for the old `2^115` threshold and gives 103 total compressions. Proving that the smaller threshold is sufficient is what makes chain cost 84—and **102 total**—available.

### Strong security is preserved

The selected cuts are injectively indexed, satisfy the disclosure constraints, and all have reconstruction cost 101. The tree proof shows that distinct cuts in this family cannot be derived from one another. The security proof then combines hidden key-generation inputs, fresh-answer prefix events, and the index potential for the smaller family. The index-security argument is checked again at this M; its hypotheses do not require M to be a power of two.

It covers a different cut, a different payload for the same cut, and signing failure, preserving strong unforgeability even for alternative signatures on the signed message. For any attainable whole-experiment budget `B ≤ 2^127`, the proof gives

$$\Pr[\mathrm{forge}]\le\frac{B-995}{2^{127}}<\frac{B}{2^{127}}.$$

Larger budgets follow from the probability bound of one. The transmitted bit-string interface also proves accepted-input canonicality, so alternative encodings do not create an unaccounted forgery.

The protected contract is unchanged. `IndexedScheme` is a submitted local interface parameterized by M; it reuses the protected graph and oracle semantics. `Shallow*` supplies the concrete construction and full proof. `README.md` maps the modules, and `NOTES.md` records the technique, experiments, unsuccessful alternatives, and next directions. The generic proof infrastructure is reused from the existing 104-compression certificate.


## Research chronology

The entries below retain the research chronology, including earlier statements
that the candidate was incomplete or the exported claim was still 104. Those
statements describe the stage at which they were written.

# Historical baseline: 104 compressions

## Idea

Use the prepared six-subtree forest with 54 chains of length 14. The cut family fits the disclosure budget and reconstructs within 103 compressions; the message-and-nonce index adds one.

## Result

This submission packages the existing 104-compressions certificate from
`TomWambsgans/ots.golf-submissions` commit `fcb41a3a86ec552a7601394fdd8f6b4cf75acfae`.
The Lean files and `claim.txt` are unchanged. See `README.md` for the construction and proof map.
The hosted verification result is pending at submission time.

## What did not work

No new proof experiments were performed while preparing this submission, and the existing
README does not record failed approaches. The local official verifier could not start because
the verifier tools are not installed in this checkout; this is a setup limitation, not a proof verdict.

## Next

Investigate alternative cut families or forest shapes while retaining signing availability, strong security and the payload budget.

## Local exploratory research (2026-09-19; not a verified improvement)

The public notes journal still reports 104 as the verified compression record. A read-only
GitHub discussion query returned no discussion threads in the submissions repository.
No GitHub writes were made during this research.

Exact integer enumeration of all disclosure shapes of the existing 6-by-3-by-3 forest,
at chain length 14 and with at most 42 disclosed words, gives only about 2^114.657122
cuts at exact reconstruction cost 102. Thus merely adding omitted shapes at that
cost does not meet the existing 2^115 index-family threshold. This is not a lower
bound for arbitrary cut families or arbitrary schemes.

A structural screen of two-level regular forests used 1--24 root children and
1--8 children at each of the next two levels. Chain lengths consumed the remaining
1024-compression key-generation budget. Counts used exact integer polynomial
coefficients, actual 16-bit-tweaked hash-input lengths, and a 42-word disclosure cap.
The best screened candidate has total verification cost 103. It simplifies to a
shallow forest with 18 ternary groups and 54 chains of length 18:

- Key generation: 54*18 + 18 + 5 = 995 compressions.
- Root input: 16 + 18*128 = 2320 bits, costing 5 compressions.
- Reveal 6 group digests and one value from each of the other 36 chains: 42 words.
- Chain reconstruction cost 85, plus 12 group hashes and 5 root compressions,
  gives 102 reconstruction compressions; the index query adds one.
- The single-shape count is C(18,6) times the coefficient of x^85 in
  (1+x+...+x^18)^36, namely 41543031742324041932159566097104416.
  This exceeds 2^115. Including other permitted exact-cost shapes gives
  43855251196801926587622830049099996 cuts, independently reproduced by a
  second enumeration of the simplified shallow forest.

These are numerical construction checks, not a security certificate. No exported
scheme, claim, security proof, or availability proof has been changed. The candidate
still needs a complete DAG construction, proof transfer, and official verification.
It is a useful baseline rather than the substantial breakthrough being sought.
Next investigate irregular trees and constructions outside the regular forest family;
also separate the sufficient 2^115 indexing threshold from the actual availability
constraint when evaluating more ambitious candidates.

## Structural follow-up and availability threshold (local, unverified)

Two additional screens used 12 local worker processes, with scratch scripts and results
in `/tmp/ots-research/` (these scratch files are not part of a proof submission):

1. 105 trees: 42--84 leaves in steps of three, each with flat, binary, ternary,
   mixed binary/ternary, mixed 2/3/7, deep ternary, or ragged branching. A bivariate
   polynomial tracks disclosure count and exact reconstruction cost. For a hash node
   with children F_i, its polynomial is y + x^h * product(F_i), with
   h = ceil((16 + 128*arity)/512). A length-L chain has polynomial
   y*(1+x+...+x^L). Coefficients above 42 disclosures or 104 reconstruction
   compressions were discarded. Positive floating-point convolution screened the
   trees; exact integer recomputation confirmed the best result, still 103 total.
   The recurrence also matched independently implemented shape counting on small
   forests and the 54-chain candidate. These sampled shapes are not exhaustive.
2. 1,098 valid constructions moved chains onto internal edges above branching nodes.
   Root arity ranged from 2 to 42; branch arity was 2, 3, 4, or 7; internal chain
   length was 0, 1, 2, 4, 8, 16, or 32. Remaining key-generation budget went to
   uniform leaf chains. A group polynomial is
   y*(1+...+x^K) + x^(K+h(a))*[y*(1+...+x^L)]^a.
   None beat 103 at the 2^115 family threshold. The best positive-internal-chain
   candidate in this screen cost 105. Three leading results were recomputed exactly.

The fixed 2^115 threshold is NOT necessary for an arbitrary oracle-program upper
submission. It is hardcoded in the protected DAG interface, so exploiting a smaller
family requires a custom submitted oracle construction and corresponding security proof;
the protected model must remain unchanged.

For 2^20 fresh independent index trials, failure <= 2^-128 requires an acceptance
family of at least ceil(2^128 * (1 - 2^(-128/2^20))) indices, whose log2 is approximately
114.4711725923. The same shallow forest has
M = 31179843107214461927616603288863712 cuts at reconstruction cost 101,
hence total verification cost 102. Its predicted failure is about 2^-138.62094.
More robustly, Python exact integer arithmetic verified

    2 * (2^128 - M)^8192 <= (2^128)^8192.

Repeating that block bound 128 times establishes the required numerical availability
inequality. This does not establish freshness, correctness, strong security, or the
Lean certificate for a changed scheme. It upgrades the numerical target to 102,
not the verified record. Cost 101 in this same candidate has only 2^114.08895 cuts,
below the actual availability threshold.

Local verification setup currently has Lean 4.32.2, while the contract pins 4.33.1;
the filesystem had about 368 MB free when checked. No large dependency installation
was attempted. Only research notes in the admitted root were changed; claim.txt and
all existing Lean proofs remain unchanged. There were no GitHub writes.

## Tree-wide envelope experiment (local, no improvement)

The public journal was read again and still listed the 104 record. The next experiment
maximized F_T(x,y), the cut generating polynomial evaluated at positive x,y, over
all rooted trees of tagged 128-bit values with key-generation cost at most 1024.
This allows arbitrary branching, arbitrary depth, and unary chains on any edge.
The hash cost for a children is 1+floor(a/4). A max-product dynamic program tracks
the child count modulo four, as well as total child cost plus floor(child count/4).
For fixed x,y, maximizing a subtree's polynomial independently is valid because all
coefficients are nonnegative. The calculation is a floating-point research tool,
not a Lean theorem or a certified numerical lower bound.

Exhaustive enumeration of all 3,317 trees with total cost at most four agreed with
the recurrence at x=5/8, y=3/8, using exact rational values for the enumeration.
Eight positive evaluation points were optimized for reconstruction budgets
60, 70, 80, 85, 90, 95, 100, and 101. The maximizing 1024-cost trees were recovered
and their full disclosure/cost spectra screened. None reached 2^115 cuts within
104 reconstruction compressions. At cost 101 their counts ranged from about
2^106.47 to 2^113.36, below the shallow forest's 2^114.586. Maximizing a polynomial
evaluation does not maximize an individual coefficient, so this is not an
optimality proof and does not exclude other trees.

A simpler counting observation is stronger than this envelope at low budgets:
encode a cut by a deterministic traversal, writing a zero for a disclosed word
and a one for each compression of an expanded hash. For this tagged-word tree
class, complete traversal strings are prefix-free. A prefix-free binary code
using at most c ones and d zeros has at most C(c+d,d) words (the two first-bit
branches give Pascal's recurrence, with boundary value one). The root is always
expanded, so for nontrivial cuts one may remove its first one, giving
C(c+41,42) with d=42. At reconstruction cost 89 this bound is below the actual
availability threshold of the independent 128-bit index sampler; at 90 it is
above. This is an informal restricted-family argument, not a new general lower
certificate. The repository already has a 90 lower record for its whole-word
framework, whose syntax differs from these 16-bit-tweaked trees.

Nonce reuse ideas were also considered, without a valid construction. Permuting
disclosed words to encode the nonce must still preserve the node-to-value
assignment; counting the permutation space twice is invalid. Selecting a nonce
from key-generation values leaves only a small set of distinct index trials.
These observations reject the naive forms, not every possible nonce-sharing scheme.

Concrete next question: can sharing hash outputs across branches produce a large
family of mutually non-derivable disclosures at lower reconstruction cost? Counting
raw DAG frontiers alone is insufficient: a revealed frontier may allow computation
of additional nodes and conversion to another purported signature. A small-DAG
experiment should calculate both reconstruction cost and this closure relation.
No question was posted to GitHub, per the user's instruction.

## Shared-DAG experiments and local proof tooling

The next screen enumerated 54,004 frontiers across 252 small single-output DAGs.
221 graphs had distinct equal-cost frontiers related by forward derivation. For
example, with a=H(tag_a||s), b=H(tag_b||s), and r=H(tag_r||a||b), the frontiers
{s,a} and {s,b} both reconstruct with two hashes but derive one another. Raw
frontier counts therefore substantially overstate usable signature families.

The filter requires a valid, relevant frontier A to be forward-closure independent:
no a in A is computable from A minus {a}. After filtering, 6,349 frontiers remained,
with no distinct equal-cost derivation in the sample. An independent exhaustive
check covered all 32,767 topologically ordered DAGs on two through six vertices
whose final vertex is a hash. It found 148,732 directed equal-cost derivation pairs
before filtering. Among 56,073 valid, relevant, independent frontiers, all 29,566
comparable distinct pairs strictly decreased reconstruction cost. Another check
covered 3,052 small two-output DAGs with gate-based costs and reached the same
conclusion for reduced frontiers.

The structural proof sketch is: if B is derivable from independent A, reconstruction
from B cannot evaluate an A disclosure, since that would derive it from the other
A disclosures. Thus the evaluated gates for B are a subset of those for A. Distinct
relevant frontiers force a proper inclusion, and positive gate costs force lower
cost. This supports repeated disjoint motifs and private source chains. This is
not yet a formal theorem or a random-oracle security reduction. Free aliases and
mixed whole/half-output encodings need additional canonicalization.

Repeated copies of the 247 distinct cleaned motif spectra, with source chains and
a common root, were screened at 14 repetition counts from 4 to 42. None beat the
existing 102 numerical target under the actual availability threshold. Exact
integer recomputation of three finalists confirmed their first passing costs.
The best non-tree motif used three sources a,b,c, u=H(a,b,c), v=H(a,c,u), with
tags on both hashes. Eighteen copies and length-18 source chains cost 1013 to
generate. At reconstruction cost 101 it has
31272784319994052187198825598130233 cuts, slightly more than the shallow tree but
still only a 102 total candidate; its preceding layer misses the threshold.

Separately, 164 fork/merge architectures exploited both 128-bit halves of each
256-bit answer. A fork's two branches could be disclosed separately or regenerated
from their common seed. Best screened total cost was 104, worse than 102. The
polynomial recurrence matched explicit enumeration on 11 small circuits and 366
canonical cuts. This rejects the tested family, not every multi-output DAG.

Scratch artifacts are in /tmp/ots-research/dag_frontiers.py, dag_motifs.py and their
JSON results, /tmp/ots-dag-security/criterion.md and exhaustive checks, and
/tmp/ots-alternative/REPORT.md and fork/merge scripts. The criterion report gives
the proof sketch, composition argument, assumptions, and caveats in detail.

The disk-space obstacle to local Lean checks has been resolved using an isolated
host RAM filesystem at /dev/shm/ots-proof-env. Pinned Lean 4.33.1 and all 8,690
Mathlib cache files were installed there, using approximately 11 GiB. The release
archive's SHA-256 was checked against its release metadata. The original contract
checkout and other tracks were not modified. The wrapper
/tmp/ots-research/lean433.py enforces eight CPUs, a 20 GiB process RSS limit and a
600-second timeout. It requires the host mount namespace (sandbox escalation).

Official verification remains a separate limitation: the host exposes Landlock
ABI 2, below the required ABI 3, and systemd 252 rejects PrivatePIDs=yes. No
official verifier gates were bypassed. Local Lean checking is not an official
submission verdict. No GitHub writes were made.

## Lean-checked shallow-family counting helper

`ShallowCount.lean` now proves the bounded-composition cardinality interpretation,
its dynamic-programming recurrence, and both exact coefficients using kernel
reduction (no native_decide):

    comp 36 85 = 2237827609476623676586919095944
    comp 36 84 = 1588422833690542979003596657572

The first coefficient gives the previously described single-shape 103 candidate.
More usefully, the second shows that the 102 candidate can ALSO use a single shape:
reveal six of eighteen group digests and 36 chain values of total cost 84. Then
5 root + 12 group + 84 chain = 101 reconstruction compressions. There are
29487481484631239862222768351166608 choices, at least 45*2^109. Using that many
accepted 128-bit indices gives success probability 45/524288 per fresh trial.
This simpler family avoids needing the union of multiple shapes for 102.

The helper passed pinned Lean 4.33.1 in 62.53 seconds, with observed peak process
RSS about 10.13 GiB. Both single_shape_ge and single_shape_102_ge use exactly
propext, Classical.choice and Quot.sound. The checked source SHA-256 is
a6142df965081e7f00f85e4f7be8aaa1fb9d6aeba757e8f71ae2adec0788bfcc.
The helper is not imported by Solution.lean and does not change the exported scheme.
It proves counts of abstract choices, not their injective realization as graph cuts,
nor admissibility or security of a new OTS.

Inspection of the existing row-potential argument found its numerical assumptions
compatible with M=45*2^109: nonceBits=idxBits, idxBits<=256, 2<=M,
2*M<=2^128, and 24*trials<=2^128. Its current declarations still refer to the
protected Dag.numCuts, so they cannot be applied unchanged to a custom M. A local
submitted scheme/program layer can reuse protected Dag.Graph and the generic
graph/cache/wire lemmas. The main concrete port is Names/Tree/Cuts, followed by
Values.card_updHash_input_le, Resample's dependency and resampling-charge lemmas,
and Events' strong-forgery case analysis. The shallow graph has 3,026 nodes,
root input length 2,320 bits, and key-generation cost 995. The security assembly's
key-generation slack would become B-995. This is a dependency analysis, not a
checked security transfer. Details are in /tmp/ots-alternative/PROOF_TRANSFER.md.

The most recent read-only discussion query found no discussion threads in either
leanEthereum/ots.golf-submissions or leanEthereum/ots.golf-dev.

`ShallowAvailability.lean` separately proves the numerical failure inequality

    (1 - (45 : Real) / 524288)^(2^20) <= (2^128 : Real)^(-1).

It uses the first four binomial terms to lower-bound
(1 + 45/524243)^8192 by two, obtains an 8192-trial block failure bound of one half,
and raises that bound to the 128th power. Huge powers are not directly expanded.
Pinned Lean 4.33.1 checked the file in 3.84 seconds with about 3.87 GiB observed peak
RSS. The block_bound and signing_failure_bound theorems use only propext,
Classical.choice, and Quot.sound. This helper is also not imported by Solution.
It proves numerical algebra; independence/freshness of actual signing trials,
the construction's correctness, and strong security remain separate obligations.
The submission claim remains 104. Source-policy checks pass for the expanded root.

## Shallow forest proof transfer, 2026-09-20

The concrete graph and cut family now pass pinned Lean, beyond the earlier
abstract counting helper. `ShallowNames` builds the 3,026-node graph with exact
key-generation cost 995. `ShallowTree` proves traversal, cut coverage and the
same-cost cut nonderivability property. `ShallowCuts` proves the choice-to-cut map
injective, the exact family cardinality above, and for every member: a valid cut,
42 disclosed words (5376 bits), and exact reconstruction cost 101. Its complete
check took 6.97 seconds with approximately 7.38 GiB observed peak RSS. Checked
ShallowCuts source SHA-256:
51af54b03f98578b7fb96bfd7a801240fc9ecad27d0e096c375446c81425f618.

`IndexedScheme` defines a local scheme parameterized by the number of accepted
indices, using the protected graph and oracle semantics. It supplies a typed
adapter and experiment/security equivalence. `IndexedSampling` specializes the
signing analysis to M=45*2^109. The protected Dag.numCuts remains unchanged.
`IndexedAvailability` proves the actual fresh-cache signing-loop failure bound;
`IndexedFreshness` lifts this to the full key-generation and signing experiment,
including arbitrary public-key-dependent message choices, whenever the graph's
hash inputs avoid the 384-bit indexing length. `IndexedCorrectness` proves
perfect correctness, and `IndexedResources` proves the generic typed resource
bounds and verification determinism. These are all checked modules.

The smaller index space has also been carried through `IndexedCharges`,
`IndexedRho`, `IndexedRows`, and `IndexedPotential`. The row-potential charge and
domination lemmas and their concrete numerical hypotheses pass Lean. All reported
axiom audits contain only propext, Classical.choice, and Quot.sound. The concrete
Values/Resample/Events and final strong-security assembly are still being ported;
these intermediate results do not yet certify a 102-compression OTS. Solution and
claim.txt continue exporting the original 104 result.

A separate mixed-cost-antichain experiment found that restricting to a single
exact-cost layer can discard useful incomparable cuts. Strict improvements occurred
in 87 of 252 cleaned sampled DAGs and 16 of 1,154 exhaustively generated small
unordered trees of arity at most three and at most five hash nodes. One small tree
has antichain width three but largest exact-cost layer two. Four copies of a tested
DAG motif have maximum antichain 196 versus largest exact-cost layer 146, under a
12-cost/12-word budget. However, none of 71 tested constructive product-rank
families beat the 102 target at full scale. This is not an exhaustive rejection of
mixed-cost constructions. Details and executable experiments are in
/tmp/ots-antichains/REPORT.md. No GitHub writes were made.

## Complete 102 certificate and final local validation

The full shallow proof transfer is complete. `ShallowValues` and
`ShallowResample` establish the concrete tagging, cache, dependency and hidden
coordinate bounds. `ShallowEvents` covers signing failure, a different cut, and
a different payload for the same cut. `ShallowStageB`, `ShallowAssembly` and
`ShallowMain` prove strong security, using the bound (B-995)/2^127 for budgets
B <= 2^127 and the probability bound of one for larger budgets. `ShallowResources`
proves typed admissibility and all-input verification cost 102. `ShallowWire`
transfers the complete certificate to the protected bit-string interface, including
accepted-input canonicality. Solution.lean and claim.txt now export 102.

A combined named Lake build of ShallowWire and Solution completed successfully
in 107.28 seconds, with observed aggregate process RSS 14,581,244 KiB (about 13.91 GiB).
The counting module rebuilt in 57 seconds during that run; other already-cached
modules were reused. This is a warm local build measurement, not the official
verifier's time or memory verdict. The raw admissible, secure and cost declarations
use only propext, Classical.choice and Quot.sound. The compiled Solution source
SHA-256 is 9617a41aa78c2898d3e5eea6c8376e25896f231306980915ca54dca857b87cea;
ShallowWire is 51206e4e10ffc82b0ce69f05ee23960b943c374195f6f8a491063af8bd112cad.
Logs and metadata: /tmp/ots-research/build-ShallowWire-Solution.log and .json.

A separate source review compared the indexed interface with protected Dag and
OracleAlgorithm. It found no weakened strong-forgery predicate, budget,
nonce behavior, cut injectivity, or all-input cost. The keygenProxy is used only
for definitionally identical key-generation lemmas. Review report:
/tmp/ots-research/shallow-semantic-audit.md. An independent consistency review
confirmed the README's counts, bit lengths and costs against the proofs.

The official command was attempted on this 102 checkout and stopped before
checking the proof: `verification tools missing; run verifier/setup_tools.sh`.
Its result directory is /tmp/ots-verify-_y9o56uu. Independently established host
limitations remain Landlock ABI 2 (required >= 3) and systemd 252 rejecting
PrivatePIDs=yes. No verifier gates were bypassed and there is no hosted verdict.

A fresh read-only registry query still found the upper-compressions record 104,
source 64165c0c55807eae3d308615226d0f2a8696a5d8, from PR 4. Both repositories again
had zero GitHub discussion threads. No issues, PRs, comments or pushes were made.
At that checkpoint, the proposed PR body was only a local file at
/tmp/ots-research/PR_BODY.md.

Independent exact-declaration audits passed for both ShallowWire and the final
Solution. They check that the scheme is a safe definition of the protected
OracleAlgorithm.Scheme type, and that admissible, secure and cost are theorem
declarations with exactly the protected predicates on that scheme, cost 102 and
no universe parameters. Transitive axiom traversal accepts only the three
permitted axioms. All 21 protected source hashes in the isolated project match the
pinned manifest. Audit logs: /tmp/ots-dag-security/ContractAuditWire.log and
/tmp/ots-dag-security/ContractAuditSolution.log.

All 26 new proof modules and the changed Solution module also passed an independent
replay with the unmodified Lean 4.33.1 `leanchecker`. Each module's declarations
were replayed against its imported environment; this was not a fresh replay of
all Mathlib/VCVio/contract declarations from an empty environment. Workspace source
and compiled artifact hashes were checked before and after each replay. The final
27 passing runs totaled 271.85 seconds, with maximum observed process RSS
9,920,524 KiB (about 9.46 GiB). Source hashes still match the final workspace.
Results, scope and per-module logs are in /tmp/ots-dag-security/kernel-replay/.

The final source-policy check passes for claim 102, and git changes are confined
to the admitted UpperCompressions root. The candidate is ready for PR review
subject to the official hosted verification that this machine cannot perform.
No GitHub writes were made.

## Initial submission

The user subsequently authorized publishing this checked 102 candidate. The PR
contains the technique note above and requests the official hosted verification.
The proof sources and their checked hashes are unchanged; the publication update
only expands the explanation and makes the verification status explicit.
