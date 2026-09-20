# A tighter index proof gives 100 compressions

The proposed improvement is a tighter security argument that permits a **127-bit index while retaining the 128-bit nonce**. This halves the required number of cut classes without changing the signing acceptance probability. On the existing graph, chain reconstruction cost 82 then gives **82 + 12 + 5 + 1 = 100 compressions**.

**Status:** the complete exported 100-compression certificate compiles locally with pinned Lean 4.33.1, including admissibility, security, and the raw-signature cost bound. The frozen dependency rebuild, independent kernel replay, exact export-type and transitive-axiom audits, protected-source hashes, and submission policy all pass. Official hosted verification is pending. The prior [official 102 record](https://ots.golf/submissions/440fbe4103a5cfff1f213e25ac09bfd9) remains published in [PR #6](https://github.com/leanEthereum/ots.golf-submissions/pull/6).

## Same graph and signature size

The graph still has 54 independent 128-bit seeds, 18 hash steps per chain, 18 ternary group hashes, and one root hash. Its tagged input lengths are 144, 400, and 2,320 bits, costing one, one, and five compressions respectively. Key generation remains `54*18 + 18 + 5 = 995` compressions.

A signature reveals six group digests and 36 chain values from the other twelve groups. The chain positions now have total remaining cost 82. Thus the signature still contains 42 words plus its nonce: `42*128 + 128 = 5,504` bits. The message-plus-nonce index query remains 384 bits and costs one compression.

The selected cut family has exact size

    choose(18,6) * [x^82](1+x+...+x^18)^36
      = 14696477531177027506903935123070536.

This exceeds the new accepted-class count

    M = 45*2^108 = 14603334914629202705242020925931520.

Let `I=2^127`, `N=2^128=2I`, and `L=2^20`. The fresh-trial acceptance rate is unchanged:

    p = M/I = 45/524288,       pL = 90.

Consequently the existing availability arithmetic still proves failure at most `2^-128`. The chain-cost-81 family is too small for this particular M; the count above is the first sufficient rank of this fixed shape.

## Reserve the signer's full trial budget

The protected `CostAtMost` predicate bounds every raw oracle-answer path, including paths that would not be consistent with a memoized random oracle. This makes the following resource argument possible.

For any requested successful signer output, choose `L-1` distinct other nonces and force rejected answers, then choose the requested nonce and force its accepted answer. The returned signature and subsequent continuation are identical, while signing takes exactly L index queries. The failure output also has a length-L path. Therefore a pathwise budget for signing followed by an arbitrary adaptive continuation reserves L calls before bounding that continuation.

This uses `L<=N` and a nonempty rejected-index set. It does **not** use inconsistent answers in the probability analysis: actual success probabilities continue to use the protected single random oracle. It uses the stronger raw-path contract solely to establish the resource bound, including when post-sign behavior depends on the observed signature and subsequent oracle answers.

## Count repeated entries, then bound the signing row

Before signing, let q be the number of cached index inputs, A the number with accepted classes, and v the number of distinct accepted classes. There are `H=A-v` repeated accepted entries. In the selected message row, let a count accepted entries and b count entries whose class appears at another cached input.

A class of multiplicity k>=2 contributes k bad entries and k-1 repeats, so

    b <= a,       b <= 2(A-v).

The generic finite-fiber inequality and its cache instantiation are kernel-checked in `RepeatedFibers.lean`.

At a signing trial, at least `f>=2I-q-L` untried nonce slots are fresh. Its bad stopping mass is `b+fv/I`, and its accepting mass is `a+pf`. Set

    T = max(A, p(q+L)/2).

If T>=M, bad mass is at most accepting mass. Otherwise T>=A>=v and

    Mb-Ta <= (M-T)b <= 2(M-T)(T-v) <= pf(T-v).

Hence the bad/accepting ratio is at most T/M. The existing disjoint signing-loop argument turns this into a bound on the complete signing event. `TightRow.lean` proves the arithmetic; `TightPotential.rho_dom` connects it to the actual cache and the `signRho_bound` interface.

## A potential with charge exactly 1/I

Use the real potential

    rho = (A + pL/2 + exp(pq/2-A))/M.

It dominates T/M because `max(d,0)<=exp(d)`. A fresh index query increments q by one and increments A by a Bernoulli(p) indicator. Writing `d=pq/2-A`,

    (1-p)exp(d+p/2) + p exp(d+p/2-1) <= exp(d).

Thus the exponential term has nonpositive expected drift, and the accepted-count term contributes exactly `p/M=1/I`. Non-index queries leave this potential unchanged. The uniform-oracle charge and row domination are checked in `TightPotential.lean`.

The potential starts positive:

    rho(empty) = L/(2I) + 1/M.

The reserved signing budget pays for it. Since pL=90>2,

    L/(2I) + 1/M < L/I.

The strict surplus is `(22/45)*2^20` compression units divided by I. The completed assembly combines this index accounting with hidden-input and spurious-reconstruction bounds in the same simulation. Encoding queries have no authentication charge; other queries have no index charge. A terminal reserve passes through the master lemma, cancelling the positive initial potential.

The essential change is therefore a **security-proof improvement that uses the whole-experiment budget**. The lower cut rank becomes available as a consequence; the graph, word width, nonce, signature size, and key-generation cost stay the same.

## Proof map and validation

The new modules are `RepeatedFibers`, `TightRow`, `TightDrift`, `TightPotential`,
`SigningReserve`, `ReservedHazard` and `MasterReserve`. `ShallowAssembly` combines
these with the existing hidden-value and spurious-reconstruction analysis.
`ShallowCount100` certifies the rank-82 count. The final `Solution` exports the
protected scheme, admissibility, strong security and all-input cost-100 bound;
`ShallowWire` proves canonical raw encoding and rejects oversized signatures.

Every submitted module in the `Solution` dependency closure was rebuilt from
frozen sources, then independently replayed with the unmodified Lean 4.33.1
`leanchecker`. All 49 modules passed; a separate admissibility audit also
passed, for 50 modules total. The combined rebuild and replay took 526.41
seconds locally. The largest observed checker process used 9.31 GiB. Each
module was replayed against its imported environment; external library and
contract environments were not freshly replayed from empty.

Exact export checks confirm a safe scheme definition, the protected
admissibility and strong-security predicates, and the cost predicate with
literal claim 100. All four exports depend only on `propext`, `Quot.sound`
and `Classical.choice`. All 21 protected source hashes match. Frozen source
and artifact manifests and the original host artifacts remained unchanged.
Submission policy, sibling imports, patch application and whitespace checks
pass. A separate semantic review found no weakened experiment or interface.

The official local command stopped before proof checking with
`verification tools missing; run verifier/setup_tools.sh`. Official hosted verification is pending for this candidate. The local timings and replay results
are development evidence, not an official resource or competition verdict.

## What led to the tighter proof

We modeled the index mechanism as an exact finite adaptive game. A state records
accepted classes and rejected entries in each message row. The adversary can
query existing or fresh rows, choose when and which message to sign, and use
fresh queries or cached class matches after the signature. The private signer's
sampling without replacement is integrated exactly. This isolates replay; it
does not model attacks on the authentication graph.

The search covered 542 parameter/budget cases, with up to six pre-sign queries,
including closed forms evaluated at the full index size. Independent checks
covered 160 explicit private-signer enumerations, 32 dense/sparse state-model
comparisons and 192 posterior-probability calculations.

At equal nonce and index sizes, a two-query adaptive strategy really can exceed
`q/I` for pre-sign replay alone. For `I=8, M=4, N=L=8`, query one new row and,
if accepted, query that row again; otherwise query a fresh row. Sign the row
containing a repeated accepted class if there is one, and a fresh row otherwise.
Its replay probability is

    29089/114688 = 2/8 + 417/114688.

This is not a whole-budget attack: the honest signing budget more than pays for
the excess. The scalable two-query formula has leading excess
`(2I/N-1)/I^2`; this cancels at `N=2I`. That observation motivated the repeated
class count and the new potential. The finite search suggested the theorem;
the Lean proof establishes it for arbitrary adaptive oracle programs.

## Other experiments and their limits

The following are scoped research results. They do not supply additional
certified improvements beyond the 100-compression construction above.

### Shared inputs and both halves of an oracle answer

An initial screen considered 2,285 two-output motifs and roughly 1.88 million
scaled scenarios. A subsequent search included reconvergent, multiple-goal
DAGs: 510 completed circuits, 457,363 reduced frontiers, 1,556,071 scaled
scenarios and 24,041 word/cost convolutions. Thirteen attempted circuits hit
explicit time or state limits. Exact independent closure/cost audits passed
for 12 small base circuits and 20 chain-expanded circuits.

There are real local antichain gains: a shared three-group ring has width 12
where the corresponding separated calls have width 9 at the same small
budget. But sharing was too expensive in the relevant low-cost tail. The best
scaled example used 18 two-output forks and 54 length-18 chains, with keygen
cost 1013. At verification cost 101 it had

    22133904102484421350863138744394944 cuts.

Removing disclosures that reconstruct a shared fork leaves

    22089998664193854885643322226165492 cuts.

The shared cuts add only 0.198757%. A shared seed saves disclosure words but
costs 19 calls to recover one branch or 37 to recover both. This experiment
used the older uniform-class target `45*2^109`; its first passing cost was
102. It is not a universal bound on DAG sharing, and its class counts alone
do not prove security for correlated revelations.

### Linear mixing and partial words

A linear-closure experiment checked 574 circuits and 5,058 budgets. In its
model, free linear mixing did not create a new authentication resource beyond
the authenticated oracle values. Nonlinear functions and nonlinear global
constraints remain outside that conclusion.

A separate experiment split oracle answers into 64-bit pieces. Across 1,307
circuits it found 7,163 reduced frontiers and checked 18,328 word/cost budgets.
Allowing backward search for a gate's sole unknown 64-bit input reduced the
maximum antichain in 3,405 budgets; the largest reduction was six to two.

For example, let four-piece answers satisfy

    u = H(tag0,c,d),
    v = H(tag1,a,u1),
    pk = first128(H(tag2,u2,u3,v1,v2,v3)).

From `(c,d,v1,v2,v3)`, compute u1, then enumerate a and check the three known
pieces of v. This derives `(a,u1,u2,u3)`. At 64 bits per piece, the search
uses about `2^64` oracle calls and tests 192 output bits, giving fewer than
`2^-128` expected false matches. This is a concrete derivability relation,
not itself a complete message-binding forgery. A scaled eight-bit instance
was exhaustively checked; all 7,163 closure computations were independently
rechecked, and 36,608 antichain calculations matched brute force.

Comparisons against one arbitrary pairing of 64-bit pieces into 128-bit words
were representation dependent and are not evidence of a construction gain.
Future partial-word schemes must account for both forward evaluation and
backward recovery.

### Fusing message binding into authentication

Using otherwise unused output bits as public coefficients in
`A_cut * message + B_cut * nonce = 0` fails: after a signature, the adversary
reconstructs those coefficients and solves for another accepted pair on the
same cut. With 128 equations and 384 message/nonce bits, the kernel has
dimension at least 256. A nonzero vector gives either a new-message forgery
or a same-message strong forgery. Two toy variants each checked 1,048,576
oracle/key/message combinations and admitted a forgery whenever signing
succeeded.

Another proposal hashes the message and nonce into an XOR target associated
with the disclosed cut and omits one recoverable word. It faces two separate
obstacles in the tested form:

- A chosen-message birthday attack forces at least 62 nonce bits. A family
  large enough for the existing availability target needs a 115-bit cut ID.
  With 42 transmitted words, this totals `42*128 + 62 + 115 = 5553` bits,
  exceeding the signature limit by 49 bits. Implicit routing would have to
  remove that metadata cost.
- The target count needs an exceptionally strong lower-tail guarantee. For
  a 115-dimensional affine cut family mapped by a random 128-by-115 binary
  matrix, a rank-114 event has probability about `2^-13` and contributes
  signing failure about `2^-105`, already too large. This stress family is
  not asserted to equal the current tree's cuts; it shows why expected
  distinct-target count is insufficient.

Common-nonce XOR/sum binding and fresh message-bearing edges also failed the
modeled availability requirements. These results concern the specific tested
fusions, not all ways to combine indexing and authentication.

## Next direction: unequal class masses and best-of-L signing

The most promising open direction changes the signing distribution. Give cut
class i public per-query mass p_i. Query all L distinct nonces, then return
an accepted class with the smallest p_i, using a symmetric tie rule. Common
classes supply availability on rare transcripts; most signatures use rare
classes. This differs essentially from stopping at the first acceptance.

Here is a simple exact candidate. For tiers j=0 through 79, set

    p_j = 2^(j-128),
    n_j = 9 * 2^(105-j).

Each tier has acceptance mass `9/2^23`; the total remains `45/524288` and
`L * acceptance = 90`. A 128-bit index can implement this by dividing the
accepted range into 80 blocks of size `9*2^105`; inside block j, each cut has
`2^j` aliases. The nonce remains 128 bits. The number of distinct cuts is

    9*(2^106-2^26) = 730166745731460135262100442316800.

The rank-74 family on the existing graph contains

    choose(18,6) * [x^74](1+x+...+x^18)^36
      = 776610074300844075289060847283864

cuts, enough for this candidate at **92 verification compressions**. This is
an exact combinatorial count, not a completed 92-compression certificate.

For fresh distinct signing queries, if P_j is cumulative tier mass, the
probability of choosing tier j is exactly

    W_j = (1-P_(j-1))^L - (1-P_j)^L.

Integer interval arithmetic certifies the failure bound and

    E[p_selected | signing succeeds] < 0.962867 * 2^-127.

A short analytic bound follows from `exp(-9/8) < 13/40`: the unconditional
mean is below `(27/28)*2^-127`. A continuous relaxation of the tier problem
requires about `4*2^107` classes, while this simple schedule uses about
`4.5*2^107`. Eight numerically optimized tiers use about `4.15629*2^107`.
All these class counts fit cost 92; even the continuous lower bound exceeds
the rank-73 family's capacity, so this fixed family and selection model
cannot reach 91 by adjusting the weights alone.

**The unresolved problem is full adaptive strong security.** The honest
mean is insufficient when the attacker queries before choosing the signed
message. Cached repeated classes and choosing a favorable message row can
bias the selected class. Post-sign queries in that same row also see a
posterior distribution: the returned minimum implies that hidden sampled
positions did not contain a rarer class. A hand-derived correction bounds
that hit rate by `p_i/(1-F_i)`, where F_i is the total mass of rarer classes;
the uniform inflation is below `1.000086`, within the numerical margin.
That does not resolve pre-sign adaptive choice or replay.

A useful next theorem would bound cached replay plus all fresh post-sign
matches using a potential with per-query charge at most `2^-127`, with the
honest L-call signing reserve paying the initial value. It must then combine
with hidden-input and spurious-reconstruction events in the same whole-budget
simulation. No such theorem or complete weighted construction is claimed here.

## Provenance

The predecessor is the [officially verified 102-compression submission](https://ots.golf/submissions/440fbe4103a5cfff1f213e25ac09bfd9),
checked at commit `ceeb8503c3950869440af1cb6fa69b52b79044fc` in
[PR #6](https://github.com/leanEthereum/ots.golf-submissions/pull/6). Its archived
source and notes contain the earlier 104-to-102 construction history. This
candidate changes only the admitted UpperCompressions root and leaves the
protected contract unchanged.

Local experiment scripts and full logs are retained in the research workspace;
they are exploratory evidence, not dependencies of the submitted proof. The
Lean modules in this root supply the complete certificate for the claim in
`claim.txt`. Every larger claimed research gain above is explicitly separate
from that certificate.
