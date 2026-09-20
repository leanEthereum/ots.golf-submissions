# Generality 3/3 lower bound: 2 compressions

No admissible, secure oracle algorithm verifies every input within one compression.
`Solution.lean` exports `OptimalOTS.Challenge.LowerGenerality3.candidate` at the claim in
`claim.txt`. The rules are on [ots.golf/rules](https://ots.golf/rules); the proof guide is
[lower-generality-3.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/lower-generality-3.md).

## Idea

Verification is deterministic, so a cost-one verifier is a constant or one short hash query
followed by a constant decision (`Shape`). Perfect correctness makes every honest verification
accept from the honest cache with probability one, hence it is either unconditional or reads a
point already in the cache. Six cases cover every honest signature on a uniform message, each
charged to an attacker or a counting bound; their masses add up to about `2^-5`, below the
signing-availability mass `1 - 2^-128`. The formal argument follows the paper plan of
`docs/research/generic-one-query.md` in the core repository, simplified by determinism.

| Case | Charged to | Mass |
|---|---|---|
| a candidate accepted on every oracle path | attacker 0 (cost `K + T + 1`) | `< (K+T+1)/2^127` |
| the cached point is useful for a second message | attacker R (cost `K + T + 2`) | `< (K+T+2)/2^127` |
| a key-generation point useful only for this message | uniform message | `≤ K / 2^256` |
| a fresh promising point (useful rate `≥ 2^-25`) | attacker H (cost `2K + T + 2`), via the cache martingale | `< 2^25 (2K+T+2)/2^127` |
| a fresh non-promising point | adaptive union bound over `T` signing queries | `≤ T · 2^-25` |

`K = 1024`, `T = 2^20`. The cache martingale (`Martingale.lean`) replaces the static-oracle
coupling of the paper argument: for a finite query set and an answer predicate, the product of
non-hit rates over the still-open members is a martingale of the lazy cache under any computation,
so the honest signer's chance of hitting a promising point is bounded by exactly the quantity the
attacker realizes by querying the whole set.

## Files

| File | Content |
|---|---|
| `WeakSecurity.lean`, `Costs.lean`, `ZeroQuery.lean`, `Proof.lean` | the previous certificate of 1 (its availability expansion is reused) |
| `OneQuery.lean` | the one-query normal form of a deterministic cost-one program |
| `CacheLemmas.lean`, `Expectation.lean`, `Support.lean` | lazy-oracle run lemmas, expectations, cache size and cost-free sampling |
| `Accept.lean`, `Honest.lean` | acceptance from a cache; honest verification is unconditional or cached |
| `Useful.lean` | useful points, their rates, the promising set, lonely and shared points |
| `Martingale.lean`, `Answers.lean` | the cache martingale, querying a whole list |
| `Union.lean` | the adaptive union bound over fresh queries |
| `Attack0.lean`, `AttackR.lean`, `AttackH.lean`, `Lonely.lean` | the three attackers and the lonely-point count |
| `Assemble.lean` | the six-way case split, the accounting and the exported bound |
| `Solution.lean` | the exported certificate |

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py lower-generality-3 --source .
```
