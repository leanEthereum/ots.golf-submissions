# Generality 2/3 lower bound: 18 compressions

Every secure DAG scheme, with arbitrary deterministic node functions and no separation or tagging
hypothesis, has worst-case verification cost at least 18 compressions. `Solution.lean` exports
`OptimalOTS.Challenge.LowerGenerality2.candidate` at the claim in `claim.txt`. The rules are on
[ots.golf/rules](https://ots.golf/rules); the proof guide is
[lower-generality-2.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/lower-generality-2.md).

## Idea

1. **Few reconstruction patterns.** Suppose every verification costs at most 17. The index and
   root each cost at least one, so each index recomputes at most 15 non-root hash nodes: fewer
   than `2^110` patterns among `2^115` indices. At least three quarters of the indices lie in
   classes of size at least eight.
2. **Signature conversion.** After receiving a signature, the attacker picks any algebraic record
   consistent with the disclosed values and observed hash outputs; its disclosure at an index with
   the same pattern verifies under the actual oracle.
3. **Search.** Fresh message prefixes make the signing law exact; a search over `2^122` nonces
   hits a large class with probability at least `1/9`. The forgery succeeds with probability at
   least `9/200` at total cost `1024 + 2^20 + 2^122 + 34`, contradicting 127-bit weak security,
   which strong security implies.

## Files

| File | Content |
|---|---|
| `WeakSecurity.lean` | the weak experiment; strong security implies weak security |
| `Semantics.lean`, `Encoding.lean` | algebraic graph records and deterministic evaluation; disclosure round trips |
| `Cache.lean`, `Expectation.lean` | lazy bare-oracle runs; expectation identities |
| `KeygenSupport.lean` | key-generation outputs satisfy the final cache's node equations |
| `Conversion.lean` | moving a disclosure between indices with equal reconstruction patterns |
| `Patterns.lean`, `PatternGoods.lean` | exact pattern counts and the large-class fraction |
| `CacheFresh.lean`, `PatternHelpers.lean` | finite-cache prefix counting and probability bounds |
| `Index.lean`, `SignFresh.lean` | signing support and its exact fresh-cache probability law |
| `PatternSearch.lean` | nonce search, its cost, correctness and success at least `1/9` |
| `CostCore.lean`, `PatternAttack.lean` | the attack and its total pathwise query cost |
| `PatternAssembly.lean`, `Solution.lean` | success bound, security contradiction, exported certificate |

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py lower-generality-2 --source .
```
