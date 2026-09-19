# Generality 1/3 lower bound: 90 compressions

Every secure whole-word DAG scheme has worst-case verification cost at least 90 compressions.
`Solution.lean` exports `OptimalOTS.Challenge.LowerGenerality1.candidate` at the claim in
`claim.txt`. The rules are on [ots.golf/rules](https://ots.golf/rules); the proof guide is
[lower-generality-1.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/lower-generality-1.md).

## Idea

1. **Few disclosed origins.** A hash origin of a node costs at least one complete 128-bit word of
   its width (a constant has no origin but still occupies 128 bits), so a 5376-bit payload
   discloses at most 42 origins.
2. **Few reconstruction patterns.** If every verification costs at most 89 (87 non-root hashes),
   the reconstruction patterns number at most `Nat.choose 129 42`, far fewer than the indices.
3. **Signature conversion.** The attacker moves a signature's disclosure to another index with the
   same pattern. Averaging over all pattern classes (Cauchy–Schwarz), with two freshness factors
   of 99/100, the fresh-message forgery succeeds with probability at least 9801/280000 at total
   cost at most `1024 + 2^20 + 2^122 + 2·88 + 2`, contradicting 127-bit weak security, which
   strong security implies.

Equal oracle inputs share answers throughout; constants, concatenations and either output half
introduce no labels.

## Files

| File | Content |
|---|---|
| `WeakSecurity.lean` | the weak experiment; strong security implies weak security |
| `Semantics.lean`, `Encoding.lean` | graph records and deterministic evaluation; disclosure round trips |
| `Cache.lean`, `CacheFresh.lean`, `Expectation.lean` | lazy-oracle caches, fresh message prefixes, expectation identities |
| `KeygenSupport.lean` | key-generation outputs satisfy the final cache's node equations |
| `WholeWordOrigins.lean` | 128 times the number of hash origins is at most a node's width; `DisclosureBound 42` |
| `DisclosurePatterns.lean`, `OrderedCounting.lean` | hash origins of disclosed values; the `Nat.choose 129 42` pattern count |
| `Patterns.lean`, `PatternGoods.lean`, `PatternHelpers.lean` | pattern counting and probability helpers |
| `Conversion.lean` | moving a disclosure between indices with equal reconstruction patterns |
| `Index.lean`, `SignFresh.lean`, `AveragedSigning.lean` | the signing loop and its exact fresh-cache law |
| `PatternSearch.lean`, `AveragedSearch.lean` | nonce search and its success per pattern class |
| `CostCore.lean`, `PatternAttack.lean`, `AveragedAttack.lean` | the attack and its pathwise cost |
| `AveragedCounting.lean`, `AveragedAssembly.lean`, `PatternAssembly.lean` | the averaged success bound and the security contradiction |
| `Solution.lean` | the exported certificate |

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py lower-generality-1 --source .
```
