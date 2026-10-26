# Generality 3/3 lower bound: 1 compression

No admissible, secure oracle algorithm verifies at zero cost. `Solution.lean` exports
`OptimalOTS.Challenge.LowerGenerality3.candidate` at the claim in `claim.txt`. The rules are on
[ots.golf/rules](https://ots.golf/rules); the proof guide is
[lower-generality-3.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/lower-generality-3.md).

## Idea

A zero-cost verifier makes no oracle queries. For every public key on which honest signing of a
fixed message can succeed, correctness gives a signature that this oracle-independent verifier
accepts with probability one, and a free classical selection chooses such a signature from public
data. The attacker signs message 0 and forges message 1: it succeeds with probability at least one
half at total cost at most `1024 + 2^20`, contradicting weak security, which strong security
implies. The proof lemma covers every signing-failure allowance at most one half.

## Files

| File | Content |
|---|---|
| `WeakSecurity.lean` | the weak experiment; strong security implies weak security |
| `Costs.lean` | structural cost rules |
| `ZeroQuery.lean` | zero-cost verification is independent of the oracle cache |
| `Proof.lean` | the attack and the security contradiction |
| `Solution.lean` | the exported certificate |

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py lower-generality-3 --source .
```
