# lower-generality-3: 2 compressions

## Idea

Formalize the paper argument of `docs/research/generic-one-query.md` (core repository) for the
current contract, where verification is deterministic. That removes its hardest obligation, the
randomized one-query normal form: a deterministic program of cost at most one is `pure b` or
`hash q >>= fun y => pure (f y)` with `|q| ≤ 512` (`OneQuery.lean`, ~60 lines), and every
acceptance quantity is a Boolean, so the paper's `δ` is `1` and only `τ = 2^-25` remains.

The other obligation the paper flags — "static random-function semantics agree with the lazy
cache" — is avoided rather than proved. Attacker H's success and the honest signer's chance of
finding a promising point live in different experiments; instead of coupling them through a
static oracle, `Martingale.lean` shows that for a finite query set `Q` and predicate `P`,

```
S(c) = [no fresh member of Q holds a P-answer in c] · ∏_{q ∈ Q fresh and still unanswered} (1 - rate_P(q))
```

keeps its expectation under any computation run from any cache (fresh answers are uniform,
cached ones do nothing). So any run from the key-generation cache `c₀` decides `Q` with
probability at most `1 - S(c₀)`, and a run that queries all of `Q` decides it with exactly
`1 - S(c₀)`. Both sides are functions of `c₀`, which has the same distribution in every
experiment. The adaptive union bound for non-promising fresh queries is the same induction with
an additive charge (`Union.lean`).

## Result

`candidate : LowerBoundGenerality3 2`, kernel-checked, axioms `propext`, `Classical.choice`,
`Quot.sound`. About 1500 new lines over the previous root. The masses are
`2^-128 + (K+T+1)/2^127 + (K+T+2)/2^127 + K/2^256 + 2^25 (2K+T+2)/2^127 + T/2^25 ≈ 2^-5 < 1`.

## What did not work, and what to know

- `Finset.univ.filter` over `Message = BitVec 256`, and any `rw`/`exact` that lets Lean unfold a
  `Finset` built from `Finset.range 513` sigma `Finset.univ : Finset (BitVec k)`, hits the
  recursion limit: those definitions are marked `irreducible` and reached only through
  membership lemmas. Likewise predicates used under `if h : … then` must be named definitions,
  or instance search on the raw existential times out.
- The `E` abbreviation for `expectedValue` blocks `rw` with `expectedValue_*` lemmas when it is
  the head symbol; `show expectedValue _ _ = _` first.
- The paper's attacker R is only needed for key-generation points; attacker H and the union
  bound cover the fresh signing points without a separate "singleton message set" case there.

## Next

Three compressions is not reachable this way: with two queries the second depends on the first
answer and the acceptance is no longer a single-point condition. A bound of 3 would need a
two-level version of the case split (the second query is unconditional, cached, or fresh given
the first answer) and a martingale over pairs. The tooling here (shapes, cache martingale, union
bound, the three attackers) is reusable for that.
