import Submissions.UpperLeanIsa.IdxLoop
import Submissions.UpperLeanIsa.TierCodec

/-!
# Rows of the index cache by tier

For a cache `d` and an extended message `M`, `rowU d M` counts the cached nonces of row `M` and
`rowN d M t` those whose answer has tier `≤ t`. The row is *good* (`RowGood`) when no tier count
falls more than `δ = 2 ^ 66` below its expectation: `rowU · P_{≤t} ≤ rowN t + δ` for `t < T`.
-/

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Params

variable (P : Params) (S : Tier.Sched)

/-- The cached nonces of row `M`. -/
def rowU (d : Cache) (M : EMessage) : ℕ :=
  (Finset.univ.filter fun η : Nonce => (d (P.encQuery (M ++ η))).isSome).card

/-- The cached nonces of row `M` whose answer has tier `≤ t`. -/
def rowN (d : Cache) (M : EMessage) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun η : Nonce =>
    ∃ w, d (P.encQuery (M ++ η)) = some w ∧ P.tierW S w ≤ t).card

/-- Row `M` of `d` meets the lower tail bound in every tier. -/
def RowGood (d : Cache) (M : EMessage) : Prop :=
  ∀ t < S.T, (P.rowU d M : ℝ) * (S.mass (t + 1) : ℝ) ≤ (P.rowN S d M t : ℝ) + 2 ^ 66

end Params

end OptimalOTS.LeanIsaBaseline.Layer
