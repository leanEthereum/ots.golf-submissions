import Submissions.LowerGenerality3.ZeroQuery

/-!
# The one-query normal form of a deterministic verifier

A deterministic oracle program of cost at most one is a constant, or a single hash query of at
most 512 bits followed by a constant decision (`Shape`). Its acceptance probability from a cache
is then explicit (`win_shape`): the cached answer decides, or, at an uncached query, the fraction
of accepting answers.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

/-- A deterministic decision procedure of cost at most one. -/
inductive Shape
  | const (b : Bool)
  | one (q : Query) (f : BitVec hashBits → Bool)

/-- The program of a shape. -/
def Shape.comp : Shape → OracleComp Spec Bool
  | .const b => pure b
  | .one q f => liftM (Spec.query (.inr q)) >>= fun y => pure (f y)

/-- A deterministic program of cost zero makes no query at all. -/
theorem eq_pure_of_zero {α : Type} (oa : OracleComp Spec α) (h0 : CostAtMost oa 0)
    (hd : Deterministic oa) : ∃ x, oa = pure x := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨x, rfl⟩
  | query_bind t k _ =>
    unfold CostAtMost at h0
    unfold Deterministic at hd
    rw [isQueryBound_query_bind_iff] at h0 hd
    cases t with
    | inl t => simp at hd
    | inr q =>
      have hc := h0.1
      change blockCost q.1 ≤ 0 at hc
      unfold blockCost at hc
      omega

/-- A deterministic program of cost at most one has a shape, with a short query. -/
theorem shape_of_one (oa : OracleComp Spec Bool) (h1 : CostAtMost oa 1)
    (hd : Deterministic oa) :
    ∃ sh : Shape, oa = sh.comp ∧ ∀ q f, sh = .one q f → q.1 ≤ 512 := by
  induction oa using OracleComp.inductionOn with
  | pure b => exact ⟨.const b, rfl, fun _ _ h => by cases h⟩
  | query_bind t k _ =>
    unfold CostAtMost at h1
    unfold Deterministic at hd
    rw [isQueryBound_query_bind_iff] at h1 hd
    cases t with
    | inl t => simp at hd
    | inr q =>
      have hc := h1.1
      change blockCost q.1 ≤ 1 at hc
      have hlen : q.1 ≤ 512 := by
        unfold blockCost blockBits at hc
        omega
      have hk : ∀ u, ∃ b, k u = pure b := by
        intro u
        refine eq_pure_of_zero (k u) ?_ (hd.2 u)
        have := h1.2 u
        change CostAtMost (k u) (1 - blockCost q.1) at this
        have hb : 1 - blockCost q.1 = 0 := by unfold blockCost; omega
        rwa [hb] at this
      choose f hf using hk
      refine ⟨.one q f, ?_, fun q' f' h => by cases h; exact hlen⟩
      show _ = liftM (Spec.query (.inr q)) >>= fun y => pure (f y)
      congr 1
      funext u
      exact hf u

end OptimalOTS.LowerGenerality3
