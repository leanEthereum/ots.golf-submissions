import OptimalOTS.OracleAlgorithm

/-! Structural cost rules used by the generic lower submission. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3.Costs

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

variable {α β : Type}

theorem CostAtMost.mono {oa : OracleComp Spec α} {b b' : ℕ} (h : CostAtMost oa b)
    (hb : b ≤ b') : CostAtMost oa b' := by
  induction oa using OracleComp.inductionOn generalizing b b' with
  | pure _ => trivial
  | query_bind t mx ih =>
      unfold CostAtMost at h ⊢
      rw [isQueryBound_query_bind_iff] at h ⊢
      exact ⟨le_trans h.1 hb, fun u => ih u (h.2 u) (by omega)⟩

theorem CostAtMost.bind {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    {b₁ b₂ : ℕ} (h₁ : CostAtMost oa b₁) (h₂ : ∀ x, CostAtMost (ob x) b₂) :
    CostAtMost (oa >>= ob) (b₁ + b₂) :=
  isQueryBound_bind (· + ·)
    (fun _ _ _ _ h => ⟨le_add_left h, le_add_right h⟩)
    (fun _ _ _ _ h => ⟨by omega, by omega⟩) h₁ h₂

theorem costAtMost_map_iff (oa : OracleComp Spec α) (f : α → β) (b : ℕ) :
    CostAtMost (f <$> oa) b ↔ CostAtMost oa b :=
  isQueryBound_map_iff _ _ _ _ _

theorem CostAtMost.map {oa : OracleComp Spec α} {b : ℕ} (h : CostAtMost oa b)
    (f : α → β) : CostAtMost (f <$> oa) b :=
  (costAtMost_map_iff oa f b).2 h

theorem CostAtMost.bind_le {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    {b₁ b₂ b : ℕ} (h₁ : CostAtMost oa b₁) (h₂ : ∀ x, CostAtMost (ob x) b₂)
    (h : b₁ + b₂ ≤ b) : CostAtMost (oa >>= ob) b :=
  CostAtMost.mono (CostAtMost.bind h₁ h₂) h

end OptimalOTS.LowerGenerality3.Costs
