import Submissions.UpperCompressions.Master

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
noncomputable section

namespace OptimalOTS

/-- A fixed nonnegative terminal reserve passes through the master inequality.
This avoids subtracting the signing reserve inside ENNReal potentials. -/
theorem master_family_reserve {α β J : Type} [Nonempty J]
    (κ reserve : ℝ≥0∞) (Φ : Cache → ℝ≥0∞) (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hΦ : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) ≤
        Φ c + κ * queryCost (.inr q))
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β)
    (Fv : α → Cache → ℝ≥0∞)
    (hF : ∀ x d b', I d b' → (∀ j, CostAtMost (k j x) b') →
      Fv x d + reserve ≤ Φ d + κ * b')
    (c : Cache) (b : ℕ) (hI : I c b)
    (hB : ∀ j, CostAtMost (oa >>= k j) b) :
    E (run oa c) (fun p => Fv p.1 p.2) + reserve ≤ Φ c + κ * b := by
  have h := master_family κ Φ I hI_fresh hI_cached hΦ oa k
    (fun x d => Fv x d + reserve) hF c b hI hB
  change expectedValue (run oa c) (fun p => Fv p.1 p.2 + reserve) ≤ _ at h
  rw [expectedValue_add, expectedValue_const (by simp)] at h
  exact h

/-- A reserve strictly larger than the initial overhead leaves a strict bound. -/
theorem reserve_cancellation {a reserve bound overhead : ℝ≥0∞}
    (hreserve : reserve ≠ ⊤) (hbound : bound ≠ ⊤)
    (hslack : overhead < reserve) (h : a + reserve ≤ bound + overhead) :
    a < bound := by
  have hh : a + reserve < bound + reserve :=
    h.trans_lt (ENNReal.add_lt_add_left hbound hslack)
  exact (ENNReal.add_lt_add_iff_right hreserve).mp hh

#print axioms master_family_reserve
#print axioms reserve_cancellation

end OptimalOTS
