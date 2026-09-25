import Submissions.UpperLeanIsa.IdxBase

/-!
# One-step lemmas of oracle programs

The cost and support of one uniform (`.inl`) or oracle (`.inr`) query followed by a continuation,
and the expectation of a uniform draw from `Fin (n + 1)`. The signing loop (`TierSign`) is
analysed with them.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.encQuery

namespace Params

/-! ### One-step lemmas -/

theorem costAtMost_inl_bind {α β : Type} (t : ℕ)
    (body : Fin (t + 1) → OracleComp Spec α) (kont : α → OracleComp Spec β) {b : ℕ}
    (h : CostAtMost (((liftM (Spec.query (.inl t)) : OracleComp Spec (Fin (t + 1)))
      >>= body) >>= kont) b) :
    ∀ j, CostAtMost (body j >>= kont) b := by
  rw [bind_assoc, costAtMost_query_bind_iff] at h
  intro j
  have := h.2 j
  rwa [show queryCost (.inl t) = 0 from rfl, Nat.sub_zero] at this

theorem costAtMost_inr_bind {α β : Type} (q : Query)
    (body : BitVec hashBits → OracleComp Spec α) (kont : α → OracleComp Spec β)
    {b : ℕ}
    (h : CostAtMost (((liftM (Spec.query (.inr q)) : OracleComp Spec (BitVec hashBits))
      >>= body) >>= kont) b) :
    queryCost (.inr q) ≤ b ∧
      ∀ w, CostAtMost (body w >>= kont) (b - queryCost (.inr q)) := by
  rw [bind_assoc, costAtMost_query_bind_iff] at h
  exact h

theorem mem_support_run_inl {α : Type} {t : ℕ} {body : Fin (t + 1) → OracleComp Spec α}
    {c : Cache} {p : α × Cache}
    (hp : p ∈ support (run ((liftM (Spec.query (.inl t)) :
      OracleComp Spec (Fin (t + 1))) >>= body) c)) :
    ∃ j, p ∈ support (run (body j) c) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inl, support_bind] at hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨w, -, hw⟩ := hu
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨u, hp⟩

theorem mem_support_run_inr_none {α : Type} {q : Query}
    {body : BitVec hashBits → OracleComp Spec α} {c : Cache} {p : α × Cache}
    (hc : c q = none)
    (hp : p ∈ support (run ((liftM (Spec.query (.inr q)) :
      OracleComp Spec (BitVec hashBits)) >>= body) c)) :
    ∃ w, p ∈ support (run (body w) (c.cacheQuery q w)) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inr_none hc, support_bind] at hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨w, -, hw⟩ := hu
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨u, hp⟩

theorem mem_support_run_inr_some {α : Type} {q : Query} {u : BitVec hashBits}
    {body : BitVec hashBits → OracleComp Spec α} {c : Cache} {p : α × Cache}
    (hc : c q = some u)
    (hp : p ∈ support (run ((liftM (Spec.query (.inr q)) :
      OracleComp Spec (BitVec hashBits)) >>= body) c)) :
    p ∈ support (run (body u) c) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u', c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inr_some hc, support_pure] at hu
  simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  exact hp

theorem E_query_unif (n : ℕ) (g : Fin (n + 1) → ℝ≥0∞) :
    E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) g =
      ∑ j, ((n : ℝ≥0∞) + 1)⁻¹ * g j := by
  rw [E, expectedValue_def, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact ProbComp.probOutput_uniformFin n j


end Params

end OptimalOTS.LeanIsaBaseline.Layer
