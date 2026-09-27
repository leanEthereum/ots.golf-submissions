import Submissions.UpperCompressions.ProofBundle04
import Submissions.UpperCompressions.ProofBundle02
import Submissions.UpperCompressions.ProofBundle03

section

/-! Authentication record potentials and a joint query-type interface.
The index potential is explicit and must be discharged by the weighted posterior proof. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag

theorem avg_const (X : ℝ≥0∞) :
    ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * X = X :=
  sum_inv_card_mul X

end OptimalOTS.WeightedConstruction.WideForest
end
end

section

/-! Expected-cost potential induction for the actual shared-cache interpreter.
The charge is accumulated on the original query stream, including cache hits. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedExpectedCharge
open OptimalOTS OptimalOTS.Dag WeightedReplacement
set_option maxHeartbeats 800000

/-- Local additive drift charges the actual expected primitive-query cost,
without replacing its expectation by the whole pathwise budget. -/
theorem master_expected {α : Type} (Φ : Cache → ℝ≥0∞)
    (charge : Spec.Domain → ℝ≥0∞) (r : ℝ≥0∞)
    (hstep : ∀ t c, E ((oracleImpl t).run c) (fun p => Φ p.2) ≤ Φ c+r*charge t)
    (oa : OracleComp Spec α) (c : Cache) :
    E (run oa c) (fun p => Φ p.2) ≤ Φ c+r*expectedCharge charge oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t k ih =>
    rw [run_query_bind, E_bind, expectedCharge_query]
    calc
      _ ≤ E ((oracleImpl t).run c) (fun p => Φ p.2+r*expectedCharge charge (k p.1) p.2) :=
        E_mono _ (fun p => ih p.1 p.2)
      _ = E ((oracleImpl t).run c) (fun p => Φ p.2)+
          r*E ((oracleImpl t).run c) (fun p => expectedCharge charge (k p.1) p.2) := by
        simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        apply tsum_congr
        intro p
        ring
      _ ≤ (Φ c+r*charge t)+r*E ((oracleImpl t).run c)
          (fun p => expectedCharge charge (k p.1) p.2) := add_le_add (hstep t c) le_rfl
      _ = _ := by ring

end WeightedExpectedCharge
end
end

section

/-! Cache locality of the actual all-trial signer. Accepted nonwinners remain
allowed in the implementation cache; every insertion is in the signed row. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.ReplacementLocality

open WeightedSampling

theorem hash_cache_other {n : ℕ} (x : BitVec n) (c : Cache)
    (p : BitVec hashBits × Cache) (hp : p ∈ support (run (hash x) c))
    (q : Query) (hq : q ≠ ⟨n, x⟩) : p.2 q = c q := by
  unfold OptimalOTS.hash run at hp
  rw [simulateQ_spec_query] at hp
  rcases hc : c ⟨n, x⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨w, _, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact QueryCache.cacheQuery_of_ne _ _ hq
  · rw [oracleImpl_run_inr_some hc, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl

theorem loop_cache_outside_row {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) :
    ∀ k c p, p ∈ support (run (loop n decode tier m k) c) →
      ∀ q : Query, (∀ η : Nonce n, q ≠ ⟨msgBits + n, m ++ η⟩) → p.2 q = c q := by
  intro k
  induction k with
  | zero =>
    intro c p hp q hq
    rw [loop, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    rfl
  | succ k ih =>
    intro c p hp q hq
    rw [run_loop_succ, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨η, _, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨w,d⟩, hd, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨r,e⟩, hr, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact (ih d (r,e) hr q hq).trans (hash_cache_other _ c (w,d) hd q (hq η))

theorem loop_new_cache_row {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (p : Option (Winner n M) × Cache)
    (hp : p ∈ support (run (loop n decode tier m k) c))
    (q : Query) (w : BitVec hashBits) (hc : c q = none) (he : p.2 q = some w) :
    ∃ η : Nonce n, q = ⟨msgBits + n, m ++ η⟩ := by
  by_contra h
  have hq : ∀ η : Nonce n, q ≠ ⟨msgBits + n, m ++ η⟩ := by simpa using h
  have ho := loop_cache_outside_row n decode tier m k c p hp q hq
  rw [he, hc] at ho
  cases ho

end OptimalOTS.ReplacementLocality

end
end

section

/-! Every accepted weighted verifier run has its index answer and reconstruction
witness recorded in the final shared-oracle cache. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedScheme

variable {M : ℕ}

theorem verify_support (S : Scheme M) (pk : PublicKey) (m : Message)
    (σ : Signature) (c : Cache) :
    ∀ p ∈ support (run (S.verify pk m σ) c),
      Cache.Sub c p.2 ∧ (p.1 = true →
        ∃ w, p.2 ⟨msgBits + 86, m ++ σ.1⟩ = some w ∧
          ∃ i : Fin M, S.decode w = some i ∧
            σ.2.length = S.graph.revealBits (S.sets i) ∧
            ∃ y : S.graph.Assignment,
              S.graph.ReconEqs p.2 (S.sets i) (S.graph.decode (S.sets i) σ.2) y ∧
              S.publicKey y = pk) := by
  intro p hp
  unfold Scheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨w, c₁⟩, hw₁, hp⟩ := hp
  obtain ⟨hsub₁, hw⟩ := Dag.Graph.hash_support (m ++ σ.1) c (w, c₁) hw₁
  cases hi : S.decode w with
  | none =>
    simp only [hi, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hsub₁, fun h => by cases h⟩
  | some i =>
    simp only [hi] at hp
    by_cases hlen : σ.2.length = S.graph.revealBits (S.sets i)
    · rw [if_pos hlen, run_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨y, c₂⟩, hy, hp⟩ := hp
      obtain ⟨hsub₂, heq⟩ := S.graph.reconstruct_support _ _ c₁ (y, c₂) hy
      rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
      exact ⟨w, hsub₂ _ _ hw, i, hi, hlen, y, heq, of_decide_eq_true hok⟩
    · rw [if_neg hlen, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hsub₁, fun h => by cases h⟩

end OptimalOTS.WeightedScheme

end
end
