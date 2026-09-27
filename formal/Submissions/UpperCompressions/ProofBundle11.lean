import Submissions.UpperCompressions.ProofBundle10
import Submissions.UpperCompressions.ProofBundle06
import Submissions.UpperCompressions.ProofBundle08
import Submissions.UpperCompressions.ProofBundle07
import Submissions.UpperCompressions.ProofBundle05
import Submissions.UpperCompressions.ProofBundle01
import Submissions.UpperCompressions.ProofBundle09

section

/-! Adaptive observed-cache completions inherit the unconditional full-table
tail. No pointwise bound is asserted for a particular adversarial transcript. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
attribute [local irreducible] hashBits msgBits signBudget

def completedTable (b : ℕ) (c : Cache) (g : BitVec b → BitVec hashBits) :
    BitVec b → BitVec hashBits := fun x => (c ⟨b,x⟩).getD (g x)

def readTable (b : ℕ) (c : Cache) : BitVec b → BitVec hashBits :=
  fun x => (c ⟨b,x⟩).getD 0

theorem readTable_preload (b : ℕ) (c : Cache) (g : BitVec b → BitVec hashBits) :
    readTable b ((lengthSlice b).preload c g) = completedTable b c g := by
  funext x
  unfold readTable completedTable QuerySlice.preload
  rw [Cache.extend_apply, lengthSlice_inside]
  cases c ⟨b,x⟩ <;> rfl

theorem preload_complete_initial (b : ℕ) (c : Cache)
    (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none) (g : BitVec b → BitVec hashBits) :
    ∀ x : BitVec b, (lengthSlice b).preload c g ⟨b,x⟩ = some (g x) := by
  intro x
  unfold QuerySlice.preload
  rw [Cache.extend_apply, hc x, lengthSlice_inside]
  rfl

theorem readTable_run_preload {α : Type} (b : ℕ) (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none)
    (g : BitVec b → BitVec hashBits) (p : α × Cache)
    (hp : p ∈ support (run oa ((lengthSlice b).preload c g))) :
    readTable b p.2 = g := by
  funext x
  have h := sub_of_mem_support_run oa _ p hp _ _ (preload_complete_initial b c hc g x)
  simp only [readTable, h, Option.getD_some]

/-- Averaging the posterior completion of the actual final public cache cannot
increase any unconditional bad-table probability. The program may be adaptive. -/
theorem completed_bad_probability_le {α : Type} (b : ℕ) (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none)
    (bad : (BitVec b → BitVec hashBits) → Prop) :
    E (run oa c) (fun p => E ($ᵗ (BitVec b → BitVec hashBits))
      (fun g => if bad (completedTable b p.2 g) then 1 else 0)) ≤
      E ($ᵗ (BitVec b → BitVec hashBits)) (fun g => if bad g then 1 else 0) := by
  have h := cacheE_finite_completion (lengthSlice b) oa c
    (fun _ d => if bad (readTable b d) then 1 else 0)
  simp only [cacheE, completePayoff, readTable_preload] at h
  rw [h]
  apply E_mono
  intro g
  calc
    _ ≤ E (run oa ((lengthSlice b).preload c g)) (fun _ => if bad g then 1 else 0) := by
      apply expectedValue_mono_of_support
      intro p hp
      rw [readTable_run_preload b oa c hc g p hp]
    _ ≤ _ := E_const_le _ _

end
end WeightedReplacement
end

section

/-! A mandatory continuation reserve is unavailable to the public prefix on
every raw query-answer path, not just on average. -/
open OracleSpec OracleComp
open OptimalOTS OptimalOTS.AlgorithmCosts
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem costAtMost_prefix_reserved {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (R : ℕ)
    (hR : ∀ a b, CostAtMost (k a) b → R ≤ b) :
    ∀ b, CostAtMost (oa >>= k) b → R ≤ b ∧ CostAtMost oa (b-R) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro b hB
    rw [pure_bind] at hB
    exact ⟨hR a b hB,costAtMost_pure _ _⟩
  | query_bind t f ih =>
    intro b hB
    rw [bind_assoc,costAtMost_query_bind_iff] at hB
    have hs (u : Spec.Range t) := ih u (b-queryCost t) (hB.2 u)
    haveI : Nonempty (Spec.Range t) := by cases t <;> infer_instance
    have hr := (hs (Classical.arbitrary (Spec.Range t))).1
    refine ⟨by omega,?_⟩
    rw [costAtMost_query_bind_iff]
    refine ⟨by omega,fun u => ?_⟩
    simpa only [Nat.sub_sub,Nat.add_comm] using (hs u).2

end
end WeightedReplacement
end

section

/-! Expected spent public-prefix cost plus its actual post-reserve remaining
budget fits in one initial public budget, without ENNReal subtraction. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem expected_spent_reserved_remaining_le {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (R : ℕ)
    (hR : ∀ a b, CostAtMost (k a) b → R ≤ b) :
    ∀ c b, CostAtMost (oa >>= k) b →
      expectedCharge (fun t => queryCost t) oa c +
        E (runRemaining oa c b) (fun r => ((r.2.2-R:ℕ):ℝ≥0∞)) ≤ (b-R:ℕ) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro c b hB; simp
  | query_bind t f ih =>
    intro c b hB
    have hprefix := (costAtMost_prefix_reserved (liftM (Spec.query t) >>= f) k R hR b hB).2
    rw [costAtMost_query_bind_iff] at hprefix
    rw [bind_assoc,costAtMost_query_bind_iff] at hB
    rw [expectedCharge_query,runRemaining_query,E_bind]
    calc
      _ = (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c) (fun p =>
          expectedCharge (fun t => queryCost t) (f p.1) p.2 +
            E (runRemaining (f p.1) p.2 (b-queryCost t)) (fun r => ((r.2.2-R:ℕ):ℝ≥0∞))) := by
        rw [add_assoc]
        exact congrArg ((queryCost t:ℝ≥0∞) + ·) (expectedValue_add _ _ _).symm
      _ ≤ (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c)
          (fun _ => ((b-queryCost t-R:ℕ):ℝ≥0∞)) :=
        add_le_add le_rfl (E_mono _ (fun p => ih p.1 p.2 _ (hB.2 p.1)))
      _ ≤ (queryCost t:ℝ≥0∞) + ((b-queryCost t-R:ℕ):ℝ≥0∞) :=
        add_le_add le_rfl (E_const_le _ _)
      _ = _ := by
        rw [← Nat.cast_add]
        congr 1
        omega

end
end WeightedReplacement
end
