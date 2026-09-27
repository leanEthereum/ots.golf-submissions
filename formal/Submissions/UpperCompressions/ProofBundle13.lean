import Submissions.UpperCompressions.ProofBundle10
import Submissions.UpperCompressions.ProofBundle12
import Submissions.UpperCompressions.ProofBundle11
import Submissions.UpperCompressions.ProofBundle03
import Submissions.UpperCompressions.ProofBundle06

section

/-! A terminal union is covered by per-target hits before one common killing
event. The common failure is charged once, without a union over time. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
namespace WeightedOracleExecution
variable {ι S α I : Type} {spec : OracleSpec ι} [spec.Inhabited] [Fintype I]

theorem terminal_union_or_kill_le_stopped (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → S → Prop) (kill : S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => (∃ i,hit i out.2) ∨ kill out.2 | (simulateQ impl oa).run s] ≤
      (∑ i,Pr[=true | firstHitRun impl (fun _ s => hit i s) (fun _ s => kill s) oa t s])+
        Pr[=true | firstHitRun impl (fun _ s => kill s) (fun _ _ => False) oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure a =>
    by_cases hh : ∃ i,hit i s
    · obtain ⟨i,hi⟩ := hh
      have hone : Pr[=true | firstHitRun impl (fun _ s => hit i s)
          (fun _ s => kill s) (pure a) t s]=1 := by simp [hi]
      have hsum := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : I => Pr[=true | firstHitRun impl (fun _ s => hit j s)
          (fun _ s => kill s) (pure a) t s]) (fun j _ => zero_le) (Finset.mem_univ i)
      rw [hone] at hsum
      exact (probEvent_le_one (mx := (simulateQ impl (pure a)).run s)
        (p := fun out => (∃ i,hit i out.2) ∨ kill out.2)).trans (hsum.trans le_self_add)
    · by_cases hk : kill s <;> simp [hh,hk]
  | query_bind q k ih =>
    by_cases hh : ∃ i,hit i s
    · obtain ⟨i,hi⟩ := hh
      have hone : Pr[=true | firstHitRun impl (fun _ s => hit i s)
          (fun _ s => kill s) ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s]=1 := by
        rw [firstHitRun_of_hit _ _ _ _ _ _ hi]
        simp
      have hsum := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : I => Pr[=true | firstHitRun impl (fun _ s => hit j s)
          (fun _ s => kill s) ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s])
        (fun j _ => zero_le) (Finset.mem_univ i)
      rw [hone] at hsum
      exact (probEvent_le_one (mx := (simulateQ impl
        ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k)).run s)
        (p := fun out => (∃ i,hit i out.2) ∨ kill out.2)).trans (hsum.trans le_self_add)
    · have hnone : ∀ i,¬hit i s := fun i hi => hh ⟨i,hi⟩
      by_cases hk : kill s
      · have hone : Pr[=true | firstHitRun impl (fun _ s => kill s)
            (fun _ _ => False) ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s]=1 := by
          rw [firstHitRun_of_hit _ _ _ _ _ _ hk]
          simp
        rw [hone]
        exact (probEvent_le_one (mx := (simulateQ impl
          ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k)).run s)
          (p := fun out => (∃ i,hit i out.2) ∨ kill out.2)).trans le_add_self
      · simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
          probEvent_bind_eq_expectedValue,firstHitRun_query_bind,hnone,hk,if_false,
          probOutput_bind_eq_expectedValue]
        rw [←expectedValue_finsetSum,←expectedValue_add]
        apply expectedValue_mono
        intro out
        exact ih out.1 (t+1) out.2

end WeightedOracleExecution
end
end
