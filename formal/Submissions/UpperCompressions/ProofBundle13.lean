import Submissions.UpperCompressions.ProofBundle10
import Submissions.UpperCompressions.ProofBundle12
import Submissions.UpperCompressions.ProofBundle11
import Submissions.UpperCompressions.ProofBundle03
import Submissions.UpperCompressions.ProofBundle06

/- Original module: Submissions.UpperCompressions.FirstHitTerminalUnion; SHA256 3b5ce25c9a2f11d14ab3149ff023d7cbcbe35f4a9c8cf0f92b2fca614a3f0e08. -/
section

/-! A terminal union is covered by per-target hits before one common killing
event. The common failure is charged once, without a union over time. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
namespace WeightedOracleExecution
variable {ι S α I : Type} {spec : OracleSpec ι} [spec.Inhabited] [Fintype I]

theorem terminal_union_le_stopped (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → S → Prop) (kill : S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => ∃ i,hit i out.2 | (simulateQ impl oa).run s] ≤
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
        (p := fun out => ∃ i,hit i out.2)).trans (hsum.trans le_self_add)
    · simp [hh]
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
        (p := fun out => ∃ i,hit i out.2)).trans (hsum.trans le_self_add)
    · have hnone : ∀ i,¬hit i s := fun i hi => hh ⟨i,hi⟩
      by_cases hk : kill s
      · have hone : Pr[=true | firstHitRun impl (fun _ s => kill s)
            (fun _ _ => False) ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s]=1 := by
          rw [firstHitRun_of_hit _ _ _ _ _ _ hk]
          simp
        rw [hone]
        exact (probEvent_le_one (mx := (simulateQ impl
          ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k)).run s)
          (p := fun out => ∃ i,hit i out.2)).trans le_add_self
      · simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
          probEvent_bind_eq_expectedValue,firstHitRun_query_bind,hnone,hk,if_false,
          probOutput_bind_eq_expectedValue]
        rw [←expectedValue_finsetSum,←expectedValue_add]
        apply expectedValue_mono
        intro out
        exact ih out.1 (t+1) out.2

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

#print axioms terminal_union_or_kill_le_stopped
#print axioms terminal_union_le_stopped
end WeightedOracleExecution
end
end

/- Original module: Submissions.UpperCompressions.WideHazardTerminal; SHA256 5bc1456b25eb04a5eec0bd5144d79fc82f32888e1274bf04246eb3b57ff126a9. -/
section

/-! Uniform actual pre-sign hazard control for every message, with one common
empirical exception and one union over message rows. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedReference WeightedConstants WeightedOracleExecution
attribute [local irreducible] Finset.univ Finset.filter

theorem common_kill_bound {β : Type} (oa : OracleComp Spec β) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[=true | firstHitRun oracleImpl kill (fun _ _ => False) oa 0 c] ≤
      ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have h := WideEmpirical.all_crossings oa c hf
  unfold WideConcentration.crossing at h
  rw [prob_stopped_hit_eq_firstHitRun] at h
  have he : kill = fun (_ : ℕ) d => ∃ i : WideEmpirical.BadIndex,WideEmpirical.event i d := by
    funext n d
    simp only [kill,WideEmpirical.Good,not_forall,not_not]
  rw [he]
  exact h

theorem terminal_hits_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (oa : OracleComp Spec β) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => ∃ m : Message,hit B m 0 out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have h := terminal_union_le_stopped oracleImpl (fun m : Message => hit B m 0)
    (fun d => ¬WideEmpirical.Good d) oa 0 c
  have hm (m : Message) :
      Pr[=true | firstHitRun oracleImpl (hit B m) kill oa 0 c] ≤
        ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
    have h := stopped_large_bound B hB m oa c hf
    rw [prob_stopped_hit_eq_firstHitRun] at h
    exact h
  have hsum : (∑ m : Message,Pr[=true | firstHitRun oracleImpl (hit B m) kill oa 0 c]) ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹) := by
    calc
      _ ≤ ∑ _m : Message,ENNReal.ofReal (Real.exp (-(2048:ℝ))) :=
        Finset.sum_le_sum (fun m _ => hm m)
      _ = (Fintype.card Message:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ = ENNReal.ofReal ((2:ℝ)^256*Real.exp (-(2048:ℝ))) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        congr 1
        norm_num [Message,msgBits,Fintype.card_bitVec]
      _ ≤ _ := ENNReal.ofReal_le_ofReal WeightedHazardConstants.message_union_margin
  exact h.trans (add_le_add hsum (common_kill_bound oa c hf))

theorem terminal_hits_or_bad_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (oa : OracleComp Spec β) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => (∃ m : Message,hit B m 0 out.2) ∨ ¬WideEmpirical.Good out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have h := terminal_union_or_kill_le_stopped oracleImpl (fun m : Message => hit B m 0)
    (fun d => ¬WideEmpirical.Good d) oa 0 c
  have hm (m : Message) :
      Pr[=true | firstHitRun oracleImpl (hit B m) kill oa 0 c] ≤
        ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
    have h := stopped_large_bound B hB m oa c hf
    rw [prob_stopped_hit_eq_firstHitRun] at h
    exact h
  have hsum : (∑ m : Message,Pr[=true | firstHitRun oracleImpl (hit B m) kill oa 0 c]) ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹) := by
    calc
      _ ≤ ∑ _m : Message,ENNReal.ofReal (Real.exp (-(2048:ℝ))) :=
        Finset.sum_le_sum (fun m _ => hm m)
      _ = (Fintype.card Message:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ = ENNReal.ofReal ((2:ℝ)^256*Real.exp (-(2048:ℝ))) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        congr 1
        norm_num [Message,msgBits,Fintype.card_bitVec]
      _ ≤ _ := ENNReal.ofReal_le_ofReal WeightedHazardConstants.message_union_margin
  exact h.trans (add_le_add hsum (common_kill_bound oa c hf))

def LargeBad (B : ℕ) (c : hashSpec.QueryCache) : Prop :=
  ∃ m : Message,alpha*(globalCount c:ℝ)+(7/100)*kappa*(B:ℝ)≤hazard m c

theorem actual_large_hazard_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (oa : OracleComp Spec β) (hbudget : CostAtMost oa B) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => LargeBad B out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  apply (probEvent_mono (fun out hout hbad => ?_)).trans
    (terminal_hits_bound B hB oa c hf)
  obtain ⟨m,hm⟩ := hbad
  have hcount := WeightedProtectedCache.count_bound indexDomain oa B hbudget c out hout
  have hzero : (WeightedCacheCounts.seen indexDomain c).card=0 :=
    (WidePreSign.index_initial c hf).1
  have hn : globalCount out.2≤B := by
    exact (hcount.trans (min_le_right _ _)).trans_eq (by rw [hzero,zero_add])
  refine ⟨m,?_,?_⟩
  · exact Nat.cast_le.mpr hn
  · change (7/100)*kappa*(B:ℝ)≤hazard m out.2-alpha*(globalCount out.2:ℝ)
    linarith

theorem actual_large_good_hazard_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (oa : OracleComp Spec β) (hbudget : CostAtMost oa B) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => ¬WideEmpirical.Good out.2 ∨ LargeBad B out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  apply (probEvent_mono (fun out hout hbad => ?_)).trans
    (terminal_hits_or_bad_bound B hB oa c hf)
  rcases hbad with hbad | hbad
  · exact Or.inr hbad
  · obtain ⟨m,hm⟩ := hbad
    have hcount := WeightedProtectedCache.count_bound indexDomain oa B hbudget c out hout
    have hzero : (WeightedCacheCounts.seen indexDomain c).card=0 :=
      (WidePreSign.index_initial c hf).1
    have hn : globalCount out.2≤B :=
      (hcount.trans (min_le_right _ _)).trans_eq (by rw [hzero,zero_add])
    refine Or.inl ⟨m,?_,?_⟩
    · exact Nat.cast_le.mpr hn
    · change (7/100)*kappa*(B:ℝ)≤hazard m out.2-alpha*(globalCount out.2:ℝ)
      linarith

#print axioms terminal_hits_or_bad_bound
#print axioms actual_large_good_hazard_bound
#print axioms terminal_hits_bound
#print axioms actual_large_hazard_bound
end OptimalOTS.WeightedConstruction.WideHazard
end
end

/- Original module: Submissions.UpperCompressions.WideLargeClock; SHA256 23f9230c4006824280f53a58d8261871efbe630f0515ddf50a2fbf316a657032. -/
section

/-! The actual large-budget good event and the same public spent/remaining clock. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
open WideDomains WeightedReference WeightedBudgetClosure
attribute [local irreducible] Finset.univ Finset.filter

def largeGood (A : forestScheme.toAlgorithm.Adversary) (B : ℕ)
    (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : Prop :=
  WideEmpirical.Good r.2.1 ∧ ¬WideHazard.LargeBad B r.2.1

def countClock (A : forestScheme.toAlgorithm.Adversary)
    (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  WideHazard.globalCount r.2.1

def preOther (A : forestScheme.toAlgorithm.Adversary) : ℝ≥0∞ :=
  ∑ pk : PublicKey, sumW (fiberA pk)*
    expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅

theorem preAuth_eq (A : forestScheme.toAlgorithm.Adversary) :
    preAuth A = ENNReal.ofReal (kappa/2)*preOther A := by
  unfold preAuth preOther
  rw [authRate_ofReal,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem choose_count_other_post_le (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    E (runRemaining (A.choose pk) ∅ (B-995)) (countClock A pk)+
      expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅+
      E (runRemaining (A.choose pk) ∅ (B-995)) (postRemaining A pk) ≤ B := by
  have hd := distinct_other_le_expected_paid (A.choose pk) ∅ (fun _ _ => rfl)
  rw [← runRemaining_project (A.choose pk) ∅ (B-995),E_map] at hd
  have hh := (add_le_add hd (le_refl
    (E (runRemaining (A.choose pk) ∅ (B-995)) (postRemaining A pk)))).trans
      (choose_spent_post_remaining_le A hB pk)
  exact hh.trans (by exact_mod_cast (Nat.sub_le (B-995) signBudget).trans (Nat.sub_le B 995))

theorem global_count_other_post_le (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) :
    weightedClock A B (countClock A)+preOther A+
      weightedClock A B (postRemaining A) ≤ B := by
  unfold weightedClock preOther
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*(B:ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro pk _
      simpa only [mul_add] using mul_le_mul' (le_refl (sumW (fiberA pk)))
        (choose_count_other_post_le A hB pk)
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

theorem large_bad_clock_le (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (hBN : WideHazard.N/10 ≤ (B:ℝ)) :
    weightedClock A B (badGate A (largeGood A B)) ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have htail (pk : PublicKey) :
      E (runRemaining (A.choose pk) ∅ (B-995)) (badGate A (largeGood A B) pk) ≤
        ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
    have hb := AlgorithmCosts.CostAtMost.mono (choose_reserved_budget A hB pk).2
      ((Nat.sub_le (B-995) signBudget).trans (Nat.sub_le B 995))
    have h := WideHazard.actual_large_good_hazard_bound B hBN (A.choose pk) hb ∅ (fun _ _ => rfl)
    have he : E (run (A.choose pk) ∅)
        (fun p => if ¬WideEmpirical.Good p.2 ∨ WideHazard.LargeBad B p.2 then 1 else 0) =
        Pr[fun p => ¬WideEmpirical.Good p.2 ∨ WideHazard.LargeBad B p.2 | run (A.choose pk) ∅] :=
      expectedValue_ite_one _ _
    rw [← he,← runRemaining_project (A.choose pk) ∅ (B-995),E_map] at h
    convert h using 1
    congr 1
    funext r
    simp only [badGate,largeGood]
    split_ifs <;> simp_all
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*
        (ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹)) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (htail pk)
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

theorem large_hazard_clock_le (A : forestScheme.toAlgorithm.Adversary) (B : ℕ) :
    weightedClock A B (gatedHazard A (largeGood A B)) ≤
      ENNReal.ofReal (C*(91/100)*kappa)*weightedClock A B (countClock A)+
        ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)) := by
  have hpoint (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) :
      gatedHazard A (largeGood A B) pk r ≤
        ENNReal.ofReal (C*(91/100)*kappa)*countClock A pk r+
          ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)) := by
    by_cases hg : largeGood A B pk r
    · rw [gatedHazard,if_pos hg]
      have hh : WideHazard.hazard r.1.1 r.2.1 <
          WideHazard.alpha*(WideHazard.globalCount r.2.1:ℝ)+(7/100)*kappa*(B:ℝ) :=
        lt_of_not_ge (fun h => hg.2 ⟨r.1.1,h⟩)
      have hc : 0 ≤ C := by norm_num [C]
      have hk : 0 ≤ kappa := by norm_num [kappa]
      have h := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hh.le hc)
      change ENNReal.ofReal (C*cacheHazard r.1.1 r.2.1) ≤ _ at h
      apply h.trans_eq
      unfold WideHazard.alpha countClock
      rw [show C*((91/100)*kappa*(WideHazard.globalCount r.2.1:ℝ)+(7/100)*kappa*(B:ℝ)) =
        (C*(91/100)*kappa)*(WideHazard.globalCount r.2.1:ℝ)+C*(7/100)*kappa*(B:ℝ) by ring,
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast]
    · rw [gatedHazard,if_neg hg]
      exact zero_le
  calc
    _ ≤ weightedClock A B (fun pk r =>
        ENNReal.ofReal (C*(91/100)*kappa)*countClock A pk r+
          ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ))) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (E_mono _ (hpoint pk))
    _ = ENNReal.ofReal (C*(91/100)*kappa)*weightedClock A B (countClock A)+
        weightedClock A B (fun _ _ => ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ))) := by
      rw [weightedClock_add,weightedClock_const_mul]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)) :=
          Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (E_const_le _ _)
        _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

#print axioms global_count_other_post_le
#print axioms large_bad_clock_le
#print axioms large_hazard_clock_le
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.ActualLargeSecurity; SHA256 533b6138035b6326f29f52c71a7c5b2d5ccb131cf08d1ba33c7b7d4a4e9322f8. -/
section

/-! Final large-budget strong-success bound for the actual typed experiment. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
open WeightedReference WeightedBudgetClosure
attribute [local irreducible] Finset.univ Finset.filter

/-- All probabilistic premises are discharged for the original strong-success
experiment. The remaining hypotheses are its protected pathwise budget and the
large-budget numerical interval. -/
theorem actual_large_security (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (hBN : (2:ℝ)^86/10 ≤ (B:ℝ)) (hcap : (B:ℝ) ≤ (2:ℝ)^127) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      ENNReal.ofReal ((991:ℝ)/1000*kappa*(B:ℝ)) := by
  have hex := global_actual_payoff_expanded A hB (largeGood A B) (fun _ _ h => h.1)
  have hbad := large_bad_clock_le A hB hBN
  have hh := large_hazard_clock_le A B
  have he := all_exception_margin_ennreal B (keygen_remaining A hB).1 hcap
  have herr : weightedClock A B (badGate A (largeGood A B))+
      (1+(B:ℝ≥0∞))*(2:ℝ≥0∞)⁻¹^761 ≤ ENNReal.ofReal (kappa*(B:ℝ)/1000) :=
    (add_le_add hbad le_rfl).trans he
  rw [preAuth_eq] at hex
  have hn := large_shared_ennreal B (weightedClock A B (countClock A)) (preOther A)
    (weightedClock A B (postRemaining A))
    (weightedClock A B (gatedHazard A (largeGood A B)))
    (weightedClock A B (badGate A (largeGood A B))+(1+(B:ℝ≥0∞))*(2:ℝ≥0∞)⁻¹^761)
    (global_count_other_post_le A hB) hh herr
  exact hex.trans (by simpa only [add_assoc] using hn)

theorem actual_large_security_strict (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (hBN : (2:ℝ)^86/10 ≤ (B:ℝ)) (hcap : (B:ℝ) ≤ (2:ℝ)^127) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue <
      ENNReal.ofReal (kappa*(B:ℝ)) := by
  have hpos : 0 < kappa*(B:ℝ) := by
    have hk : 0 < kappa := by norm_num [kappa]
    have hb : 0 < (B:ℝ) := lt_of_lt_of_le (by norm_num) hBN
    exact mul_pos hk hb
  apply (actual_large_security A hB hBN hcap).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hpos).mpr
  nlinarith

#print axioms actual_large_security
#print axioms actual_large_security_strict
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.WideBudgetEndpoints; SHA256 3bbd98beaab39e219e09670cea8027d323c2b796166c53c28ce9c8b6a90e9129. -/
section

/-! Positive budget and strict scalar endpoints for the protected experiment.
No probability bound or security premise is silently introduced here. -/
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.WideBudgetEndpoints
open OracleComp ENNReal
open WideForest WideWire WeightedReference

theorem experiment_budget (A : typed.Adversary) (B : ℕ)
    (hB : CostAtMost (typed.experiment A) B) : 995 ≤ B := by
  have h := GraphKeygenBridge.costAtMost_keygen_bind
    forestScheme.graph forestScheme.publicKey _ hB
  rw [forestScheme_keygenCost] at h
  exact h.1

theorem raw_experiment_budget (A : OracleAlgorithm.Adversary) (B : ℕ)
    (hB : CostAtMost (OracleAlgorithm.experiment scheme A) B) : 995 ≤ B := by
  change CostAtMost (OracleAlgorithm.experiment (WireAdapter.scheme typed decode) A) B at hB
  rw [WireAdapter.experiment_eq typed decode decode_encode canonical A] at hB
  exact experiment_budget _ B hB

theorem small_strict (K : ℝ) (hK : 0 < K) :
    (243337:ℝ)/245000*kappa*K < kappa*K := by
  have hk : 0 < kappa*K := mul_pos (by norm_num [kappa]) hK
  nlinarith

theorem large_strict (K : ℝ) (hK : 0 < K) :
    (991:ℝ)/1000*kappa*K < kappa*K := by
  have hk : 0 < kappa*K := mul_pos (by norm_num [kappa]) hK
  nlinarith

theorem above_trivial_budget (p : ℝ) (hp : p ≤ 1) (B : ℕ) (hB : 2^127 < B) :
    p < kappa*(B:ℝ) := by
  have hBr : (2:ℝ)^127 < B := by exact_mod_cast hB
  have hk := mul_lt_mul_of_pos_left hBr (show 0 < kappa by norm_num [kappa])
  have he : kappa*(2:ℝ)^127=1 := by norm_num [kappa]
  rw [he] at hk
  exact hp.trans_lt hk

/-- Canonical raw encoding transfers the eventual typed theorem exactly. -/
theorem raw_secure_of_typed (h : typed.Secure) : scheme.Secure :=
  WireAdapter.secure typed decode decode_encode canonical h

#print axioms experiment_budget
#print axioms raw_experiment_budget
#print axioms raw_secure_of_typed
end OptimalOTS.WeightedConstruction.WideBudgetEndpoints
end
end

/- Original module: Submissions.UpperCompressions.WideSecurityClosure; SHA256 9b63d9240cd77248a543e19dc5634670d6b324e81882c3a963dd6789b1d0e7e6. -/
section

/-! The exact protected security conclusion from two explicit actual-game
branch bounds. This module is conditional until those bounds are supplied. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideSecurityClosure
open WideForest WideBudgetEndpoints WeightedReference
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem probTrue_eq_success (oa : OracleComp Spec Bool) :
    probTrue oa = E (run oa ∅) successValue := by
  unfold probTrue
  rw [run'_eq,probOutput_map_eq_tsum_ite,E,expectedValue_def]
  refine tsum_congr fun x => ?_
  rcases x with ⟨b,c⟩
  cases b <;> simp [successValue]

theorem security_rate (B : ℕ) :
    ENNReal.ofReal (kappa*(B:ℝ)) = (B:ℝ≥0∞)/2^securityBits := by
  rw [ENNReal.ofReal_mul (by norm_num [kappa])]
  norm_num [kappa,securityBits,ENNReal.ofReal_div_of_pos]
  simp only [div_eq_mul_inv,mul_comm]

/-- Strict security for every natural budget, including the exact endpoints
at the row threshold and at2^127. Budgets above2^127 need only success≤1. -/
theorem typed_secure_of_bounds
    (small : ∀ (A : forestScheme.toAlgorithm.Adversary) (B : ℕ),
      CostAtMost (forestScheme.toAlgorithm.experiment A) B →
      (B:ℝ)≤(2:ℝ)^86/10 → B≤2^127 →
      E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
        ENNReal.ofReal ((243337:ℝ)/245000*kappa*(B:ℝ)))
    (large : ∀ (A : forestScheme.toAlgorithm.Adversary) (B : ℕ),
      CostAtMost (forestScheme.toAlgorithm.experiment A) B →
      (2:ℝ)^86/10≤(B:ℝ) → B≤2^127 →
      E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
        ENNReal.ofReal ((991:ℝ)/1000*kappa*(B:ℝ))) :
    forestScheme.toAlgorithm.Secure := by
  intro A B hB
  have hbudget : 995≤B := experiment_budget A B hB
  have hpos : 0<(B:ℝ) := by exact_mod_cast (show 0<B by omega)
  have hrate : 0<kappa*(B:ℝ) := mul_pos (by norm_num [kappa]) hpos
  rw [probTrue_eq_success,← security_rate]
  by_cases hcap : B≤2^127
  · by_cases hsmall : (B:ℝ)≤(2:ℝ)^86/10
    · exact (small A B hB hsmall hcap).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hrate).mpr (small_strict B hpos))
    · exact (large A B hB (le_of_not_ge hsmall) hcap).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hrate).mpr (large_strict B hpos))
  · have ht : (1:ℝ)<kappa*(B:ℝ) :=
      above_trivial_budget 1 le_rfl B (lt_of_not_ge hcap)
    have he : (1:ℝ≥0∞)<ENNReal.ofReal (kappa*(B:ℝ)) := by
      simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff hrate).mpr ht
    exact (E_le_one _ successValue_le_one).trans_lt he

#print axioms probTrue_eq_success
#print axioms security_rate
#print axioms typed_secure_of_bounds
end OptimalOTS.WeightedConstruction.WideSecurityClosure
end
end

/- Original module: Submissions.UpperCompressions.WideSecure; SHA256 de2988cab8e51fb92e400b113e4ac806654b4152981ac9009039d03faaab5fa9. -/
section

/-! Full strong security of the weighted, wide-word forest construction. -/
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.WideSecure
open WideForest

theorem typed_secure : forestScheme.toAlgorithm.Secure := by
  apply WideSecurityClosure.typed_secure_of_bounds
  · intro A B hB hsmall hcap
    exact WideSmallSecurity.actual_small_security A hB hsmall (by exact_mod_cast hcap)
  · intro A B hB hlarge hcap
    exact actual_large_security A hB hlarge (by exact_mod_cast hcap)

theorem raw_secure : WideWire.scheme.Secure :=
  WideBudgetEndpoints.raw_secure_of_typed typed_secure

#print axioms typed_secure
#print axioms raw_secure
end OptimalOTS.WeightedConstruction.WideSecure
end
end

