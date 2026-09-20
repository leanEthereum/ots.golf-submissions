import Submissions.UpperCompressions.ProofBundle05
import Submissions.UpperCompressions.ProofBundle03
import Submissions.UpperCompressions.ProofBundle04
import Submissions.UpperCompressions.ProofBundle00

/- Original module: Submissions.UpperCompressions.WideAuthGame; SHA256 cba85ce34505e2c5b92796714543045d895ee788e658dd412e34721a3ef9cc77. -/
section

/-! Actual typed strong-forgery continuation and hidden-graph cache coupling.
The remaining alternate-class event includes accepted private signing trials. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter OptimalOTS.WeightedResearch92.classes
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

variable (A : forestScheme.toAlgorithm.Adversary)

def stB (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) : OracleComp Spec Bool := do
  let (m₂, σ₂) ← A.forge st σ
  let ok ← forestScheme.verify pk m₂ σ₂
  return ok && decide (σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

def successValue (p : Bool × Cache) : ℝ≥0∞ := if p.1 = true then 1 else 0

theorem successValue_le_one (p : Bool × Cache) : successValue p ≤ 1 := by
  unfold successValue
  split_ifs <;> simp

theorem stB_success (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stB A pk m₁ st σ) c)) (hok : p.1 = true) :
    ∃ m₂ σ₂ c₁, σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂) ∧
      (true, p.2) ∈ support (run (forestScheme.verify pk m₂ σ₂) c₁) := by
  unfold stB at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m₂, σ₂⟩, c₁⟩, h₁, hp⟩ := hp
  dsimp only at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok, c₂⟩, h₂, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  subst ok
  exact ⟨m₂, σ₂, c₁, hne, h₂⟩

theorem stB_events_some (ξ : Rec) (i : Fin WeightedSchedule.M) (η : BitVec 86)
    (m₁ : Message) (st : A.State) (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stB A (pkOf ξ) m₁ st
      (some (η, revealed (setsName i) ξ))) c)) (hok : p.1 = true) :
    Spr p.2 ξ ∨ Cache.Hits p.2 (fHid (some (setsName i)) ξ) ∨ AlternateClass p.2 (m₁, η) i := by
  obtain ⟨m₂, σ₂, c₁, hne, hv⟩ := stB_success A (pkOf ξ) m₁ st _ c p hp hok
  apply accepted_strong_event ξ i (m₁, η) m₂ σ₂ c₁ p.2 hv
  intro he
  apply hne
  exact congrArg some he.symm

theorem stB_events_none (ξ : Rec) (m₁ : Message) (st : A.State) (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stB A (pkOf ξ) m₁ st none) c)) (hok : p.1 = true) :
    Spr p.2 ξ ∨ Cache.Hits p.2 (kc ξ) := by
  obtain ⟨m₂, σ₂, c₁, _, hv⟩ := stB_success A (pkOf ξ) m₁ st none c p hp hok
  exact accepted_none_event ξ m₂ σ₂ c₁ p.2 hv

theorem ind_of {p : Prop} (h : p) : ind p = 1 := by rw [ind, if_pos h]
theorem ind_not {p : Prop} (h : ¬ p) : ind p = 0 := by rw [ind, if_neg h]

/-- Remove the hidden graph cache under the actual oracle law, charging its
first query through the checked identical-until-bad theorem. -/
theorem graph_iub (oa : OracleComp Spec Bool) (ξ : Rec) (A? : Option (Finset Name))
    (d d' : Cache) (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run oa (Cache.extend d' (kc ξ))) successValue ≤
      E (run oa (Cache.extend d' (fExp A? ξ)))
        (fun p => if Cache.Hits p.2 (fHid A? ξ) then 1 else successValue p) := by
  have hkc : Cache.extend d' (kc ξ) =
      Cache.extend (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    rw [Cache.extend_assoc, extend_fExp_fHid]
  have hdisj : Cache.Disjoint (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    intro q hq
    have hkq : (kc ξ q).isSome := by
      obtain ⟨h, p, hp, _, hqp⟩ := (fHid_isSome_iff _ ξ q).1 hq
      exact (kc_isSome_iff ξ q).2 ⟨h, p, hp, hqp⟩
    rw [Cache.extend_apply, indexExtension_kc_none hd' hξ hkq, Option.none_or]
    exact disjoint_fExp_fHid _ ξ q hq
  rw [hkc]
  exact iub oa (fHid A? ξ) successValue successValue_le_one _ hdisj

/-- Actual forge/verify/strong-check success is bounded by authentication bad
indicators plus the alternate-class event, after hidden graph points are removed. -/
theorem stB_iub_some (ξ : Rec) (i : Fin WeightedSchedule.M) (η : BitVec 86)
    (m₁ : Message) (st : A.State) (d d' : Cache)
    (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run (stB A (pkOf ξ) m₁ st (some (η, revealed (setsName i) ξ)))
      (Cache.extend d' (kc ξ))) successValue ≤
      E (run (stB A (pkOf ξ) m₁ st (some (η, revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
          ind (AlternateClass p.2 (m₁, η) i)) := by
  refine (graph_iub _ ξ (some (setsName i)) d d' hd' hξ).trans ?_
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hh : Cache.Hits p.2 (fHid (some (setsName i)) ξ)
  · rw [if_pos hh, ind_of hh]
    exact le_add_right le_self_add
  · rw [if_neg hh]
    by_cases hok : p.1 = true
    · rw [successValue, if_pos hok]
      rcases stB_events_some A ξ i η m₁ st _ p hp hok with hs | hh' | hi
      · rw [ind_of hs]
        exact le_add_right le_add_self
      · exact absurd hh' hh
      · rw [ind_of hi]
        exact le_add_self
    · rw [successValue, if_neg hok]
      exact zero_le

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.stB_events_some
#print axioms OptimalOTS.WeightedConstruction.WideForest.stB_iub_some
end
end

/- Original module: Submissions.UpperCompressions.WideAuthWitness; SHA256 c04e99d0fcbcc881a670607176d40bef0839ff42e92c4e6957fc1f67dfeebcfc. -/
section

/-! Retain the actual forged input for the public-exposure posterior proof.
The terminal event is tied to that output, not an existential private-cache hit. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter OptimalOTS.WeightedResearch92.classes
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name
variable (A : forestScheme.toAlgorithm.Adversary)

abbrev ForgeryResult := Message × WeightedScheme.Signature × Bool

def stBWithForgery (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) : OracleComp Spec ForgeryResult := do
  let (m₂, σ₂) ← A.forge st σ
  let ok ← forestScheme.verify pk m₂ σ₂
  return (m₂, σ₂, ok && decide (σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂)))

theorem stBWithForgery_map (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) :
    (fun r : ForgeryResult => r.2.2) <$> stBWithForgery A pk m₁ st σ = stB A pk m₁ st σ := by
  unfold stBWithForgery stB
  simp only [map_bind, map_pure]

theorem stBWithForgery_support (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option WeightedScheme.Signature) (c : Cache) (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A pk m₁ st σ) c)) (hok : p.1.2.2 = true) :
    ∃ c₁, σ.map (fun s => (m₁, s)) ≠ some (p.1.1, p.1.2.1) ∧
      (true, p.2) ∈ support (run (forestScheme.verify pk p.1.1 p.1.2.1) c₁) := by
  unfold stBWithForgery at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m₂, σ₂⟩, c₁⟩, h₁, hp⟩ := hp
  dsimp only at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok, c₂⟩, h₂, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  subst ok
  exact ⟨c₁, hne, h₂⟩

/-- The selected forged message/nonce is explicitly retained. Outside graph
badness its own verification query has the signed class and is a different input. -/
theorem stBWithForgery_index_witness (ξ : Rec) (i : Fin WeightedSchedule.M) (η : BitVec 86)
    (m₁ : Message) (st : A.State) (c : Cache) (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A (pkOf ξ) m₁ st
      (some (η, revealed (setsName i) ξ))) c)) (hok : p.1.2.2 = true) :
    ∃ w, p.2 (encQuery (p.1.1, p.1.2.1.1)) = some w ∧
      (Spr p.2 ξ ∨ Cache.Hits p.2 (fHid (some (setsName i)) ξ) ∨
        (WeightedSchedule.decode w = some i ∧ (p.1.1, p.1.2.1.1) ≠ (m₁,η))) := by
  obtain ⟨c₁, hne, hv⟩ := stBWithForgery_support A (pkOf ξ) m₁ st _ c p hp hok
  obtain ⟨w, hw, j, hj, he | hs | hh⟩ :=
    accepted_class_cases ξ i p.1.1 p.1.2.1 c₁ p.2 hv
  · obtain ⟨rfl, hpayload⟩ := he
    refine ⟨w, hw, Or.inr (Or.inr ⟨hj, ?_⟩)⟩
    intro hinput
    have hm : p.1.1 = m₁ := congrArg (fun u : EncInput => u.1) hinput
    have hn : p.1.2.1.1 = η := congrArg (fun u : EncInput => u.2) hinput
    have hpair : (p.1.1, p.1.2.1) = (m₁, (η, revealed (setsName j) ξ)) :=
      Prod.ext hm (Prod.ext hn hpayload)
    exact hne (congrArg some hpair.symm)
  · exact ⟨w, hw, Or.inl hs⟩
  · exact ⟨w, hw, Or.inr (Or.inl hh)⟩

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.stBWithForgery_map
#print axioms OptimalOTS.WeightedConstruction.WideForest.stBWithForgery_index_witness
end
end

/- Original module: Submissions.UpperCompressions.AuthPreSignExpected; SHA256 bb3c9b34f68cdb1e2db3058bcd30e4534d996d9465fa755140236b3425038f94. -/
section

/-! Authentication before signing and after signing failure, with only actual
expected non-index paid queries charged in either stage. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits Finset.univ Finset.filter

theorem authPotential_charge_none (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk) (c : Cache) (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T none (c.cacheQuery q u)) ≤
      authPotential T none c + authRate * sumW (fiberA pk) * queryCost (.inr q) := by
  simp only [authPotential_eq, fHid_none, mul_add, Finset.sum_add_distrib]
  have hh := (hits_avg_le T kc c q).trans
    (add_le_add_right (hits_charge_A' pk hT q) _)
  have hs := (spr_avg_le T c q hq).trans
    (add_le_add_right (mul_le_mul_right (sumW_mono hT) (ε * blockCost q.1)) _)
  have hc := mul_le_mul_right (authentication_charge_budget q) (sumW (fiberA pk))
  calc
    _ ≤ ((∑ ξ ∈ T, w * ind (Cache.Hits c (kc ξ))) + ε * sumW (fiberA pk)) +
        ((∑ ξ ∈ T, w * ind (Spr c ξ)) + (ε * blockCost q.1) * sumW (fiberA pk)) :=
      add_le_add hh hs
    _ = ((∑ ξ ∈ T, w * ind (Cache.Hits c (kc ξ))) +
        (∑ ξ ∈ T, w * ind (Spr c ξ))) +
        (ε + ε * blockCost q.1) * sumW (fiberA pk) := by ring
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [authRate, queryCost, mul_assoc, mul_comm, mul_left_comm] using hc

theorem presign_auth_query_expected (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (t : Spec.Domain) (c : Cache) :
    E ((oracleImpl t).run c) (fun p => authPotential T none p.2) ≤
      authPotential T none c +(authRate*sumW (fiberA pk))*otherPaid isIndex t := by
  cases t with
  | inl n =>
    rw [oracleImpl_run_inl, E_bind]
    simp only [E_pure, otherPaid, queryCost]
    split_ifs <;> simpa using E_const_le (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n))
      (authPotential T none c)
  | inr q =>
    cases hc : c q with
    | some u =>
      rw [oracleImpl_run_inr_some hc, E_pure]
      exact le_self_add
    | none =>
      rw [oracleImpl_run_inr_none hc, E_bind, E_uniform]
      simp only [E_pure]
      by_cases hi : isIndex (.inr q)
      · obtain ⟨u,rfl⟩ := hindex q hi
        rw [authPotential_index, otherPaid, if_pos hi, mul_zero, add_zero]
      · rw [otherPaid, if_neg hi]
        exact authPotential_charge_none pk hT c q hc

theorem presign_auth_expected {α : Type} (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec α) (c : Cache) :
    E (run oa c) (fun p => authPotential T none p.2) ≤
      authPotential T none c +
        (authRate*sumW (fiberA pk))*expectedCharge (otherPaid isIndex) oa c :=
  WeightedExpectedCharge.master_expected (authPotential T none) (otherPaid isIndex)
    (authRate*sumW (fiberA pk)) (presign_auth_query_expected pk hT isIndex hindex) oa c

theorem authPotential_empty (T : Finset Rec) (A? : Option (Finset Name)) :
    authPotential T A? ∅ = 0 := by
  simp [authPotential, ind, Cache.not_hits_empty, not_spr_empty]

/-- This is the actual attacker's choose program, on the reduced initially empty
cache. Hidden keygen cache removal is a separate identical-until-bad step. -/
theorem stageA_auth_expected (A : forestScheme.toAlgorithm.Adversary)
    (pk : BitVec 128) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u) :
    E (run (A.choose pk) ∅) (fun p => authPotential (fiberA pk) none p.2) ≤
      (authRate*sumW (fiberA pk))*expectedCharge (otherPaid isIndex) (A.choose pk) ∅ := by
  simpa only [authPotential_empty, zero_add] using
    presign_auth_expected pk (Finset.Subset.refl _) isIndex hindex (A.choose pk) ∅

/-- No-signature continuation: index-only private signing work preserves all
graph events, and public continuation charges only its expected non-index cost. -/
theorem no_sign_auth_expected {α : Type} (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (d d' : Cache) (hd' : IndexExtension d d')
    (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec α) :
    (∑ ξ ∈ T, w*E (run oa d')
      (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ))) ≤
      (∑ ξ ∈ T, w*ind (Spr d ξ)) +
        (authRate*sumW (fiberA pk))*expectedCharge (otherPaid isIndex) oa d' := by
  have hinit := authPotential_after_sign hd' T none hTd ∅ (fun ξ _ => fExp_none ξ)
  rw [Cache.extend_empty] at hinit
  have hsum : (∑ ξ ∈ T, w*E (run oa d')
      (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ))) =
      E (run oa d') (fun p => authPotential T none p.2) := by
    simp only [authPotential, fHid_none]
    rw [E_finsetSum]
    exact Finset.sum_congr rfl fun ξ _ => E_const_mul _ _ _
  rw [hsum]
  exact (presign_auth_expected pk hT isIndex hindex oa d').trans_eq (by rw [hinit])

/-- Actual strong forgery after a failed signature has only graph badness after
the hidden cache is removed; no index-forgery event is introduced. -/
theorem stB_iub_none (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (m₁ : Message) (st : A.State) (d d' : Cache)
    (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run (stB A (pkOf ξ) m₁ st none) (Cache.extend d' (kc ξ))) successValue ≤
      E (run (stB A (pkOf ξ) m₁ st none) d')
        (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ)) := by
  have h := graph_iub (stB A (pkOf ξ) m₁ st none) ξ none d d' hd' hξ
  simp only [fExp_none, Cache.extend_empty, fHid_none] at h
  refine h.trans ?_
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hh : Cache.Hits p.2 (kc ξ)
  · rw [if_pos hh, ind_of hh]
    exact le_self_add
  · rw [if_neg hh, ind_not hh, zero_add]
    by_cases hok : p.1 = true
    · rw [successValue, if_pos hok]
      rcases stB_events_none A ξ m₁ st d' p hp hok with hs | hh'
      · rw [ind_of hs]
      · exact absurd hh' hh
    · rw [successValue, if_neg hok]
      exact zero_le

/-- The actual failed-signature success branch on a fixed public-key record
fiber is now reduced to pre-sign spurious mass and its own expected graph cost. -/
theorem failed_sign_success_expected (A : forestScheme.toAlgorithm.Adversary)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m₁ : Message) (st : A.State) (d d' : Cache)
    (hd' : IndexExtension d d') (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u) :
    (∑ ξ ∈ T, w*E (run (stB A (pkOf ξ) m₁ st none)
      (Cache.extend d' (kc ξ))) successValue) ≤
      (∑ ξ ∈ T, w*ind (Spr d ξ)) +
        (authRate*sumW (fiberA pk))*
          expectedCharge (otherPaid isIndex) (stB A pk m₁ st none) d' := by
  have hpks := pkOf_of_subset_fiberA hT
  calc
    _ ≤ ∑ ξ ∈ T, w*E (run (stB A (pkOf ξ) m₁ st none) d')
        (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ)) :=
      Finset.sum_le_sum fun ξ hξ =>
        mul_le_mul_right (stB_iub_none A ξ m₁ st d d' hd' (hTd ξ hξ)) w
    _ = ∑ ξ ∈ T, w*E (run (stB A pk m₁ st none) d')
        (fun p => ind (Cache.Hits p.2 (kc ξ))+ind (Spr p.2 ξ)) := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [hpks ξ hξ]
    _ ≤ _ := no_sign_auth_expected pk T hT d d' hd' hTd isIndex hindex _

#print axioms stageA_auth_expected
#print axioms no_sign_auth_expected
#print axioms stB_iub_none
#print axioms failed_sign_success_expected
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.ExpectedChargeTower; SHA256 88dd3fdf8b1bec9c6ca8d14d0d32d7c66c292a3f332e00c92f726c2ae3664a89. -/
section

/-! Exact accounting across actual public/private phases of a shared-cache
OracleComp program. No pathwise budget is spent a second time at a phase split. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedReplacement
open OptimalOTS
set_option maxHeartbeats 800000

theorem expectedCharge_bind {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache) :
    expectedCharge charge (oa >>= k) c = expectedCharge charge oa c +
      E (run oa c) (fun p => expectedCharge charge (k p.1) p.2) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t next ih =>
    rw [bind_assoc, expectedCharge_query]
    simp_rw [ih]
    rw [expectedCharge_query, run_query_bind, E_bind]
    simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]
    ring

theorem expectedCharge_bind_pure {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (f : α → β) (c : Cache) :
    expectedCharge charge (oa >>= fun a => pure (f a)) c = expectedCharge charge oa c := by
  rw [expectedCharge_bind]
  simp [E, expectedValue_def]

theorem expectedCharge_map {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (f : α → β) (c : Cache) :
    expectedCharge charge (f <$> oa) c = expectedCharge charge oa c := by
  rw [map_eq_bind_pure_comp]
  exact expectedCharge_bind_pure charge oa f c

/-- The separate phase expectations recombine to precisely the original
program's cost, with each continuation starting at the real terminal cache. -/
theorem expectedCharge_three_phases {α β γ : Type} (charge : Spec.Domain → ℝ≥0∞)
    (pre : OracleComp Spec α) (middle : α → OracleComp Spec β)
    (post : α → β → OracleComp Spec γ) (c : Cache) :
    expectedCharge charge (pre >>= fun a => middle a >>= post a) c =
      expectedCharge charge pre c + E (run pre c) (fun p =>
        expectedCharge charge (middle p.1) p.2 +
          E (run (middle p.1) p.2) (fun q => expectedCharge charge (post p.1 q.1) q.2)) := by
  rw [expectedCharge_bind]
  apply congrArg (expectedCharge charge pre c + ·)
  congr 1
  funext p
  exact expectedCharge_bind charge _ _ _

#print axioms expectedCharge_bind
#print axioms expectedCharge_map
#print axioms expectedCharge_three_phases
end WeightedReplacement
end
end

/- Original module: Submissions.UpperCompressions.ExpectedSigningCharge; SHA256 6d0d6d9be31456d029fba3616ffdd8e59aea947026a41006dbb4e1397c819bce. -/
section

/-! The concrete all-L signer spends no non-index paid cost. Combining public
phases across it preserves exactly the non-index clock used by authentication. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedReplacement
open OptimalOTS OptimalOTS.WeightedSampling
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits signBudget

theorem otherPaid_le_queryCost (isIndex : Spec.Domain → Prop) (t : Spec.Domain) :
    otherPaid isIndex t ≤ queryCost t := by
  unfold otherPaid
  split_ifs <;> simp

theorem expectedCharge_other_private {α : Type} (isIndex : Spec.Domain → Prop)
    (oa : ProbComp α) (c : Cache) :
    expectedCharge (otherPaid isIndex) (liftM oa : OracleComp Spec α) c = 0 := by
  apply le_antisymm _ zero_le
  have h := expectedCharge_budget (otherPaid isIndex) 1
    (fun t => by simpa only [one_mul] using otherPaid_le_queryCost isIndex t)
    (liftM oa : OracleComp Spec α) 0 (AlgorithmCosts.costAtMost_liftM_probComp oa 0) c
  simpa only [Nat.cast_zero, mul_zero] using h

theorem expectedCharge_other_hash {n : ℕ} (isIndex : Spec.Domain → Prop)
    (x : BitVec n) (hx : isIndex (.inr ⟨n,x⟩)) (c : Cache) :
    expectedCharge (otherPaid isIndex) (hash x) c = 0 := by
  have h := expectedCharge_query (otherPaid isIndex) (.inr ⟨n,x⟩)
    (fun u => pure u) c
  simpa only [OptimalOTS.hash, bind_pure, expectedCharge_pure, E, expectedValue_def, mul_zero,
    tsum_zero, add_zero, otherPaid, if_pos hx] using h

theorem loop_otherPaid_zero {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (isIndex : Spec.Domain → Prop)
    (hi : ∀ η : Nonce n, isIndex (.inr ⟨msgBits+n,m++η⟩)) :
    ∀ k c, expectedCharge (otherPaid isIndex) (loop n decode tier m k) c = 0 := by
  intro k
  induction k with
  | zero => intro c; simp [loop]
  | succ k ih =>
    intro c
    rw [loop, expectedCharge_bind]
    rw [show expectedCharge (otherPaid isIndex) (sampleBits n) c = 0 from
      expectedCharge_other_private isIndex _ c]
    simp only [zero_add]
    have hpoint (p : Nonce n × Cache) :
        expectedCharge (otherPaid isIndex)
          (hash (m++p.1) >>= fun u => loop n decode tier m k >>= fun r =>
            pure (best (fun r => tier r.2) (candidate decode p.1 u) r)) p.2 = 0 := by
      rw [expectedCharge_bind, expectedCharge_other_hash isIndex _ (hi p.1)]
      simp only [expectedCharge_bind_pure, ih, E, expectedValue_def, mul_zero,
        tsum_zero, add_zero]
    simp_rw [hpoint]
    simp [E, expectedValue_def]

/-- All accepted nonwinning queries of the actual signer are included. They
are paid index queries and therefore do not consume the graph charge clock. -/
theorem sign_otherPaid_zero {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (isIndex : Spec.Domain → Prop)
    (hi : ∀ η : Nonce 86, isIndex (.inr ⟨msgBits+86,m++η⟩)) :
    expectedCharge (otherPaid isIndex) (S.sign x m) c = 0 := by
  rw [WeightedScheme.Scheme.sign, expectedCharge_map]
  exact loop_otherPaid_zero 86 S.decode S.tier m isIndex hi signBudget c

theorem sign_post_otherPaid {M : ℕ} {α : Type} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (isIndex : Spec.Domain → Prop)
    (hi : ∀ η : Nonce 86, isIndex (.inr ⟨msgBits+86,m++η⟩))
    (post : Option WeightedScheme.Signature → OracleComp Spec α) :
    expectedCharge (otherPaid isIndex) (S.sign x m >>= post) c =
      E (run (S.sign x m) c) (fun p => expectedCharge (otherPaid isIndex) (post p.1) p.2) := by
  rw [expectedCharge_bind, sign_otherPaid_zero S x m c isIndex hi, zero_add]

#print axioms loop_otherPaid_zero
#print axioms sign_otherPaid_zero
#print axioms sign_post_otherPaid
end WeightedReplacement
end
end

/- Original module: Submissions.UpperCompressions.ReplacementPublicUnion; SHA256 073b8da3b45bc6d6fea161eb9410cc4203f5c8ad9a62139ead9cded92ce08556. -/
section

/-! The terminal chosen input is charged to its actual first public query.
This uses the program's query prefix, not membership in a private signer cache. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementPublicUnion_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits blockBits msgBits signBudget

theorem publicHit_le_one {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache) :
    publicHit u oa c ≤ 1 := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    rw [publicHit_query]
    split_ifs
    · exact le_rfl
    · exact E_le_one _ (fun p => ih p.1 p.2)

theorem publicHit_query_target {α : Type} (u : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) :
    publicHit u (liftM (Spec.query (.inr u)) >>= k) c = 1 := by
  rw [publicHit_query]
  simp

theorem publicHit_hash_target {α : Type} {n : ℕ} (x : BitVec n)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) :
    publicHit ⟨n,x⟩ (hash x >>= k) c = 1 := by
  unfold OptimalOTS.hash
  exact publicHit_query_target _ k c

/-- A hit during the continuation is a hit of the whole public program. Hits
that already occurred in the prefix only strengthen this inequality. -/
theorem publicHit_bind_ge {α β : Type} (u : Query) (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (c : Cache) :
    E (run oa c) (fun p => publicHit u (k p.1) p.2) ≤ publicHit u (oa >>= k) c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t next ih =>
    rw [bind_assoc, publicHit_query]
    split_ifs
    · exact E_le_one _ (fun p => publicHit_le_one u (k p.1) p.2)
    · rw [run_query_bind, E_bind]
      exact E_mono _ (fun p => ih p.1 p.2)

/-- If each selected continuation really queries its chosen input, the selected
input event is bounded by the probability of that input's first public query. -/
theorem publicHit_query_output {α β : Type} (u : Query) (chosen : α → Query)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache)
    (hquery : ∀ a, chosen a = u → ∀ d, publicHit u (k a) d = 1) :
    E (run oa c) (fun p => if chosen p.1 = u then 1 else 0) ≤ publicHit u (oa >>= k) c := by
  apply (E_mono (run oa c) (fun p => ?_)).trans (publicHit_bind_ge u oa k c)
  by_cases h : chosen p.1 = u
  · rw [if_pos h, hquery p.1 h p.2]
  · rw [if_neg h]
    exact bot_le

/-- Finite union for a forger's actual selected input, provided its continuation
queries that input. Fixed initial-public-cache and signed-input exclusions may
be put in `allowed`; target class membership is `good`. -/
theorem selected_input_union {D α β : Type} [Fintype D]
    (e : D → Query) (chosen : α → D) (allowed good : D → Prop)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache)
    (hquery : ∀ a, ∀ d, publicHit (e (chosen a)) (k a) d = 1) :
    E (run oa c) (fun p => if allowed (chosen p.1) ∧ good (chosen p.1) then 1 else 0) ≤
      ∑ d, if allowed d ∧ good d then publicHit (e d) (oa >>= k) c else 0 := by
  have hpoint (p : α × Cache) :
      (if allowed (chosen p.1) ∧ good (chosen p.1) then (1:ℝ≥0∞) else 0) =
      ∑ d, if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0 := by
    have hh (d : D) :
        (if allowed d ∧ good d then (if chosen p.1 = d then (1:ℝ≥0∞) else 0) else 0) =
        if chosen p.1 = d then (if allowed d ∧ good d then 1 else 0) else 0 := by
      split_ifs <;> rfl
    simp_rw [hh]
    simp
  calc
    _ = E (run oa c) (fun p => ∑ d, if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0) := by
      congr 1
      funext p
      exact hpoint p
    _ = ∑ d, E (run oa c) (fun p => if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0) :=
      expectedValue_finsetSum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : allowed d ∧ good d
      · simp only [if_pos hd]
        have hdom : E (run oa c) (fun p => if chosen p.1 = d then 1 else 0) ≤
            E (run oa c) (fun p => if e (chosen p.1) = e d then 1 else 0) := E_mono _ (fun p => by
          by_cases hp : chosen p.1 = d
          · simp [hp]
          · simp [hp])
        apply hdom.trans
        apply publicHit_query_output (e d) (e ∘ chosen) oa k c
        intro a ha d'
        exact ha ▸ hquery a d'
      · simp only [if_neg hd]
        exact E_const_le _ 0

#print axioms publicHit_bind_ge
#print axioms publicHit_query_output
#print axioms selected_input_union

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementCoordinate; SHA256 79723c5c5230991322696736259eabe4975f7fc42be21d39e70af64ecbfd6c80. -/
section

/-! Exact single-coordinate decomposition for real table updates, followed by a
Bayes bound for the actual first-minimum sampling likelihood. No Good event is
conditioned on. Adaptive transcript/filtration integration remains separate. -/

namespace WeightedReplacement

open OptimalOTS.WeightedSampling
open scoped Classical
noncomputable section
local instance stagedLocal_ReplacementCoordinate_1 {α : Type*} : DecidableEq α := Classical.decEq α

noncomputable def fractionExcept {ι : Type} [Fintype ι] (p : ι → Prop) (u : ι) : ℝ :=
  (∑ a ∈ Finset.univ.erase u, if p a then (1 : ℝ) else 0) / Fintype.card ι

theorem fractionExcept_nonneg {ι : Type} [Fintype ι] (p : ι → Prop) (u : ι) :
    0 ≤ fractionExcept p u := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a ha
  split_ifs <;> norm_num

theorem fraction_update {ι Ω : Type} [Fintype ι] (table : ι → Ω)
    (p : Ω → Prop) (u : ι) (y : Ω) :
    fraction (p ∘ Function.update table u y) = fractionExcept (p ∘ table) u +
      if p y then 1 / (Fintype.card ι : ℝ) else 0 := by
  have hs : (∑ a, if p (Function.update table u y a) then (1 : ℝ) else 0) =
      (∑ a ∈ Finset.univ.erase u, if p (table a) then (1 : ℝ) else 0) +
        (if p y then 1 else 0) := by
    calc
      _ = (∑ a ∈ Finset.univ.erase u,
          if p (Function.update table u y a) then (1 : ℝ) else 0) +
          (if p (Function.update table u y u) then 1 else 0) :=
        (Finset.sum_erase_add Finset.univ
          (fun a => if p (Function.update table u y a) then (1 : ℝ) else 0)
          (Finset.mem_univ u)).symm
      _ = _ := by
        rw [Function.update_self]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [Function.update_of_ne (Finset.mem_erase.mp ha).1]
  unfold fraction uniformMean fractionExcept
  simp only [Function.comp_apply]
  rw [hs, add_div]
  by_cases hy : p y <;> simp [hy]

/-- The exact first-minimum target likelihood on one concrete decoded table. -/
noncomputable def tableWinnerLikelihood {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (v : ι) (i : γ) : ℝ :=
  iidMean k (fun xs => if select (fun p : ι × γ => tier p.2)
      (xs.map fun a => (fun j => (a,j)) <$> decode (table a)) = some (v,i)
    then (1 : ℝ) else 0)

theorem tableWinnerLikelihood_eq {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (v : ι) (i : γ) (hv : decode (table v) = some i) :
    tableWinnerLikelihood k table decode tier v i =
      kernel k (fraction (weakRank tier i ∘ decode ∘ table))
        (fraction (strictRank tier i ∘ decode ∘ table)) / Fintype.card ι := by
  have h := iid_tagged_table_probability (decode ∘ table) tier v i hv k
  unfold tableWinnerLikelihood
  convert h using 1
  congr 1

/-- Changing a distinct unknown nonce changes each survival endpoint only by
that coordinate's exact mass 1/N. This identifies the generic Bayes kernel with
the actual selector likelihood, not an assumed likelihood surrogate. -/
theorem tableWinnerLikelihood_update {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (u v : ι) (i : γ) (hvu : v ≠ u) (hv : decode (table v) = some i) (y : Ω) :
    tableWinnerLikelihood k (Function.update table u y) decode tier v i =
      coordinateLikelihood k
        (fractionExcept (weakRank tier i ∘ decode ∘ table) u)
        (fractionExcept (strictRank tier i ∘ decode ∘ table) u)
        (1 / (Fintype.card ι : ℝ)) (Fintype.card ι)
        (weakRank tier i ∘ decode) (strictRank tier i ∘ decode) y := by
  rw [tableWinnerLikelihood_eq k _ decode tier v i
    (by simpa only [Function.update_of_ne hvu] using hv)]
  have hweak := fraction_update table (weakRank tier i ∘ decode) u y
  have hstrict := fraction_update table (strictRank tier i ∘ decode) u y
  simp only [Function.comp_assoc] at hweak hstrict
  rw [hweak, hstrict]
  rfl

/-- Posterior bound for a fresh coordinate, pointwise in every other table entry.
The signed nonce v differs from the unknown nonce u. -/
theorem updated_table_posterior_bound {ι Ω γ : Type} [Fintype ι] [Fintype Ω]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (u v : ι) (i : γ) (hvu : v ≠ u) (hv : decode (table v) = some i)
    (weight : Ω → ℝ) (hw : ∀ y, 0 ≤ weight y)
    (hmass : 0 < weightedMass weight (weakRank tier i ∘ decode))
    (hden : 0 < ∑ y, weight y *
      tableWinnerLikelihood k (Function.update table u y) decode tier v i) :
    (∑ y, if decode y = some i then weight y *
      tableWinnerLikelihood k (Function.update table u y) decode tier v i else 0) /
      (∑ y, weight y * tableWinnerLikelihood k (Function.update table u y) decode tier v i) ≤
      weightedMass weight (fun y => decode y = some i) /
        weightedMass weight (weakRank tier i ∘ decode) := by
  simp_rw [tableWinnerLikelihood_update k table decode tier u v i hvu hv] at hden ⊢
  have ht : ∀ y, decode y = some i →
      (weakRank tier i ∘ decode) y ∧ ¬ (strictRank tier i ∘ decode) y := by
    intro y hy
    simp [hy, weakRank, strictRank]
  have h := coordinate_posterior_bound k
    (fractionExcept (weakRank tier i ∘ decode ∘ table) u)
    (fractionExcept (strictRank tier i ∘ decode ∘ table) u)
    (1 / (Fintype.card ι : ℝ)) (Fintype.card ι) weight
    (fun y => decode y = some i) (weakRank tier i ∘ decode) (strictRank tier i ∘ decode)
    (fractionExcept_nonneg _ _) (fractionExcept_nonneg _ _)
    (div_nonneg zero_le_one (Nat.cast_nonneg _)) (Nat.cast_nonneg _) hw ht hmass hden
  convert h using 1 <;> congr 2
  funext y
  split_ifs <;> rfl

def lowerRank {γ : Type} (tier : γ → ℕ) (i : γ) : Option γ → Prop
  | none => False
  | some j => tier j < tier i

theorem weakRank_iff_not_lowerRank {γ : Type} (tier : γ → ℕ) (i : γ) (x : Option γ) :
    weakRank tier i x ↔ ¬ lowerRank tier i x := by
  cases x <;> simp [weakRank, lowerRank, Nat.not_lt]

theorem weightedMass_add_complement {Ω : Type} [Fintype Ω]
    (weight : Ω → ℝ) (p : Ω → Prop) :
    weightedMass weight p + weightedMass weight (fun y => ¬ p y) = ∑ y, weight y := by
  unfold weightedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hp : p y <;> simp [hp]

/-- With a normalized prior, exact class mass p and lower-tier prefix mass F,
the concrete updated-table Bayes posterior is at most p/(1-F). -/
theorem updated_table_posterior_class_bound {ι Ω γ : Type} [Fintype ι] [Fintype Ω]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (u v : ι) (i : γ) (hvu : v ≠ u) (hv : decode (table v) = some i)
    (weight : Ω → ℝ) (hw : ∀ y, 0 ≤ weight y) (hunit : ∑ y, weight y = 1)
    (p F : ℝ) (hp : weightedMass weight (fun y => decode y = some i) = p)
    (hF : weightedMass weight (lowerRank tier i ∘ decode) = F) (hFlt : F < 1)
    (hden : 0 < ∑ y, weight y *
      tableWinnerLikelihood k (Function.update table u y) decode tier v i) :
    (∑ y, if decode y = some i then weight y *
      tableWinnerLikelihood k (Function.update table u y) decode tier v i else 0) /
      (∑ y, weight y * tableWinnerLikelihood k (Function.update table u y) decode tier v i) ≤
      p / (1-F) := by
  have hweak : weightedMass weight (weakRank tier i ∘ decode) = 1-F := by
    have h := weightedMass_add_complement weight (lowerRank tier i ∘ decode)
    have he : (fun y => ¬ (lowerRank tier i ∘ decode) y) = weakRank tier i ∘ decode := by
      funext y
      exact propext (weakRank_iff_not_lowerRank tier i (decode y)).symm
    rw [he, hF, hunit] at h
    linarith
  have hmass : 0 < weightedMass weight (weakRank tier i ∘ decode) := by
    rw [hweak]
    linarith
  simpa only [hp, hweak] using
    updated_table_posterior_bound k table decode tier u v i hvu hv weight hw hmass hden

#print axioms fraction_update
#print axioms tableWinnerLikelihood_update
#print axioms updated_table_posterior_class_bound

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementMixture; SHA256 256cd26d28456e6eb2a37e99ca451bca843358a7c40c38c35f7be11f3a03ffcb. -/
section

/-! The posterior bound survives arbitrary coordinate-independent evidence and
finite mixtures over all other coordinates. Individual mixture components may
have zero signing likelihood; only the aggregate conditioning event must have
positive probability. No Good-event conditioning is used. -/

namespace WeightedReplacement

open scoped Classical

noncomputable def mixedLikelihood {Z Ω : Type} [Fintype Z]
    (latent evidence : Z → ℝ) (likelihood : Z → Ω → ℝ) (y : Ω) : ℝ :=
  ∑ z, (latent z * evidence z) * likelihood z y

/-- A Bayes likelihood comparison is stable under arbitrary nonnegative evidence
independent of the unknown coordinate, and under mixing all other coordinates.
Zero-likelihood components need no separate conditioning or division. -/
theorem finite_bayes_evidence_mixture_bound {Z Ω : Type} [Fintype Z] [Fintype Ω]
    (weight : Ω → ℝ) (latent evidence : Z → ℝ) (likelihood : Z → Ω → ℝ)
    (target survival : Ω → Prop) (c : Z → ℝ)
    (hw : ∀ y, 0 ≤ weight y) (hz : ∀ z, 0 ≤ latent z) (he : ∀ z, 0 ≤ evidence z)
    (hl : ∀ z y, 0 ≤ likelihood z y)
    (ht : ∀ z y, target y → likelihood z y = c z)
    (hs : ∀ z y, survival y → c z ≤ likelihood z y)
    (hmass : 0 < weightedMass weight survival)
    (hden : 0 < ∑ y, weight y * mixedLikelihood latent evidence likelihood y) :
    (∑ y, if target y then weight y * mixedLikelihood latent evidence likelihood y else 0) /
      (∑ y, weight y * mixedLikelihood latent evidence likelihood y) ≤
      weightedMass weight target / weightedMass weight survival := by
  apply finite_bayes_likelihood_bound weight (mixedLikelihood latent evidence likelihood)
    target survival (∑ z, (latent z * evidence z) * c z) hw
  · intro y
    exact Finset.sum_nonneg fun z _ => mul_nonneg (mul_nonneg (hz z) (he z)) (hl z y)
  · intro y hy
    apply Finset.sum_congr rfl
    intro z hz'
    rw [ht z y hy]
  · intro y hy
    apply Finset.sum_le_sum
    intro z hz'
    exact mul_le_mul_of_nonneg_left (hs z y hy) (mul_nonneg (hz z) (he z))
  · exact hmass
  · exact hden

/-- Kernel specialization: other-coordinate endpoints and evidence may vary with
the latent state, while the unknown answer retains the same prior. -/
theorem coordinate_evidence_mixture_bound {Z Ω : Type} [Fintype Z] [Fintype Ω]
    (L : ℕ) (A B : Z → ℝ) (δ N : ℝ) (weight : Ω → ℝ)
    (latent evidence : Z → ℝ) (target weak strict : Ω → Prop)
    (hA : ∀ z, 0 ≤ A z) (hB : ∀ z, 0 ≤ B z) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (hw : ∀ y, 0 ≤ weight y) (hz : ∀ z, 0 ≤ latent z) (he : ∀ z, 0 ≤ evidence z)
    (ht : ∀ y, target y → weak y ∧ ¬ strict y)
    (hmass : 0 < weightedMass weight weak)
    (hden : 0 < ∑ y, weight y * mixedLikelihood latent evidence
      (fun z => coordinateLikelihood L (A z) (B z) δ N weak strict) y) :
    (∑ y, if target y then weight y * mixedLikelihood latent evidence
        (fun z => coordinateLikelihood L (A z) (B z) δ N weak strict) y else 0) /
      (∑ y, weight y * mixedLikelihood latent evidence
        (fun z => coordinateLikelihood L (A z) (B z) δ N weak strict) y) ≤
      weightedMass weight target / weightedMass weight weak := by
  apply finite_bayes_evidence_mixture_bound weight latent evidence _ target weak
    (fun z => kernel L (A z + δ) (B z) / N) hw hz he
  · intro z
    exact coordinateLikelihood_nonneg L (A z) (B z) δ N weak strict (hA z) (hB z) hδ hN
  · intro z y hy
    exact coordinateLikelihood_same L (A z) (B z) δ N weak strict y (ht y hy).1 (ht y hy).2
  · intro z
    exact coordinateLikelihood_survival L (A z) (B z) δ N weak strict (hA z) (hB z) hδ hN
  · exact hmass
  · exact hden

#print axioms finite_bayes_evidence_mixture_bound
#print axioms coordinate_evidence_mixture_bound

end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementFactorization; SHA256 7a96e36d463a2df1d08f1117eb787ed306444486cd4ee678d8b49ef59dae1074. -/
section

/-! Compositional probability factorization: after fixing the returned signing
value, any adaptive public-prefix event contributes coordinate-independent
evidence. The equality is proved from actual `ProbComp` bind semantics. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementFactorization_1 {α : Type*} : DecidableEq α := Classical.decEq α

def taggedBind {β α : Type} (p : ProbComp β) (post : β → ProbComp α) : ProbComp (β × α) := do
  let b ← p
  let a ← post b
  pure (b,a)

/-- Fixing the first computation's returned value factors its probability from
the conditional continuation. No independence of the unconditioned outcomes is asserted. -/
theorem E_taggedBind_event {β α : Type} (p : ProbComp β) (post : β → ProbComp α)
    (b : β) (event : α → Prop) :
    E (taggedBind p post) (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
      E p (fun b' => if b' = b then 1 else 0) *
        E (post b) (fun a => if event a then 1 else 0) := by
  calc
    _ = E p (fun b' => (if b' = b then 1 else 0) *
        E (post b) (fun a => if event a then 1 else 0)) := by
      rw [taggedBind, E_bind]
      congr 1
      funext b'
      simp only [E_bind, E_pure]
      by_cases hb : b' = b
      · subst b'
        simp
      · simp [hb, E, expectedValue_def]
    _ = _ := expectedValue_mul_const p _ _

/-- Actual adaptive post-sign evidence is unchanged when the hidden table cell
is resampled. The signer distribution p is allowed to depend on that cell. -/
theorem E_taggedPrefix_update {β α : Type} (p : ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query)
    (table : Query → BitVec hashBits) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) :
    E (taggedBind p (fun b' => prefixRun u (Function.update table u y) (post b')))
        (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
      E p (fun b' => if b' = b then 1 else 0) *
        E (prefixRun u table (post b)) (fun a => if event a then 1 else 0) := by
  rw [E_taggedBind_event, prefix_event_update]

def prefixEvidence {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (event : Option α × PublicTrace → Prop) : ℝ :=
  (E (prefixRun u table oa) (fun t => if event t then 1 else 0)).toReal

theorem prefixEvidence_nonneg {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (event : Option α × PublicTrace → Prop) :
    0 ≤ prefixEvidence u table oa event := ENNReal.toReal_nonneg

theorem ofReal_prefixEvidence {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (event : Option α × PublicTrace → Prop) :
    ENNReal.ofReal (prefixEvidence u table oa event) =
      E (prefixRun u table oa) (fun t => if event t then 1 else 0) := by
  apply ENNReal.ofReal_toReal
  apply ne_of_lt
  apply lt_of_le_of_lt (E_le_one _ (fun _ => by split_ifs <;> simp))
  simp

/-- Real-valued form of the actual program factorization, ready for the finite
Bayes mixture lemma. The supplied signing likelihood is an exact probability,
not an upper bound; the complete-row sampler theorem supplies this premise. -/
theorem E_taggedPrefix_ofReal {β α : Type} (p : ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query)
    (table : Query → BitVec hashBits) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) (likelihood : ℝ)
    (hl : 0 ≤ likelihood)
    (hp : E p (fun b' => if b' = b then 1 else 0) = ENNReal.ofReal likelihood) :
    E (taggedBind p (fun b' => prefixRun u (Function.update table u y) (post b')))
        (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
      ENNReal.ofReal (likelihood * prefixEvidence u table (post b) event) := by
  rw [E_taggedPrefix_update, hp, ENNReal.ofReal_mul hl, ofReal_prefixEvidence]

#print axioms E_taggedBind_event
#print axioms E_taggedPrefix_update
#print axioms E_taggedPrefix_ofReal

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementConcentration; SHA256 dcba941eeb9bd910ba091e8ff5780b0fc28f66fa35266def2328552fec60ea1f. -/
section

/-! Finite product concentration of uniform function tables. All expectations
are finite normalized sums, then connected to the actual uniform ProbComp. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementConcentration_1 {α : Type*} : DecidableEq α := Classical.decEq α

def meanLinear (α : Type*) [Fintype α] : (α → ℝ) →ₗ[ℝ] ℝ where
  toFun := uniformMean
  map_add' f g := uniformMean_add f g
  map_smul' r f := by
    change uniformMean (fun a => r*f a) = r*uniformMean f
    simp only [uniformMean, ← Finset.mul_sum]
    ring

theorem uniformMean_mono {α : Type*} [Fintype α] (f g : α → ℝ)
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, Finset.sum_const, nsmul_eq_mul]

theorem uniformMean_product {D W : Type*} [Fintype D] [Fintype W]
    (f : D → W → ℝ) :
    uniformMean (fun g : D → W => ∏ d, f d (g d)) = ∏ d, uniformMean (f d) := by
  simp only [uniformMean, Fintype.card_fun, Nat.cast_pow]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

theorem uniformMean_centered_indicator_mgf {W : Type*} [Fintype W] [Nonempty W]
    (P : W → Prop) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    uniformMean (fun w => Real.exp (θ * (fraction P - if P w then 1 else 0) - θ^2)) ≤ 1 := by
  let X : W → ℝ := fun w => fraction P - if P w then 1 else 0
  have hμ0 : 0 ≤ fraction P := by
    unfold fraction
    exact (show uniformMean (fun _ : W => (0:ℝ)) ≤ _ from
      uniformMean_mono _ _ (fun w => by split_ifs <;> norm_num)).trans_eq' (uniformMean_const 0)
  have hμ1 : fraction P ≤ 1 := by
    unfold fraction
    calc
      _ ≤ uniformMean (fun _ : W => (1:ℝ)) := uniformMean_mono _ _ (fun w => by split_ifs <;> norm_num)
      _ = _ := uniformMean_const 1
  have hb : ∀ w, |X w| ≤ 1 := by
    intro w
    dsimp [X]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hm : meanLinear W X = 0 := by
    change uniformMean X = 0
    dsimp [X]
    simp [uniformMean, fraction, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      sub_div, mul_div_cancel_left₀ _ (show (Fintype.card W:ℝ) ≠ 0 by positivity)]
  have hs : meanLinear W (fun w => (X w)^2) ≤ 1 := by
    change uniformMean _ ≤ 1
    calc
      _ ≤ uniformMean (fun _ : W => (1:ℝ)) := uniformMean_mono _ _ (fun w => (sq_le_one_iff_abs_le_one _).2 (hb w))
      _ = _ := uniformMean_const 1
  have hx := WeightedMGF.centered_mgf (meanLinear W) (fun f g h => uniformMean_mono f g h)
    (uniformMean_const 1) X θ 1 1 hθ0 (by norm_num) (by nlinarith) hb hm hs
  have hc : θ^2 * 1 / (2 * (1-θ*1/3)) ≤ θ^2 := by
    have hd : 0 < 2*(1-θ*1/3) := by linarith
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg θ]
  have hbase : uniformMean (fun w => Real.exp (θ*X w)) ≤ Real.exp (θ^2) :=
    hx.trans (Real.exp_le_exp.mpr hc)
  have hf : (fun w => Real.exp (θ*X w-θ^2)) =
      (fun w => Real.exp (θ*X w) * Real.exp (-θ^2)) := by
    funext w
    rw [sub_eq_add_neg, Real.exp_add]
  change uniformMean (fun w => Real.exp (θ*X w-θ^2)) ≤ 1
  rw [hf, uniformMean_mul_const]
  calc
    _ ≤ Real.exp (θ^2)*Real.exp (-θ^2) :=
      mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

def empirical {D W : Type*} [Fintype D] (P : W → Prop) (g : D → W) : ℝ :=
  fraction (P ∘ g)

theorem uniform_table_deficit {D W : Type*} [Fintype D] [Nonempty D]
    [Fintype W] [Nonempty W] (P : W → Prop) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    uniformMean (fun g : D → W => if empirical P g ≤ fraction P - δ then 1 else 0) ≤
      Real.exp (-((Fintype.card D : ℝ) * δ^2 / 4)) := by
  let θ := δ/2
  let X : W → ℝ := fun w => fraction P - if P w then 1 else 0
  let Z : (D → W) → ℝ := fun g => ∑ d, (θ*X (g d)-θ^2)
  have hmgf : uniformMean (fun g : D → W => Real.exp (Z g)) ≤ 1 := by
    have hf : (fun g : D → W => Real.exp (Z g)) =
        (fun g => ∏ d, Real.exp (θ*X (g d)-θ^2)) := by
      funext g
      exact Real.exp_sum _ _
    rw [hf, uniformMean_product (fun _d : D => fun w => Real.exp (θ*X w-θ^2))]
    calc
      _ ≤ ∏ _d : D, (1:ℝ) := Finset.prod_le_prod
        (fun d _ => div_nonneg (Finset.sum_nonneg (fun w _ => Real.exp_nonneg _)) (by positivity))
        (fun d _ => uniformMean_centered_indicator_mgf P θ (by dsimp [θ]; positivity) (by dsimp [θ]; linarith))
      _ = _ := by simp
  have hbad (g : D → W) (hg : empirical P g ≤ fraction P-δ) :
      (Fintype.card D:ℝ)*δ^2/4 ≤ Z g := by
    have hN : 0 < (Fintype.card D:ℝ) := by positivity
    have hsum : (∑ d, if P (g d) then (1:ℝ) else 0) ≤
        (fraction P-δ)*(Fintype.card D:ℝ) := by
      apply (div_le_iff₀ hN).mp
      exact hg
    dsimp [Z, X, θ]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    nlinarith
  exact WeightedKernel.exponential_tail (meanLinear (D → W))
    (fun f g h => uniformMean_mono f g h) _ Z ((Fintype.card D:ℝ)*δ^2/4) hbad hmgf

#print axioms uniformMean_product
#print axioms uniform_table_deficit

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementTableGood; SHA256 973830f43a663d73f7bce2b4d4e03f26e2ee5d4860370c39acd49a4b6cd291f7. -/
section

/-! Actual full-table concentration, using the exact uniform restriction law. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementTableGood_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem E_uniform_ofReal {A : Type} [Fintype A] [Nonempty A] [SampleableType A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    E ($ᵗ A) (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal (uniformMean f) := by
  rw [ofReal_uniformMean f hf, E, expectedValue_def, tsum_fintype]
  simp only [probOutput_uniformSample]

theorem E_uniform_restrict {A B W : Type} [Fintype A] [Fintype B] [Fintype W]
    [Nonempty W] [SampleableType W] [SampleableType (A → W)] [SampleableType (B → W)]
    (e : A → B) (he : Function.Injective e) (f : (A → W) → ℝ≥0∞) :
    E ($ᵗ (B → W)) (fun g => f (g ∘ e)) = E ($ᵗ (A → W)) f := by
  have hd := evalSPMF_uniformSample_map_comp_injective (R := W) he
  have h := expectedValue_congr (mx := (do let g ← $ᵗ (B → W); pure (g ∘ e)))
    (my := ($ᵗ (A → W))) (fun g => by
      simpa only [probOutput_def] using congrArg (fun p : SPMF (A → W) => p g) hd) f
  simpa only [E, expectedValue_bind, expectedValue_pure] using h

theorem E_table_deficit {A B W : Type} [Fintype A] [Nonempty A]
    [Fintype B] [Fintype W] [Nonempty W] [SampleableType W]
    [SampleableType (A → W)] [SampleableType (B → W)]
    (e : A → B) (he : Function.Injective e) (P : W → Prop)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    E ($ᵗ (B → W)) (fun g => if empirical P (g ∘ e) ≤ fraction P - δ then 1 else 0) ≤
      ENNReal.ofReal (Real.exp (-((Fintype.card A:ℝ)*δ^2/4))) := by
  rw [E_uniform_restrict e he (fun g => if empirical P g ≤ fraction P-δ then 1 else 0)]
  have hx := E_uniform_ofReal (fun g : A → W =>
    if empirical P g ≤ fraction P-δ then (1:ℝ) else 0) (fun g => by split_ifs <;> norm_num)
  simp only [apply_ite, ENNReal.ofReal_one, ENNReal.ofReal_zero] at hx
  rw [hx]
  exact ENNReal.ofReal_le_ofReal (uniform_table_deficit P δ hδ0 hδ1)

theorem E_finite_union {T I : Type} [Fintype I] (p : ProbComp T)
    (bad : I → T → Prop) (ε : ℝ≥0∞)
    (hb : ∀ i, E p (fun t => if bad i t then 1 else 0) ≤ ε) :
    E p (fun t => if ∃ i, bad i t then 1 else 0) ≤ (Fintype.card I:ℝ≥0∞)*ε := by
  calc
    _ ≤ E p (fun t => ∑ i, if bad i t then 1 else 0) := E_mono p (fun t => by
      split_ifs with h
      · obtain ⟨i, hi⟩ := h
        have hle := Finset.single_le_sum (s := Finset.univ)
          (f := fun j => if bad j t then (1:ℝ≥0∞) else 0)
          (fun _ _ => bot_le) (Finset.mem_univ i)
        simpa only [if_pos hi] using hle
      · exact bot_le)
    _ = ∑ i, E p (fun t => if bad i t then 1 else 0) := expectedValue_finsetSum p _ _
    _ ≤ ∑ _i : I, ε := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp [nsmul_eq_mul]

def fullRowBad (P : Fin 72 → BitVec hashBits → Prop)
    (g : BitVec (msgBits+86) → BitVec hashBits) : Prop :=
  ∃ s : Message × Fin 72,
    empirical (P s.2) (fun η : BitVec 86 => g (s.1 ++ η)) ≤
      fraction (P s.2) - 1/(100*(2:ℝ)^20)

theorem append_right_injective (m : Message) :
    Function.Injective (fun η : BitVec 86 => m ++ η) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun x : BitVec (msgBits+86) => x.getLsbD i) h
  simpa only [BitVec.getLsbD_append, if_pos hi] using hh

theorem concrete_row_exponent :
    Real.exp (-((Fintype.card (BitVec 86):ℝ)*(1/(100*(2:ℝ)^20))^2/4)) ≤
      (2:ℝ)⁻¹^1024 := by
  have hnum : (1024:ℝ) ≤ (Fintype.card (BitVec 86):ℝ)*(1/(100*(2:ℝ)^20))^2/4 := by
    norm_num
  have hexp : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  calc
    _ ≤ Real.exp (-(1024:ℝ)) := Real.exp_le_exp.mpr (neg_le_neg hnum)
    _ = (Real.exp 1)⁻¹^1024 := by rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (inv_anti₀ (by norm_num) hexp) 1024

theorem full_table_bad_probability (P : Fin 72 → BitVec hashBits → Prop) :
    E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
      (fun g => if ∃ s : Message × Fin 72,
        empirical (P s.2) (fun η : BitVec 86 => g (s.1 ++ η)) ≤
          fraction (P s.2)-1/(100*(2:ℝ)^20) then 1 else 0) ≤ (2:ℝ≥0∞)⁻¹^761 := by
  let bad : (Message × Fin 72) → (BitVec (msgBits+86) → BitVec hashBits) → Prop :=
    fun s g => empirical (P s.2) (fun η : BitVec 86 => g (s.1 ++ η)) ≤
      fraction (P s.2)-1/(100*(2:ℝ)^20)
  have hb (s : Message × Fin 72) :
      E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g => if bad s g then 1 else 0) ≤
        (2:ℝ≥0∞)⁻¹^1024 := by
    have hx := E_table_deficit (fun η : BitVec 86 => s.1 ++ η) (append_right_injective s.1)
      (P s.2) (1/(100*(2:ℝ)^20)) (by positivity) (by norm_num)
    have he : ENNReal.ofReal ((2:ℝ)⁻¹^1024) = (2:ℝ≥0∞)⁻¹^1024 := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    exact hx.trans (he ▸ ENNReal.ofReal_le_ofReal concrete_row_exponent)
  have h := E_finite_union ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) bad
    ((2:ℝ≥0∞)⁻¹^1024) hb
  have hc : (Fintype.card (Message × Fin 72):ℝ≥0∞) ≤ (2:ℝ≥0∞)^263 := by
    have hn : Fintype.card (Message × Fin 72) ≤ 2^263 := by
      have hcard : Fintype.card (Message × Fin 72) = 2^256*72 := by
        norm_num [Message, msgBits, Fintype.card_prod]
      rw [hcard]
      calc
        2^256*72 ≤ 2^256*2^7 := Nat.mul_le_mul_left _ (by norm_num)
        _ = 2^263 := by rw [← pow_add]
    exact_mod_cast hn
  have hnum : (Fintype.card (Message × Fin 72):ℝ≥0∞)*(2:ℝ≥0∞)⁻¹^1024 ≤ (2:ℝ≥0∞)⁻¹^761 := by
    calc
      _ ≤ (2:ℝ≥0∞)^263 * (2:ℝ≥0∞)⁻¹^1024 := mul_le_mul' hc le_rfl
      _ = (2:ℝ≥0∞)⁻¹^761 := by
        rw [show 1024 = 263+761 by omega, pow_add, ← mul_assoc, ← mul_pow]
        have hh : (2:ℝ≥0∞)*(2:ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [hh, one_pow, one_mul]
  exact h.trans hnum

#print axioms E_uniform_restrict
#print axioms E_table_deficit
#print axioms full_table_bad_probability

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementJointPosterior; SHA256 ebdb01710fb67248d255d99f88388f73b59e053d271400d5f22a8d9bff1e01c8. -/
section

/-! Denominator-free first-exposure bounds. Zero-probability public prefixes
require no exceptional conditioning argument. Evidence remains joint throughout. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementJointPosterior_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem finite_likelihood_joint {Ω : Type*} [Fintype Ω]
    (weight likelihood : Ω → ℝ) (target survival : Ω → Prop) (c : ℝ)
    (hw : ∀ y, 0 ≤ weight y) (hl : ∀ y, 0 ≤ likelihood y)
    (ht : ∀ y, target y → likelihood y = c)
    (hs : ∀ y, survival y → c ≤ likelihood y)
    (hmass : 0 < weightedMass weight survival) :
    (∑ y, if target y then weight y * likelihood y else 0) ≤
      (weightedMass weight target / weightedMass weight survival) *
        (∑ y, weight y * likelihood y) := by
  have hnum : (∑ y, if target y then weight y * likelihood y else 0) =
      weightedMass weight target * c := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : target y <;> simp [hy, ht y]
  have hlow : weightedMass weight survival * c ≤ ∑ y, weight y * likelihood y := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : survival y
    · simp only [if_pos hy]
      exact mul_le_mul_of_nonneg_left (hs y hy) (hw y)
    · simp only [if_neg hy, zero_mul]
      exact mul_nonneg (hw y) (hl y)
  rw [hnum]
  have hcp : c ≤ (∑ y, weight y * likelihood y) / weightedMass weight survival := by
    apply (le_div_iff₀ hmass).2
    simpa only [mul_comm] using hlow
  calc
    _ ≤ weightedMass weight target * ((∑ y, weight y * likelihood y) / weightedMass weight survival) :=
      mul_le_mul_of_nonneg_left hcp (weightedMass_nonneg weight target hw)
    _ = _ := by ring

theorem weightedMass_uniform {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    weightedMass (fun _ : Ω => 1/(Fintype.card Ω:ℝ)) P = fraction P := by
  unfold weightedMass fraction uniformMean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

theorem coordinate_uniform_joint {Ω : Type*} [Fintype Ω]
    (L : ℕ) (A B δ N : ℝ) (target weak strict : Ω → Prop)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (ht : ∀ y, target y → weak y ∧ ¬ strict y) (hmass : 0 < fraction weak) :
    uniformMean (fun y => if target y then coordinateLikelihood L A B δ N weak strict y else 0) ≤
      (fraction target / fraction weak) * uniformMean (coordinateLikelihood L A B δ N weak strict) := by
  have h := finite_likelihood_joint (fun _ : Ω => 1/(Fintype.card Ω:ℝ))
    (coordinateLikelihood L A B δ N weak strict) target weak (kernel L (A+δ) B/N)
    (fun _ => by positivity) (coordinateLikelihood_nonneg L A B δ N weak strict hA hB hδ hN)
    (fun y hy => coordinateLikelihood_same L A B δ N weak strict y (ht y hy).1 (ht y hy).2)
    (coordinateLikelihood_survival L A B δ N weak strict hA hB hδ hN)
    (by simpa only [weightedMass_uniform] using hmass)
  simp only [weightedMass_uniform] at h
  have hn : (∑ y, if target y then (1/(Fintype.card Ω:ℝ))*coordinateLikelihood L A B δ N weak strict y else 0) =
      uniformMean (fun y => if target y then coordinateLikelihood L A B δ N weak strict y else 0) := by
    simp only [uniformMean, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  have hd : (∑ y, (1/(Fintype.card Ω:ℝ))*coordinateLikelihood L A B δ N weak strict y) =
      uniformMean (coordinateLikelihood L A B δ N weak strict) := by
    simp [uniformMean, div_eq_mul_inv, mul_comm, ← Finset.mul_sum]
  rwa [hn, hd] at h

def hybridEvidence {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) : ℝ :=
  (E (hybridPrefix u oa c []) (fun p => if event p then 1 else 0)).toReal

theorem hybridEvidence_nonneg {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) : 0 ≤ hybridEvidence u oa c event := ENNReal.toReal_nonneg

theorem ofReal_hybridEvidence {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) :
    ENNReal.ofReal (hybridEvidence u oa c event) =
      E (hybridPrefix u oa c []) (fun p => if event p then 1 else 0) := by
  apply ENNReal.ofReal_toReal
  exact ne_of_lt (lt_of_le_of_lt (E_le_one _ (fun _ => by split_ifs <;> simp)) (by simp))

theorem E_taggedHybridPrefix {α β : Type} (p : ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) :
    E (taggedBind p (fun b' => hybridPrefix u (post b') (overwrite c u y) []))
      (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
        E p (fun b' => if b' = b then 1 else 0) * ENNReal.ofReal (hybridEvidence u (post b) c event) := by
  rw [E_taggedBind_event, hybridPrefix_event_overwrite, ofReal_hybridEvidence]

def resampledSignedPrefix {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (u : Query) (c : Cache) :
    ProbComp (BitVec hashBits × β × (Option α × PublicTrace)) := do
  let y ← $ᵗ BitVec hashBits
  let r ← taggedBind (p y) (fun b => hybridPrefix u (post b) (overwrite c u y) [])
  pure (y,r)

/-- Exact joint factorization under an actual uniform coordinate resampling.
The public program is fully adaptive and uses the original mixed lazy oracle. -/
theorem resampledSignedPrefix_joint {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache)
    (event : Option α × PublicTrace → Prop) (target : BitVec hashBits → Prop)
    (likelihood : BitVec hashBits → ℝ) (hl : ∀ y, 0 ≤ likelihood y)
    (hp : ∀ y, E (p y) (fun b' => if b' = b then 1 else 0) = ENNReal.ofReal (likelihood y)) :
    E (resampledSignedPrefix p post u c)
      (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0) =
      ENNReal.ofReal (uniformMean (fun y => if target y then likelihood y else 0) *
        hybridEvidence u (post b) c event) := by
  rw [resampledSignedPrefix, E_bind]
  have hpoint (y : BitVec hashBits) :
      E (taggedBind (p y) (fun b' => hybridPrefix u (post b') (overwrite c u y) []))
        (fun r => E (pure (y,r)) (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0)) =
      ENNReal.ofReal ((if target y then likelihood y else 0) * hybridEvidence u (post b) c event) := by
    simp only [E_pure]
    by_cases hy : target y
    · simp only [hy, true_and, if_true]
      rw [E_taggedHybridPrefix, hp y, ENNReal.ofReal_mul (hl y)]
    · simp [hy, E, expectedValue_def]
  simp only [E_bind, hpoint]
  rw [E_uniform_ofReal _ (fun y => mul_nonneg (by split_ifs <;> simp [hl]) (hybridEvidence_nonneg _ _ _ _)),
    uniformMean_mul_const]

theorem resampledSignedPrefix_bound {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache)
    (event : Option α × PublicTrace → Prop) (target : BitVec hashBits → Prop)
    (likelihood : BitVec hashBits → ℝ) (rate : ℝ) (hl : ∀ y, 0 ≤ likelihood y)
    (hr : 0 ≤ rate)
    (hp : ∀ y, E (p y) (fun b' => if b' = b then 1 else 0) = ENNReal.ofReal (likelihood y))
    (hb : uniformMean (fun y => if target y then likelihood y else 0) ≤ rate*uniformMean likelihood) :
    E (resampledSignedPrefix p post u c)
      (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0) ≤
      ENNReal.ofReal rate * E (resampledSignedPrefix p post u c)
        (fun r => if r.2.1 = b ∧ event r.2.2 then 1 else 0) := by
  have hden := resampledSignedPrefix_joint p post b u c event (fun _ => True) likelihood hl hp
  simp only [true_and, if_true] at hden
  rw [resampledSignedPrefix_joint p post b u c event target likelihood hl hp, hden,
    ← ENNReal.ofReal_mul hr]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (rate*uniformMean likelihood)*hybridEvidence u (post b) c event :=
      mul_le_mul_of_nonneg_right hb (hybridEvidence_nonneg _ _ _ _)
    _ = _ := by ring

#print axioms finite_likelihood_joint
#print axioms coordinate_uniform_joint
#print axioms resampledSignedPrefix_bound

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementActualPrefix; SHA256 4051228cea698f721fdf6daebf9bcd5d2d30f5262d42a96585a93f4c5825aaf6. -/
section

/-! Actual all-trial signing followed by an adaptive stopped public prefix.
The prefix keeps the original mixed lazy oracle, and the final signer cache is
passed to it. On a complete row that cache is unchanged, including private hits. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementActualPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

theorem rowQuery_injective (n : ℕ) (m : Message) :
    Function.Injective (fun η : Nonce n => (⟨msgBits+n,m++η⟩ : Query)) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hh := congrArg (fun q : Query => q.2.getLsbD j) h
  simpa only [BitVec.getLsbD_append, if_pos hj] using hh

theorem overwrite_complete_row (n : ℕ) (m : Message) (table : Nonce n → BitVec hashBits)
    (c : Cache) (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (u : Nonce n) (y : BitVec hashBits) :
    ∀ η, overwrite c ⟨msgBits+n,m++u⟩ y ⟨msgBits+n,m++η⟩ =
      some (Function.update table u y η) := by
  intro η
  by_cases hη : η = u
  · subst η
    simp [overwrite]
  · have hq : (⟨msgBits+n,m++η⟩ : Query) ≠ ⟨msgBits+n,m++u⟩ := by
      intro h
      exact hη (rowQuery_injective n m h)
    simp [overwrite, Function.update, hq, Ne.symm hq, hη, Ne.symm hη, hc]

def actualSignedPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (u : Query) (c : Cache) :
    ProbComp (Option (Winner n M) × (Option α × PublicTrace)) := do
  let r ← run (loop n decode tier m k) c
  let t ← hybridPrefix u (post r.1) r.2 []
  pure (r.1,t)

theorem actualSignedPrefix_fixed_row {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u : Query) :
    actualSignedPrefix n decode tier m k post u c =
      taggedBind (Prod.fst <$> run (loop n decode tier m k) c)
        (fun b => hybridPrefix u (post b) c []) := by
  rw [actualSignedPrefix, taggedBind, run_loop_fixed_row n decode tier m table c hc k]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

def resampledActualPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (u : Nonce n) (c : Cache) :
    ProbComp (BitVec hashBits × Option (Winner n M) × (Option α × PublicTrace)) := do
  let y ← $ᵗ BitVec hashBits
  let r ← actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
    (overwrite c ⟨msgBits+n,m++u⟩ y)
  pure (y,r)

theorem resampledActualPrefix_eq {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u : Nonce n) :
    resampledActualPrefix n decode tier m k post u c =
      resampledSignedPrefix
        (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        post ⟨msgBits+n,m++u⟩ c := by
  unfold resampledActualPrefix resampledSignedPrefix
  apply bind_congr
  intro y
  rw [actualSignedPrefix_fixed_row n decode tier m k (Function.update table u y)
    (overwrite c ⟨msgBits+n,m++u⟩ y) (overwrite_complete_row n m table c hc u y)]

theorem loop_cached_target_zero {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (v : Nonce n) (i : Fin M) (c : Cache) (w : BitVec hashBits)
    (hc : c ⟨msgBits+n,m++v⟩ = some w) (hw : decode w ≠ some i) :
    E (Prod.fst <$> run (loop n decode tier m k) c) (fun b => if b = some (v,i) then 1 else 0) = 0 := by
  rw [E_map]
  apply le_antisymm _ bot_le
  apply (expectedValue_mono_of_support (mx := run (loop n decode tier m k) c)
    (h := fun _ => (0:ℝ≥0∞)) ?_).trans (E_const_le _ 0)
  intro p hp
  by_cases hret : p.1 = some (v,i)
  · obtain ⟨hsub, hwin⟩ := loop_support n decode tier m k c p hp
    obtain ⟨w', hw', hd⟩ := hwin v i hret
    have he : w' = w := Option.some.inj (hw'.symm.trans (hsub _ _ hc))
    exact False.elim (hw (he ▸ hd))
  · simp [Function.comp_def, hret]

/-- A fresh uniform resampling of one publicly unexposed row coordinate, then
the actual all-L signer and actual adaptive mixed-oracle prefix. The joint class
and prefix probability is at most p_i/(1-F_i) times the prefix probability.
The returned nonce is fixed to v≠u; there is no Good-event conditioning and no
assumption that u is absent from the implementation cache. -/
theorem actual_prefix_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u v : Nonce n) (i : Fin M)
    (hvu : v ≠ u) (event : Option α × PublicTrace → Prop)
    (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    E (resampledActualPrefix n decode tier m k post u c)
      (fun r => if decode r.1 = some i ∧ r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E (resampledActualPrefix n decode tier m k post u c)
          (fun r => if r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) := by
  rw [resampledActualPrefix_eq n decode tier m k table c hc post u]
  have hrate : 0 ≤ fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) := by
    apply div_nonneg _ hmass.le
    unfold fraction uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)
  by_cases hv : decode (table v) = some i
  · let A := fractionExcept (weakRank tier i ∘ decode ∘ table) u
    let B := fractionExcept (strictRank tier i ∘ decode ∘ table) u
    let lik := coordinateLikelihood k A B (1/(Fintype.card (Nonce n):ℝ)) (Fintype.card (Nonce n))
      (weakRank tier i ∘ decode) (strictRank tier i ∘ decode)
    have hl : ∀ y, 0 ≤ lik y := coordinateLikelihood_nonneg k A B _ _ _ _
      (fractionExcept_nonneg _ _) (fractionExcept_nonneg _ _) (by positivity) (by positivity)
    have hp : ∀ y, E (Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        (fun b => if b = some (v,i) then 1 else 0) = ENNReal.ofReal (lik y) := by
      intro y
      rw [E_map]
      have hv' : decode (Function.update table u y v) = some i := by
        rw [Function.update_of_ne hvu]
        exact hv
      have hh := E_loop_fixed_row_target n M k decode tier m (Function.update table u y)
        (overwrite c ⟨msgBits+n,m++u⟩ y) (overwrite_complete_row n m table c hc u y) v i hv'
      rw [← tableWinnerLikelihood_eq k (Function.update table u y) decode tier v i hv',
        tableWinnerLikelihood_update k table decode tier u v i hvu hv y] at hh
      convert hh using 1
      congr 1
      funext r
      split_ifs <;> rfl
    have hb : uniformMean (fun y => if decode y = some i then lik y else 0) ≤
        (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode))*uniformMean lik := by
      exact coordinate_uniform_joint k A B _ _ _ _ _
        (fractionExcept_nonneg _ _) (fractionExcept_nonneg _ _) (by positivity) (by positivity)
        (fun y hy => by simp [hy, weakRank, strictRank]) hmass
    have hh := resampledSignedPrefix_bound
      (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
      post (some (v,i)) ⟨msgBits+n,m++u⟩ c event (fun y => decode y = some i) lik _ hl hrate hp hb
    convert hh using 1 <;> congr 1 <;> (try funext r) <;> split_ifs <;> rfl
  · have hp : ∀ y, E (Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        (fun b => if b = some (v,i) then 1 else 0) = ENNReal.ofReal (0:ℝ) := by
      intro y
      rw [ENNReal.ofReal_zero]
      apply loop_cached_target_zero n decode tier m k v i _ (table v) _ hv
      have hq : (⟨msgBits+n,m++v⟩ : Query) ≠ ⟨msgBits+n,m++u⟩ :=
        fun h => hvu (rowQuery_injective n m h)
      simpa [overwrite, Function.update, hq, Ne.symm hq] using hc v
    have hh := resampledSignedPrefix_bound
      (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
      post (some (v,i)) ⟨msgBits+n,m++u⟩ c event (fun y => decode y = some i) (fun _ => 0) _
      (fun _ => le_rfl) hrate hp (by simp only [ite_self, uniformMean_const, mul_zero, le_refl])
    convert hh using 1 <;> congr 1 <;> (try funext r) <;> split_ifs <;> rfl

#print axioms actualSignedPrefix_fixed_row
#print axioms actual_prefix_class_bound

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementSignedUnion; SHA256 1188d1ed79238bf1101d00f9817260a6ddc4db551cef09485069351cd643c34b. -/
section

/-! Two-phase finite union, retaining the actual signer's terminal cache and
the signed value as a joint event. All costs refer to the same continuation. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementSignedUnion_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def signedHit {β γ : Type} (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ)
    (b : β) (q : Query) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then publicHit q (post r.1) r.2 else 0)

def signedCharge {β γ : Type} (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ)
    (b : β) (charge : Spec.Domain → ℝ≥0∞) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then expectedCharge charge (post r.1) r.2 else 0)

def signedChosen {D β α : Type} (p : ProbComp (β × Cache)) (forge : β → OracleComp Spec α)
    (chosen : α → D) (b : β) (allowed good : D → Prop) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then E (run (forge r.1) r.2)
    (fun s => if allowed (chosen s.1) ∧ good (chosen s.1) then 1 else 0) else 0)

theorem E_gate {α : Type} (p : ProbComp α) (P : Prop) (f : α → ℝ≥0∞) :
    E p (fun a => if P then f a else 0) = if P then E p f else 0 := by
  by_cases hP : P <;> simp [hP, E, expectedValue_def]

theorem signedChosen_union {D β α γ : Type} [Fintype D]
    (p : ProbComp (β × Cache)) (forge : β → OracleComp Spec α)
    (verify : β → α → OracleComp Spec γ) (e : D → Query) (chosen : α → D)
    (b : β) (allowed good : D → Prop)
    (hquery : ∀ s a c, publicHit (e (chosen a)) (verify s a) c = 1) :
    signedChosen p forge chosen b allowed good ≤
      ∑ d, if allowed d ∧ good d then signedHit p (fun s => forge s >>= verify s) b (e d) else 0 := by
  have hpoint (r : β × Cache) :
      (if r.1 = b then E (run (forge r.1) r.2)
        (fun s => if allowed (chosen s.1) ∧ good (chosen s.1) then 1 else 0) else 0) ≤
      ∑ d, if allowed d ∧ good d then (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0 := by
    by_cases hr : r.1 = b
    · simp only [if_pos hr]
      exact selected_input_union e chosen allowed good (forge r.1) (verify r.1) r.2 (hquery r.1)
    · simp [hr]
  calc
    _ ≤ E p (fun r => ∑ d, if allowed d ∧ good d then
        (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0) := E_mono p hpoint
    _ = ∑ d, E p (fun r => if allowed d ∧ good d then
        (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0) :=
      expectedValue_finsetSum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : allowed d ∧ good d <;> simp [hd, signedHit, E, expectedValue_def]

theorem signedHit_sum_le_indexPaid {D β γ : Type} [Fintype D] (e : D → Query)
    (he : Function.Injective e) (isIndex : Spec.Domain → Prop)
    (hi : ∀ d, isIndex (.inr (e d))) (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d)))
    (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ) (b : β) :
    (∑ d, signedHit p post b (e d)) ≤ signedCharge p post b (indexPaid isIndex) := by
  unfold signedHit signedCharge
  rw [← expectedValue_finsetSum p Finset.univ (fun d r => if r.1 = b then publicHit (e d) (post r.1) r.2 else 0)]
  apply E_mono p
  intro r
  by_cases hr : r.1 = b
  · simp only [if_pos hr]
    exact publicHit_sum_le_indexPaid e he isIndex hi hpaid (post r.1) r.2
  · simp [hr]

theorem signedHit_actual_eq {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (b : Option (Winner n M)) (u : Query) (c : Cache) :
    signedHit (run (loop n decode tier m k) c) post b u =
      E (actualSignedPrefix n decode tier m k post u c)
        (fun r => if r.1 = b ∧ r.2.1 = none then 1 else 0) := by
  unfold signedHit actualSignedPrefix
  simp only [E_bind, E_pure]
  congr 1
  funext r
  by_cases hr : r.1 = b
  · simp only [hr, true_and, if_pos]
    exact publicHit_eq_prefix u (post b) r.2 []
  · simp [hr, E, expectedValue_def]

theorem signedHit_actual_gate {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (b : Option (Winner n M))
    (u : Query) (c : Cache) (P : Prop) :
    (if P then signedHit (run (loop n decode tier m k) c) post b u else 0) =
      E (actualSignedPrefix n decode tier m k post u c)
        (fun r => if P ∧ r.1 = b ∧ r.2.1 = none then 1 else 0) := by
  by_cases hP : P
  · simp only [hP, true_and, if_true]
    exact signedHit_actual_eq n decode tier m k post b u c
  · simp [hP, E, expectedValue_def]

/-- Joint posterior estimates at each eligible coordinate combine with actual
public input selection and the shared paid-index cost. The estimates are later
instantiated with the checked same-row and cross-row sampler laws. -/
theorem integrated_signedChosen_bound {Z D β α γ : Type} [Fintype D]
    (latent : ProbComp Z) (p : Z → ProbComp (β × Cache))
    (forge : β → OracleComp Spec α) (verify : β → α → OracleComp Spec γ)
    (e : D → Query) (chosen : α → D) (b : β) (allowed : D → Prop) (good : Z → D → Prop)
    (isIndex : Spec.Domain → Prop) (rate : ℝ≥0∞)
    (he : Function.Injective e) (hi : ∀ d, isIndex (.inr (e d)))
    (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d)))
    (hquery : ∀ s a c, publicHit (e (chosen a)) (verify s a) c = 1)
    (hposterior : ∀ d, allowed d →
      E latent (fun z => if good z d then signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) ≤
        rate * E latent (fun z => signedHit (p z) (fun s => forge s >>= verify s) b (e d))) :
    E latent (fun z => signedChosen (p z) forge chosen b allowed (good z)) ≤
      rate * E latent (fun z => signedCharge (p z) (fun s => forge s >>= verify s) b (indexPaid isIndex)) := by
  calc
    _ ≤ E latent (fun z => ∑ d, if allowed d ∧ good z d then
        signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) :=
      E_mono latent (fun z => signedChosen_union (p z) forge verify e chosen b allowed (good z) hquery)
    _ = ∑ d, E latent (fun z => if allowed d ∧ good z d then
        signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) := expectedValue_finsetSum _ _ _
    _ ≤ ∑ d, rate * E latent (fun z => signedHit (p z) (fun s => forge s >>= verify s) b (e d)) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : allowed d
      · simpa only [hd, true_and] using hposterior d hd
      · simp only [hd, false_and, if_false]
        exact (E_const_le _ 0).trans bot_le
    _ = rate * E latent (fun z => ∑ d, signedHit (p z) (fun s => forge s >>= verify s) b (e d)) := by
      rw [← Finset.mul_sum]
      apply congrArg (rate * ·)
      exact (expectedValue_finsetSum latent Finset.univ
        (fun d z => signedHit (p z) (fun s => forge s >>= verify s) b (e d))).symm
    _ ≤ _ := mul_le_mul' le_rfl (E_mono latent
      (fun z => signedHit_sum_le_indexPaid e he isIndex hi hpaid (p z) (fun s => forge s >>= verify s) b))

#print axioms signedChosen_union
#print axioms signedHit_actual_eq
#print axioms integrated_signedChosen_bound

end
end WeightedReplacement
end

