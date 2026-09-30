import Submissions.UpperCompressions.LongChain91AuthGame

/-!
# Cross-cut authentication for the cost-87 shared-DAG construction

Every scheduled cut has reconstruction cost 86, so two distinct scheduled cuts
differ at a hash node `u` that the forged cut reconstructs and the signed cut
does not (`exists_hidden_of_ne`).  The descent of
`LongChain91AuthClosure` gives either a spurious binding or the honest input
of `u`, which is a hidden key-generation point of the signed cut.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## The cross-cut event -/

theorem events_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hne : A ≠ A') {xi : Rec} {d : Cache}
    {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y)
    (hacc : lowPk (yv y Name.rh) = pkOf xi) :
    Spr d xi ∨ Cache.Hits d (fHid (some A) xi) := by
  obtain ⟨c, hc, rfl⟩ := hA
  obtain ⟨c', hc', rfl⟩ := hA'
  obtain ⟨u, huE', huE, hu, -⟩ := exists_hidden_of_ne hc hc' hne
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 ((hashParent_isSome_iff u).2 hu)
  rcases descent_query ⟨c', hc', rfl⟩ hy hacc hp huE' with hs | hq
  · exact Or.inl hs
  · right
    refine ⟨pointOf xi u p, ?_, hq⟩
    rw [fHid_isSome_some_iff]
    exact ⟨u, p, hp, huE, rfl⟩

theorem crossCutAuthentication : CrossCutAuthentication := by
  intro xi signedClass i d given y hic hy hacc
  have hA := isCut_of_mem_family (setsName_mem signedClass)
  have hA' := isCut_of_mem_family (setsName_mem i)
  exact events_ne hA hA'
    (fun he => hic (setsName_injective he.symm)) hy hacc

theorem accepted_class_cases_actual
    (xi : Rec) (signedClass : Fin M) (m : Message)
    (sigma : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf xi) m sigma) c)) :
    ∃ answer, d (encQuery (m, sigma.1)) = some answer ∧
      ∃ i : Fin M, LongChain91Schedule.decode answer = some i ∧
        ((i = signedClass ∧
            sigma.2 = graph.encode (fins (setsName signedClass))
              (graph.evalRec xi)) ∨
          Spr d xi ∨
          Cache.Hits d (fHid (some (setsName signedClass)) xi)) :=
  accepted_class_cases crossCutAuthentication xi signedClass m sigma c d h

end OptimalOTS.WeightedConstruction.LongChain91

/-!
# Actual authentication continuation for the cost-91 long-chain scheme

This module retains the real choose/sign/forge execution and charges graph
 authentication only through the actual expected non-index query clock.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name WeightedReplacement
attribute [local irreducible] hashBits blockBits msgBits Finset.univ Finset.filter

/-! ## Small expectation and fiber adapters -/

theorem E_const_mul {alpha : Type} (p : ProbComp alpha) (c : ℝ≥0∞)
    (g : alpha → ℝ≥0∞) : c * E p g = E p (fun x => c * g x) := by
  rw [E, E, expectedValue_def, expectedValue_def, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun x => by ring

theorem E_finsetSum {alpha iota : Type} (p : ProbComp alpha)
    (s : Finset iota) (g : iota → alpha → ℝ≥0∞) :
    E p (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, E p (g i) :=
  expectedValue_finsetSum p s g

private theorem pkOf_eq_of_mem_fiberA {pk : BitVec 128} {xi : Rec}
    (hxi : xi ∈ fiberA pk) : pkOf xi = pk := by
  change xi ∈ Finset.univ.filter (fun z : Rec => pkOf z = pk) at hxi
  exact (Finset.mem_filter.mp hxi).2

private theorem dataOf_eq_of_mem_fiberB {Ac : Finset Name} {dt : Data} {xi : Rec}
    (hxi : xi ∈ fiberB Ac dt) : dataOf Ac xi = dt := by
  change xi ∈ Finset.univ.filter (fun z : Rec => dataOf Ac z = dt) at hxi
  exact (Finset.mem_filter.mp hxi).2

theorem pkOf_of_subset_fiberA {pk : BitVec 128} {T : Finset Rec}
    (hT : T ⊆ fiberA pk) : ∀ xi ∈ T, pkOf xi = pk := by
  intro xi hxi
  exact pkOf_eq_of_mem_fiberA (hT hxi)

theorem record_regroup (T : Finset Rec) (Ac : Finset Name)
    (f : Rec → ℝ≥0∞) :
    (∑ xi ∈ T, f xi) =
      ∑ dt ∈ T.image (dataOf Ac), ∑ xi ∈ T with dataOf Ac xi = dt, f xi :=
  (Finset.sum_fiberwise_of_maps_to
    (fun xi hxi => Finset.mem_image_of_mem _ hxi) f).symm

/-! ## The actual forge/verify continuation -/

variable (A : scheme.toAlgorithm.Adversary)

def stB (pk : PublicKey) (m1 : Message) (st : A.State)
    (sigma : Option WeightedScheme.Signature) : OracleComp Spec Bool := do
  let (m2, sigma2) ← A.forge st sigma
  let ok ← scheme.verify pk m2 sigma2
  return ok && decide (sigma.map (fun s => (m1, s)) ≠ some (m2, sigma2))

def successValue (p : Bool × Cache) : ℝ≥0∞ :=
  if p.1 = true then 1 else 0

theorem successValue_le_one (p : Bool × Cache) : successValue p ≤ 1 := by
  unfold successValue
  split_ifs <;> simp

theorem stB_success (pk : PublicKey) (m1 : Message) (st : A.State)
    (sigma : Option WeightedScheme.Signature) (c : Cache)
    (p : Bool × Cache)
    (hp : p ∈ support (run (stB A pk m1 st sigma) c))
    (hok : p.1 = true) :
    ∃ m2 sigma2 c1, sigma.map (fun s => (m1, s)) ≠ some (m2, sigma2) ∧
      (true, p.2) ∈ support (run (scheme.verify pk m2 sigma2) c1) := by
  unfold stB at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m2, sigma2⟩, c1⟩, _, hp⟩ := hp
  dsimp only at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok, _c2⟩, h2, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  subst ok
  exact ⟨m2, sigma2, c1, hne, h2⟩

theorem stB_events_none (xi : Rec) (m1 : Message) (st : A.State)
    (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stB A (pkOf xi) m1 st none) c))
    (hok : p.1 = true) : Spr p.2 xi ∨ Cache.Hits p.2 (kc xi) := by
  obtain ⟨m2, sigma2, c1, _, hv⟩ :=
    stB_success A (pkOf xi) m1 st none c p hp hok
  exact accepted_none_event xi m2 sigma2 c1 p.2 hv

theorem ind_of {p : Prop} (h : p) : ind p = 1 := by
  rw [ind, if_pos h]

theorem ind_not {p : Prop} (h : ¬p) : ind p = 0 := by
  rw [ind, if_neg h]

theorem graph_iub (oa : OracleComp Spec Bool) (xi : Rec)
    (Aq : Option (Finset Name)) (d d' : Cache)
    (hd' : IndexExtension d d') (hxi : ¬ Cache.Hits d (kc xi)) :
    E (run oa (Cache.extend d' (kc xi))) successValue ≤
      E (run oa (Cache.extend d' (fExp Aq xi)))
        (fun p => if Cache.Hits p.2 (fHid Aq xi) then 1 else successValue p) := by
  have hkc : Cache.extend d' (kc xi) =
      Cache.extend (Cache.extend d' (fExp Aq xi)) (fHid Aq xi) := by
    rw [Cache.extend_assoc, extend_fExp_fHid]
  have hdisj : Cache.Disjoint (Cache.extend d' (fExp Aq xi))
      (fHid Aq xi) := by
    intro q hq
    have hkq : (kc xi q).isSome := by
      obtain ⟨h, p, hp, _, hqp⟩ := (fHid_isSome_iff _ xi q).1 hq
      exact (kc_isSome_iff xi q).2 ⟨h, p, hp, hqp⟩
    rw [Cache.extend_apply, indexExtension_kc_none hd' hxi hkq,
      Option.none_or]
    exact disjoint_fExp_fHid _ xi q hq
  rw [hkc]
  exact iub oa (fHid Aq xi) successValue successValue_le_one _ hdisj

/-! ## Retaining the forged message and signature -/

abbrev ForgeryResult := Message × WeightedScheme.Signature × Bool

def forgerySuccess (p : ForgeryResult × Cache) : ℝ≥0∞ :=
  if p.1.2.2 = true then 1 else 0

def stBWithForgery (pk : PublicKey) (m1 : Message) (st : A.State)
    (sigma : Option WeightedScheme.Signature) : OracleComp Spec ForgeryResult := do
  let (m2, sigma2) ← A.forge st sigma
  let ok ← scheme.verify pk m2 sigma2
  return (m2, sigma2,
    ok && decide (sigma.map (fun s => (m1, s)) ≠ some (m2, sigma2)))

theorem stBWithForgery_map (pk : PublicKey) (m1 : Message) (st : A.State)
    (sigma : Option WeightedScheme.Signature) :
    (fun r : ForgeryResult => r.2.2) <$> stBWithForgery A pk m1 st sigma =
      stB A pk m1 st sigma := by
  unfold stBWithForgery stB
  simp only [map_bind, map_pure]

theorem stBWithForgery_support (pk : PublicKey) (m1 : Message)
    (st : A.State) (sigma : Option WeightedScheme.Signature)
    (c : Cache) (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A pk m1 st sigma) c))
    (hok : p.1.2.2 = true) :
    ∃ c1, sigma.map (fun s => (m1, s)) ≠ some (p.1.1, p.1.2.1) ∧
      (true, p.2) ∈ support
        (run (scheme.verify pk p.1.1 p.1.2.1) c1) := by
  unfold stBWithForgery at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m2, sigma2⟩, c1⟩, _, hp⟩ := hp
  dsimp only at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok, _c2⟩, h2, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  subst ok
  exact ⟨c1, hne, h2⟩

theorem stBWithForgery_index_witness (xi : Rec) (i : Fin M)
    (eta : BitVec 86) (m1 : Message) (st : A.State)
    (c : Cache) (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A (pkOf xi) m1 st
      (some (eta, revealed (setsName i) xi))) c))
    (hok : p.1.2.2 = true) :
    ∃ answer, p.2 (encQuery (p.1.1, p.1.2.1.1)) = some answer ∧
      (Spr p.2 xi ∨ Cache.Hits p.2 (fHid (some (setsName i)) xi) ∨
        (LongChain91Empirical.cacheDecode answer = some i ∧
          (p.1.1, p.1.2.1.1) ≠ (m1, eta))) := by
  obtain ⟨c1, hne, hv⟩ :=
    stBWithForgery_support A (pkOf xi) m1 st _ c p hp hok
  obtain ⟨answer, ha, j, hj, he | hs | hh⟩ :=
    accepted_class_cases_actual xi i p.1.1 p.1.2.1 c1 p.2 hv
  · obtain ⟨rfl, hpayload⟩ := he
    refine ⟨answer, ha, Or.inr (Or.inr ⟨hj, ?_⟩)⟩
    intro hinput
    have hm : p.1.1 = m1 := congrArg (fun u : EncInput => u.1) hinput
    have hn : p.1.2.1.1 = eta :=
      congrArg (fun u : EncInput => u.2) hinput
    have hpair : (p.1.1, p.1.2.1) =
        (m1, (eta, revealed (setsName j) xi)) :=
      Prod.ext hm (Prod.ext hn hpayload)
    exact hne (congrArg some hpair.symm)
  · exact ⟨answer, ha, Or.inl hs⟩
  · exact ⟨answer, ha, Or.inr (Or.inl hh)⟩

/-! ## Authentication before and after signing -/

theorem authPotential_charge_none (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk) (c : Cache)
    (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T none (c.cacheQuery q u)) ≤
      authPotential T none c +
        authRate * sumW (fiberA pk) * queryCost (.inr q) := by
  simp only [authPotential_eq, fHid_none, mul_add, Finset.sum_add_distrib]
  have hh := (hits_avg_le T kc c q).trans
    (add_le_add_right (hits_charge_A' pk hT q) _)
  have hs := (spr_avg_le T c q hq).trans
    (add_le_add_right
      (mul_le_mul_right (sumW_mono hT) (ε * blockCost q.1)) _)
  have hc := mul_le_mul_right (authentication_charge_budget q)
    (sumW (fiberA pk))
  calc
    _ ≤ ((∑ xi ∈ T, w * ind (Cache.Hits c (kc xi))) +
          ε * sumW (fiberA pk)) +
        ((∑ xi ∈ T, w * ind (Spr c xi)) +
          (ε * blockCost q.1) * sumW (fiberA pk)) :=
      add_le_add hh hs
    _ = ((∑ xi ∈ T, w * ind (Cache.Hits c (kc xi))) +
        (∑ xi ∈ T, w * ind (Spr c xi))) +
        (ε + ε * blockCost q.1) * sumW (fiberA pk) := by
      ring
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [authRate, queryCost, mul_assoc, mul_comm, mul_left_comm]
        using hc

theorem presign_auth_query_expected (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (t : Spec.Domain) (c : Cache) :
    E ((oracleImpl t).run c) (fun p => authPotential T none p.2) ≤
      authPotential T none c +
        (authRate * sumW (fiberA pk)) * otherPaid isIndex t := by
  cases t with
  | inl n =>
      rw [oracleImpl_run_inl, E_bind]
      simp only [E_pure, otherPaid, queryCost]
      split_ifs <;> simpa using E_const_le
        (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n))
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
          · obtain ⟨u, rfl⟩ := hindex q hi
            rw [authPotential_index, otherPaid, if_pos hi, mul_zero, add_zero]
          · rw [otherPaid, if_neg hi]
            exact authPotential_charge_none pk hT c q hc

theorem presign_auth_expected {alpha : Type} (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec alpha) (c : Cache) :
    E (run oa c) (fun p => authPotential T none p.2) ≤
      authPotential T none c +
        (authRate * sumW (fiberA pk)) *
          expectedCharge (otherPaid isIndex) oa c :=
  WeightedExpectedCharge.master_expected (authPotential T none)
    (otherPaid isIndex) (authRate * sumW (fiberA pk))
    (presign_auth_query_expected pk hT isIndex hindex) oa c

theorem authPotential_empty (T : Finset Rec)
    (Aq : Option (Finset Name)) : authPotential T Aq ∅ = 0 := by
  simp [authPotential, ind, Cache.not_hits_empty, not_spr_empty]

theorem stageA_auth_expected (A : scheme.toAlgorithm.Adversary)
    (pk : BitVec 128) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u) :
    E (run (A.choose pk) ∅)
        (fun p => authPotential (fiberA pk) none p.2) ≤
      (authRate * sumW (fiberA pk)) *
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅ := by
  simpa only [authPotential_empty, zero_add] using
    presign_auth_expected pk (Finset.Subset.refl _)
      isIndex hindex (A.choose pk) ∅

theorem no_sign_auth_expected {alpha : Type} (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (d d' : Cache) (hd' : IndexExtension d d')
    (hTd : ∀ xi ∈ T, ¬ Cache.Hits d (kc xi))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec alpha) :
    (∑ xi ∈ T, w * E (run oa d')
      (fun p => ind (Cache.Hits p.2 (kc xi)) + ind (Spr p.2 xi))) ≤
      (∑ xi ∈ T, w * ind (Spr d xi)) +
        (authRate * sumW (fiberA pk)) *
          expectedCharge (otherPaid isIndex) oa d' := by
  have hinit := authPotential_after_sign hd' T none hTd ∅
    (fun xi _ => fExp_none xi)
  rw [Cache.extend_empty] at hinit
  have hsum : (∑ xi ∈ T, w * E (run oa d')
      (fun p => ind (Cache.Hits p.2 (kc xi)) + ind (Spr p.2 xi))) =
      E (run oa d') (fun p => authPotential T none p.2) := by
    simp only [authPotential, fHid_none]
    rw [E_finsetSum]
    exact Finset.sum_congr rfl fun xi _ => E_const_mul _ _ _
  rw [hsum]
  exact (presign_auth_expected pk hT isIndex hindex oa d').trans_eq
    (by rw [hinit])

theorem stB_iub_none (xi : Rec) (m1 : Message) (st : A.State)
    (d d' : Cache) (hd' : IndexExtension d d')
    (hxi : ¬ Cache.Hits d (kc xi)) :
    E (run (stB A (pkOf xi) m1 st none)
      (Cache.extend d' (kc xi))) successValue ≤
      E (run (stB A (pkOf xi) m1 st none) d')
        (fun p => ind (Cache.Hits p.2 (kc xi)) + ind (Spr p.2 xi)) := by
  have h := graph_iub (stB A (pkOf xi) m1 st none) xi none d d' hd' hxi
  simp only [fExp_none, Cache.extend_empty, fHid_none] at h
  refine h.trans ?_
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hh : Cache.Hits p.2 (kc xi)
  · rw [if_pos hh, ind_of hh]
    exact le_self_add
  · rw [if_neg hh, ind_not hh, zero_add]
    by_cases hok : p.1 = true
    · rw [successValue, if_pos hok]
      rcases stB_events_none A xi m1 st d' p hp hok with hs | hh'
      · rw [ind_of hs]
      · exact absurd hh' hh
    · rw [successValue, if_neg hok]
      exact zero_le

theorem failed_sign_success_expected (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m1 : Message) (st : A.State) (d d' : Cache)
    (hd' : IndexExtension d d')
    (hTd : ∀ xi ∈ T, ¬ Cache.Hits d (kc xi))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u) :
    (∑ xi ∈ T, w * E (run (stB A (pkOf xi) m1 st none)
      (Cache.extend d' (kc xi))) successValue) ≤
      (∑ xi ∈ T, w * ind (Spr d xi)) +
        (authRate * sumW (fiberA pk)) *
          expectedCharge (otherPaid isIndex) (stB A pk m1 st none) d' := by
  have hpks := pkOf_of_subset_fiberA hT
  calc
    _ ≤ ∑ xi ∈ T, w * E (run (stB A (pkOf xi) m1 st none) d')
        (fun p => ind (Cache.Hits p.2 (kc xi)) + ind (Spr p.2 xi)) :=
      Finset.sum_le_sum fun xi hxi =>
        mul_le_mul_right (stB_iub_none A xi m1 st d d' hd' (hTd xi hxi)) w
    _ = ∑ xi ∈ T, w * E (run (stB A pk m1 st none) d')
        (fun p => ind (Cache.Hits p.2 (kc xi)) + ind (Spr p.2 xi)) := by
      apply Finset.sum_congr rfl
      intro xi hxi
      rw [hpks xi hxi]
    _ ≤ _ := no_sign_auth_expected pk T hT d d' hd' hTd
      isIndex hindex _

/-! ## Post-sign fiber expectation -/

theorem auth_query_expected {Ac : Finset Name} (hAc : IsCut Ac)
    (dt : Data) {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (t : Spec.Domain) (c : Cache) :
    E ((oracleImpl t).run c) (fun p => authPotential T (some Ac) p.2) ≤
      authPotential T (some Ac) c +
        (authRate * sumW (fiberB Ac dt)) * otherPaid isIndex t := by
  cases t with
  | inl n =>
      rw [oracleImpl_run_inl, E_bind]
      simp only [E_pure, otherPaid, queryCost]
      split_ifs <;> simpa using E_const_le
        (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n))
        (authPotential T (some Ac) c)
  | inr q =>
      cases hc : c q with
      | some u =>
          rw [oracleImpl_run_inr_some hc, E_pure]
          exact le_self_add
      | none =>
          rw [oracleImpl_run_inr_none hc, E_bind, E_uniform]
          simp only [E_pure]
          by_cases hi : isIndex (.inr q)
          · obtain ⟨u, rfl⟩ := hindex q hi
            rw [authPotential_index, otherPaid, if_pos hi, mul_zero, add_zero]
          · rw [otherPaid, if_neg hi]
            exact authPotential_charge hAc dt hT c q hc

theorem auth_continuation_expected {alpha : Type} {Ac : Finset Name}
    (hAc : IsCut Ac) (dt : Data) {T : Finset Rec}
    (hT : T ⊆ fiberB Ac dt) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec alpha) (c : Cache) :
    E (run oa c) (fun p => authPotential T (some Ac) p.2) ≤
      authPotential T (some Ac) c +
        (authRate * sumW (fiberB Ac dt)) *
          expectedCharge (otherPaid isIndex) oa c :=
  WeightedExpectedCharge.master_expected (authPotential T (some Ac))
    (otherPaid isIndex) (authRate * sumW (fiberB Ac dt))
    (auth_query_expected hAc dt hT isIndex hindex) oa c

theorem fiber_auth_expected {alpha : Type} {Ac : Finset Name}
    (hAc : IsCut Ac) (dt : Data) {T : Finset Rec}
    (hT : T ⊆ fiberB Ac dt) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (K : Data → OracleComp Spec alpha) (d : Cache) :
    (∑ xi ∈ T, w * E
      (run (K (dataOf Ac xi)) (Cache.extend d (fExp (some Ac) xi)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) xi)) +
        ind (Spr p.2 xi))) ≤
      authPotential T (some Ac) (Cache.extend d dt.2.2) +
        (authRate * sumW (fiberB Ac dt)) *
          expectedCharge (otherPaid isIndex) (K dt)
            (Cache.extend d dt.2.2) := by
  have hdata : ∀ xi ∈ T, dataOf Ac xi = dt :=
    fun xi hxi => dataOf_eq_of_mem_fiberB (hT hxi)
  have hrun : ∀ xi ∈ T,
      run (K (dataOf Ac xi)) (Cache.extend d (fExp (some Ac) xi)) =
        run (K dt) (Cache.extend d dt.2.2) := by
    intro xi hxi
    have hd := hdata xi hxi
    have hf : fExp (some Ac) xi = dt.2.2 :=
      congrArg (fun a : Data => a.2.2) hd
    rw [hd, hf]
  have hsum : (∑ xi ∈ T, w * E
      (run (K (dataOf Ac xi)) (Cache.extend d (fExp (some Ac) xi)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) xi)) +
        ind (Spr p.2 xi))) =
      E (run (K dt) (Cache.extend d dt.2.2))
        (fun p => authPotential T (some Ac) p.2) := by
    unfold authPotential
    rw [E_finsetSum]
    apply Finset.sum_congr rfl
    intro xi hxi
    rw [hrun xi hxi, E_const_mul]
  rw [hsum]
  exact auth_continuation_expected hAc dt hT isIndex hindex
    (K dt) (Cache.extend d dt.2.2)

theorem fiber_costs_le (Ac : Finset Name) {T : Finset Rec}
    {pk : BitVec 128} (hT : T ⊆ fiberA pk) (F : Data → ℝ≥0∞) :
    (∑ dt ∈ T.image (dataOf Ac), sumW (fiberB Ac dt) * F dt) ≤
      ∑ xi ∈ fiberA pk, w * F (dataOf Ac xi) := by
  have hTpk := pkOf_of_subset_fiberA hT
  have hsub : ∀ dt ∈ T.image (dataOf Ac), fiberB Ac dt ⊆
      ((fiberA pk).filter fun xi =>
        dataOf Ac xi ∈ T.image (dataOf Ac)).filter
          fun xi => dataOf Ac xi = dt := by
    intro dt hdt
    obtain ⟨xi0, hxi0T, hxi0⟩ := Finset.mem_image.1 hdt
    have hpk0 := hTpk xi0 hxi0T
    intro xi hxi
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and] at hxi
    have hpk : pkOf xi = pkOf xi0 := by
      have he := hxi.trans hxi0.symm
      simp only [dataOf, Prod.mk.injEq] at he
      exact he.1
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hpk.trans hpk0, ?_⟩, hxi⟩
    rw [hxi]
    exact hdt
  have hcost (dt : Data) : sumW (fiberB Ac dt) * F dt =
      ∑ xi ∈ fiberB Ac dt, w * F (dataOf Ac xi) := by
    rw [sumW, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro xi hxi
    rw [dataOf_eq_of_mem_fiberB hxi]
  calc
    _ = ∑ dt ∈ T.image (dataOf Ac),
        ∑ xi ∈ fiberB Ac dt, w * F (dataOf Ac xi) :=
      Finset.sum_congr rfl fun dt _ => hcost dt
    _ ≤ ∑ dt ∈ T.image (dataOf Ac),
        ∑ xi ∈ ((fiberA pk).filter fun xi =>
          dataOf Ac xi ∈ T.image (dataOf Ac)) with dataOf Ac xi = dt,
            w * F (dataOf Ac xi) :=
      Finset.sum_le_sum fun dt hdt =>
        Finset.sum_le_sum_of_subset (hsub dt hdt)
    _ = ∑ xi ∈ ((fiberA pk).filter fun xi =>
          dataOf Ac xi ∈ T.image (dataOf Ac)),
        w * F (dataOf Ac xi) :=
      Finset.sum_fiberwise_of_maps_to
        (fun xi hxi => (Finset.mem_filter.1 hxi).2) _
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem postsign_auth_expected {alpha : Type} {Ac : Finset Name}
    (hAc : IsCut Ac) (pk : BitVec 128) (T : Finset Rec)
    (hT : T ⊆ fiberA pk) (d d' : Cache)
    (hd' : IndexExtension d d')
    (hTd : ∀ xi ∈ T, ¬ Cache.Hits d (kc xi))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (K : Data → OracleComp Spec alpha) :
    (∑ xi ∈ T, w * E
      (run (K (dataOf Ac xi)) (Cache.extend d' (fExp (some Ac) xi)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) xi)) +
        ind (Spr p.2 xi))) ≤
      (∑ xi ∈ T, w * ind (Spr d xi)) +
        authRate * ∑ xi ∈ fiberA pk, w *
          expectedCharge (otherPaid isIndex) (K (dataOf Ac xi))
            (Cache.extend d' (fExp (some Ac) xi)) := by
  have hfiber : ∀ dt ∈ T.image (dataOf Ac),
      (∑ xi ∈ T with dataOf Ac xi = dt, w * E
        (run (K (dataOf Ac xi)) (Cache.extend d' (fExp (some Ac) xi)))
        (fun p => ind (Cache.Hits p.2 (fHid (some Ac) xi)) +
          ind (Spr p.2 xi))) ≤
      (∑ xi ∈ T with dataOf Ac xi = dt, w * ind (Spr d xi)) +
        authRate * (sumW (fiberB Ac dt) *
          expectedCharge (otherPaid isIndex) (K dt)
            (Cache.extend d' dt.2.2)) := by
    intro dt hdt
    let Td := T.filter fun xi => dataOf Ac xi = dt
    have hdata : ∀ xi ∈ Td, dataOf Ac xi = dt :=
      fun xi hxi => (Finset.mem_filter.mp hxi).2
    have hsub : Td ⊆ fiberB Ac dt := by
      intro xi hxi
      simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdata xi hxi
    have hfe : ∀ xi ∈ Td, fExp (some Ac) xi = dt.2.2 :=
      fun xi hxi => congrArg (fun a : Data => a.2.2) (hdata xi hxi)
    have hc := fiber_auth_expected hAc dt hsub isIndex hindex K d'
    rw [authPotential_after_sign hd' Td (some Ac)
      (fun xi hxi => hTd xi (Finset.mem_filter.mp hxi).1) dt.2.2 hfe] at hc
    simpa only [mul_assoc] using hc
  rw [record_regroup T Ac,
    record_regroup T Ac (fun xi => w * ind (Spr d xi))]
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply add_le_add_right
  apply mul_le_mul_right
  exact fiber_costs_le Ac hT (fun dt =>
    expectedCharge (otherPaid isIndex) (K dt) (Cache.extend d' dt.2.2))

/-! ## Wire-query and signer adapters consumed by the game layer -/

theorem isCut_setsName (i : Fin M) : IsCut (setsName i) :=
  isCut_of_mem_family (setsName_mem i)

theorem exists_encQuery_of_length (q : Query)
    (hq : q.1 = msgBits + 86) : ∃ u : EncInput, q = encQuery u := by
  rcases q with ⟨n, x⟩
  dsimp only at hq
  subst n
  refine ⟨(x.extractLsb' 86 msgBits, x.extractLsb' 0 86), ?_⟩
  exact congrArg
    (fun y : BitVec (msgBits + 86) => (⟨msgBits + 86, y⟩ : Query))
    BitVec.extractLsb'_append_extractLsb'.symm

abbrev SignedWinner := Option (WeightedSampling.Winner 86 M)

def signatureFromWinner (xi : Rec) (s : SignedWinner) :
    Option WeightedScheme.Signature :=
  s.map fun r => (r.1, revealed (setsName r.2) xi)

end OptimalOTS.WeightedConstruction.LongChain91
