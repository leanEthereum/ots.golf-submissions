import Submissions.UpperCompressions.ProofBundle08
import Submissions.UpperCompressions.ProofBundle04
import Submissions.UpperCompressions.ProofBundle02
import Submissions.UpperCompressions.ProofBundle07
import Submissions.UpperCompressions.ProofBundle00
import Submissions.UpperCompressions.ProofBundle03
import Mathlib
import OptimalOTS.Model
import VCVio.EvalDist.Expectation

/- Original module: Submissions.UpperCompressions.WideInitialGame; SHA256 80a0ff072e29eb3ab66f9910237c373c89d18391582a2d0e2a291da451b447e0. -/
section

/-! Actual mixed72 keygen and adaptive message-choice decomposition. The
reduced choose run starts with an empty public cache; hidden graph points are
removed by the checked identical-until-bad coupling. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter CostAtMost
attribute [local irreducible] WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

def afterChoose (pk : PublicKey) (sk : forestScheme.graph.Assignment) (x : Message × A.State) : OracleComp Spec Bool :=
  forestScheme.sign sk x.1 >>= stB A pk x.1 x.2

def afterKeygen (p : PublicKey × forestScheme.graph.Assignment) : OracleComp Spec Bool :=
  A.choose p.1 >>= afterChoose A p.1 p.2

theorem experiment_eq : forestScheme.toAlgorithm.experiment A =
    forestScheme.keygen >>= afterKeygen A := by
  unfold TypedScheme.experiment afterKeygen afterChoose stB
  apply bind_congr
  rintro ⟨pk,sk⟩
  apply bind_congr
  rintro ⟨m,st⟩
  apply bind_congr
  intro σ
  apply bind_congr
  rintro ⟨m₂,σ₂⟩
  apply bind_congr
  intro ok
  congr 1
  by_cases h : σ.map (fun s => (m,s)) ≠ some (m₂,σ₂)
  · simp [h]
    intro _
    exact h
  · simp [h]
    intro _
    exact not_not.mp h

theorem publicKey_record (ξ : Rec) : forestScheme.publicKey (graph.evalRec ξ) = pkOf ξ := by
  change lowPk (graph.evalRec ξ graph.root) = lowPk (ξ.2 rh.fin)
  rw [← val_rh ξ]
  unfold val
  exact (lowPk_cast_eq (graph_len_fin rh) (graph.evalRec ξ rh.fin)).symm


theorem E_keygen (F : (PublicKey × forestScheme.graph.Assignment) × Cache → ℝ≥0∞) :
    E (run forestScheme.keygen ∅) F = ∑ ξ : Rec, w*F ((pkOf ξ,graph.evalRec ξ),kc ξ) := by
  rw [WeightedScheme.Scheme.keygen, GraphKeygenBridge.E_run_keygen forestScheme.graph forestScheme.publicKey tagging F]
  change (∑ ξ : Rec, w*F ((forestScheme.publicKey (graph.evalRec ξ),graph.evalRec ξ),kc ξ)) = _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [publicKey_record]

theorem E_experiment (F : Bool × Cache → ℝ≥0∞) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) F =
      ∑ ξ : Rec, w*E (run (afterKeygen A (pkOf ξ,graph.evalRec ξ)) (kc ξ)) F := by
  rw [experiment_eq,run_bind,E_bind,E_keygen]

theorem keygen_remaining {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) :
    995 ≤ B ∧ ∀ ξ : Rec,
      CostAtMost (afterKeygen A (pkOf ξ,graph.evalRec ξ)) (B-995) := by
  rw [experiment_eq,WeightedScheme.Scheme.keygen] at hB
  obtain ⟨hc,hr⟩ := GraphKeygenBridge.costAtMost_keygen_bind forestScheme.graph forestScheme.publicKey (afterKeygen A) hB
  rw [forestScheme_keygenCost] at hc hr
  refine ⟨hc,fun ξ => ?_⟩
  have hh := hr ξ
  change CostAtMost (afterKeygen A (forestScheme.publicKey (graph.evalRec ξ),graph.evalRec ξ)) (B-995) at hh
  rwa [publicKey_record] at hh

theorem afterChoose_loop (pk : PublicKey) (ξ : Rec) (x : Message × A.State) :
    afterChoose A pk (graph.evalRec ξ) x =
      loop 86 WeightedSchedule.decode WeightedSchedule.tier x.1 signBudget >>=
        fun r => stB A pk x.1 x.2 (signatureFromWinner ξ r) := by
  unfold afterChoose WeightedScheme.Scheme.sign
  rw [bind_map_left]
  rfl

theorem afterChoose_extend (pk : PublicKey) (ξ : Rec) (x : Message × A.State) (d : Cache) :
    E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue =
      E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier x.1 signBudget) d)
        (fun p => E (run (stB A pk x.1 x.2 (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (kc ξ))) successValue) := by
  rw [afterChoose_loop,run_bind,run_loop_extend 86 WeightedSchedule.decode WeightedSchedule.tier x.1 (kc ξ) (fun η => kc_enc ξ (x.1,η)) signBudget d,
    bind_map_left,E_bind]

theorem stageA_iub (ξ : Rec) :
    E (run (afterKeygen A (pkOf ξ,graph.evalRec ξ)) (kc ξ)) successValue ≤
      E (run (A.choose (pkOf ξ)) ∅) (fun p => if Cache.Hits p.2 (kc ξ) then 1 else
        E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) successValue) := by
  unfold afterKeygen
  rw [run_bind,E_bind]
  have h := iub (A.choose (pkOf ξ)) (kc ξ)
    (fun p => E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1) p.2) successValue)
    (fun p => E_le_one _ successValue_le_one) ∅ (fun _ _ => rfl)
  rw [Cache.empty_extend] at h
  exact h

theorem regroup (G : Rec → (Message × A.State) × Cache → ℝ≥0∞) :
    (∑ ξ : Rec, w*E (run (A.choose (pkOf ξ)) ∅) (G ξ)) =
      ∑ pk : PublicKey, E (run (A.choose pk) ∅)
        (fun p => ∑ ξ ∈ fiberA pk, w*G ξ p) := by
  symm
  calc
    _ = ∑ pk : PublicKey, ∑ ξ ∈ fiberA pk, w*E (run (A.choose (pkOf ξ)) ∅) (G ξ) := by
      apply Finset.sum_congr rfl
      intro pk _
      rw [E_finsetSum]
      apply Finset.sum_congr rfl
      intro ξ hξ
      have hpk : pkOf ξ = pk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
      rw [hpk]
      exact (E_const_mul _ _ _).symm
    _ = _ := by
      unfold fiberA
      exact Finset.sum_fiberwise Finset.univ pkOf _

def conditional (pk : PublicKey) (x : Message × A.State) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiberA pk, w * (if Cache.Hits d (kc ξ) then 0 else
    E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue)

/-- The actual global success decomposes into pre-sign graph authentication
cost and the record-weighted actual conditional sign/post experiment. -/
theorem global_reduced (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : WideForest.EncInput, q=WideForest.encQuery u) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (run (A.choose pk) ∅) (fun p => conditional A pk p.1 p.2) := by
  rw [E_experiment]
  calc
    _ ≤ ∑ ξ : Rec, w*E (run (A.choose (pkOf ξ)) ∅) (fun p =>
        if Cache.Hits p.2 (kc ξ) then 1 else
          E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1)
            (Cache.extend p.2 (kc ξ))) successValue) :=
      Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl (stageA_iub A ξ)
    _ = ∑ pk : PublicKey, E (run (A.choose pk) ∅) (fun p =>
        ∑ ξ ∈ fiberA pk, w*(if Cache.Hits p.2 (kc ξ) then 1 else
          E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1)
            (Cache.extend p.2 (kc ξ))) successValue)) := regroup A _
    _ ≤ ∑ pk : PublicKey, ((authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅ +
        E (run (A.choose pk) ∅) (fun p => conditional A pk p.1 p.2)) := by
      apply Finset.sum_le_sum
      intro pk _
      calc
        _ ≤ E (run (A.choose pk) ∅) (fun p => authPotential (fiberA pk) none p.2 +
            conditional A pk p.1 p.2) := by
          apply E_mono
          intro p
          unfold conditional authPotential
          simp only [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro ξ hξ
          have hpk : pkOf ξ = pk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
          rw [hpk,fHid_none]
          by_cases hh : Cache.Hits p.2 (kc ξ)
          · simp only [if_pos hh,ind_of hh,mul_zero,add_zero]
            exact mul_le_mul' le_rfl (le_add_right (le_refl (1:ℝ≥0∞)))
          · simp only [if_neg hh,ind_not hh,zero_add]
            exact le_add_of_nonneg_left (bot_le : (0:ℝ≥0∞) ≤ _)
        _ = E (run (A.choose pk) ∅) (fun p => authPotential (fiberA pk) none p.2) +
            E (run (A.choose pk) ∅) (fun p => conditional A pk p.1 p.2) := expectedValue_add _ _ _
        _ ≤ _ := add_le_add (stageA_auth_expected A pk isIndex hindex) le_rfl
    _ = _ := Finset.sum_add_distrib

#print axioms E_experiment
#print axioms keygen_remaining
#print axioms global_reduced
end OptimalOTS.WeightedConstruction.WideInitialGame
end
end

/- Original module: Submissions.UpperCompressions.WideInitialEager; SHA256 abd9b9930f1c6a86461b7ab47a79ae5a2609806e01361b3c758118bf0df46ad9. -/
section

/-! The reduced actual sign/post continuation as the full-table expectation
used by the signed/no-sign conditional master. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter graph CostAtMost WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

theorem kc_indexLength_none (ξ : Rec) (q : Query) (hq : q.1 = msgBits+86) : kc ξ q = none := by
  cases hc : kc ξ q with
  | none => rfl
  | some u =>
    obtain ⟨h,p,hp,he,_⟩ := (kc_apply_iff ξ q u).mp hc
    exact False.elim (len_hashParent_ne_enc hp ((congrArg Sigma.fst he).symm.trans hq))

theorem afterChoose_eager (pk : PublicKey) (ξ : Rec) (x : Message × A.State) (d : Cache) :
    E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue =
      E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
        E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier x.1 signBudget)
          ((lengthSlice (msgBits+86)).preload d g)) (fun p =>
          E (run (stBWithForgery A pk x.1 x.2 (signatureFromWinner ξ p.1))
            (Cache.extend p.2 (kc ξ))) forgerySuccess)) := by
  have h := outE_length_preload (msgBits+86) (afterChoose A pk (graph.evalRec ξ) x)
    (Cache.extend d (kc ξ)) (fun b => if b = true then 1 else 0)
  change E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue = _ at h
  rw [h]
  apply congrArg (E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)))
  funext g
  rw [preload_extend_commute _ d (kc ξ) (kc_indexLength_none ξ)]
  change E (run (afterChoose A pk (graph.evalRec ξ) x)
    (Cache.extend ((lengthSlice (msgBits+86)).preload d g) (kc ξ))) successValue = _
  rw [afterChoose_extend]
  congr 1
  funext p
  exact (retained_success_eq A pk x.1 x.2 (signatureFromWinner ξ p.1) _).symm

/-- The initial first-stage conditional is exactly a joint full-table average,
with original-public-cache exclusions kept outside the sign/post experiment. -/
theorem conditional_eager (pk : PublicKey) (x : Message × A.State) (d : Cache) :
    conditional A pk x d = ∑ ξ ∈ (fiberA pk).filter (fun ξ => ¬ Cache.Hits d (kc ξ)), w *
      E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
        E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier x.1 signBudget)
          ((lengthSlice (msgBits+86)).preload d g)) (fun p =>
          E (run (stBWithForgery A pk x.1 x.2 (signatureFromWinner ξ p.1))
            (Cache.extend p.2 (kc ξ))) forgerySuccess)) := by
  unfold conditional
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases hh : Cache.Hits d (kc ξ)
  · simp [hh]
  · simp only [hh,if_false,not_false_eq_true,if_true]
    rw [afterChoose_eager]

#print axioms afterChoose_eager
#print axioms conditional_eager
end OptimalOTS.WeightedConstruction.WideInitialGame
end
end

/- Original module: Submissions.UpperCompressions.ReplacementRemainingClock; SHA256 17cbf2d67e54cb66daf7ce6a64b1355949447702c9218afd6dfa86a88278e26d. -/
section

/-! Retain the actual pathwise remaining budget alongside the original shared
cache interpreter, without requiring a finite adversary state space. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical

def runRemaining {α : Type} (oa : OracleComp Spec α) : Cache → ℕ → ProbComp (α × Cache × ℕ) :=
  OracleComp.construct (fun a c b => pure (a,c,b))
    (fun t _ rec c b => do
      let r ← (oracleImpl t).run c
      rec r.1 r.2 (b-queryCost t)) oa

@[simp] theorem runRemaining_pure {α : Type} (a : α) (c : Cache) (b : ℕ) :
    runRemaining (pure a) c b = pure (a,c,b) := by simp [runRemaining]

theorem runRemaining_query {α : Type} (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) (b : ℕ) :
    runRemaining (liftM (Spec.query t) >>= k) c b =
      (oracleImpl t).run c >>= fun r => runRemaining (k r.1) r.2 (b-queryCost t) := by
  simp [runRemaining]

theorem runRemaining_project {α : Type} (oa : OracleComp Spec α) (c : Cache) (b : ℕ) :
    (fun r : α × Cache × ℕ => (r.1,r.2.1)) <$> runRemaining oa c b = run oa c := by
  induction oa using OracleComp.inductionOn generalizing c b with
  | pure a => simp [run_pure]
  | query_bind t k ih =>
    rw [runRemaining_query,run_query_bind,map_bind]
    exact bind_congr fun r => ih r.1 r.2 _

/-- All members of the continuation family inherit the same pathwise remaining
budget after every supported actual first-stage execution. -/
theorem runRemaining_family_support {α β J : Type} [Nonempty J]
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β) :
    ∀ c b, (∀ j, CostAtMost (oa >>= k j) b) →
      ∀ r ∈ support (runRemaining oa c b),
        r.2.2 ≤ b ∧ ∀ j, CostAtMost (k j r.1) r.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c b hB r hr
    rw [runRemaining_pure,support_pure,Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl,fun j => by simpa only [pure_bind] using hB j⟩
  | query_bind t f ih =>
    intro c b hB r hr
    have hB' : ∀ a j, CostAtMost (f a >>= k j) (b-queryCost t) := by
      intro a j
      have h := hB j
      rw [bind_assoc,costAtMost_query_bind_iff] at h
      exact h.2 a
    rw [runRemaining_query,support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨p,_,hr⟩ := hr
    obtain ⟨hle,hk⟩ := ih p.1 p.2 _ (hB' p.1) r hr
    exact ⟨hle.trans (Nat.sub_le _ _),hk⟩

/-- The expected spent query cost and expected remaining budget share the
original budget. This is useful when averaging a continuation-rate bound. -/
theorem expected_spent_remaining_le {α β J : Type} [Nonempty J]
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β) :
    ∀ c b, (∀ j, CostAtMost (oa >>= k j) b) →
      expectedCharge (fun t => queryCost t) oa c +
        E (runRemaining oa c b) (fun r => (r.2.2:ℝ≥0∞)) ≤ b := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro c b hB; simp [E_pure]
  | query_bind t f ih =>
    intro c b hB
    have hh := hB (Classical.arbitrary J)
    rw [bind_assoc,costAtMost_query_bind_iff] at hh
    have hB' : ∀ a j, CostAtMost (f a >>= k j) (b-queryCost t) := by
      intro a j
      have h := hB j
      rw [bind_assoc,costAtMost_query_bind_iff] at h
      exact h.2 a
    rw [expectedCharge_query,runRemaining_query,E_bind]
    calc
      _ = (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c) (fun p =>
          expectedCharge (fun t => queryCost t) (f p.1) p.2 +
            E (runRemaining (f p.1) p.2 (b-queryCost t)) (fun r => (r.2.2:ℝ≥0∞))) := by
        rw [add_assoc]
        exact congrArg ((queryCost t:ℝ≥0∞) + ·) (expectedValue_add _ _ _).symm
      _ ≤ (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c)
          (fun _ => ((b-queryCost t:ℕ):ℝ≥0∞)) :=
        add_le_add le_rfl (E_mono _ (fun p => ih p.1 p.2 _ (hB' p.1)))
      _ ≤ (queryCost t:ℝ≥0∞) + ((b-queryCost t:ℕ):ℝ≥0∞) :=
        add_le_add le_rfl (E_const_le _ _)
      _ = _ := by rw [← Nat.cast_add,Nat.add_sub_of_le hh.1]

#print axioms runRemaining_project
#print axioms runRemaining_family_support
#print axioms expected_spent_remaining_le
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementSupportReserve; SHA256 a0edc8fa4c7f8f597778eb267e0aa6e98dca14bb35581273e119c53951aaf0eb. -/
section

/-! The all-L syntactic reserve applies to every supported outcome of the
actual shared-cache signer, without a full-support assumption on that cache. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem run_output_mem_support {α : Type} (oa : OracleComp Spec α) :
    ∀ c p, p ∈ support (run oa c) → p.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c p hp
    rw [run_pure,support_pure,Set.mem_singleton_iff] at hp
    subst p
    simp
  | query_bind t k ih =>
    intro c p hp
    rw [run_query_bind,support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨r,_,hp⟩ := hp
    rw [support_bind]
    simp only [Set.mem_iUnion]
    exact ⟨r.1,by simp,ih r.1 r.2 p hp⟩

theorem actual_loop_reserve {M : ℕ} {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (hc : blockCost (msgBits+n) = 1)
    (k : ℕ) (kont : Option (Winner n M) → OracleComp Spec β) (b : ℕ)
    (hB : CostAtMost (loop n decode tier m k >>= kont) b) :
    k ≤ b ∧ ∀ c p, p ∈ support (run (loop n decode tier m k) c) →
      CostAtMost (kont p.1) (b-k) := by
  obtain ⟨hk,hr⟩ := loop_reserve n decode tier m hc k kont b hB
  exact ⟨hk,fun c p hp => hr p.1 (run_output_mem_support _ c p hp)⟩

#print axioms run_output_mem_support
#print axioms actual_loop_reserve
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.WideInitialBudget; SHA256 d4e30cf5d3f89f79bde728f1fa4014a1d43592c40c02c2c4925420cd48f24535. -/
section

/-! Pathwise budgets for the actual reduced adaptive choose run and all-L
signer. Only supported actual signer outcomes need continuation budgets. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter graph CostAtMost WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

theorem fiber_nonempty (pk : PublicKey) : (fiberA pk).Nonempty := by
  refine ⟨(fun _ => 0, fun _ => pk.setWidth 256), ?_⟩
  simp only [fiberA,Finset.mem_filter,Finset.mem_univ,true_and]
  show lowPk (pk.setWidth 256) = pk
  rw [lowPk,BitVec.setWidth_setWidth_of_le _ (by norm_num [pkBits])]
  exact BitVec.setWidth_eq pk

theorem choose_remaining_support (pk : PublicKey) (b : ℕ)
    (hB : ∀ ξ ∈ fiberA pk, CostAtMost (afterKeygen A (pkOf ξ,graph.evalRec ξ)) b)
    (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ b)) :
    r.2.2 ≤ b ∧ ∀ ξ ∈ fiberA pk,
      CostAtMost (afterChoose A pk (graph.evalRec ξ) r.1) r.2.2 := by
  letI : Nonempty {ξ : Rec // ξ ∈ fiberA pk} := (fiber_nonempty pk).to_subtype
  have hb : ∀ j : {ξ : Rec // ξ ∈ fiberA pk},
      CostAtMost (A.choose pk >>= afterChoose A pk (graph.evalRec j.1)) b := by
    intro j
    have h := hB j.1 j.2
    have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) j.1 j.2
    simpa only [afterKeygen,hpk] using h
  obtain ⟨hle,hk⟩ := runRemaining_family_support (A.choose pk)
    (fun j : {ξ : Rec // ξ ∈ fiberA pk} => afterChoose A pk (graph.evalRec j.1)) ∅ b hb r hr
  exact ⟨hle,fun ξ hξ => hk ⟨ξ,hξ⟩⟩

/-- After the actual choose output, every consistent supported signer return
leaves the same reserved L-subtracted budget for the retained-forgery program. -/
theorem choose_supported_sign_reserve (pk : PublicKey) (b : ℕ)
    (hB : ∀ ξ ∈ fiberA pk, CostAtMost (afterKeygen A (pkOf ξ,graph.evalRec ξ)) b)
    (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ b)) :
    signBudget ≤ r.2.2 ∧ r.2.2 ≤ b ∧
      ∀ ξ ∈ fiberA pk, ∀ c p,
        p ∈ support (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier r.1.1 signBudget) c) →
        CostAtMost (stBWithForgery A pk r.1.1 r.1.2 (signatureFromWinner ξ p.1)) (r.2.2-signBudget) := by
  obtain ⟨hle,hk⟩ := choose_remaining_support A pk b hB r hr
  have hres (ξ : Rec) (hξ : ξ ∈ fiberA pk) := actual_loop_reserve 86
    WeightedSchedule.decode WeightedSchedule.tier r.1.1 index86_cost signBudget
    (fun s => stB A pk r.1.1 r.1.2 (signatureFromWinner ξ s)) r.2.2
    (by rw [← afterChoose_loop]; exact hk ξ hξ)
  obtain ⟨ξ₀,hξ₀⟩ := fiber_nonempty pk
  refine ⟨(hres ξ₀ hξ₀).1,hle,?_⟩
  intro ξ hξ c p hp
  have hh := (hres ξ hξ).2 c p hp
  rw [← stBWithForgery_map] at hh
  exact (AlgorithmCosts.costAtMost_map_iff _ _ _).1 hh

theorem experiment_choose_reserve {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-995))) :
    signBudget ≤ r.2.2 ∧ r.2.2 ≤ B-995 ∧
      ∀ ξ ∈ fiberA pk, ∀ c p,
        p ∈ support (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier r.1.1 signBudget) c) →
        CostAtMost (stBWithForgery A pk r.1.1 r.1.2 (signatureFromWinner ξ p.1)) (r.2.2-signBudget) :=
  choose_supported_sign_reserve A pk (B-995) (fun ξ _ => (keygen_remaining A hB).2 ξ) r hr

theorem choose_spent_remaining_le {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    expectedCharge (fun t => queryCost t) (A.choose pk) ∅ +
      E (runRemaining (A.choose pk) ∅ (B-995)) (fun r => (r.2.2:ℝ≥0∞)) ≤ (B-995:ℕ) := by
  letI : Nonempty {ξ : Rec // ξ ∈ fiberA pk} := (fiber_nonempty pk).to_subtype
  apply expected_spent_remaining_le (A.choose pk)
    (fun j : {ξ : Rec // ξ ∈ fiberA pk} => afterChoose A pk (graph.evalRec j.1)) ∅ (B-995)
  intro j
  have h := (keygen_remaining A hB).2 j.1
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) j.1 j.2
  simpa only [afterKeygen,hpk] using h

/-- The same global factorization with the actual remaining budget retained
in the first-stage output, ready for a path-dependent continuation bound. -/
theorem global_reduced_clock (b : ℕ) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : WideForest.EncInput, q=WideForest.encQuery u) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ b)
        (fun r => conditional A pk r.1 r.2.1) := by
  have h := global_reduced A isIndex hindex
  have he (pk : PublicKey) : E (run (A.choose pk) ∅) (fun p => conditional A pk p.1 p.2) =
      E (runRemaining (A.choose pk) ∅ b) (fun r => conditional A pk r.1 r.2.1) := by
    rw [← runRemaining_project (A.choose pk) ∅ b,E_map]
  simp_rw [he] at h
  exact h

#print axioms global_reduced_clock
#print axioms choose_supported_sign_reserve
#print axioms experiment_choose_reserve
#print axioms choose_spent_remaining_le
end OptimalOTS.WeightedConstruction.WideInitialGame
end
end

/- Original module: Submissions.UpperCompressions.WideInitialPayoff; SHA256 946aaa2a41d0a2f94c4dc225d8decbcda88b9f96b7ffcdb49b34beecc80f033f. -/
section

/-! Sharp initial authentication accounting: the surviving pre-sign Spr term
is absorbed together with the stageA hit event exactly once. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

def hitMass (pk : PublicKey) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiberA pk, w*ind (Cache.Hits d (kc ξ))

def survivingSpr (pk : PublicKey) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ (fiberA pk).filter (fun ξ => ¬ Cache.Hits d (kc ξ)), w*ind (Spr d ξ)

theorem hit_survivingSpr_le_auth (pk : PublicKey) (d : Cache) :
    hitMass pk d + survivingSpr pk d ≤ authPotential (fiberA pk) none d := by
  have hs : survivingSpr pk d ≤ ∑ ξ ∈ fiberA pk, w*ind (Spr d ξ) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine (add_le_add le_rfl hs).trans_eq ?_
  simp only [hitMass,authPotential,fHid_none,mul_add,Finset.sum_add_distrib]

theorem global_reduced_hits :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      ∑ pk : PublicKey, E (run (A.choose pk) ∅)
        (fun p => hitMass pk p.2 + conditional A pk p.1 p.2) := by
  rw [E_experiment]
  calc
    _ ≤ ∑ ξ : Rec, w*E (run (A.choose (pkOf ξ)) ∅) (fun p =>
        if Cache.Hits p.2 (kc ξ) then 1 else
          E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1)
            (Cache.extend p.2 (kc ξ))) successValue) :=
      Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl (stageA_iub A ξ)
    _ = ∑ pk : PublicKey, E (run (A.choose pk) ∅) (fun p =>
        ∑ ξ ∈ fiberA pk, w*(if Cache.Hits p.2 (kc ξ) then 1 else
          E (run (afterChoose A (pkOf ξ) (graph.evalRec ξ) p.1)
            (Cache.extend p.2 (kc ξ))) successValue)) := regroup A _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pk _
      congr 1
      funext p
      unfold hitMass conditional
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ]
      by_cases hh : Cache.Hits p.2 (kc ξ) <;> simp [hh,ind]

theorem global_reduced_hits_clock (b : ℕ) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ b)
        (fun r => hitMass pk r.2.1 + conditional A pk r.1 r.2.1) := by
  have h := global_reduced_hits A
  have he (pk : PublicKey) :
      E (run (A.choose pk) ∅) (fun p => hitMass pk p.2 + conditional A pk p.1 p.2) =
      E (runRemaining (A.choose pk) ∅ b) (fun r => hitMass pk r.2.1 + conditional A pk r.1 r.2.1) := by
    rw [← runRemaining_project (A.choose pk) ∅ b,E_map]
  simp_rw [he] at h
  exact h

/-- A supported conditional sign/post bound carrying the surviving pre-Spr
term lifts to the global game, charging pre-sign authentication only once. -/
theorem global_payoff_clock (b : ℕ) (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : WideForest.EncInput, q=WideForest.encQuery u)
    (payoff : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞)
    (hpay : ∀ pk r, r ∈ support (runRemaining (A.choose pk) ∅ b) →
      conditional A pk r.1 r.2.1 ≤ survivingSpr pk r.2.1 + payoff pk r) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ b) (payoff pk) := by
  refine (global_reduced_hits_clock A b).trans ?_
  calc
    _ ≤ ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ b)
        (fun r => authPotential (fiberA pk) none r.2.1 + payoff pk r) := by
      apply Finset.sum_le_sum
      intro pk _
      apply expectedValue_mono_of_support
      intro r hr
      calc
        _ ≤ hitMass pk r.2.1 + (survivingSpr pk r.2.1 + payoff pk r) := add_le_add le_rfl (hpay pk r hr)
        _ ≤ _ := by rw [← add_assoc]; exact add_le_add (hit_survivingSpr_le_auth pk r.2.1) le_rfl
    _ = ∑ pk : PublicKey, (E (run (A.choose pk) ∅) (fun p => authPotential (fiberA pk) none p.2) +
        E (runRemaining (A.choose pk) ∅ b) (payoff pk)) := by
      apply Finset.sum_congr rfl
      intro pk _
      calc
        _ = E (runRemaining (A.choose pk) ∅ b) (fun r => authPotential (fiberA pk) none r.2.1) +
            E (runRemaining (A.choose pk) ∅ b) (payoff pk) := expectedValue_add _ _ _
        _ = _ := by rw [← runRemaining_project (A.choose pk) ∅ b,E_map]
    _ ≤ ∑ pk : PublicKey, ((authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid isIndex) (A.choose pk) ∅ +
        E (runRemaining (A.choose pk) ∅ b) (payoff pk)) :=
      Finset.sum_le_sum fun pk _ => add_le_add (stageA_auth_expected A pk isIndex hindex) le_rfl
    _ = _ := Finset.sum_add_distrib

#print axioms global_reduced_hits
#print axioms global_payoff_clock
end OptimalOTS.WeightedConstruction.WideInitialGame
end
end

/- Original module: Submissions.UpperCompressions.ActualGamePayoff; SHA256 69ad9ff56c514eee27b52421264b229ad5654e73fdbfa1c6d8c14030256a0bc0. -/
section

/-! The actual complete mixed72 experiment reduces to physical pre-sign-cache
replay and excess payoffs, with the genuine remaining-budget clock. There are
no assumed posterior, security, or conditional-game bounds in this theorem. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

theorem signerAverage_eq_actual (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → ℝ≥0∞) :
    signerAverage m c k F = outE (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k) c F :=
  (outE_length_preload (msgBits+86) (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k) c F).symm

theorem conditional_eq_game (A : forestScheme.toAlgorithm.Adversary) (pk : PublicKey)
    (m : Message) (st : A.State) (c : Cache) :
    conditional A pk (m,st) c =
      conditionalGame A ((fiberA pk).filter (fun ξ => ¬ Cache.Hits c (kc ξ))) m st c signBudget := by
  rw [conditional_eager]
  unfold conditionalGame outcomeSuccessLoss
  apply Finset.sum_congr rfl
  intro ξ hξ
  have hpk := pkOf_of_subset_fiberA (Finset.filter_subset _ _) ξ hξ
  rw [hpk]

theorem conditional_actual_master (A : forestScheme.toAlgorithm.Adversary) (pk : PublicKey)
    (m : Message) (st : A.State) (c : Cache) (B : ℕ)
    (hB : SupportedPostBudget A pk m st c signBudget B) :
    conditional A pk (m,st) c ≤ survivingSpr pk c + sumW (fiberA pk) *
      (signerAverage m c signBudget (winnerReplay c m) +
        B*(authRate+signerAverage m c signBudget winnerExcess)) := by
  rw [conditional_eq_game]
  exact conditional_game_master A pk _ (Finset.filter_subset _ _) m st c signBudget B
    (fun ξ hξ => (Finset.mem_filter.mp hξ).2) hB

theorem supportedPostBudget_of_experiment (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey)
    (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-995))) :
    SupportedPostBudget A pk r.1.1 r.1.2 r.2.1 signBudget (r.2.2-signBudget) := by
  intro ξ hξ g p hp
  have h := (experiment_choose_reserve A hB pk r hr).2.2 ξ hξ _ p hp
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
  simpa only [hpk] using h

def continuationPayoff (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  sumW (fiberA pk) * (signerAverage r.1.1 r.2.1 signBudget (winnerReplay r.2.1 r.1.1) +
    (r.2.2-signBudget : ℕ)*(authRate+signerAverage r.1.1 r.2.1 signBudget winnerExcess))

/-- Full actual experiment-to-payoff bound. The public choose stage and all
remaining sign/post stages use their actual shared-cache semantics and one
residual budget. Pre-sign spurious loss is absorbed exactly once. -/
theorem global_actual_game_payoff (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ (B-995)) (continuationPayoff A pk) := by
  apply global_payoff_clock A (B-995) (isIndexLength (msgBits+86))
    (fun q hq => exists_encQuery_of_length q hq) (continuationPayoff A)
  intro pk r hr
  exact conditional_actual_master A pk r.1.1 r.1.2 r.2.1 (r.2.2-signBudget)
    (supportedPostBudget_of_experiment A hB pk r hr)

#print axioms conditional_actual_master
#print axioms supportedPostBudget_of_experiment
#print axioms global_actual_game_payoff
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.ActualGamePayoffGated; SHA256 9027d275dbb45ebb41fa88f25ed0c9113e5d65f370390a4264743b35bda4285e. -/
section

/-! Preserve the actual conditional success cap before expanding empirical
payoffs. A combined Good/large-deviation exception is therefore paid once. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

theorem conditional_le_fiber (A : forestScheme.toAlgorithm.Adversary) (pk : PublicKey)
    (x : Message × A.State) (c : Cache) : conditional A pk x c ≤ sumW (fiberA pk) := by
  unfold conditional sumW
  apply Finset.sum_le_sum
  intro ξ _
  calc
    _ ≤ w*1 := by
      apply mul_le_mul_right
      split_ifs
      · exact zero_le
      · exact E_le_one _ successValue_le_one
    _ = _ := mul_one _

def gatedContinuationPayoff (A : forestScheme.toAlgorithm.Adversary)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  sumW (fiberA pk) * (if good pk r then
    signerAverage r.1.1 r.2.1 signBudget (winnerReplay r.2.1 r.1.1) +
      (r.2.2-signBudget : ℕ)*(authRate+signerAverage r.1.1 r.2.1 signBudget winnerExcess)
    else 1)

theorem conditional_supported_gated (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-995))) :
    conditional A pk r.1 r.2.1 ≤ survivingSpr pk r.2.1 + gatedContinuationPayoff A good pk r := by
  by_cases hg : good pk r
  · rw [gatedContinuationPayoff,if_pos hg]
    exact conditional_actual_master A pk r.1.1 r.1.2 r.2.1 (r.2.2-signBudget)
      (supportedPostBudget_of_experiment A hB pk r hr)
  · rw [gatedContinuationPayoff,if_neg hg,mul_one]
    exact (conditional_le_fiber A pk r.1 r.2.1).trans le_add_self

/-- Full actual strong-success probability with the empirical/large-deviation
split made at the conditional success cap. An arbitrary conjunction of bad
conditions may be represented by `¬good`, without multiplying it by a budget. -/
theorem global_actual_game_payoff_gated (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ (B-995))
        (gatedContinuationPayoff A good pk) := by
  apply global_payoff_clock A (B-995) (isIndexLength (msgBits+86))
    (fun q hq => exists_encQuery_of_length q hq) (gatedContinuationPayoff A good)
  exact conditional_supported_gated A hB good

#print axioms conditional_le_fiber
#print axioms global_actual_game_payoff_gated
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.WideDecoderLaw; SHA256 0a9f8bb45c1a2e9125ab4850438d8fbf8bd780db39f6c5cd29254fad53a43464. -/
section

/-! The actual256-bit decoder law, including the rejection atom. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open scoped Classical
open WeightedReference WeightedRow.Weights
attribute [local irreducible] Finset.univ Finset.filter

theorem card_decode_none :
    (Finset.univ.filter fun b : BitVec 256 => decode b=none).card =
      2^256-A*2^127 := by
  have h := WeightedSampling.Availability.card_option_none decode (A*2^127) accepted_decode_count
  have hs : (Finset.univ.filter fun b : BitVec 256 => decode b=none) =
      Finset.univ.filter fun b : BitVec 256 => (decode b).isNone := by
    apply Finset.filter_congr
    intro b hb
    cases decode b <;> simp
  exact (congrArg Finset.card hs).trans h

theorem decoder_law (x : Option (Fin M)) :
    ((Finset.univ.filter fun b : BitVec 256 => decode b=x).card:ℝ)/
      Fintype.card (BitVec 256) = securityWeights.classMass x := by
  cases x with
  | none =>
    rw [card_decode_none,Fintype.card_bitVec]
    change ((2^256-A*2^127:ℕ):ℝ)/(2^256:ℕ) = 1-∑ i : Fin M,classProbability i
    rw [classProbability_sum]
    change ((2^256-WeightedResearch92.acceptedAliases*2^127:ℕ):ℝ)/(2^256:ℕ) = _
    rw [WeightedResearch92.aliases_exact]
    norm_num [acceptance]
  | some i =>
    change ((Finset.univ.filter fun b : BitVec 256 => decode b=some i).card:ℝ)/
      Fintype.card (BitVec 256) = classProbability i
    rw [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
    exact class_probability_real i

#print axioms decoder_law
end OptimalOTS.WeightedConstruction.WeightedSchedule
end
end

/- Original module: Submissions.UpperCompressions.WideIndexDomains; SHA256 4ee5ad808e934513efc7f767cc4944f915b29a99226668facbf3ecfec13b1e35. -/
section

/-! The concrete finite public index domain and its nonce rows. Counts are
computed from the real cache, so each row has at most2^86 distinct inputs. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideDomains
open scoped Classical
open WeightedCacheCounts WideForest
attribute [local irreducible] Finset.univ Finset.filter

def indexDomain : Finset Query := Finset.univ.image (fun x : BitVec 342 => (⟨342,x⟩ : Query))
def rowDomain (m : Message) : Finset Query :=
  Finset.univ.image (fun η : BitVec 86 => WideForest.encQuery (m,η))

theorem mem_indexDomain (q : Query) : q ∈ indexDomain ↔ q.1=342 := by
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
    exact (congrArg Sigma.fst he).symm
  · rcases q with ⟨n,x⟩
    intro hn
    dsimp at hn
    subst n
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩

theorem mem_rowDomain (m : Message) (q : Query) :
    q ∈ rowDomain m ↔ ∃ η : BitVec 86,WideForest.encQuery (m,η)=q := by
  simp only [rowDomain,Finset.mem_image,Finset.mem_univ,true_and]

theorem row_subset (m : Message) : rowDomain m ⊆ indexDomain := by
  intro q hq
  obtain ⟨η,rfl⟩ := (mem_rowDomain m q).mp hq
  exact (mem_indexDomain _).mpr rfl

theorem row_card (m : Message) : (rowDomain m).card=2^86 := by
  unfold rowDomain
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ,Fintype.card_bitVec]
  · intro η ζ h
    exact WeightedSampling.Availability.nonce_query_inj m h

theorem seen_row_bound (m : Message) (c : hashSpec.QueryCache) :
    (seen (rowDomain m) c).card ≤ 2^86 :=
  (seen_card_le _ _).trans_eq (row_card m)

theorem seen_row_subset (m : Message) (c : hashSpec.QueryCache) :
    seen (rowDomain m) c ⊆ seen indexDomain c := by
  intro q hq
  exact Finset.mem_filter.mpr ⟨row_subset m (Finset.mem_filter.mp hq).1,
    (Finset.mem_filter.mp hq).2⟩

theorem fresh_seen_empty (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) : seen indexDomain c=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := Finset.mem_filter.mp hq
  have hc := hf q ((mem_indexDomain q).mp h.1)
  simpa only [hc,Option.isSome_none,Bool.false_eq_true] using h.2

theorem fresh_counts_zero (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    classCounts indexDomain c WeightedSchedule.decode = fun _ => 0 := by
  unfold classCounts
  rw [fresh_seen_empty c hf]
  funext i
  simp [WeightedPublicCounts.counts]

#print axioms row_card
#print axioms seen_row_bound
#print axioms fresh_counts_zero
end OptimalOTS.WeightedConstruction.WideDomains
end
end

/- Original module: Submissions.UpperCompressions.ActualRealExpectation; SHA256 e175feba8d3d38cd3ae09ddc4b8f06db9e2163f6279cdfa68469166a7b44cadf. -/
section

/-! Signed finite expectation for actual ProbComp programs. Defined by their
uniform-query syntax, with exact bind laws and a proved ENNReal semantic bridge.
No integrability or execution-law equality is supplied as a hypothesis. -/

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal BigOperators
namespace WeightedRealExecution

set_option maxHeartbeats 800000
variable {α β : Type}

/-- The real expectation functional of a finite private-randomness program. -/
def realEval (oa : ProbComp α) : (α → ℝ) →ₗ[ℝ] ℝ :=
  OracleComp.construct (fun a => LinearMap.proj a)
    (fun q _ rec => (Fintype.card (unifSpec.Range q):ℝ)⁻¹ • ∑ u, rec u) oa

@[simp] theorem realEval_pure (a : α) (f : α → ℝ) : realEval (pure a) f = f a := by
  simp [realEval]

@[simp] theorem realEval_query_bind (q : unifSpec.Domain)
    (k : unifSpec.Range q → ProbComp α) (f : α → ℝ) :
    realEval ((liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) >>= k) f =
      (Fintype.card (unifSpec.Range q):ℝ)⁻¹ * ∑ u, realEval (k u) f := by
  simp [realEval, LinearMap.sum_apply]

/-- The real tower property follows from actual ProbComp syntax. -/
theorem realEval_bind (oa : ProbComp α) (k : α → ProbComp β) (f : β → ℝ) :
    realEval (oa >>= k) f = realEval oa (fun a => realEval (k a) f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [bind_assoc, realEval_query_bind, realEval_query_bind]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    exact ih u

/-- Positivity may be restricted to outputs in the actual computation support. -/
theorem realEval_mono_of_support (oa : ProbComp α) (f g : α → ℝ)
    (hfg : ∀ a ∈ support oa, f a ≤ g a) : realEval oa f ≤ realEval oa g := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using hfg a (by simp)
  | query_bind q next ih =>
    rw [realEval_query_bind, realEval_query_bind]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro u _
    apply ih u
    intro a ha
    apply hfg a
    exact (mem_support_bind_iff _ _ _).2 ⟨u, by simp, ha⟩

theorem realEval_mono (oa : ProbComp α) (f g : α → ℝ)
    (hfg : ∀ a, f a ≤ g a) : realEval oa f ≤ realEval oa g :=
  realEval_mono_of_support oa f g (fun a _ => hfg a)

theorem realEval_nonneg (oa : ProbComp α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ realEval oa f := by
  have hx := realEval_mono oa (fun _ => 0) f hf
  change realEval oa (0 : α → ℝ) ≤ realEval oa f at hx
  rw [(realEval oa).map_zero] at hx
  exact hx

@[simp] theorem realEval_const (oa : ProbComp α) (c : ℝ) : realEval oa (fun _ => c) = c := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [realEval_query_bind]
    simp only [ih, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (unifSpec.Range q):ℝ) ≠ 0 := by positivity
    field_simp

@[simp] theorem realEval_add (oa : ProbComp α) (f g : α → ℝ) :
    realEval oa (fun a => f a+g a) = realEval oa f+realEval oa g := (realEval oa).map_add _ _

@[simp] theorem realEval_sub (oa : ProbComp α) (f g : α → ℝ) :
    realEval oa (fun a => f a-g a) = realEval oa f-realEval oa g := (realEval oa).map_sub _ _

@[simp] theorem realEval_mul (oa : ProbComp α) (c : ℝ) (f : α → ℝ) :
    realEval oa (fun a => c*f a) = c*realEval oa f := by
  change realEval oa (c • f) = c • realEval oa f
  exact (realEval oa).map_smul c f

theorem realEval_le_const_of_support (oa : ProbComp α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ a ∈ support oa, f a ≤ c) : realEval oa f ≤ c := by
  simpa using realEval_mono_of_support oa f (fun _ => c) hf

/-- Exact agreement with VCVio's ENNReal expectation for nonnegative payoffs. -/
theorem ofReal_realEval (oa : ProbComp α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (realEval oa f) = expectedValue oa (fun a => ENNReal.ofReal (f a)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [realEval_query_bind, expectedValue_bind]
    have hc : 0 < (Fintype.card (unifSpec.Range q):ℝ) := by positivity
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hc]
    rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => realEval_nonneg (next u) f hf)]
    simp_rw [ih]
    rw [expectedValue_def, tsum_fintype]
    simp only [probOutput_query, ENNReal.ofReal_natCast, Finset.mul_sum]

variable {ι : Type} {spec : OracleSpec ι} {S : Type}

/-- Signed local drift lifts directly through actual stateful OracleComp execution. -/
theorem realEval_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ)
    (hstep : ∀ q s, realEval ((impl q).run s) (fun out => Φ out.2) ≤ Φ s)
    (oa : OracleComp spec α) (s : S) :
    realEval ((simulateQ impl oa).run s) (fun out => Φ out.2) ≤ Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [realEval_bind]
    have hc : ∀ out : spec.Range q × S,
        realEval ((simulateQ impl (next out.1)).run out.2) (fun out => Φ out.2) ≤ Φ out.2 :=
      fun out => ih out.1 out.2
    exact (realEval_mono ((impl q).run s) _ _ hc).trans (hstep q s)

/-- Exact signed martingale expectation, requiring only primitive-query drift. -/
theorem realEval_simulate_eq
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ)
    (hstep : ∀ q s, realEval ((impl q).run s) (fun out => Φ out.2) = Φ s)
    (oa : OracleComp spec α) (s : S) :
    realEval ((simulateQ impl oa).run s) (fun out => Φ out.2) = Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [realEval_bind]
    have hf : (fun out : spec.Range q × S =>
        realEval ((simulateQ impl (next out.1)).run out.2) (fun out => Φ out.2)) =
        (fun out => Φ out.2) := by
      funext out
      exact ih out.1 out.2
    rw [hf, hstep]

#print axioms realEval_bind
#print axioms realEval_mono_of_support
#print axioms realEval_const
#print axioms ofReal_realEval
#print axioms realEval_simulate_le
#print axioms realEval_simulate_eq

end WeightedRealExecution
end
end

/- Original module: Submissions.UpperCompressions.ActualUniformExpectation; SHA256 5f0b06cc2df68a8d884f80386d56ff12a491a69c65f9fb9dc045a9f1878c3bc5. -/
section

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal BigOperators
namespace WeightedRealExecution

set_option maxHeartbeats 800000
variable {α : Type} [Fintype α] [SampleableType α]

private theorem realEval_uniform_nonneg (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    realEval ($ᵗ α) f = (∑ a, f a) / Fintype.card α := by
  have hl := ofReal_realEval ($ᵗ α) f hf
  rw [expectedValue_def, tsum_fintype] at hl
  simp only [probOutput_uniformSample] at hl
  rw [← Finset.mul_sum] at hl
  have hc : 0 < (Fintype.card α:ℝ) := by positivity
  have hs : 0 ≤ ∑ a, f a := Finset.sum_nonneg (fun a _ => hf a)
  have he : ENNReal.ofReal (realEval ($ᵗ α) f) =
      ENNReal.ofReal ((∑ a, f a) / Fintype.card α) := by
    rw [hl, div_eq_mul_inv, ENNReal.ofReal_mul hs,
      ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a), mul_comm]
  have hx := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (realEval_nonneg _ _ hf),
    ENNReal.toReal_ofReal (div_nonneg hs hc.le)] using hx

/-- The exact signed average for the library's actual uniform-sampling computation. -/
theorem realEval_uniform (f : α → ℝ) :
    realEval ($ᵗ α) f = (∑ a, f a) / Fintype.card α := by
  have hf : f = fun a => max (f a) 0 - max (-f a) 0 := by
    funext a
    rcases le_total (f a) 0 with h | h
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  rw [hf, realEval_sub,
    realEval_uniform_nonneg _ (fun a => le_max_right _ _),
    realEval_uniform_nonneg _ (fun a => le_max_right _ _),
    Finset.sum_sub_distrib, sub_div]

@[simp] theorem realEval_map {β : Type} (oa : ProbComp α) (g : α → β) (f : β → ℝ) :
    realEval (g <$> oa) f = realEval oa (fun a => f (g a)) := by
  rw [map_eq_bind_pure_comp, realEval_bind]
  simp only [Function.comp_apply, realEval_pure]

theorem realEval_decoded_uniform {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : WeightedRow.Weights ι) (decode : α → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card α = w.classMass x) (f : Option ι → ℝ) :
    realEval ($ᵗ α) (fun b => f (decode b)) = w.expect f :=
  (realEval_uniform _).trans (w.uniform_decoder_expect decode hfiber f)

#print axioms realEval_uniform
#print axioms realEval_decoded_uniform
end WeightedRealExecution
end
end

/- Original module: Submissions.UpperCompressions.DirectCacheLaw; SHA256 6957c42c4181241ba7e133b2cfabc73b6555298479b2e40c5aa8a8668ed684cb. -/
section

/-! Statistics computed directly from the actual cache, over a finite selected
domain. Unlike an auxiliary counter, their finite-domain bound is immediate. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace WeightedDirectCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
set_option maxHeartbeats 800000
variable {D B ι : Type} [DecidableEq D] [Fintype B] [SampleableType B]
  [Fintype ι] [DecidableEq ι]

def fresh (A : Finset D) (q : D) (cache : D → Option B) : Bool :=
  decide (q ∈ A) && (cache q).isNone

/-- Exact one-query class law for the library's actual memoized uniform oracle.
The output alphabet remains generic here to avoid expanding a concrete giant sampler. -/
theorem hash_query_law (w : WeightedRow.Weights ι)
    (A : Finset D) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (q : D) (cache : (D →ₒ B).QueryCache) (f : ℕ → (ι → ℕ) → ℝ) :
    realEval (((D →ₒ B).randomOracle q).run cache)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    w.expect (fun x => f (step (fresh A q cache) (seen A cache).card (classCounts A cache decode) x).1
      (step (fresh A q cache) (seen A cache).card (classCounts A cache decode) x).2) := by
  rw [randomOracle.run_eq]
  cases hc : cache q with
  | some u => simp [hc, fresh, step, expect_const]
  | none =>
    simp only [realEval_bind, realEval_pure]
    by_cases hq : q ∈ A
    · have hcard (u : B) : (seen A (cache.cacheQuery q u)).card = (seen A cache).card+1 :=
        seen_card_update A cache q u hq hc
      have hcounts (u : B) : classCounts A (cache.cacheQuery q u) decode =
          advance (classCounts A cache decode) (decode u) :=
        classCounts_update_of_mem A cache decode q u hq hc
      simp only [hcard, hcounts, fresh, hq, decide_true, hc, Option.isNone_none,
        Bool.and_self, step, ite_true]
      exact realEval_decoded_uniform w decode hfiber (fun x =>
        f ((seen A cache).card+1) (advance (classCounts A cache decode) x))
    · have hseen (u : B) : seen A (cache.cacheQuery q u) = seen A cache :=
        seen_update_of_not_mem A cache q u hq
      have hcounts (u : B) : classCounts A (cache.cacheQuery q u) decode = classCounts A cache decode :=
        classCounts_update_of_not_mem A cache decode q u hq
      simp only [hseen, hcounts, fresh, hq, decide_false, Bool.false_and,
        step_not_fresh, realEval_const, expect_const]

/-- Generic protected oracle, with free private randomness and the shared cache. -/
def protectedImpl : QueryImpl (unifSpec+(D →ₒ B)) (StateT (D →ₒ B).QueryCache ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (D →ₒ B).QueryCache ProbComp) + (D →ₒ B).randomOracle

def protectedFresh (A : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (cache : (D →ₒ B).QueryCache) : Bool :=
  match t with
  | .inl _ => false
  | .inr q => fresh A q cache

theorem protected_query_law (w : WeightedRow.Weights ι)
    (A : Finset D) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (t : (unifSpec+(D →ₒ B)).Domain) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → ℝ) :
    realEval ((protectedImpl (D := D) (B := B) t).run cache)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    w.expect (fun x => f
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).1
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).2) := by
  cases t with
  | inl t =>
    simp only [protectedImpl, protectedFresh, step_not_fresh, expect_const]
    change realEval ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) (fun out => f (seen A out.2).card (classCounts A out.2 decode)) = _
    rw [realEval_bind]
    simp only [realEval_pure, realEval_const]
  | inr q => exact hash_query_law w A decode hfiber q cache f

/-- A hash query adds at most one selected cache entry on every supported outcome. -/
theorem hash_count_le_one (A : Finset D) (q : D) (cache : (D →ₒ B).QueryCache)
    (out : B × (D →ₒ B).QueryCache)
    (hout : out ∈ support (((D →ₒ B).randomOracle q).run cache)) :
    (seen A out.2).card ≤ (seen A cache).card+1 := by
  rw [randomOracle.run_eq] at hout
  cases hc : cache q with
  | some u =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact Nat.le_succ _
  | none =>
    simp only [hc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨u, hu, rfl⟩ := hout
    by_cases hq : q ∈ A
    · exact (seen_card_update A cache q u hq hc).le
    · rw [show seen A (cache.cacheQuery q u) = seen A cache from seen_update_of_not_mem A cache q u hq]
      exact Nat.le_succ _

/-- Free private queries preserve the selected cache count; hashes add at most one. -/
theorem protected_count_le (A : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (cache : (D →ₒ B).QueryCache) (out : (unifSpec+(D →ₒ B)).Range t × (D →ₒ B).QueryCache)
    (hout : out ∈ support ((protectedImpl (D := D) (B := B) t).run cache)) :
    (seen A out.2).card ≤ (seen A cache).card+(if t.isRight then 1 else 0) := by
  cases t with
  | inl t =>
    change out ∈ support ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) at hout
    obtain ⟨u, hu, hp⟩ := (mem_support_bind_iff _ _ _).1 hout
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst out
    simp
  | inr q => exact hash_count_le_one A q cache out hout

#print axioms hash_count_le_one
#print axioms protected_count_le

#print axioms protected_query_law

#print axioms hash_query_law
end WeightedDirectCache
end
end

/- Original module: Submissions.UpperCompressions.OracleExecutionConcentration; SHA256 f044151c41628dcd6ba788c4e6fdb07b3b4db1a31a906a31a09d4c56dc97bfed. -/
section

/-! Concentration induction over actual OracleComp stateful simulation.
The expectedValue and probability are VCVio's genuine distribution semantics,
not a newly assumed execution law. Concrete one-query drift is still required. -/

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
namespace WeightedOracleExecution

set_option maxHeartbeats 800000

variable {ι : Type} {spec : OracleSpec ι} {S α : Type}

/-- An actual stateful oracle implementation preserves a nonnegative potential
in expectation through any OracleComp program if each primitive query does so.
Free private queries need no budget or count assumption. -/
theorem expected_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ≥0∞)
    (hstep : ∀ q s, expectedValue ((impl q).run s) (fun out => Φ out.2) ≤ Φ s)
    (oa : OracleComp spec α) (s : S) :
    expectedValue ((simulateQ impl oa).run s) (fun out => Φ out.2) ≤ Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [expectedValue_bind]
    have hcont : ∀ out : spec.Range q × S,
        expectedValue ((simulateQ impl (k out.1)).run out.2) (fun out => Φ out.2) ≤ Φ out.2 :=
      fun out => ih out.1 out.2
    exact (expectedValue_mono ((impl q).run s) hcont).trans (hstep q s)

open WeightedFirstHit

variable [spec.Inhabited]

/-- Instrument the actual implementation with the checked first-hit classifier.
After stopping, dummy answers let the finite program finish while the recorded
state and clock remain fixed. No original oracle query is executed after stop. -/
def stoppedImpl (impl : QueryImpl spec (StateT S ProbComp))
    (hit kill : ℕ → S → Prop) : QueryImpl spec (StateT (StoppedState hit kill) ProbComp) :=
  fun q st => if st.status = .active then do
    let (answer, s') ← (impl q).run st.value
    return (answer, classify hit kill (st.clock+1) s')
  else pure (default, st)

@[simp] theorem stoppedImpl_run
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (q : spec.Domain) (st : StoppedState hit kill) :
    ((stoppedImpl impl hit kill) q).run st =
      if st.status = .active then (do
        let (answer, s') ← (impl q).run st.value
        return (answer, classify hit kill (st.clock+1) s'))
      else pure (default, st) := rfl

/-- Local drift is needed only on active states; stopping freezes the potential. -/
theorem expected_stopped_step_le
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (Φ : ℕ → S → ℝ≥0∞)
    (hstep : ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s) (fun out => Φ (t+1) out.2) ≤ Φ t s)
    (q : spec.Domain) (st : StoppedState hit kill) :
    expectedValue (((stoppedImpl impl hit kill) q).run st)
      (fun out => Φ out.2.clock out.2.value) ≤ Φ st.clock st.value := by
  change expectedValue (if st.status = .active then _ else _) _ ≤ _
  split_ifs with hs
  · rw [expectedValue_bind]
    simpa only [expectedValue_pure, classify_clock, classify_value] using
      hstep q st.clock st.value (st.safe hs).1 (st.safe hs).2
  · simp

/-- The stopped potential bound is now about the actual VCVio simulation law. -/
theorem expected_stopped_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (Φ : ℕ → S → ℝ≥0∞)
    (hstep : ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s) (fun out => Φ (t+1) out.2) ≤ Φ t s)
    (oa : OracleComp spec α) (s : S) :
    expectedValue ((simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s))
      (fun out => Φ out.2.clock out.2.value) ≤ Φ 0 s := by
  have hx := expected_simulate_le (stoppedImpl impl hit kill)
    (fun st => Φ st.clock st.value)
    (expected_stopped_step_le impl hit kill Φ hstep) oa (classify hit kill 0 s)
  simpa only [classify_clock, classify_value] using hx

/-- Exponential Markov for the actual finite probability semantics. -/
theorem actual_exponential_tail (oa : ProbComp α) (bad : α → Prop)
    (Z : α → ℝ) (b : ℝ) (hbad : ∀ x, bad x → b ≤ Z x)
    (hmgf : expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x))) ≤ 1) :
    Pr[bad | oa] ≤ ENNReal.ofReal (Real.exp (-b)) := by
  let c := ENNReal.ofReal (Real.exp (-b))
  have hcost (x : α) (hx : bad x) :
      1 ≤ ENNReal.ofReal (Real.exp (Z x)) * c := by
    dsimp [c]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    have he : (1:ℝ) ≤ Real.exp (Z x + -b) := by
      rw [Real.one_le_exp_iff]
      linarith [hbad x hx]
    exact_mod_cast ENNReal.ofReal_le_ofReal he
  have hp := probEvent_le_tsum_probOutput_mul_cost oa bad
    (fun x => ENNReal.ofReal (Real.exp (Z x))*c) hcost
  change Pr[bad | oa] ≤ expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x))*c) at hp
  rw [expectedValue_mul_const] at hp
  apply hp.trans
  calc
    expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x)))*c ≤ 1*c := by gcongr
    _ = c := one_mul c

/-- Actual OracleComp maximal Freedman bound under primitive-query drift.
The probability is that the instrumented concrete simulation ever records a
hit before killing. Free and paid queries are both part of the syntax; only the
caller-supplied variance proxy is charged to the paid-query budget. -/
theorem actual_stopped_freedman
    (impl : QueryImpl spec (StateT S ProbComp)) (oa : OracleComp spec α)
    (Z W : ℕ → S → ℝ) (s₀ : S) (a v J : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ0 : Z 0 s₀ = 0) (hW0 : W 0 s₀ = 0)
    (hit kill : ℕ → S → Prop)
    (hstep : ∀ θ, 0 < θ → θ*J < 3 → ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s)
        (fun out => ENNReal.ofReal (Real.exp (θ*Z (t+1) out.2-θ^2*W (t+1) out.2/(2*(1-θ*J/3))))) ≤
        ENNReal.ofReal (Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3)))))
    (hZ : ∀ t s, hit t s → a ≤ Z t s) (hW : ∀ t s, hit t s → W t s ≤ v) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
        ENNReal.ofReal (Real.exp (-a^2/(2*(v+J*a/3)))) := by
  let θ := a/(v+J*a/3)
  obtain ⟨hθ, hθJ, heq⟩ := WeightedKernel.optimized_exponent a v J ha hv hJ
  change 0 < θ at hθ
  change θ*J < 3 at hθJ
  change θ*a-θ^2*v/(2*(1-θ*J/3)) = a^2/(2*(v+J*a/3)) at heq
  let F : ℕ → S → ℝ := fun t s => θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))
  have hmgf := expected_stopped_simulate_le impl hit kill
    (fun t s => ENNReal.ofReal (Real.exp (F t s))) (hstep θ hθ hθJ) oa s₀
  have hinit : ENNReal.ofReal (Real.exp (F 0 s₀)) = 1 := by simp [F, hZ0, hW0]
  rw [hinit] at hmgf
  have hcoef : 0 ≤ θ^2/(2*(1-θ*J/3)) := by
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hbad (out : α × StoppedState hit kill) (hs : out.2.status = .hit) :
      a^2/(2*(v+J*a/3)) ≤ F out.2.clock out.2.value := by
    have hh := out.2.valid hs
    have hz := mul_le_mul_of_nonneg_left (hZ _ _ hh) hθ.le
    have hw := mul_le_mul_of_nonneg_left (hW _ _ hh) hcoef
    have heqv : θ^2*v/(2*(1-θ*J/3)) = (θ^2/(2*(1-θ*J/3)))*v := by ring
    have heqw : θ^2*W out.2.clock out.2.value/(2*(1-θ*J/3)) =
        (θ^2/(2*(1-θ*J/3)))*W out.2.clock out.2.value := by ring
    dsimp [F]
    rw [← heq, heqv, heqw]
    linarith
  have hx := actual_exponential_tail
    ((simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀))
    (fun out => out.2.status = .hit) (fun out => F out.2.clock out.2.value)
    (a^2/(2*(v+J*a/3))) hbad hmgf
  simpa only [neg_div] using hx

/-- A real-valued state quantity whose per-query increase is charged to `cost`
is bounded pathwise by the program's structural query budget. -/
theorem state_bound_of_query_budget
    (impl : QueryImpl spec (StateT S ProbComp)) (V : S → ℝ)
    (cost : spec.Domain → ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ q s out, out ∈ support ((impl q).run s) →
      V out.2 ≤ V s+c*(cost q : ℝ))
    (oa : OracleComp spec α) (B : ℕ)
    (hbudget : oa.IsQueryBound B (fun q b => cost q ≤ b) (fun q b => b-cost q))
    (s : S) (out : α × S) (hout : out ∈ support ((simulateQ impl oa).run s)) :
    V out.2 ≤ V s+c*(B:ℝ) := by
  induction oa using OracleComp.inductionOn generalizing B s out with
  | pure x =>
    have he : out = (x,s) := by simpa using hout
    subst out
    have hnonneg : 0 ≤ c*(B:ℝ) := by positivity
    exact le_add_of_nonneg_right hnonneg
  | query_bind q k ih =>
    obtain ⟨hcost, hrest⟩ := hbudget
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hout
    obtain ⟨mid, hmid, hout⟩ := hout
    have hnext := ih mid.1 (B-cost q) (hrest mid.1) mid.2 out hout
    have hlocal := hstep q s mid hmid
    have hsum : ((B-cost q : ℕ):ℝ)+(cost q:ℝ) = (B:ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hcost
    nlinarith

/-- Specialization to the protected cost model: private sampling has cost zero,
while every hash, including a cache hit, keeps its complete compression cost. -/
theorem state_bound_of_protected_budget
    {S α : Type} (impl : QueryImpl OptimalOTS.Spec (StateT S ProbComp))
    (V : S → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ q s out, out ∈ support ((impl q).run s) →
      V out.2 ≤ V s+c*(OptimalOTS.queryCost q : ℝ))
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (s : S) (out : α × S) (hout : out ∈ support ((simulateQ impl oa).run s)) :
    V out.2 ≤ V s+c*(B:ℝ) :=
  state_bound_of_query_budget impl V OptimalOTS.queryCost c hc hstep oa B hbudget s out hout

/-- An explicit early-stopping interpreter using the actual query
implementation. Its Boolean result records a hit before kill, including the
initial state and the state after the last primitive query. -/
def firstHitRun (impl : QueryImpl spec (StateT S ProbComp))
    (hit kill : ℕ → S → Prop) (oa : OracleComp spec α) : ℕ → S → ProbComp Bool :=
  OracleComp.construct
    (fun _ t s => pure (decide (hit t s)))
    (fun q _ rec t s => if hit t s then pure true else if kill t s then pure false else do
      let (answer, s') ← (impl q).run s
      rec answer (t+1) s') oa

@[simp] theorem firstHitRun_pure
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (x : α) (t : ℕ) (s : S) :
    firstHitRun impl hit kill (pure x) t s = pure (decide (hit t s)) := by
  simp [firstHitRun]

@[simp] theorem firstHitRun_query_bind
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (q : spec.Domain) (k : spec.Range q → OracleComp spec α) (t : ℕ) (s : S) :
    firstHitRun impl hit kill ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s =
      if hit t s then pure true else if kill t s then pure false else (do
        let (answer, s') ← (impl q).run s
        firstHitRun impl hit kill (k answer) (t+1) s') := by
  simp [firstHitRun]

/-- Once stopped, the remaining real OracleComp syntax is interpreted with
deterministic dummy answers, and its recorded state is exactly unchanged. -/
theorem stopped_simulate_of_stop
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (oa : OracleComp spec α) (st : StoppedState hit kill) (hstop : st.status ≠ .active) :
    (simulateQ (stoppedImpl impl hit kill) oa).run st =
      pure (evalWithAnswerFn (fun _ => default) oa, st) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change ((if st.status = .active then _ else pure (default, st)) >>= _) = _
    rw [if_neg hstop]
    simp only [pure_bind]
    rw [ih]
    congr 1

/-- The instrumented simulation's hit flag has exactly the early-interpreter
probability. This removes any assumed link between stopping and execution. -/
theorem prob_stopped_hit_eq_firstHitRun
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill t s)] =
      Pr[= true | firstHitRun impl hit kill oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure x =>
    by_cases hh : hit t s
    · simp [hh]
    · by_cases hk : kill t s <;> simp [classify, hh, hk]
  | query_bind q k ih =>
    by_cases hh : hit t s
    · rw [stopped_simulate_of_stop _ _ _ _ _ (by simp [hh])]
      simp [hh]
    · by_cases hk : kill t s
      · rw [stopped_simulate_of_stop _ _ _ _ _ (by simp [hh, hk])]
        simp [hh, hk]
      · rw [firstHitRun_query_bind, if_neg hh, if_neg hk]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp only [stoppedImpl_run, classify_status_active _ _ _ _ hh hk, if_true,
          classify_clock, classify_value]
        simp only [classify_clock, classify_value, bind_assoc, pure_bind]
        rw [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
        apply tsum_congr
        intro out
        congr 1
        exact ih out.1 (t+1) out.2

#print axioms expected_simulate_le
#print axioms expected_stopped_step_le
#print axioms expected_stopped_simulate_le
#print axioms actual_exponential_tail
#print axioms actual_stopped_freedman
#print axioms state_bound_of_query_budget
#print axioms state_bound_of_protected_budget
#print axioms stopped_simulate_of_stop
#print axioms prob_stopped_hit_eq_firstHitRun

end WeightedOracleExecution
end
end

