import Submissions.UpperCompressions.LongChain91AuthConditional
import Submissions.UpperCompressions.LongChain91Continuation
import Submissions.UpperCompressions.ProofBundle09

/-!
# Actual initial game for the cost-87 long-chain construction

This is the concrete adaptive choose/sign/forge reduction.  It preserves the
actual shared cache and the exact remaining query clock while averaging over
the finite key-generation records.
-/

section

/-! Actual chain18 keygen and adaptive message-choice decomposition. The
reduced choose run starts with an empty public cache; hidden graph points are
removed by the checked identical-until-bad coupling. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.LongChain91InitialGame
open OptimalOTS.Dag LongChain91 LongChain91.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter CostAtMost
variable (A : scheme.toAlgorithm.Adversary)

def afterChoose (pk : PublicKey) (sk : scheme.graph.Assignment) (x : Message × A.State) : OracleComp Spec Bool :=
  scheme.sign sk x.1 >>= stB A pk x.1 x.2

def afterKeygen (p : PublicKey × scheme.graph.Assignment) : OracleComp Spec Bool :=
  A.choose p.1 >>= afterChoose A p.1 p.2

theorem experiment_eq : scheme.toAlgorithm.experiment A =
    scheme.keygen >>= afterKeygen A := by
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

theorem publicKey_record (ξ : Rec) : scheme.publicKey (graph.evalRec ξ) = pkOf ξ := by
  change lowPk (graph.evalRec ξ graph.root) = lowPk (ξ.2 rh.fin)
  rw [← val_rh ξ]
  unfold val
  exact (lowPk_cast_eq (graph_len_fin rh) (graph.evalRec ξ rh.fin)).symm

theorem E_keygen (F : (PublicKey × scheme.graph.Assignment) × Cache → ℝ≥0∞) :
    E (run scheme.keygen ∅) F = ∑ ξ : Rec, w*F ((pkOf ξ,graph.evalRec ξ),kc ξ) := by
  rw [WeightedScheme.Scheme.keygen, GraphKeygenBridge.E_run_keygen scheme.graph scheme.publicKey tagging F]
  change (∑ ξ : Rec, w*F ((scheme.publicKey (graph.evalRec ξ),graph.evalRec ξ),kc ξ)) = _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [publicKey_record]

theorem E_experiment (F : Bool × Cache → ℝ≥0∞) :
    E (run (scheme.toAlgorithm.experiment A) ∅) F =
      ∑ ξ : Rec, w*E (run (afterKeygen A (pkOf ξ,graph.evalRec ξ)) (kc ξ)) F := by
  rw [experiment_eq,run_bind,E_bind,E_keygen]

theorem keygen_remaining {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B) :
    865 ≤ B ∧ ∀ ξ : Rec,
      CostAtMost (afterKeygen A (pkOf ξ,graph.evalRec ξ)) (B-865) := by
  rw [experiment_eq,WeightedScheme.Scheme.keygen] at hB
  obtain ⟨hc,hr⟩ := GraphKeygenBridge.costAtMost_keygen_bind scheme.graph scheme.publicKey (afterKeygen A) hB
  rw [scheme_keygenCost] at hc hr
  refine ⟨hc,fun ξ => ?_⟩
  have hh := hr ξ
  change CostAtMost (afterKeygen A (scheme.publicKey (graph.evalRec ξ),graph.evalRec ξ)) (B-865) at hh
  rwa [publicKey_record] at hh

theorem afterChoose_loop (pk : PublicKey) (ξ : Rec) (x : Message × A.State) :
    afterChoose A pk (graph.evalRec ξ) x =
      loop 86 signedDecode signedTier x.1 signBudget >>=
        fun r => stB A pk x.1 x.2 (signatureFromWinner ξ r) := by
  unfold afterChoose WeightedScheme.Scheme.sign
  rw [bind_map_left]
  rfl

theorem afterChoose_extend (pk : PublicKey) (ξ : Rec) (x : Message × A.State) (d : Cache) :
    E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue =
      E (run (loop 86 signedDecode signedTier x.1 signBudget) d)
        (fun p => E (run (stB A pk x.1 x.2 (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (kc ξ))) successValue) := by
  rw [afterChoose_loop,run_bind,run_loop_extend 86 signedDecode signedTier x.1 (kc ξ) (fun η => kc_enc ξ (x.1,η)) signBudget d,
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

end OptimalOTS.WeightedConstruction.LongChain91InitialGame
end
end

section

/-! The reduced actual sign/post continuation as the full-table expectation
used by the signed/no-sign conditional master. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.LongChain91InitialGame
open OptimalOTS.Dag LongChain91 LongChain91.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter graph CostAtMost
variable (A : scheme.toAlgorithm.Adversary)

theorem kc_indexLength_none (ξ : Rec) (q : Query) (hq : q.1 = msgBits+86) : kc ξ q = none := by
  cases hc : kc ξ q with
  | none => rfl
  | some u =>
    obtain ⟨h,p,hp,he,_⟩ := (kc_apply_iff ξ q u).mp hc
    exact False.elim (len_hashParent_ne_enc hp ((congrArg Sigma.fst he).symm.trans hq))

theorem afterChoose_eager (pk : PublicKey) (ξ : Rec) (x : Message × A.State) (d : Cache) :
    E (run (afterChoose A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) successValue =
      E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
        E (run (loop 86 signedDecode signedTier x.1 signBudget)
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
        E (run (loop 86 signedDecode signedTier x.1 signBudget)
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

end OptimalOTS.WeightedConstruction.LongChain91InitialGame
end
end

section

/-! Pathwise budgets for the actual reduced adaptive choose run and all-L
signer. Only supported actual signer outcomes need continuation budgets. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace OptimalOTS.WeightedConstruction.LongChain91InitialGame
open OptimalOTS.Dag LongChain91 LongChain91.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter graph CostAtMost
variable (A : scheme.toAlgorithm.Adversary)

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
        p ∈ support (run (loop 86 signedDecode signedTier r.1.1 signBudget) c) →
        CostAtMost (stBWithForgery A pk r.1.1 r.1.2 (signatureFromWinner ξ p.1)) (r.2.2-signBudget) := by
  obtain ⟨hle,hk⟩ := choose_remaining_support A pk b hB r hr
  have hres (ξ : Rec) (hξ : ξ ∈ fiberA pk) := actual_loop_reserve 86
    signedDecode signedTier r.1.1 index86_cost signBudget
    (fun s => stB A pk r.1.1 r.1.2 (signatureFromWinner ξ s)) r.2.2
    (by rw [← afterChoose_loop]; exact hk ξ hξ)
  obtain ⟨ξ₀,hξ₀⟩ := fiber_nonempty pk
  refine ⟨(hres ξ₀ hξ₀).1,hle,?_⟩
  intro ξ hξ c p hp
  have hh := (hres ξ hξ).2 c p hp
  rw [← stBWithForgery_map] at hh
  exact (AlgorithmCosts.costAtMost_map_iff _ _ _).1 hh

theorem experiment_choose_reserve {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-865))) :
    signBudget ≤ r.2.2 ∧ r.2.2 ≤ B-865 ∧
      ∀ ξ ∈ fiberA pk, ∀ c p,
        p ∈ support (run (loop 86 signedDecode signedTier r.1.1 signBudget) c) →
        CostAtMost (stBWithForgery A pk r.1.1 r.1.2 (signatureFromWinner ξ p.1)) (r.2.2-signBudget) :=
  choose_supported_sign_reserve A pk (B-865) (fun ξ _ => (keygen_remaining A hB).2 ξ) r hr

end OptimalOTS.WeightedConstruction.LongChain91InitialGame
end
end

section

/-! Sharp initial authentication accounting: the surviving pre-sign Spr term
is absorbed together with the stageA hit event exactly once. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.LongChain91InitialGame
open OptimalOTS.Dag LongChain91 LongChain91.Name WeightedReplacement
attribute [local irreducible] Finset.univ Finset.filter
variable (A : scheme.toAlgorithm.Adversary)

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
    E (run (scheme.toAlgorithm.experiment A) ∅) successValue ≤
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
    E (run (scheme.toAlgorithm.experiment A) ∅) successValue ≤
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
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : LongChain91.EncInput, q=LongChain91.encQuery u)
    (payoff : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞)
    (hpay : ∀ pk r, r ∈ support (runRemaining (A.choose pk) ∅ b) →
      conditional A pk r.1 r.2.1 ≤ survivingSpr pk r.2.1 + payoff pk r) :
    E (run (scheme.toAlgorithm.experiment A) ∅) successValue ≤
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

end OptimalOTS.WeightedConstruction.LongChain91InitialGame
end
end

section

/-! The actual complete chain18 experiment reduces to physical pre-sign-cache
replay and excess payoffs, with the genuine remaining-budget clock. There are
no assumed posterior, security, or conditional-game bounds in this theorem. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.LongChain91
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling LongChain91InitialGame
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

theorem signerAverage_eq_actual (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → ℝ≥0∞) :
    signerAverage m c k F = outE (loop 86 signedDecode signedTier m k) c F :=
  (outE_length_preload (msgBits+86) (loop 86 signedDecode signedTier m k) c F).symm

theorem conditional_eq_game (A : scheme.toAlgorithm.Adversary) (pk : PublicKey)
    (m : Message) (st : A.State) (c : Cache) :
    conditional A pk (m,st) c =
      conditionalGame A ((fiberA pk).filter (fun ξ => ¬ Cache.Hits c (kc ξ))) m st c signBudget := by
  rw [conditional_eager]
  unfold conditionalGame outcomeSuccessLoss
  apply Finset.sum_congr rfl
  intro ξ hξ
  have hpk := pkOf_of_subset_fiberA (Finset.filter_subset _ _) ξ hξ
  rw [hpk]

theorem conditional_actual_master (A : scheme.toAlgorithm.Adversary) (pk : PublicKey)
    (m : Message) (st : A.State) (c : Cache) (B : ℕ)
    (hB : SupportedPostBudget A pk m st c signBudget B) :
    conditional A pk (m,st) c ≤ survivingSpr pk c + sumW (fiberA pk) *
      (signerAverage m c signBudget (winnerReplay c m) +
        B*(authRate+signerAverage m c signBudget winnerExcess)) := by
  rw [conditional_eq_game]
  exact conditional_game_master A pk _ (Finset.filter_subset _ _) m st c signBudget B
    (fun ξ hξ => (Finset.mem_filter.mp hξ).2) hB

theorem supportedPostBudget_of_experiment (A : scheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B) (pk : PublicKey)
    (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-865))) :
    SupportedPostBudget A pk r.1.1 r.1.2 r.2.1 signBudget (r.2.2-signBudget) := by
  intro ξ hξ g p hp
  have h := (experiment_choose_reserve A hB pk r hr).2.2 ξ hξ _ p hp
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
  simpa only [hpk] using h

end OptimalOTS.WeightedConstruction.LongChain91
end
end

section

/-! Preserve the actual conditional success cap before expanding empirical
payoffs. A combined Good/large-deviation exception is therefore paid once. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.LongChain91
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling LongChain91InitialGame
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

theorem conditional_le_fiber (A : scheme.toAlgorithm.Adversary) (pk : PublicKey)
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

def gatedContinuationPayoff (A : scheme.toAlgorithm.Adversary)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  sumW (fiberA pk) * (if good pk r then
    signerAverage r.1.1 r.2.1 signBudget (winnerReplay r.2.1 r.1.1) +
      (r.2.2-signBudget : ℕ)*(authRate+signerAverage r.1.1 r.2.1 signBudget winnerExcess)
    else 1)

theorem conditional_supported_gated (A : scheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ)
    (hr : r ∈ support (runRemaining (A.choose pk) ∅ (B-865))) :
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
theorem global_actual_game_payoff_gated (A : scheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop) :
    E (run (scheme.toAlgorithm.experiment A) ∅) successValue ≤
      (∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅) +
      ∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ (B-865))
        (gatedContinuationPayoff A good pk) := by
  apply global_payoff_clock A (B-865) (isIndexLength (msgBits+86))
    (fun q hq => exists_encQuery_of_length q hq) (gatedContinuationPayoff A good)
  exact conditional_supported_gated A hB good

end OptimalOTS.WeightedConstruction.LongChain91
end
end
