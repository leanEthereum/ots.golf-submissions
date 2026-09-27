import Submissions.UpperCompressions.LongChain91PayoffExpansion
import Submissions.UpperCompressions.LongChain91TailArithmetic
import Submissions.UpperCompressions.LongChain91SecurityClosure
import Submissions.UpperCompressions.ProofBundle12
import Submissions.UpperCompressions.LongChain91SmallMoments
import Submissions.UpperCompressions.LongChain91BudgetArithmetic
import Submissions.UpperCompressions.ProofBundle11

/-!
# Shared-clock small-budget core for the cost-91 construction

The stopped pair envelope and the authentication/post-sign clocks share one
physical query budget.  This module records the independent real and ENNReal
closure through the split `B <= 2^86 / 64`; it does not depend on the concrete
key-generation or final-game assembly.
-/

noncomputable section

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators

namespace OptimalOTS.WeightedConstruction.LongChain91SmallShared

open LongChain91SmallMoments
open WeightedRealExecution

set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

def smallRate : ℝ :=
  LongChain91BudgetArithmetic.C * (65 / 64) * (967 / 1000) *
    LongChain91BudgetArithmetic.kappa

theorem smallRate_nonneg : 0 ≤ smallRate := by
  unfold smallRate
  exact mul_nonneg
    (mul_nonneg (mul_nonneg LongChain91BudgetArithmetic.C_nonneg
      (by norm_num)) (by norm_num))
    LongChain91BudgetArithmetic.kappa_pos.le

theorem authRate_le_smallRate : kappa / 2 ≤ smallRate := by
  change LongChain91BudgetArithmetic.kappa / 2 ≤ _
  unfold smallRate LongChain91BudgetArithmetic.C
  have hk := LongChain91BudgetArithmetic.kappa_pos.le
  nlinarith

theorem postRate_le_smallRate :
    LongChain91BudgetArithmetic.postRate ≤ smallRate := by
  unfold smallRate LongChain91BudgetArithmetic.postRate
    LongChain91BudgetArithmetic.C
  have hk := LongChain91BudgetArithmetic.kappa_pos.le
  nlinarith

/-- The stopped pair process is charged at the common rate used by the
authentication and post-sign clocks.  Its covariance allowance remains
explicit for the final bad-event budget. -/
theorem small_payoff_actual {α : Type}
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : Cache) (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    realEval (run oa c) (fun out =>
      C * pairEnvelope out.2 +
        smallRate * ((B : ℝ) - (queryCount out.2 : ℝ))) ≤
      smallRate * (B : ℝ) + kappa * (B : ℝ) / 1000 := by
  have h := sharp_stopped_payoff_actual oa B hB
    (budget64_le_budget10 B hBN) c hf smallRate
  have hfactor := factor_65_of_budget64 B hBN
  have hcm :
      C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86) ≤ smallRate := by
    have h1 : C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86) ≤
        C * mean * (65 / 64) := mul_le_mul_of_nonneg_left hfactor
      (mul_nonneg LongChain91BudgetArithmetic.C_nonneg mean_nonneg)
    have h2 : C * (65 / 64) * mean ≤
        C * (65 / 64) * ((967 / 1000) * kappa) :=
      mul_le_mul_of_nonneg_left
      LongChain91Security.securityWeights_mean
      (mul_nonneg LongChain91BudgetArithmetic.C_nonneg (by norm_num))
    unfold smallRate
    nlinarith
  rw [max_eq_left hcm] at h
  simpa only [mul_comm (B : ℝ) smallRate] using h

theorem actual_small_shared_real {α : Type}
    (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : Cache) (hf : ∀ q : Query, q.1 = 342 → c q = none)
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hclock : realEval (run oa c)
        (fun out => (queryCount out.2 : ℝ)) + a + t ≤ B) :
    C * realEval (run oa c) (fun out => pairEnvelope out.2) +
        (kappa / 2) * a + LongChain91BudgetArithmetic.postRate * t +
          kappa * (B : ℝ) / 1000 ≤
      (6235189 / 6272000) * kappa * (B : ℝ) := by
  have h := small_payoff_actual oa B hB hBN c hf
  change realEval (run oa c) (fun out =>
      C * pairEnvelope out.2 +
        smallRate * ((B : ℝ) - (queryCount out.2 : ℝ))) ≤ _ at h
  rw [realEval_add, realEval_mul, realEval_mul, realEval_sub,
    realEval_const] at h
  have hshare := mul_le_mul_of_nonneg_left hclock smallRate_nonneg
  have hauth := mul_le_mul_of_nonneg_right authRate_le_smallRate ha
  have hpost := mul_le_mul_of_nonneg_right postRate_le_smallRate ht
  have hid : smallRate * (B : ℝ) + 2 * (kappa * (B : ℝ) / 1000) =
      (6235189 / 6272000) * kappa * (B : ℝ) := by
    simpa only [smallRate] using
      LongChain91BudgetArithmetic.small_coefficient_identity (B : ℝ)
  nlinarith

theorem actual_small_shared_ennreal {α : Type}
    (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : Cache) (hf : ∀ q : Query, q.1 = 342 → c q = none)
    (a t : ℝ≥0∞)
    (hclock : E (run oa c) (fun out => (queryCount out.2 : ℝ≥0∞)) + a + t ≤ B) :
    ENNReal.ofReal C * E (run oa c)
        (fun out => ENNReal.ofReal (pairEnvelope out.2)) +
      ENNReal.ofReal (kappa / 2) * a +
        ENNReal.ofReal LongChain91BudgetArithmetic.postRate * t +
      ENNReal.ofReal (kappa * (B : ℝ) / 1000) ≤
        ENNReal.ofReal ((6235189 / 6272000) * kappa * (B : ℝ)) := by
  let execution := run oa c
  let Q := realEval execution (fun out => (queryCount out.2 : ℝ))
  let P := realEval execution (fun out => pairEnvelope out.2)
  have hQ0 : 0 ≤ Q := realEval_nonneg execution _
    (fun out => Nat.cast_nonneg _)
  have hP0 : 0 ≤ P := realEval_nonneg execution _
    (fun out => pairEnvelope_nonneg out.2)
  have hQ : E execution (fun out => (queryCount out.2 : ℝ≥0∞)) =
      ENNReal.ofReal Q := by
    simpa only [ENNReal.ofReal_natCast] using
      (ofReal_realEval execution (fun out => (queryCount out.2 : ℝ))
        (fun out => Nat.cast_nonneg _)).symm
  have hP : E execution (fun out => ENNReal.ofReal (pairEnvelope out.2)) =
      ENNReal.ofReal P :=
    (ofReal_realEval execution (fun out => pairEnvelope out.2)
      (fun out => pairEnvelope_nonneg out.2)).symm
  change E execution _ + a + t ≤ B at hclock
  rw [hQ] at hclock
  have haB : a ≤ (B : ℝ≥0∞) :=
    (le_add_self.trans le_self_add).trans hclock
  have htB : t ≤ (B : ℝ≥0∞) := le_add_self.trans hclock
  have haTop : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) haB
  have htTop : t ≠ ⊤ := ne_top_of_le_ne_top (by simp) htB
  have hsum : ENNReal.ofReal Q + a ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, haTop⟩
  have hc := ENNReal.toReal_mono
    (show (B : ℝ≥0∞) ≠ ⊤ by simp) hclock
  rw [ENNReal.toReal_add hsum htTop,
    ENNReal.toReal_add ENNReal.ofReal_ne_top haTop,
    ENNReal.toReal_ofReal hQ0, ENNReal.toReal_natCast] at hc
  have hr := actual_small_shared_real oa B hB hBN c hf
    a.toReal t.toReal ENNReal.toReal_nonneg ENNReal.toReal_nonneg hc
  have hk0 : 0 ≤ kappa / 2 := div_nonneg
    LongChain91BudgetArithmetic.kappa_pos.le (by norm_num)
  have htail : 0 ≤ kappa * (B : ℝ) / 1000 :=
    div_nonneg (mul_nonneg LongChain91BudgetArithmetic.kappa_pos.le
      (Nat.cast_nonneg B)) (by norm_num)
  have hCP : 0 ≤ C * P :=
    mul_nonneg LongChain91BudgetArithmetic.C_nonneg hP0
  have hka : 0 ≤ (kappa / 2) * a.toReal :=
    mul_nonneg hk0 ENNReal.toReal_nonneg
  have hpt : 0 ≤ LongChain91BudgetArithmetic.postRate * t.toReal :=
    mul_nonneg LongChain91BudgetArithmetic.postRate_nonneg
      ENNReal.toReal_nonneg
  have he := ENNReal.ofReal_le_ofReal hr
  change ENNReal.ofReal (C * P + (kappa / 2) * a.toReal +
      LongChain91BudgetArithmetic.postRate * t.toReal +
        kappa * (B : ℝ) / 1000) ≤ _ at he
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hCP hka) hpt) htail,
    ENNReal.ofReal_add (add_nonneg hCP hka) hpt,
    ENNReal.ofReal_add hCP hka,
    ENNReal.ofReal_mul LongChain91BudgetArithmetic.C_nonneg,
    ENNReal.ofReal_mul hk0,
    ENNReal.ofReal_mul LongChain91BudgetArithmetic.postRate_nonneg,
    ENNReal.ofReal_toReal haTop, ENNReal.ofReal_toReal htTop] at he
  change ENNReal.ofReal C * E execution
      (fun out => ENNReal.ofReal (pairEnvelope out.2)) + _ + _ + _ ≤ _
  rw [hP]
  exact he

end OptimalOTS.WeightedConstruction.LongChain91SmallShared

/-!
# Small-budget actual-game closure for the cost-89 long-chain construction

The stopped pair envelope and the authentication/post-sign clocks share one
physical query budget.  The branch closes through `B <= 2^86 / 64`.
-/

/-! Small-budget numerical closure of the actual strong-forgery experiment. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
namespace OptimalOTS.WeightedConstruction.LongChain91SmallSecurity
open LongChain91 LongChain91InitialGame WeightedReplacement
open LongChain91SmallMoments WideDomains WeightedCacheCounts
open WeightedRealExecution LongChain91SmallShared
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter

variable (A : scheme.toAlgorithm.Adversary)

def smallGood (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : Prop :=
  LongChain91Empirical.Good r.2.1

def pairPayoff (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C*pairEnvelope r.2.1)

theorem choose_budget {B : ℕ} (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (pk : PublicKey) : CostAtMost (A.choose pk) B :=
  OptimalOTS.AlgorithmCosts.CostAtMost.mono (choose_reserved_budget A hB pk).2 ((Nat.sub_le _ _).trans (Nat.sub_le _ _))

theorem choose_shared_clock {B : ℕ} (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (pk : PublicKey) :
    E (run (A.choose pk) ∅) (fun p => (queryCount p.2:ℝ≥0∞))+
      expectedCharge (otherPaid (isIndexLength 342)) (A.choose pk) ∅+
      E (runRemaining (A.choose pk) ∅ (B-1101)) (postRemaining A pk) ≤ B := by
  have h := (add_le_add (distinct_other_le_expected_paid (A.choose pk) ∅ (fun _ _ => rfl))
    (le_refl (E (runRemaining (A.choose pk) ∅ (B-1101)) (postRemaining A pk)))).trans
      (choose_spent_post_remaining_le A hB pk)
  exact h.trans (by exact_mod_cast ((Nat.sub_le (B-1101) signBudget).trans (Nat.sub_le B 1101)))

theorem hazard_le_pair (B : ℕ) :
    weightedClock A B (gatedHazard A (smallGood A)) ≤ weightedClock A B (pairPayoff A) := by
  apply Finset.sum_le_sum
  intro pk hpk
  apply mul_le_mul_right
  apply E_mono
  intro r
  by_cases hg : smallGood A pk r
  · rw [gatedHazard,if_pos hg,pairPayoff]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (hazard_le_pairEnvelope r.1.1 r.2.1)
      LongChain91BudgetArithmetic.C_nonneg
  · rw [gatedHazard,if_neg hg]
    exact bot_le

theorem bad_gate_bound (B : ℕ) :
    weightedClock A B (badGate A (smallGood A)) ≤ ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have ht (pk : PublicKey) :
      E (runRemaining (A.choose pk) ∅ (B-1101)) (badGate A (smallGood A) pk) ≤
        ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
    have h := LongChain91Empirical.terminal_bad (A.choose pk) ∅ (fun _ _ => rfl)
    change Pr[fun out => ¬LongChain91Empirical.Good out.2 | run (A.choose pk) ∅] ≤ _ at h
    rw [← expectedValue_ite_one] at h
    change E (run (A.choose pk) ∅) _ ≤ _ at h
    rw [← runRemaining_project (A.choose pk) ∅ (B-1101),E_map] at h
    convert h using 1
    congr 1
    funext r
    unfold badGate smallGood
    by_cases hg : LongChain91Empirical.Good r.2.1 <;> simp only [hg,not_true_eq_false,not_false_eq_true,if_true,if_false]
  calc
    _ ≤ ∑ pk : PublicKey,sumW (fiberA pk)*ENNReal.ofReal (((2:ℝ)^512)⁻¹) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul_right (ht pk) _
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

theorem small_core_bound {B : ℕ} (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (hBN : (B:ℝ) ≤ (2:ℝ)^86/64) :
    preAuth A+weightedClock A B (pairPayoff A)+
      ENNReal.ofReal LongChain91BudgetArithmetic.postRate*
        weightedClock A B (postRemaining A)+
      ENNReal.ofReal (kappa*(B:ℝ)/1000) ≤
        ENNReal.ofReal ((6235189:ℝ)/6272000*kappa*(B:ℝ)) := by
  have hp (pk : PublicKey) := actual_small_shared_ennreal (A.choose pk) B
    (choose_budget A hB pk) hBN ∅ (fun _ _ => rfl)
    (expectedCharge (otherPaid (isIndexLength 342)) (A.choose pk) ∅)
    (E (runRemaining (A.choose pk) ∅ (B-1101)) (postRemaining A pk))
    (choose_shared_clock A hB pk)
  have hpair (pk : PublicKey) :
      E (runRemaining (A.choose pk) ∅ (B-1101)) (pairPayoff A pk)=
        ENNReal.ofReal C*E (run (A.choose pk) ∅) (fun p => ENNReal.ofReal (pairEnvelope p.2)) := by
    rw [E_const_mul]
    have h := runRemaining_project (A.choose pk) ∅ (B-1101)
    rw [← h,E_map]
    congr 1
    funext r
    exact ENNReal.ofReal_mul LongChain91BudgetArithmetic.C_nonneg
  have hs : (∑ pk : PublicKey,sumW (fiberA pk)*
      (E (runRemaining (A.choose pk) ∅ (B-1101)) (pairPayoff A pk)+
        ENNReal.ofReal (kappa/2)*expectedCharge (otherPaid (isIndexLength 342)) (A.choose pk) ∅+
        ENNReal.ofReal LongChain91BudgetArithmetic.postRate*
          E (runRemaining (A.choose pk) ∅ (B-1101)) (postRemaining A pk)+
        ENNReal.ofReal (kappa*(B:ℝ)/1000))) ≤
      ENNReal.ofReal ((6235189:ℝ)/6272000*kappa*(B:ℝ)) := by
    calc
      _ ≤ ∑ pk : PublicKey,sumW (fiberA pk)*
          ENNReal.ofReal ((6235189:ℝ)/6272000*kappa*(B:ℝ)) := by
        apply Finset.sum_le_sum
        intro pk hpk
        apply mul_le_mul_right
        rw [hpair]
        exact hp pk
      _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]
  convert hs using 1
  unfold preAuth weightedClock
  rw [authRate_ofReal]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,sum_fiber_weights,one_mul,Finset.mul_sum]
  congr 2
  · rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro pk hpk
    rw [show msgBits+86=342 from rfl]
    ring
  · apply Finset.sum_congr rfl
    intro pk hpk
    ring

/-- Actual strong-success bound with every probabilistic premise discharged. -/
theorem actual_small_security {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (hBN : (B:ℝ) ≤ (2:ℝ)^86/64) (hcap : (B:ℝ) ≤ (2:ℝ)^127) :
    E (run (scheme.toAlgorithm.experiment A) ∅) successValue ≤
      ENNReal.ofReal ((6235189:ℝ)/6272000*kappa*(B:ℝ)) := by
  have hex := global_actual_payoff_expanded A hB (smallGood A) (fun _ _ h => h)
  have hbad := bad_gate_bound A B
  have hh := hazard_le_pair A B
  have he := LongChain91TailArithmetic.completion_exception_margin_ennreal B
    (keygen_remaining A hB).1 hcap
  have hbad_dominated : ENNReal.ofReal (((2 : ℝ)^512)⁻¹) ≤
      (2 : ℝ≥0∞)⁻¹^334 := by
    have hr : ((2 : ℝ)^512)⁻¹ ≤ ((2 : ℝ)^334)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) (by decide)
    have hh := ENNReal.ofReal_le_ofReal hr
    calc
      _ ≤ ENNReal.ofReal (((2 : ℝ)^334)⁻¹) := hh
      _ = _ := by
        rw [ENNReal.ofReal_inv_of_pos
            (by positivity : (0 : ℝ) < (2 : ℝ)^334),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat]
        simpa only [ENNReal.inv_pow]
  have herr : weightedClock A B (badGate A (smallGood A))+
      (1+(B:ℝ≥0∞))*(2:ℝ≥0∞)⁻¹^760 ≤ ENNReal.ofReal (kappa*(B:ℝ)/1000) := by
    apply (add_le_add hbad le_rfl).trans
    exact (add_le_add hbad_dominated le_rfl).trans he
  have hm := add_le_add
    (add_le_add (add_le_add (le_refl (preAuth A)) hh)
      (le_refl (ENNReal.ofReal LongChain91BudgetArithmetic.postRate*
        weightedClock A B (postRemaining A)))) herr
  have hc := small_core_bound A hB hBN
  rw [add_assoc (preAuth A + weightedClock A B (gatedHazard A (smallGood A)) +
    ENNReal.ofReal LongChain91BudgetArithmetic.postRate*
      weightedClock A B (postRemaining A))] at hex
  exact hex.trans (hm.trans hc)

end OptimalOTS.WeightedConstruction.LongChain91SmallSecurity
end
