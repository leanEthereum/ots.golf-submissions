import Submissions.UpperCompressions.LongChain91PayoffExpansion
import Submissions.UpperCompressions.LongChain91SmallShared
import Submissions.UpperCompressions.LongChain91TailArithmetic
import Submissions.UpperCompressions.LongChain91SecurityClosure
import Submissions.UpperCompressions.ProofBundle12

/-!
# Small-budget actual-game closure for the cost-90 long-chain construction

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
      E (runRemaining (A.choose pk) ∅ (B-1087)) (postRemaining A pk) ≤ B := by
  have h := (add_le_add (distinct_other_le_expected_paid (A.choose pk) ∅ (fun _ _ => rfl))
    (le_refl (E (runRemaining (A.choose pk) ∅ (B-1087)) (postRemaining A pk)))).trans
      (choose_spent_post_remaining_le A hB pk)
  exact h.trans (by exact_mod_cast ((Nat.sub_le (B-1087) signBudget).trans (Nat.sub_le B 1087)))

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
      E (runRemaining (A.choose pk) ∅ (B-1087)) (badGate A (smallGood A) pk) ≤
        ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
    have h := LongChain91Empirical.terminal_bad (A.choose pk) ∅ (fun _ _ => rfl)
    change Pr[fun out => ¬LongChain91Empirical.Good out.2 | run (A.choose pk) ∅] ≤ _ at h
    rw [← expectedValue_ite_one] at h
    change E (run (A.choose pk) ∅) _ ≤ _ at h
    rw [← runRemaining_project (A.choose pk) ∅ (B-1087),E_map] at h
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
    (E (runRemaining (A.choose pk) ∅ (B-1087)) (postRemaining A pk))
    (choose_shared_clock A hB pk)
  have hpair (pk : PublicKey) :
      E (runRemaining (A.choose pk) ∅ (B-1087)) (pairPayoff A pk)=
        ENNReal.ofReal C*E (run (A.choose pk) ∅) (fun p => ENNReal.ofReal (pairEnvelope p.2)) := by
    rw [E_const_mul]
    have h := runRemaining_project (A.choose pk) ∅ (B-1087)
    rw [← h,E_map]
    congr 1
    funext r
    exact ENNReal.ofReal_mul LongChain91BudgetArithmetic.C_nonneg
  have hs : (∑ pk : PublicKey,sumW (fiberA pk)*
      (E (runRemaining (A.choose pk) ∅ (B-1087)) (pairPayoff A pk)+
        ENNReal.ofReal (kappa/2)*expectedCharge (otherPaid (isIndexLength 342)) (A.choose pk) ∅+
        ENNReal.ofReal LongChain91BudgetArithmetic.postRate*
          E (runRemaining (A.choose pk) ∅ (B-1087)) (postRemaining A pk)+
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

#print axioms actual_small_security
#print axioms choose_shared_clock
#print axioms bad_gate_bound
#print axioms small_core_bound
end OptimalOTS.WeightedConstruction.LongChain91SmallSecurity
end
