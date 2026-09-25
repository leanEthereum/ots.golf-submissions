import Submissions.LowerGenerality2.PatternAttack
import Submissions.LowerGenerality2.PatternGoods
import Submissions.LowerGenerality2.PatternHelpers

/-! Assembly of the bare-oracle forgery attack from support and probability bounds. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.PatternAttack

open OptimalOTS.Dag


open BareLower

variable (S : Scheme)

attribute [local irreducible] signIdx signIdxLoop Scheme.sign Scheme.signLoop
  weakExperiment forge adversary Graph.encode Scheme.hashPattern Scheme.samePattern goodIndices

/-- The continuation after the signer has selected its nonce and disclosure index. -/
def afterSign (T : ℕ) (pk : PublicKey) (x : S.graph.Assignment)
    (m : Message) (r : Option (Nonce × Fin numCuts)) :
    OracleComp Spec Bool := do
  let σ := r.map fun p => (p.1, S.graph.encode (S.sets p.2) x)
  let out ← forge S T m σ
  let ok ← S.verify pk out.1 out.2
  return ok && (σ.isNone || decide (out.1 ≠ m))

theorem experiment_eq (T : ℕ) :
    weakExperiment S (adversary S T) = (do
      let (pk,x) ← S.keygen
      let m ← sampleBits msgBits
      let r ← signIdx m
      afterSign S T pk x m r) := by
  simp only [weakExperiment, adversary, sign_eq_map, afterSign,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

theorem afterSign_some (T : ℕ) (x : S.graph.Assignment) (m : Message)
    (η : Nonce) (i : Fin numCuts) :
    afterSign S T (S.publicKey x) x m (some (η,i)) =
      forge S T m (some (η,S.graph.encode (S.sets i) x)) >>= check S (S.publicKey x) m := by
  simp only [afterSign, Option.map_some, Option.isNone_some, Bool.false_or, check]
  rfl

theorem signed_stage_ge (hcost : ∀ i, S.verifyCost i ≤ 17)
    (x : S.graph.Assignment) (c : Cache) (hc : S.graph.CacheConsistent x c)
    (D : Finset Query) (hD : HasSupport c D) (hcard : D.card ≤ 1024)
    (m : Message) (hfresh : FreshMessage c m) :
    (1 / 20 : ℝ≥0∞) ≤ E (run (signIdx m) c)
      (fun p => E (run (afterSign S (2 ^ 122) (S.publicKey x) x m p.1) p.2) win) := by
  have hsign := FreshSign.paper_reward_ge_half (goodIndices S) (goodIndices_lt S)
    (card_goodIndices S hcost) m c hfresh
  have hstage : E (run (signIdx m) c)
      (fun p => FreshSign.reward (goodIndices S) p.1) * (1 / 10) ≤
      E (run (signIdx m) c)
        (fun p => E (run (afterSign S (2 ^ 122) (S.publicKey x) x m p.1) p.2) win) := by
    rw [← expectedValue_mul_const]
    apply expectedValue_mono_of_support
    intro p hp
    obtain ⟨hsub, _, hidx⟩ := signIdx_support m c p hp
    obtain ⟨D', hD', hcard'⟩ := exists_support_run (signIdx m)
      (cost_signIdx S (by decide) m) hD p hp
    have hcard'' : D'.card ≤ 2 ^ 22 := by
      change D'.card ≤ D.card + 2 ^ 20 at hcard'
      omega
    cases hr : p.1 with
    | none => simp only [FreshSign.reward, hr, zero_mul, zero_le]
    | some r =>
      obtain ⟨η,i⟩ := r
      by_cases hi : i.val ∈ goodIndices S
      · simp only [FreshSign.reward, hr, if_pos hi, one_mul, afterSign_some]
        obtain ⟨w, hw, hwi⟩ := hidx η i hr
        exact forge_success_ge S i x p.2 (Graph.CacheConsistent.mono _ hsub hc)
          ((mem_goodIndices S i).mp hi) D' hD' hcard'' m η w hw hwi
      · simp only [FreshSign.reward, hr, if_neg hi, zero_mul, zero_le]
  calc
    (1 / 20 : ℝ≥0∞) = (1 / 2) * (1 / 10) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
    _ ≤ _ := (mul_le_mul' hsign le_rfl).trans hstage

theorem choose_stage_ge (hcost : ∀ i, S.verifyCost i ≤ 17)
    (x : S.graph.Assignment) (c : Cache) (hc : S.graph.CacheConsistent x c)
    (D : Finset Query) (hD : HasSupport c D) (hcard : D.card ≤ 1024) :
    (9 / 200 : ℝ≥0∞) ≤ E ($ᵗ BitVec msgBits) (fun m =>
      E (run (signIdx m) c)
        (fun p => E (run (afterSign S (2 ^ 122) (S.publicKey x) x m p.1) p.2) win)) := by
  have hmass := fresh_mass_paper hD (hcard.trans (by norm_num : 1024 ≤ 2 ^ 22))
  have h := expectedValue_ge_indicator ($ᵗ BitVec msgBits) (FreshMessage c)
    (fun m => E (run (signIdx m) c)
      (fun p => E (run (afterSign S (2 ^ 122) (S.publicKey x) x m p.1) p.2) win))
    (1 / 20) (fun m _ hm => signed_stage_ge S hcost x c hc D hD hcard m hm)
  calc
    (9 / 200 : ℝ≥0∞) = (9 / 10) * (1 / 20) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
    _ ≤ _ := (mul_le_mul' hmass le_rfl).trans h

theorem success_ge (hcost : ∀ i, S.verifyCost i ≤ 17) :
    (9 / 200 : ℝ≥0∞) ≤ probTrue (weakExperiment S (adversary S (2 ^ 122))) := by
  rw [probTrue_eq_expectation, experiment_eq, run_bind, E_bind]
  change (9 / 200 : ℝ≥0∞) ≤ E (run S.keygen ∅) _
  rw [← expectedValue_const (mx := run S.keygen ∅) (by simp)
    (9 / 200 : ℝ≥0∞)]
  apply expectedValue_mono_of_support
  intro p hp
  obtain ⟨hpk, hc⟩ := S.keygen_cacheConsistent ∅ p hp
  obtain ⟨D, hD, hcard⟩ := exists_support_run_empty S.costAtMost_keygen p hp
  change D.card ≤ 1024 at hcard
  rcases p with ⟨⟨pk,x⟩,c⟩
  dsimp only at hpk hc hD hcard ⊢
  subst hpk
  rw [run_bind, E_bind, sampleBits, run_liftM, E_map]
  simp only [run_bind, E_bind]
  exact choose_stage_ge S hcost x c hc D hD hcard

/-- The elementary pattern attack already beats the required security threshold. -/
theorem budget_lt :
    ((keygenBudget + trials + 2 ^ 122 + 2 * 16 + 2 : ℕ) : ℝ≥0∞) /
      2 ^ securityBits < 9 / 200 := by
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, hashBits, blockBits, pkBits, msgBits, securityBits, maxSignatureBits, keygenBudget, signBudget, nonceBits, idxBits, numCuts, trials, idxCost, blockCost, signBudget, msgBits, blockBits]

end OptimalOTS.PatternAttack
