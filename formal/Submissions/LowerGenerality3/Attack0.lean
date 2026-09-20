import Submissions.LowerGenerality3.Support

/-!
# Attacker 0: an unconditionally accepted candidate

The attacker draws a uniform message `m`, asks for a signature on `m + 1`, and forges on `m`
with a candidate accepted on every oracle path, when one exists (`Good0`). Its success is at
least the probability of `Good0` over key generation and the uniform message.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits securityBits maxSignatureBits keygenBudget signBudget

variable (S : OracleAlgorithm.Scheme) (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic)

/-- A uniform message. -/
def uniformMsg : OracleComp Spec Message := liftM ($ᵗ BitVec msgBits : ProbComp _)

theorem run_uniformMsg (c : Cache) : run uniformMsg c = (fun m => (m, c)) <$> ($ᵗ BitVec msgBits) :=
  run_liftM _ c

theorem cost_uniformMsg : CostAtMost uniformMsg 0 := costAtMost_liftM _

/-- An unconditionally accepted candidate for `m`, if any. -/
def sel0 (pk : PublicKey) (m : Message) : OracleAlgorithm.Signature :=
  if h : Good0 S hv hd pk m then h.choose else []

theorem sel0_uncond {pk : PublicKey} {m : Message} (h : Good0 S hv hd pk m) :
    (shape S hv hd pk m (sel0 S hv hd pk m)).Uncond := by
  simp only [sel0, dif_pos h]
  exact h.choose_spec

def adv0 : OracleAlgorithm.Adversary where
  State := PublicKey × Message
  choose pk := do let m ← uniformMsg; pure (m + 1, (pk, m))
  forge st _ := pure (st.2, sel0 S hv hd st.1 st.2)

theorem experiment0_eq :
    S.weakExperiment (adv0 S hv hd) = (do
      let k ← S.keygen
      let m ← uniformMsg
      let _ ← S.sign k.2 (m + 1)
      S.verify k.1 m (sel0 S hv hd k.1 m)) := by
  unfold OracleAlgorithm.Scheme.weakExperiment adv0
  simp only [bind_assoc, pure_bind]
  congr 1
  funext k
  congr 1
  funext m
  congr 1
  funext σ
  have hdec : decide (m ≠ m + 1) = true := decide_eq_true (Ne.symm (succ_ne m))
  simp only [hdec, Bool.or_true, Bool.and_true, bind_pure]

theorem cost0 {K T : ℕ} (hk : S.KeygenCostAtMost K) (hs : S.SignCostAtMost T) :
    CostAtMost (S.weakExperiment (adv0 S hv hd)) (K + T + 1) := by
  rw [experiment0_eq]
  refine Costs.CostAtMost.bind_le hk (b₂ := T + 1) (fun k => ?_) le_rfl
  refine Costs.CostAtMost.bind_le cost_uniformMsg (b₂ := T + 1) (fun m => ?_) (by omega)
  exact Costs.CostAtMost.bind (hs k.2 (m + 1)) fun _ => hv _ _ _

/-- The success of attacker 0 is at least the mass of `Good0`. -/
theorem success0 :
    E (run S.keygen ∅) (fun k => E ($ᵗ BitVec msgBits) (fun m =>
      if Good0 S hv hd k.1.1 m then 1 else 0)) ≤ probTrue (S.weakExperiment (adv0 S hv hd)) := by
  rw [experiment0_eq, probTrue_eq_win, win_bind]
  apply E_mono
  intro k
  rw [win_bind, run_uniformMsg, E_map]
  apply E_mono
  intro m
  rw [win_bind]
  by_cases hg : Good0 S hv hd k.1.1 m
  · simp only [if_pos hg]
    calc (1 : ℝ≥0∞) = E (run (S.sign k.1.2 (m + 1)) k.2) (fun _ => (1 : ℝ≥0∞)) := (E_const _ _).symm
      _ ≤ _ := E_mono _ fun s => by
          rw [verify_eq_shape S hv hd, win_of_uncond (sel0_uncond S hv hd hg)]
  · simp only [if_neg hg]
    exact zero_le

end OptimalOTS.LowerGenerality3
