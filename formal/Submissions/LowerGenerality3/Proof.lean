import Submissions.LowerGenerality3.ZeroQuery
import Submissions.LowerGenerality3.WeakSecurity

/-! Under the paper's resource and availability limits, no correct, weakly secure algorithm
can verify every input at zero query cost. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

variable (S : OracleAlgorithm.Scheme)

def rejection (pk : PublicKey) (m : Message) (σ : OracleAlgorithm.Signature) : ℝ≥0∞ :=
  Pr[= false | freeRun (S.verify pk m σ)]

/-- Some signature is accepted with probability one under the cache-free simulator. -/
def Good (pk : PublicKey) (m : Message) : Prop := ∃ σ, rejection S pk m σ = 0

/-- Public, noncomputable signature selection; deterministic computation is free in this model. -/
def selected [Nonempty OracleAlgorithm.Signature] (pk : PublicKey) (m : Message) : OracleAlgorithm.Signature :=
  if h : Good S pk m then h.choose else Classical.choice inferInstance

theorem selected_accepts [Nonempty OracleAlgorithm.Signature] (pk : PublicKey) (m : Message)
    (h : Good S pk m) : Pr[= true | freeRun (S.verify pk m (selected S pk m))] = 1 := by
  have hb : rejection S pk m (selected S pk m) = 0 := by
    simp only [selected, dif_pos h]
    exact h.choose_spec
  have hs := probOutput_true_add_false (freeRun (S.verify pk m (selected S pk m)))
  change Pr[= false | freeRun (S.verify pk m (selected S pk m))] = 0 at hb
  simpa [hb] using hs

theorem win_not_zero (oa : OracleComp Spec Bool) (h : CostAtMost oa 0) (c : Cache) :
    win (do let b ← oa; pure (!b)) c = Pr[= false | freeRun oa] := by
  rw [bind_pure_comp]
  rw [win_zero _ (Costs.CostAtMost.map h _)]
  simp [freeRun]

theorem correct_expanded (hc : S.Correct) (hz : S.VerifyCostAtMost 0) (m : Message) :
    E (run S.keygen ∅) (fun k => E (run (S.sign k.1.2 m) k.2) (fun s =>
      match s.1 with | none => 0 | some σ => rejection S k.1.1 m σ)) = 0 := by
  have h := hc (fun _ => m)
  rw [probTrue_eq_win, win_bind] at h
  convert h using 1
  apply congrArg (E (run S.keygen ∅))
  funext k
  rw [win_bind]
  apply congrArg (E (run (S.sign k.1.2 m) k.2))
  funext s
  cases hs : s.1 with
  | none => simp [win_pure]
  | some σ => simpa [hs, rejection] using (win_not_zero (S.verify k.1.1 m σ) (hz _ _ _) s.2).symm

theorem failure_expanded {ε : ℝ≥0∞} (ha : S.SigningFailureAtMost ε) (m : Message) :
    E (run S.keygen ∅) (fun k => E (run (S.sign k.1.2 m) k.2)
      (fun s => if s.1.isNone then 1 else 0)) ≤ ε := by
  have h := ha (fun _ => m)
  simpa only [probTrue_eq_win, win_bind, win_pure] using h

theorem signature_nonempty {ε : ℝ≥0∞} (ha : S.SigningFailureAtMost ε) (hε : ε < 1)
    (m : Message) : Nonempty OracleAlgorithm.Signature := by
  by_contra hn
  have hn' : ∀ σ : Option OracleAlgorithm.Signature, σ.isNone = true := by
    intro σ
    cases σ with
    | none => rfl
    | some σ => exact (hn ⟨σ⟩).elim
  have h := failure_expanded S ha m
  simp only [hn', if_true, E_const] at h
  exact (not_lt_of_ge h) hε

theorem good_of_honest (hc : S.Correct) (hz : S.VerifyCostAtMost 0) (m : Message)
    (k : (PublicKey × S.SecretKey) × Cache) (hk : k ∈ support (run S.keygen ∅))
    (σ : OracleAlgorithm.Signature) (c : Cache) (hs : (some σ, c) ∈ support (run (S.sign k.1.2 m) k.2)) :
    Good S k.1.1 m := by
  have h := E_eq_zero_on_support _ _ (correct_expanded S hc hz m) hk
  exact ⟨σ, E_eq_zero_on_support _ _ h hs⟩

theorem good_mass {ε : ℝ≥0∞} (hc : S.Correct) (hz : S.VerifyCostAtMost 0)
    (ha : S.SigningFailureAtMost ε) (m : Message) :
    1 ≤ ε + E (run S.keygen ∅) (fun k => if Good S k.1.1 m then 1 else 0) := by
  have hpoint : ∀ k ∈ support (run S.keygen ∅),
      (1 : ℝ≥0∞) ≤ E (run (S.sign k.1.2 m) k.2) (fun s => if s.1.isNone then 1 else 0) +
        (if Good S k.1.1 m then 1 else 0) := by
    intro k hk
    have h := expectedValue_mono_of_support (mx := run (S.sign k.1.2 m) k.2)
      (g := fun _ => (1 : ℝ≥0∞))
      (h := fun s => (if s.1.isNone then 1 else 0) + (if Good S k.1.1 m then 1 else 0)) ?_
    · simpa only [E_const, expectedValue_add] using h
    · intro s hs
      rcases s with ⟨σ, c⟩
      cases σ with
      | none => simp
      | some σ => simp [good_of_honest S hc hz m k hk σ c hs]
  have h := expectedValue_mono_of_support hpoint
  simp only [E_const, expectedValue_add] at h
  exact h.trans (add_le_add (failure_expanded S ha m) le_rfl)

/-- Ignore the requested signature and use public data to select a forgery on `m₁`.
For a good public key it is accepted with probability one. -/
def adversary [Nonempty OracleAlgorithm.Signature] (m₀ m₁ : Message) : OracleAlgorithm.Adversary where
  State := PublicKey
  choose pk := pure (m₀, pk)
  forge pk _ := pure (m₁, selected S pk m₁)

theorem experiment_eq [Nonempty OracleAlgorithm.Signature] (m₀ m₁ : Message) (hm : m₀ ≠ m₁) :
    S.weakExperiment (adversary S m₀ m₁) = (do
      let k ← S.keygen
      let _ ← S.sign k.2 m₀
      S.verify k.1 m₁ (selected S k.1 m₁)) := by
  unfold OracleAlgorithm.Scheme.weakExperiment adversary
  simp only [pure_bind]
  congr 1
  funext k
  congr 1
  funext σ
  simp [Ne.symm hm]

theorem attack_cost [Nonempty OracleAlgorithm.Signature] (m₀ m₁ : Message) (hm : m₀ ≠ m₁)
    {K T : ℕ} (hk : S.KeygenCostAtMost K) (hs : S.SignCostAtMost T)
    (hz : S.VerifyCostAtMost 0) : CostAtMost (S.weakExperiment (adversary S m₀ m₁)) (K + T) := by
  rw [experiment_eq S m₀ m₁ hm]
  refine Costs.CostAtMost.bind hk fun k => ?_
  exact Costs.CostAtMost.bind_le (hs k.2 m₀) (fun _ => hz _ _ _) (by omega)

theorem attack_probability [Nonempty OracleAlgorithm.Signature] (m₀ m₁ : Message) (hm : m₀ ≠ m₁)
    (hz : S.VerifyCostAtMost 0) :
    probTrue (S.weakExperiment (adversary S m₀ m₁)) =
      E (run S.keygen ∅) (fun k => Pr[= true | freeRun (S.verify k.1.1 m₁ (selected S k.1.1 m₁))]) := by
  rw [experiment_eq S m₀ m₁ hm, probTrue_eq_win, win_bind]
  apply congrArg (E (run S.keygen ∅))
  funext k
  rw [win_bind]
  calc
    _ = E (run (S.sign k.1.2 m₀) k.2) (fun _ =>
        Pr[= true | freeRun (S.verify k.1.1 m₁ (selected S k.1.1 m₁))]) := by
      apply congrArg (E (run (S.sign k.1.2 m₀) k.2))
      funext s
      exact win_zero _ (hz _ _ _) _
    _ = _ := E_const _ _

theorem attack_ge_good [Nonempty OracleAlgorithm.Signature] (m₀ m₁ : Message) (hm : m₀ ≠ m₁)
    (hz : S.VerifyCostAtMost 0) :
    E (run S.keygen ∅) (fun k => if Good S k.1.1 m₁ then 1 else 0) ≤
      probTrue (S.weakExperiment (adversary S m₀ m₁)) := by
  rw [attack_probability S m₀ m₁ hm hz]
  apply expectedValue_mono
  intro k
  by_cases hg : Good S k.1.1 m₁
  · simp [hg, selected_accepts S _ _ hg]
  · simp [hg]

/-- Zero-cost verification permits a fresh-message forgery with success at least one half,
contradicting security when `(K + T) / 2 ^ securityBits < 1 / 2`. -/
theorem no_zero_verifier (hc : S.Correct) (ha : S.SigningFailureAtMost (1 / 2))
    {K T : ℕ} (hk : S.KeygenCostAtMost K) (hs : S.SignCostAtMost T)
    (m₀ m₁ : Message) (hm : m₀ ≠ m₁)
    (hgap : ((K + T : ℕ) : ℝ≥0∞) / 2 ^ securityBits < 1 / 2)
    (hsecure : S.WeaklySecure) : ¬ S.VerifyCostAtMost 0 := by
  intro hz
  let : Nonempty OracleAlgorithm.Signature := signature_nonempty S ha (by norm_num) m₁
  have hsuccess := hsecure (adversary S m₀ m₁) (K + T) (attack_cost S m₀ m₁ hm hk hs hz)
  have hgood := good_mass S hc hz ha m₁
  have hbound := attack_ge_good S m₀ m₁ hm hz
  have hf : (1 : ℝ≥0∞) < 1 := calc
    1 ≤ 1 / 2 + E (run S.keygen ∅) (fun k => if Good S k.1.1 m₁ then 1 else 0) := hgood
    _ ≤ 1 / 2 + probTrue (S.weakExperiment (adversary S m₀ m₁)) := add_le_add le_rfl hbound
    _ < 1 / 2 + 1 / 2 := ENNReal.add_lt_add_left (by norm_num) (hsuccess.trans hgap)
    _ = 1 := ENNReal.add_halves 1
  exact (lt_irrefl _) hf

attribute [local semireducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

/-- The paper budgets are far below the cost at which a half-success forgery is allowed. -/
theorem paper_attack_gap :
    (((keygenBudget + signBudget : ℕ) : ℝ≥0∞) / 2 ^ securityBits) < 1 / 2 := by
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, hashBits, blockBits, pkBits, msgBits, securityBits, maxSignatureBits, keygenBudget, signBudget]

/-- Every admissible, secure algorithm needs a verification budget of at least one
compression. -/
theorem paper_lowerBound_one : LowerBoundGenerality3 1 := by
  intro S hA hS v hv
  by_contra h
  have hv0 : v = 0 := by omega
  subst v
  have hε : (1 / 2 ^ signingFailureBits : ℝ≥0∞) ≤ 1 / 2 := by
    rw [signingFailureBits]
    exact ENNReal.div_le_div_left (by norm_num) 1
  have ha : S.SigningFailureAtMost (1 / 2) := fun m => (hA.signingFailure m).trans hε
  exact no_zero_verifier S hA.correct ha hA.keygenCost hA.signCost
    (0 : Message) (1 : Message) (by decide) paper_attack_gap hS.weaklySecure hv

end OptimalOTS.LowerGenerality3
