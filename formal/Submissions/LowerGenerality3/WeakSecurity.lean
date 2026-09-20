import OptimalOTS.OracleAlgorithm

/-!
# Weak unforgeability for oracle algorithms

The weak experiment runs the strong experiment's oracle calls and differs only in its winning
condition. Every weak win is a strong win, so every secure algorithm is weakly secure with the
same budget and bound. The lower-bound attack forges on a new message.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS
namespace OracleAlgorithm.Scheme

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget


/-- An accepted forgery wins if signing failed or the forged message differs from the signed one. -/
def weakExperiment (S : OracleAlgorithm.Scheme) (A : OracleAlgorithm.Adversary) : OracleComp Spec Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && (σ₁.isNone || decide (m₂ ≠ m₁))

/-- Weak unforgeability: success is strictly below `B / 2 ^ securityBits` for every
pathwise budget `B` of the whole experiment. -/
def WeaklySecure (S : OracleAlgorithm.Scheme) : Prop :=
  ∀ (A : OracleAlgorithm.Adversary) (B : ℕ), CostAtMost (S.weakExperiment A) B →
    probTrue (S.weakExperiment A) < (B : ℝ≥0∞) / 2 ^ securityBits

namespace SecurityBridge

/-- Signed message, signing result, forged message, forged signature, and verification result. -/
abbrev Outcome (S : OracleAlgorithm.Scheme) :=
  Message × Option OracleAlgorithm.Signature × Message × OracleAlgorithm.Signature × Bool

/-- The execution shared by strong and weak security; only their winning conditions differ. -/
def experimentRun (S : OracleAlgorithm.Scheme) (A : OracleAlgorithm.Adversary) : OracleComp Spec (Outcome S) := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return (m₁, σ₁, m₂, σ₂, ok)

def strongWin {S : OracleAlgorithm.Scheme} (r : Outcome S) : Bool :=
  r.2.2.2.2 && decide (r.2.1.map (fun s => (r.1, s)) ≠ some (r.2.2.1, r.2.2.2.1))

def weakWin {S : OracleAlgorithm.Scheme} (r : Outcome S) : Bool :=
  r.2.2.2.2 && (r.2.1.isNone || decide (r.2.2.1 ≠ r.1))

theorem experiment_eq_map (S : OracleAlgorithm.Scheme) (A : OracleAlgorithm.Adversary) :
    OracleAlgorithm.experiment S A = strongWin <$> experimentRun S A := by
  simp only [OracleAlgorithm.experiment, experimentRun, strongWin, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp]

theorem weakExperiment_eq_map (S : OracleAlgorithm.Scheme) (A : OracleAlgorithm.Adversary) :
    S.weakExperiment A = weakWin <$> experimentRun S A := by
  simp only [weakExperiment, experimentRun, weakWin, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp]

theorem strongWin_of_weakWin {S : OracleAlgorithm.Scheme} (r : Outcome S)
    (h : weakWin r = true) : strongWin r = true := by
  obtain ⟨m₁, σ₁, m₂, σ₂, ok⟩ := r
  simp only [weakWin, strongWin, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨h.1, ?_⟩
  rcases h.2 with hnone | hne
  · cases σ₁ with
    | none => simp
    | some s => simp at hnone
  · cases σ₁ with
    | none => simp
    | some s =>
      intro heq
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      exact hne heq.1.symm

theorem cost_iff (S : OracleAlgorithm.Scheme) (A : OracleAlgorithm.Adversary) (B : ℕ) :
    CostAtMost (OracleAlgorithm.experiment S A) B ↔ CostAtMost (S.weakExperiment A) B := by
  unfold CostAtMost
  rw [experiment_eq_map, weakExperiment_eq_map, isQueryBound_map_iff, isQueryBound_map_iff]

theorem weak_success_le (S : OracleAlgorithm.Scheme) (A : OracleAlgorithm.Adversary) :
    probTrue (S.weakExperiment A) ≤ probTrue (OracleAlgorithm.experiment S A) := by
  unfold probTrue
  rw [experiment_eq_map, weakExperiment_eq_map, simulateQ_map, simulateQ_map, StateT.run'_map',
    StateT.run'_map', ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  exact probEvent_mono'' fun r h => strongWin_of_weakWin r h

end SecurityBridge

/-- Every generic strongly secure scheme also meets fresh-message security. -/
theorem Secure.weaklySecure {S : OracleAlgorithm.Scheme} (h : S.Secure) : S.WeaklySecure := fun A B hB =>
  lt_of_le_of_lt (SecurityBridge.weak_success_le S A)
    (h A B ((SecurityBridge.cost_iff S A B).2 hB))

end OracleAlgorithm.Scheme
end OptimalOTS
