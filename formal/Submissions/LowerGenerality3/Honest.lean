import Submissions.LowerGenerality3.Accept
import Submissions.LowerGenerality3.WeakSecurity

/-!
# Honest verification under a cost-one deterministic verifier

Every verification has a `Shape` (`shape`). Perfect correctness makes honest verification accept
with probability one from the honest cache, so its shape is unconditional (`Shape.Uncond`: accepts
every oracle) or it queries a point already in the cache and accepts the cached answer
(`cached_or_uncond`, `honest_cached_or_uncond`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

variable (S : OracleAlgorithm.Scheme)

/-- The shape of one verification. -/
def shape (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic) (pk : PublicKey)
    (m : Message) (σ : OracleAlgorithm.Signature) : Shape :=
  (shape_of_one _ (hv pk m σ) (hd pk m σ)).choose

theorem verify_eq_shape (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic) (pk : PublicKey)
    (m : Message) (σ : OracleAlgorithm.Signature) :
    S.verify pk m σ = (shape S hv hd pk m σ).comp :=
  (shape_of_one _ (hv pk m σ) (hd pk m σ)).choose_spec.1

theorem shape_short (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic) (pk : PublicKey)
    (m : Message) (σ : OracleAlgorithm.Signature) :
    ∀ q f, shape S hv hd pk m σ = .one q f → q.1 ≤ 512 :=
  (shape_of_one _ (hv pk m σ) (hd pk m σ)).choose_spec.2

/-- A shape that accepts on every oracle path. -/
def Shape.Uncond : Shape → Prop
  | .const b => b = true
  | .one _ f => ∀ y, f y = true

theorem win_of_uncond {sh : Shape} (h : sh.Uncond) (c : Cache) : win sh.comp c = 1 := by
  cases sh with
  | const b =>
    rw [win_const]
    simp only [Shape.Uncond] at h
    simp [h]
  | one q f =>
    rcases hc : c q with _ | y
    · rw [win_one_none hc, rate, probOutput_eq_one_iff_forall]
      refine ⟨by simp, ?_⟩
      intro b hb
      rw [support_map] at hb
      obtain ⟨x, -, rfl⟩ := hb
      exact h x
    · rw [win_one_some hc]
      simp [h y]

/-- Acceptance with probability one: unconditional, or a cached query whose answer is accepted. -/
theorem cached_or_uncond {sh : Shape} {c : Cache} (hw : win sh.comp c = 1) :
    sh.Uncond ∨ ∃ q f y, sh = .one q f ∧ c q = some y ∧ f y = true := by
  cases sh with
  | const b =>
    left
    rw [win_const] at hw
    cases b <;> simp_all [Shape.Uncond]
  | one q f =>
    rcases hc : c q with _ | y
    · left
      rw [win_one_none hc] at hw
      exact all_of_rate_one hw
    · right
      refine ⟨q, f, y, rfl, hc, ?_⟩
      rw [win_one_some hc] at hw
      by_contra hf
      simp [hf] at hw

/-- Rejection probability from a cache. -/
def rej (oa : OracleComp Spec Bool) (c : Cache) : ℝ≥0∞ := win (do let b ← oa; pure (!b)) c

theorem win_eq_one_of_rej_zero {oa : OracleComp Spec Bool} {c : Cache} (h : rej oa c = 0) :
    win oa c = 1 := by
  unfold rej win at *
  rw [bind_pure_comp, run_map, Functor.map_map] at h
  rw [probOutput_eq_one_iff_forall]
  refine ⟨by simp, ?_⟩
  intro b hb
  rw [support_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  by_contra hne
  have hmem : true ∈ support ((fun a => !a.1) <$> run oa c) := by
    rw [support_map]
    exact ⟨a, ha, by cases h1 : a.1 <;> simp_all⟩
  exact ((probOutput_pos_iff _ _).mpr hmem).ne' h

/-- Correctness, expanded over the honest key-generation and signing runs with their caches. -/
theorem correct_run (hc : S.Correct) (m : Message) :
    E (run S.keygen ∅) (fun k => E (run (S.sign k.1.2 m) k.2) (fun s =>
      match s.1 with | none => 0 | some σ => rej (S.verify k.1.1 m σ) s.2)) = 0 := by
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
  | some σ => simp [rej]

/-- On every honest history that produces a signature, its verification is unconditional or
reads a cached point. -/
theorem honest_cached_or_uncond (hc : S.Correct) (hv : S.VerifyCostAtMost 1)
    (hd : S.VerifyDeterministic) (m : Message)
    (k : (PublicKey × S.SecretKey) × Cache) (hk : k ∈ support (run S.keygen ∅))
    (σ : OracleAlgorithm.Signature) (c : Cache)
    (hs : (some σ, c) ∈ support (run (S.sign k.1.2 m) k.2)) :
    (shape S hv hd k.1.1 m σ).Uncond ∨
      ∃ q f y, shape S hv hd k.1.1 m σ = .one q f ∧ c q = some y ∧ f y = true := by
  have h := E_eq_zero_on_support _ _ (correct_run S hc m) hk
  have h2 := E_eq_zero_on_support _ _ h hs
  simp only at h2
  have hw : win (S.verify k.1.1 m σ) c = 1 := win_eq_one_of_rej_zero h2
  rw [verify_eq_shape S hv hd] at hw
  exact cached_or_uncond hw

end OptimalOTS.LowerGenerality3
