import Submissions.UpperRiscvHint.Wire

/-! Strong security survives a lossy signature projection when the verifier
recovers a full signature, checks its projection, and runs the original verifier.
The recovery queries are charged inside the new experiment. This is a generic
oracle reduction and does not assume that recovery succeeds or is efficient. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.ProjectionTransfer

abbrev Signature := OracleAlgorithm.Signature

variable (S : OracleAlgorithm.Scheme) (project : Signature → Signature)
  (recover : PublicKey → Message → Signature → OracleComp Spec (Option Signature))

def verify (pk : PublicKey) (m : Message) (σ : Signature) : OracleComp Spec Bool := do
  let full ← recover pk m σ
  let ok ← S.verify pk m (full.getD [])
  pure (full.isSome && decide (project (full.getD []) = σ) && ok)

def scheme : OracleAlgorithm.Scheme where
  SecretKey := S.SecretKey
  keygen := S.keygen
  sign := fun sk m => Option.map project <$> S.sign sk m
  verify := verify S project recover

def adversary (A : OracleAlgorithm.Adversary) : OracleAlgorithm.Adversary where
  State := PublicKey × A.State
  choose := fun pk => (fun p => (p.1, (pk, p.2))) <$> A.choose pk
  forge := fun state signed => do
    let forged ← A.forge state.2 (signed.map project)
    let full ← recover state.1 forged.1 forged.2
    pure (forged.1, full.getD [])

structure RunData where
  signedMessage : Message
  signed : Option Signature
  forgedMessage : Message
  forged : Signature
  full : Option Signature
  ok : Bool

def core (A : OracleAlgorithm.Adversary) : OracleComp Spec RunData := do
  let (pk, sk) ← S.keygen
  let (m₁, state) ← A.choose pk
  let signed ← S.sign sk m₁
  let (m₂, forged) ← A.forge state (signed.map project)
  let full ← recover pk m₂ forged
  let ok ← S.verify pk m₂ (full.getD [])
  pure ⟨m₁, signed, m₂, forged, full, ok⟩

def projectedSuccess (d : RunData) : Bool :=
  (d.full.isSome && decide (project (d.full.getD []) = d.forged) && d.ok) &&
    decide ((d.signed.map project).map (fun σ => (d.signedMessage, σ)) ≠
      some (d.forgedMessage, d.forged))

def fullSuccess (d : RunData) : Bool :=
  d.ok && decide (d.signed.map (fun σ => (d.signedMessage, σ)) ≠
    some (d.forgedMessage, d.full.getD []))

theorem projected_experiment (A : OracleAlgorithm.Adversary) :
    OracleAlgorithm.experiment (scheme S project recover) A =
      projectedSuccess project <$> core S project recover A := by
  simp only [OracleAlgorithm.experiment, scheme, verify, core, projectedSuccess,
    bind_map_left, map_bind, map_pure, bind_assoc, pure_bind]

theorem full_experiment (A : OracleAlgorithm.Adversary) :
    OracleAlgorithm.experiment S (adversary project recover A) =
      fullSuccess <$> core S project recover A := by
  simp only [OracleAlgorithm.experiment, adversary, core, fullSuccess,
    bind_map_left, map_bind, map_pure, bind_assoc, pure_bind]

theorem success_mono (d : RunData) :
    projectedSuccess project d = true → fullSuccess d = true := by
  intro h
  simp only [projectedSuccess, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hp⟩, hok⟩, hne⟩ := h
  simp only [fullSuccess, hok, Bool.true_and, decide_eq_true_eq]
  intro equal
  apply hne
  have projected := congrArg (Option.map (fun p : Message × Signature => (p.1, project p.2))) equal
  simpa only [Option.map_map, Option.map_some, Function.comp_def, hp] using projected

theorem probTrue_map_mono {α : Type} (oa : OracleComp Spec α) (f g : α → Bool)
    (h : ∀ x, f x = true → g x = true) : probTrue (f <$> oa) ≤ probTrue (g <$> oa) := by
  rw [Forest.probTrue_eq_E_run, Forest.probTrue_eq_E_run, run_map, run_map, E_map, E_map]
  apply E_mono
  intro p
  by_cases hf : f p.1 = true
  · simp [hf, h p.1 hf]
  · simp [hf]

/-- The reduction spends exactly the recovery and verification work of the new scheme. -/
theorem secure (hS : S.Secure) : (scheme S project recover).Secure := by
  intro A B hB
  rw [projected_experiment] at hB ⊢
  have coreBound := (AlgorithmCosts.costAtMost_map_iff _ _ _).1 hB
  have liftedBound : CostAtMost (OracleAlgorithm.experiment S (adversary project recover A)) B := by
    rw [full_experiment]
    exact AlgorithmCosts.CostAtMost.map coreBound _
  have hs := hS (adversary project recover A) B liftedBound
  rw [full_experiment] at hs
  exact (probTrue_map_mono _ _ _ (success_mono project)).trans_lt hs

theorem signingFailure (ε : ℝ≥0∞) (h : S.SigningFailureAtMost ε) :
    (scheme S project recover).SigningFailureAtMost ε := by
  intro message
  simpa only [scheme, bind_map_left, Option.isNone_map] using h message

theorem signatureSize (n : ℕ) (hp : ∀ σ, (project σ).length ≤ n) :
    (scheme S project recover).SignatureSizeAtMost n := by
  intro sk m σ h
  change some σ ∈ support (Option.map project <$> S.sign sk m) at h
  rw [support_map] at h
  obtain ⟨signed, _, equal⟩ := h
  cases signed with
  | none => cases equal
  | some full =>
    have he : project full = σ := Option.some.inj equal
    rw [← he]
    exact hp full

theorem keygenCost (n : ℕ) (h : S.KeygenCostAtMost n) :
    (scheme S project recover).KeygenCostAtMost n := h

theorem signCost (n : ℕ) (h : S.SignCostAtMost n) :
    (scheme S project recover).SignCostAtMost n := by
  intro sk m
  exact AlgorithmCosts.CostAtMost.map (h sk m) _

theorem rejectsOversized (n : ℕ) (hp : ∀ σ, (project σ).length ≤ n) :
    (scheme S project recover).RejectsOversized n := by
  intro pk m σ hlen accepted
  change true ∈ support (verify S project recover pk m σ) at accepted
  unfold verify at accepted
  rw [mem_support_bind_iff] at accepted
  obtain ⟨full, _, accepted⟩ := accepted
  rw [mem_support_bind_iff] at accepted
  obtain ⟨ok, _, accepted⟩ := accepted
  have hpure : true = (full.isSome && decide (project (full.getD []) = σ) && ok) := by
    simpa only [support_pure, Set.mem_singleton_iff] using accepted
  have decoded := hpure.symm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at decoded
  have he : project (full.getD []) = σ := decoded.1.2
  have bound := hp (full.getD [])
  rw [he] at bound
  omega

end OptimalOTS.ProjectionTransfer
