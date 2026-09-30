import Submissions.UpperRiscvHint.ProjectionTransfer

/-! The transmitted signature omits the final three bits of a disclosed bottom
top. The pure projection keeps 5495 bits. Recovery tries the short signature and
its eight three-bit extensions; the original verifier decides which length the
index requires. A final verification is included in the algorithm so the generic
security reduction preserves the exact query budget. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.Completion

attribute [local irreducible] RiscvUpperForest.Wire.scheme maxSignatureBits signBudget keygenBudget

abbrev Signature := OracleAlgorithm.Signature

theorem full_cost : RiscvUpperForest.Wire.scheme.VerifyCostAtMost 180 :=
  RiscvUpperForest.Wire.cost

def project (σ : Signature) : Signature := σ.take 5495

def candidates (σ : Signature) : List Signature :=
  if σ.length = 5495 then
    σ :: (List.finRange 8).map (fun j => σ ++ List.ofFn (fun b : Fin 3 => decide ((j.val / 2^b.val) % 2 = 1)))
  else []

def findValid (pk : PublicKey) (m : Message) : List Signature → OracleComp Spec (Option Signature)
  | [] => pure none
  | σ :: rest => do
      let ok ← RiscvUpperForest.Wire.scheme.verify pk m σ
      if ok then pure (some σ) else findValid pk m rest

def recover (pk : PublicKey) (m : Message) (σ : Signature) : OracleComp Spec (Option Signature) :=
  findValid pk m (candidates σ)

def scheme : OracleAlgorithm.Scheme :=
  ProjectionTransfer.scheme RiscvUpperForest.Wire.scheme project recover

/-- Complete strong unforgeability for the new fixed-length signature scheme. -/
theorem secure : scheme.Secure :=
  ProjectionTransfer.secure _ _ _ RiscvUpperForest.Wire.secure

theorem candidates_length (σ : Signature) : (candidates σ).length ≤ 9 := by
  unfold candidates
  split_ifs <;> simp

theorem candidate_project {σ full : Signature} (h : full ∈ candidates σ) : project full = σ := by
  unfold candidates at h
  split_ifs at h with hn
  · simp only [List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨j, _, rfl⟩
    · simp [project, hn]
    · simp [project, ← hn]
  · simp at h

theorem findValid_mem (pk : PublicKey) (m : Message) (l : List Signature) (full : Signature)
    (h : some full ∈ support (findValid pk m l)) : full ∈ l := by
  induction l with
  | nil => simp [findValid] at h
  | cons σ rest ih =>
    rw [findValid, mem_support_bind_iff] at h
    obtain ⟨ok, _, h⟩ := h
    cases ok
    · simp only [Bool.false_eq_true, if_false] at h
      exact List.mem_cons_of_mem σ (ih h)
    · have equal : full = σ := by simpa using h
      subst full
      exact List.mem_cons_self

theorem findValid_cost (pk : PublicKey) (m : Message) (l : List Signature) :
    CostAtMost (findValid pk m l) (180 * l.length) := by
  induction l with
  | nil => exact AlgorithmCosts.costAtMost_pure _ _
  | cons σ rest ih =>
    rw [findValid]
    apply AlgorithmCosts.CostAtMost.bind_le
      (full_cost pk m σ) (b₂ := 180 * rest.length)
    · intro ok
      cases ok
      · exact ih
      · exact AlgorithmCosts.costAtMost_pure _ _
    · simp; omega

theorem recover_cost (pk : PublicKey) (m : Message) (σ : Signature) :
    CostAtMost (recover pk m σ) 1620 :=
  (findValid_cost pk m (candidates σ)).mono (by have := candidates_length σ; omega)

/-- The extra completion work remains well inside the contract's verifier budget. -/
theorem verify_cost : scheme.VerifyCostAtMost 1800 := by
  intro pk m σ
  change CostAtMost (ProjectionTransfer.verify _ _ _ pk m σ) 1800
  unfold ProjectionTransfer.verify
  apply AlgorithmCosts.CostAtMost.bind_le (recover_cost pk m σ) (b₂ := 180)
  · intro full
    exact AlgorithmCosts.CostAtMost.bind_le
      (full_cost pk m (full.getD []))
      (b₂ := 0) (fun _ => AlgorithmCosts.costAtMost_pure _ _) (by omega)
  · omega

theorem findValid_deterministic (pk : PublicKey) (m : Message) (l : List Signature) :
    Deterministic (findValid pk m l) := by
  induction l with
  | nil => exact Deterministic.of_pure _
  | cons σ rest ih =>
    unfold findValid
    apply Deterministic.bind (RiscvUpperForest.Wire.admissible.verifyDeterministic pk m σ)
    intro ok
    cases ok
    · exact ih
    · exact Deterministic.of_pure _

theorem verify_deterministic : scheme.VerifyDeterministic := by
  intro pk m σ
  change Deterministic (ProjectionTransfer.verify _ _ _ pk m σ)
  unfold ProjectionTransfer.verify
  apply Deterministic.bind (findValid_deterministic pk m (candidates σ))
  intro full
  exact Deterministic.bind (RiscvUpperForest.Wire.admissible.verifyDeterministic pk m (full.getD []))
    (fun _ => Deterministic.of_pure _)

theorem project_length (σ : Signature) : (project σ).length ≤ maxSignatureBits := by
  simp only [project, List.length_take]
  have : maxSignatureBits = 5504 := by unfold maxSignatureBits; rfl
  omega

theorem signing_failure : scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) :=
  ProjectionTransfer.signingFailure _ _ _ _ RiscvUpperForest.Wire.admissible.signingFailure

theorem signature_size : scheme.SignatureSizeAtMost maxSignatureBits :=
  ProjectionTransfer.signatureSize _ _ _ _ project_length

theorem keygen_cost : scheme.KeygenCostAtMost keygenBudget :=
  ProjectionTransfer.keygenCost _ _ _ _ RiscvUpperForest.Wire.admissible.keygenCost

theorem sign_cost : scheme.SignCostAtMost signBudget :=
  ProjectionTransfer.signCost _ _ _ _ RiscvUpperForest.Wire.admissible.signCost

theorem rejects_oversized : scheme.RejectsOversized maxSignatureBits :=
  ProjectionTransfer.rejectsOversized _ _ _ _ project_length

end OptimalOTS.Completion
