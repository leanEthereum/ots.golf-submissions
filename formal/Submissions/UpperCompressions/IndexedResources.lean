import Submissions.UpperCompressions.IndexedScheme
import Submissions.UpperCompressions.Resources
import Submissions.UpperCompressions.Deterministic

/-!
# Honest-party resources for an arbitrary accepted-index count

The graph-generic cost, encoding and determinism lemmas are reused unchanged.
Only the scheme-facing wrappers are generalized to `IndexedDag.Scheme M`.
Every cost bound covers rejecting inputs and every oracle-answer path.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.IndexedDag

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits
  maxSignatureBits keygenBudget signBudget Dag.nonceBits Dag.idxBits Dag.numCuts Dag.trials

namespace Scheme

open OptimalOTS.AlgorithmCosts

variable {M : ℕ} (S : Scheme M)

theorem costAtMost_keygen_exact : CostAtMost S.keygen S.graph.keygenCost :=
  CostAtMost.bind_le (AlgorithmCosts.Dag.Graph.costAtMost_keygen S.graph)
    (fun _ => costAtMost_pure _ 0) (by simp)

theorem costAtMost_keygen : CostAtMost S.keygen keygenBudget :=
  CostAtMost.mono S.costAtMost_keygen_exact S.keygen_le

theorem costAtMost_signLoop (hidx : blockCost (msgBits + Dag.nonceBits) = 1)
    (x : S.graph.Assignment) (m : Message) :
    ∀ k tried, CostAtMost (S.signLoop x m k tried) k
  | 0, _ => costAtMost_pure _ _
  | k + 1, tried => by
      rw [Scheme.signLoop]
      split_ifs
      · refine CostAtMost.bind_le (costAtMost_liftM_probComp _ 0)
          (b₂ := k + 1) (fun j => ?_) (by simp)
        refine CostAtMost.bind_le (costAtMost_index hidx _ _)
          (b₂ := k) (fun i => ?_) (by omega)
        split_ifs with hi
        · exact costAtMost_pure _ _
        · exact costAtMost_signLoop hidx x m k _
      · exact costAtMost_pure _ _

theorem costAtMost_sign (hidx : blockCost (msgBits + Dag.nonceBits) = 1)
    (x : S.graph.Assignment) (m : Message) : CostAtMost (S.sign x m) Dag.trials :=
  costAtMost_signLoop S hidx x m _ _

theorem costAtMost_verify (hidx : blockCost (msgBits + Dag.nonceBits) = 1) {v : ℕ}
    (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) (pk : PublicKey) (m : Message)
    (σ : Dag.Signature) : CostAtMost (S.verify pk m σ) (1 + v) := by
  unfold Scheme.verify
  refine CostAtMost.bind_le (costAtMost_index hidx _ _) (b₂ := v) (fun i => ?_) le_rfl
  split_ifs with hi
  · dsimp only
    split_ifs
    · exact CostAtMost.bind_le
        (CostAtMost.mono
          (AlgorithmCosts.Dag.Graph.costAtMost_reconstruct S.graph (S.sets ⟨i, hi⟩) _)
          (hv _))
        (fun _ => costAtMost_pure _ 0) (by simp)
    · exact costAtMost_pure _ _
  · exact costAtMost_pure _ _

theorem deterministic_verify (pk : PublicKey) (m : Message) (σ : Dag.Signature) :
    Deterministic (S.verify pk m σ) := by
  unfold Scheme.verify Dag.index
  refine Deterministic.bind (Deterministic.map (Deterministic.hash _) _) fun i => ?_
  split_ifs
  · dsimp only
    split_ifs
    · exact Deterministic.bind (S.graph.deterministic_reconstruct _ _)
        fun _ => Deterministic.of_pure _
    · exact Deterministic.of_pure _
  · exact Deterministic.of_pure _

end Scheme

namespace AlgorithmAdapter

variable {M : ℕ} (S : Scheme M)

theorem signLoop_returns (x : S.graph.Assignment) (m : Message) :
    ∀ k tried σ, some σ ∈ support (S.signLoop x m k tried) →
      ∃ i, σ.2 = S.graph.encode (S.sets i) x
  | 0, _, _, h => by simp [Scheme.signLoop] at h
  | k + 1, tried, σ, h => by
    rw [Scheme.signLoop] at h
    split_ifs at h with hf
    · rw [support_bind] at h
      simp only [Set.mem_iUnion] at h
      obtain ⟨j, _, h⟩ := h
      rw [support_bind] at h
      simp only [Set.mem_iUnion] at h
      obtain ⟨i, _, h⟩ := h
      split_ifs at h with hi
      · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h
        exact ⟨⟨i, hi⟩, congrArg Prod.snd h⟩
      · exact signLoop_returns x m k _ σ h
    · simp at h

/-- The real nonce-and-disclosure encoding meets the protected bit budget. -/
theorem signatureSize : S.toAlgorithm.SignatureSizeAtMost maxSignatureBits := by
  change ∀ (sk : S.graph.Assignment) (m : Message) (σ : Dag.Signature),
    some σ ∈ support (S.sign sk m) →
      (OptimalOTS.AlgorithmAdapter.encodeSignature σ).length ≤ maxSignatureBits
  intro sk m σ hσ
  obtain ⟨i, hi⟩ := signLoop_returns S sk m Dag.trials ∅ σ hσ
  rw [OptimalOTS.AlgorithmAdapter.length_encodeSignature, hi,
    OptimalOTS.AlgorithmAdapter.length_encode]
  have h := S.reveal_le i
  omega

theorem rejectsOversized : S.toAlgorithm.RejectsOversized maxSignatureBits := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Dag.Signature),
    maxSignatureBits < (OptimalOTS.AlgorithmAdapter.encodeSignature σ).length →
      true ∉ support (S.verify pk m σ)
  intro pk m σ hlen hmem
  rw [OptimalOTS.AlgorithmAdapter.length_encodeSignature] at hlen
  rw [Scheme.verify, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨i, _, hmem⟩ := hmem
  by_cases hi : i < M
  · have hwrong : σ.2.length ≠ S.graph.revealBits (S.sets ⟨i, hi⟩) := by
      have h := S.reveal_le ⟨i, hi⟩
      omega
    simp only [dif_pos hi, if_neg hwrong, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
  · simp [hi] at hmem

theorem keygenCost : S.toAlgorithm.KeygenCostAtMost keygenBudget :=
  S.costAtMost_keygen

theorem keygenCost_exact : S.toAlgorithm.KeygenCostAtMost S.graph.keygenCost :=
  S.costAtMost_keygen_exact

theorem signCost (hidx : blockCost (msgBits + Dag.nonceBits) = 1) :
    S.toAlgorithm.SignCostAtMost Dag.trials :=
  S.costAtMost_sign hidx

theorem verifyCost (hidx : blockCost (msgBits + Dag.nonceBits) = 1)
    {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    S.toAlgorithm.VerifyCostAtMost (1 + v) :=
  S.costAtMost_verify hidx hv

theorem verifyDeterministic : S.toAlgorithm.VerifyDeterministic :=
  fun pk m σ => S.deterministic_verify pk m σ

/-- The protected message-and-nonce input uses one compression. -/
theorem index_cost_one : blockCost (msgBits + Dag.nonceBits) = 1 := by
  norm_num [blockCost, msgBits, Dag.nonceBits, blockBits]

theorem trials_eq_signBudget : Dag.trials = signBudget := by
  simp [Dag.trials, Dag.idxCost, index_cost_one]

theorem signCostAtBudget : S.toAlgorithm.SignCostAtMost signBudget := by
  simpa only [trials_eq_signBudget] using signCost S index_cost_one

theorem verifyCostBound {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    S.toAlgorithm.VerifyCostAtMost (1 + v) :=
  verifyCost S index_cost_one hv

end AlgorithmAdapter

end OptimalOTS.IndexedDag
