import Submissions.UpperCompressions.AlgorithmCosts

/-! Honest-party resource bounds and wire-size bounds for the generic DAG adapter. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.AlgorithmAdapter

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials


theorem length_encode (G : Graph) (A : Finset (Fin G.size)) (x : G.Assignment) :
    (G.encode A x).length = G.revealBits A := by
  unfold Graph.encode Graph.revealBits
  rw [List.length_flatMap]
  simp only [toBits, List.length_ofFn]
  rw [← List.sum_toFinset _ ((List.nodup_finRange _).filter _)]
  congr 1
  ext v
  simp

theorem signLoop_returns (S : Scheme) (x : S.graph.Assignment) (m : Message) :
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
      · exact signLoop_returns S x m k _ σ h
    · simp at h

theorem signatureSize (S : Scheme) :
    S.toAlgorithm.SignatureSizeAtMost (nonceBits + (maxSignatureBits - nonceBits)) := by
  change ∀ (sk : S.graph.Assignment) (m : Message) (σ : Signature),
    some σ ∈ support (S.sign sk m) → (encodeSignature σ).length ≤ nonceBits + (maxSignatureBits - nonceBits)
  intro sk m σ hσ
  obtain ⟨i, hi⟩ := signLoop_returns S sk m trials ∅ σ hσ
  rw [length_encodeSignature, hi, length_encode]
  have h := S.reveal_le i
  omega

theorem rejectsOversized (S : Scheme) :
    S.toAlgorithm.RejectsOversized (nonceBits + (maxSignatureBits - nonceBits)) := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    nonceBits + (maxSignatureBits - nonceBits) < (encodeSignature σ).length →
      true ∉ support (S.verify pk m σ)
  intro pk m σ hlen hmem
  change nonceBits + (maxSignatureBits - nonceBits) < (encodeSignature σ).length at hlen
  rw [length_encodeSignature] at hlen
  change true ∈ support (S.verify pk m σ) at hmem
  rw [Scheme.verify, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨i, _, hmem⟩ := hmem
  by_cases hi : i < numCuts
  · have hwrong : σ.2.length ≠ S.graph.revealBits (S.sets ⟨i, hi⟩) := by
      have h := S.reveal_le ⟨i, hi⟩
      omega
    simp only [dif_pos hi, if_neg hwrong, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
  · simp [hi] at hmem

theorem keygenCost (S : Scheme) : S.toAlgorithm.KeygenCostAtMost keygenBudget :=
  AlgorithmCosts.Dag.Scheme.costAtMost_keygen S

theorem signCost (S : Scheme) (hidx : blockCost (msgBits + nonceBits) = 1) :
    S.toAlgorithm.SignCostAtMost trials :=
  AlgorithmCosts.Dag.Scheme.costAtMost_sign S hidx

theorem verifyCost (S : Scheme) (hidx : blockCost (msgBits + nonceBits) = 1)
    {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    S.toAlgorithm.VerifyCostAtMost (1 + v) :=
  AlgorithmCosts.Dag.Scheme.costAtMost_verify S hidx hv

end OptimalOTS.AlgorithmAdapter
