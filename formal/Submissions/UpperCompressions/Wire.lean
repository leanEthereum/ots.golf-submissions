import Submissions.UpperCompressions.ForestAlgorithm
import Submissions.UpperCompressions.WireAdapter

/-! The forest on transmitted bit strings: the nonce bits followed by the disclosed values.
Verification parses its input; every accepted input is the encoding of its parse. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.GenericUpperForest.Wire

open OptimalOTS.Dag

/-- Parse a bit string: the first `nonceBits` bits are the nonce (zero-extended if the string is
shorter), the rest are the disclosed values. -/
def decode (bits : List Bool) : Signature :=
  (ofBits nonceBits (bits.take nonceBits), bits.drop nonceBits)

theorem decode_encode (σ : Signature) : decode (AlgorithmAdapter.encodeSignature σ) = σ := by
  rcases σ with ⟨nonce, payload⟩
  have hn : (toBits nonce).length = nonceBits := length_toBits nonce
  simp only [decode, AlgorithmAdapter.encodeSignature, List.take_left' hn, List.drop_left' hn,
    ofBits_toBits]

theorem encode_decode (bits : List Bool) (hlen : nonceBits ≤ bits.length) :
    AlgorithmAdapter.encodeSignature (decode bits) = bits := by
  change toBits (ofBits nonceBits (bits.take nonceBits)) ++ bits.drop nonceBits = bits
  rw [toBits_ofBits _ (by simp [hlen]), List.take_append_drop]

/-- Every cut of the family discloses at least one 128-bit value. -/
theorem reveal_positive (i : Fin numCuts) :
    0 < Forest.forestScheme.graph.revealBits (Forest.forestScheme.sets i) := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin (2 ^ 115), (j : Fin numCuts) = i := ⟨i, rfl⟩
  change 0 < Forest.graph.revealBits (Forest.fins (Forest.setsName j))
  rw [Forest.revealBits_eq]
  have hcut := Forest.isCut_setsName j
  obtain ⟨n, hn⟩ : ∃ n, n ∈ Forest.setsName j := by
    rcases hcut.covers 0 with h | ⟨m, hm, _⟩
    · exact ⟨_, h⟩
    · exact ⟨m, hm⟩
  have bound : n.len ≤ ∑ x ∈ Forest.setsName j, x.len :=
    Finset.single_le_sum (f := fun n => n.len) (fun _ _ => Nat.zero_le _) hn
  have len := hcut.values n hn
  omega

theorem accepted_payload_positive (pk : PublicKey) (m : Message) (σ : Signature)
    (accepted : true ∈ support (Forest.forestScheme.verify pk m σ)) : 0 < σ.2.length := by
  rw [Scheme.verify, support_bind] at accepted
  simp only [Set.mem_iUnion] at accepted
  obtain ⟨i, _, accepted⟩ := accepted
  split_ifs at accepted with hi hlen
  · rw [hlen]
    exact reveal_positive ⟨i, hi⟩
  · simp at accepted
  · simp at accepted

theorem canonical (pk : PublicKey) (m : Message) (bits : List Bool)
    (accepted : true ∈ support (GenericUpperForest.scheme.verify pk m (decode bits))) :
    GenericUpperForest.scheme.encodeSignature (decode bits) = bits := by
  have positive := accepted_payload_positive pk m (decode bits) accepted
  have hlen : nonceBits ≤ bits.length := by
    change 0 < (bits.drop nonceBits).length at positive
    rw [List.length_drop] at positive
    omega
  exact encode_decode bits hlen

/-- The forest's programs on bit strings. -/
def scheme : OracleAlgorithm.Scheme := WireAdapter.scheme GenericUpperForest.scheme decode

theorem secure : scheme.Secure :=
  WireAdapter.secure GenericUpperForest.scheme decode decode_encode canonical
    GenericUpperForest.secure

theorem admissible : scheme.Admissible :=
  WireAdapter.admissible GenericUpperForest.scheme decode decode_encode canonical
    GenericUpperForest.admissible

theorem cost : scheme.VerifyCostAtMost 104 :=
  WireAdapter.verifyCost GenericUpperForest.scheme decode 104 GenericUpperForest.cost

end OptimalOTS.GenericUpperForest.Wire
