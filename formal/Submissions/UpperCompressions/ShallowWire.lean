import Submissions.UpperCompressions.ShallowResources
import Submissions.UpperCompressions.ShallowMain
import Submissions.UpperCompressions.WireAdapter

/-! The forest on transmitted bit strings: the nonce bits followed by the disclosed values.
Verification parses its input; every accepted input is the encoding of its parse. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.ShallowUpperForest.Wire

open OptimalOTS.Dag

local notation "numCuts" => OptimalOTS.IndexedAnalysis.numCuts

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
    0 < ShallowForest.forestScheme.graph.revealBits (ShallowForest.forestScheme.sets i) := by
  rw [ShallowForest.forestScheme_revealBits]
  norm_num

theorem accepted_payload_positive (pk : PublicKey) (m : Message) (σ : Signature)
    (accepted : true ∈ support (ShallowForest.forestScheme.verify pk m σ)) : 0 < σ.2.length := by
  rw [IndexedDag.Scheme.verify, support_bind] at accepted
  simp only [Set.mem_iUnion] at accepted
  obtain ⟨i, _, accepted⟩ := accepted
  split_ifs at accepted with hi hlen
  · rw [hlen]
    exact reveal_positive ⟨i, hi⟩
  · simp at accepted
  · simp at accepted

theorem canonical (pk : PublicKey) (m : Message) (bits : List Bool)
    (accepted : true ∈ support (ShallowUpperForest.scheme.verify pk m (decode bits))) :
    ShallowUpperForest.scheme.encodeSignature (decode bits) = bits := by
  have positive := accepted_payload_positive pk m (decode bits) accepted
  have hlen : nonceBits ≤ bits.length := by
    change 0 < (bits.drop nonceBits).length at positive
    rw [List.length_drop] at positive
    omega
  exact encode_decode bits hlen

/-- The forest's programs on bit strings. -/
def scheme : OracleAlgorithm.Scheme := WireAdapter.scheme ShallowUpperForest.scheme decode

theorem secure : scheme.Secure :=
  WireAdapter.secure ShallowUpperForest.scheme decode decode_encode canonical
    ((IndexedDag.AlgorithmAdapter.secure_iff ShallowForest.forestScheme).mpr
      ShallowForest.forestScheme_secure)

theorem admissible : scheme.Admissible :=
  WireAdapter.admissible ShallowUpperForest.scheme decode decode_encode canonical
    ShallowUpperForest.admissible

theorem cost : scheme.VerifyCostAtMost 102 :=
  WireAdapter.verifyCost ShallowUpperForest.scheme decode 102 ShallowUpperForest.cost

end OptimalOTS.ShallowUpperForest.Wire

#print axioms OptimalOTS.ShallowUpperForest.Wire.secure
#print axioms OptimalOTS.ShallowUpperForest.Wire.admissible
#print axioms OptimalOTS.ShallowUpperForest.Wire.cost
