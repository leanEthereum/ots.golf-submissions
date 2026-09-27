import Submissions.UpperRiscv.ForestAlgorithm
import Submissions.UpperRiscv.WireAdapter

/-! The fixed-layout forest on the raw signature bit strings loaded by the machine, with the
strict verifier that reads only full-length signatures. Its admissibility supplies the key
generation and signing requirements of the submitted scheme. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.RiscvUpperForest.Wire

open OptimalOTS.Dag

attribute [local irreducible] validSet numValid

theorem accepted_payload_positive (pk : PublicKey) (m : Message)
    (σ : Signature) (accepted : true ∈ support (Forest.forestScheme.verify pk m σ)) :
    0 < σ.2.length := by
  rw [GScheme.verify, support_bind] at accepted
  simp only [Set.mem_iUnion] at accepted
  obtain ⟨i, _, accepted⟩ := accepted
  split_ifs at accepted with hi hlen
  · rw [hlen.1]
    change 0 < _ + (Forest.freeTag ⟨i, hi⟩).length
    rw [Forest.length_freeTag]
    omega
  · simp at accepted
  · simp at accepted

theorem canonical (pk : PublicKey) (m : Message) (bits : List Bool)
    (accepted : true ∈ support (RiscvUpperForest.scheme.verify pk m (Forest.decodeSignature bits))) :
    RiscvUpperForest.scheme.encodeSignature (Forest.decodeSignature bits) = bits := by
  have positive := accepted_payload_positive pk m (Forest.decodeSignature bits) accepted
  have hlen : 128 ≤ bits.length := by
    change 0 < (Payload.permute (bits.drop 128)).length at positive
    rw [Payload.length_permute] at positive
    rw [List.length_drop] at positive
    omega
  exact Forest.encode_decode bits hlen

def scheme : OracleAlgorithm.Scheme := WireAdapter.scheme RiscvUpperForest.scheme Forest.decodeSignature

theorem admissible : scheme.Admissible :=
  WireAdapter.admissible RiscvUpperForest.scheme Forest.decodeSignature Forest.decode_encode canonical
    RiscvUpperForest.admissible 191 RiscvUpperForest.cost (by decide)

theorem cost : scheme.VerifyCostAtMost 191 :=
  WireAdapter.verifyCost RiscvUpperForest.scheme Forest.decodeSignature 191 RiscvUpperForest.cost

/--
info: 'OptimalOTS.RiscvUpperForest.Wire.admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms admissible

end OptimalOTS.RiscvUpperForest.Wire
