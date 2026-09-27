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

theorem reveal_positive (i : Idx) :
    0 < Forest.forestScheme.graph.revealBits (Forest.forestScheme.sets i) := by
  change 0 < Forest.graph.revealBits (Forest.fins (Forest.setsName i))
  rw [Forest.revealBits_eq]
  have present : Forest.chainNode 0 (Forest.fixedChoice i 0) ∈ Forest.setsName i := by
    change _ ∈ Forest.cutOf (Forest.fixedChoice i)
    rw [Forest.mem_cutOf_iff]
    exact ⟨0, rfl⟩
  have bound := Finset.single_le_sum (s := Forest.setsName i)
    (f := fun n => n.len) (fun _ _ => Nat.zero_le _) present
  have len : (Forest.chainNode 0 (Forest.fixedChoice i 0)).len = 144 := Forest.chainNode_len _ _
  rw [len] at bound
  omega

theorem accepted_payload_positive (pk : PublicKey) (m : Message)
    (σ : Signature) (accepted : true ∈ support (Forest.forestScheme.verify pk m σ)) :
    0 < σ.2.length := by
  rw [GScheme.verify, support_bind] at accepted
  simp only [Set.mem_iUnion] at accepted
  obtain ⟨i, _, accepted⟩ := accepted
  split_ifs at accepted with hi hlen
  · rw [hlen]
    exact reveal_positive ⟨i, hi⟩
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
    RiscvUpperForest.admissible 203 RiscvUpperForest.cost (by decide)

theorem cost : scheme.VerifyCostAtMost 203 :=
  WireAdapter.verifyCost RiscvUpperForest.scheme Forest.decodeSignature 203 RiscvUpperForest.cost

/--
info: 'OptimalOTS.RiscvUpperForest.Wire.admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms admissible

end OptimalOTS.RiscvUpperForest.Wire
