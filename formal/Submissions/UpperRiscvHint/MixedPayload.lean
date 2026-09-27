import Submissions.UpperRiscvHint.MixedMemory
import Submissions.UpperRiscvHint.MixedIndexPhase
import Submissions.UpperRiscvHint.ViewLayout

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

/-- The index phase preserves every chain value at its view address. -/
theorem afterIndex_payloadFrom (pk : PublicKey) (m : Message) (view : List Bool)
    (answer : BitVec hashBits) : PayloadFrom (afterIndex pk m view answer) view 0 := by
  intro j _
  have h0 := loadView_memBits image pk m view image_data_length
  have hc := wireOffset_contained j
  unfold honestViewBits at hc
  have ha := wireOffset_aligned j
  have hw := chainBits_le j
  have h := memBits_extract (start := wireOffset j) (len := chainBits j) h0 ha (by omega)
  rw [ofBits_extract _ (by omega)] at h
  have e : Riscv.signatureBase + BitVec.ofNat 64 (wireOffset j / 8) = W (work j) := by
    rw [show Riscv.signatureBase = W 0x400030 from rfl, W_add, work_eq_view]
  rw [e] at h
  apply memBits_of_word_frame _ _ _ _ h
  intro i hi
  apply afterIndex_frame
  rw [alignToDword_toNat, W_add, W_toNat _ (by rw [work_eq_view]; omega), work_eq_view]
  refine ⟨Or.inr ?_, Or.inl ?_⟩ <;> simp only [dataAddr, laneBase] <;> omega

end OptimalOTS.RiscvMixedProgram
