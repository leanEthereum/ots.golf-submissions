import Submissions.UpperRiscv.MixedMemory
import Submissions.UpperRiscv.MixedIndexPhase
import Submissions.UpperRiscv.Payload

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

theorem wireOff_eq' : ∀ k : Fin 33, Payload.wireOff k = wireOffset k ∧
    Payload.width k = chainBits k := by
  decide +kernel

theorem graphOff_step' : ∀ k : Fin 33, Payload.graphOff (k.val+1) = Payload.graphOff k + chainBits k := by
  decide +kernel

/-- The graph payload presents exactly the wire value of each chain. -/
theorem permute_read (bits : List Bool) (hlen : 5328 ≤ bits.length) (k : Fin 33) :
    ofBits (chainBits k) ((Payload.permute bits).drop (Payload.graphOff k)) =
      ofBits (chainBits k) (bits.drop (wireOffset k)) := by
  obtain ⟨hw, hc⟩ := wireOff_eq' k
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [Payload.getElem?_permute_chain bits (by unfold Payload.valueBits; omega) k.isLt
    (by rw [hc]; exact hi), hw]

/-- The index phase preserves every chain value at its physical address. -/
theorem afterIndex_payloadFrom (pk : PublicKey) (m : Message) (bits : List Bool)
    (answer : BitVec hashBits) : PayloadFrom (afterIndex pk m bits answer) (bits.drop 128) 0 := by
  intro j _
  have h0 := initialState_signature image pk m bits image_data_length
  have hc := wireOffset_contained j
  have ha := wireOffset_aligned j
  have hw := chainBits_le j
  have h := memBits_extract (start := 128+wireOffset j) (len := chainBits j) h0 (by omega) (by omega)
  rw [ofBits_extract _ (by omega), ofBits_drop_take _ (by omega)] at h
  rw [List.drop_drop]
  have e : Riscv.signatureBase + BitVec.ofNat 64 ((128+wireOffset j)/8) = W (valueAddr j) := by
    rw [show Riscv.signatureBase = W 0x400030 from rfl, W_add, valueAddr_eq]
    congr 1; unfold payloadAddr; omega
  rw [e] at h
  apply memBits_of_word_frame _ _ _ _ h
  intro i hi
  apply afterIndex_frame
  have hv := valueAddr_eq j
  rw [alignToDword_toNat, W_add, W_toNat _ (by unfold payloadAddr at hv; omega)]
  refine ⟨Or.inr ?_, Or.inl ?_⟩ <;> simp only [dataAddr, laneBase] <;> unfold payloadAddr at hv <;>
    omega

/-- Any byte-aligned signature slice past the public-key words and before the lanes survives the
index phase. -/
theorem afterIndex_sigBits (pk : PublicKey) (m : Message) (bits : List Bool)
    (answer : BitVec hashBits) (off len : ℕ) (ha : off % 8 = 0) (hl : len % 8 = 0)
    (hoff : off + len ≤ 5504) :
    MemBits (afterIndex pk m bits answer) (W (0x400030 + off / 8)) (ofBits len (bits.drop off)) := by
  have h0 := initialState_signature image pk m bits image_data_length
  have h := memBits_extract (start := off) (len := len) h0 ha hoff
  rw [ofBits_extract _ (by omega), ofBits_drop_take _ (by omega)] at h
  have e : Riscv.signatureBase + BitVec.ofNat 64 (off/8) = W (0x400030 + off / 8) := by
    rw [show Riscv.signatureBase = W 0x400030 from rfl, W_add]
  rw [e] at h
  apply memBits_of_word_frame _ _ _ _ h
  intro i hi
  apply afterIndex_frame
  rw [alignToDword_toNat, W_add, W_toNat _ (by omega)]
  refine ⟨Or.inr ?_, Or.inl ?_⟩ <;> simp only [dataAddr, laneBase] <;> omega

/-- The index phase preserves the six signature bytes past the region. -/
theorem afterIndex_tail (pk : PublicKey) (m : Message) (bits : List Bool)
    (answer : BitVec hashBits) :
    MemBits (afterIndex pk m bits answer) (W tailAddr) (ofBits 48 ((bits.drop 128).drop 5328)) := by
  rw [List.drop_drop]
  have h := afterIndex_sigBits pk m bits answer (5328 + 128) 48 (by norm_num) (by norm_num)
    (by norm_num)
  have e : 0x400030 + (5328 + 128) / 8 = tailAddr := by unfold tailAddr regionAddr; norm_num
  rw [e] at h
  exact h

end OptimalOTS.RiscvMixedProgram
