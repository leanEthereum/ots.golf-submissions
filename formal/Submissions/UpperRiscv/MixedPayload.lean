import Submissions.UpperRiscv.MixedMemory
import Submissions.UpperRiscv.MixedIndexPhase

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

theorem cursor_contained (k : Fin 32) : cursor k + chainBits k ≤ 5376 := by
  have h := Payload.graphUnit_add k k.isLt
  rw [chainBits_units k]
  unfold cursor
  omega

/-- The payload adapter presents exactly the wire block used by each chain. -/
theorem permute_read (bits : List Bool) (hlen : bits.length = 5376) (k : Fin 32) :
    ofBits (chainBits k) ((Payload.permute bits).drop (cursor k)) =
      ofBits (chainBits k) (bits.drop (wireOffset k)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : cursor k+i < (Payload.permute bits).length := by
    rw [Payload.length_permute, hlen]; have := cursor_contained k; omega
  have hw : wireOffset k+i < bits.length := by
    rw [hlen]; have := wireOffset_contained k; omega
  simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_eq_getElem hc, List.getElem?_eq_getElem hw, Option.getD_some]
  simp only [Payload.getElem_permute, hlen, payload_index k i hi]

/-- The index phase preserves every disclosed block at its physical wire address. -/
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
  have e : Riscv.signatureBase + BitVec.ofNat 64 ((128+wireOffset j)/8) = W (wireSlot j) := by
    rw [show Riscv.signatureBase = W 0x400030 from rfl, W_add, wireSlot_eq]
    congr 1; omega
  rw [e] at h
  apply memBits_of_word_frame _ _ _ _ h
  intro i hi
  apply afterIndex_frame
  rw [alignToDword_toNat, W_add, W_toNat _ (by rw [wireSlot_eq]; omega), wireSlot_eq]
  constructor <;> right <;> simp only [dataAddr, laneBase] <;> omega

end OptimalOTS.RiscvMixedProgram
