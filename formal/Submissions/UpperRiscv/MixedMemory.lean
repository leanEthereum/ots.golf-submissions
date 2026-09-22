import Submissions.UpperRiscv.MixedLayout

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

def PayloadFrom (s : MachineState) (payload : List Bool) (k : ℕ) : Prop :=
  ∀ j : Fin 32, k ≤ j.val →
    MemBits s (W (wireSlot j)) (ofBits (chainBits j) (payload.drop (wireOffset j)))

def Holds (s : MachineState) (k : Fin 32) (v : BitVec (chainBits k)) : Prop :=
  MemBits s (W (slot k)) v

def rootSliceStart (k : ℕ) : ℕ := if k < 8 ∨ k = 31 then 0 else 64
def rootSlice (k : ℕ) (y : BitVec 256) : BitVec (rootSliceBits k) :=
  y.extractLsb' (rootSliceStart k) (rootSliceBits k)

def Completed (s : MachineState) (tops : Fin 32 → BitVec 256) (k : ℕ) : Prop :=
  ∀ j : Fin 32, j.val < k → MemBits s (W (rootSliceAddr j)) (rootSlice j (tops j))

theorem rootSlice_contained (k : ℕ) : rootSliceStart k + rootSliceBits k ≤ 256 := by
  unfold rootSliceStart rootSliceBits
  split_ifs <;> omega

theorem rootSlice_aligned (k : ℕ) : rootSliceStart k % 8 = 0 := by
  unfold rootSliceStart; split_ifs <;> decide

theorem rootSlice_address (k : Fin 32) :
    rootSliceAddr k = outAddr k + rootSliceStart k / 8 := by
  have hs := slot_bounds k
  unfold rootSliceAddr rootSliceStart outAddr
  split_ifs <;> omega

/-- A hash writes exactly the slice needed by the root, even at the two full-width boundaries. -/
theorem rootSlice_of_answer (s : MachineState) (k : Fin 32) (y : BitVec 256)
    (ho : s.getReg .x12 = W (outAddr k)) :
    MemBits (Riscv.writeHash s y) (W (rootSliceAddr k)) (rootSlice k y) := by
  have h := writeHash_memBits s y (by rw [ho]; exact aligned_W _ (output_bounds k).2.2 (by have := output_bounds k; omega))
  rw [ho] at h
  have e := memBits_extract h (rootSlice_aligned k) (rootSlice_contained k)
  rw [W_add, ← rootSlice_address k] at e
  exact e

/-- Both state widths start 64 bits into the full hash output. -/
theorem holds_of_answer (s : MachineState) (k : Fin 32) (y : BitVec 256)
    (ho : s.getReg .x12 = W (outAddr k)) :
    Holds (Riscv.writeHash s y) k (Forest.trunc k y) := by
  have h := writeHash_memBits s y (by rw [ho]; exact aligned_W _ (output_bounds k).2.2 (by have := output_bounds k; omega))
  rw [ho] at h
  have e := memBits_extract (start := 64) (len := chainBits k) h (by decide)
    (by change 64+chainBits k ≤ 256; have := chainBits_le k; omega)
  have hs := slot_bounds k
  rw [show (64:ℕ)/8=8 by decide, W_add,
    show outAddr k+8=slot k by unfold outAddr; omega] at e
  have ht : min 64 (256-chainBits k) = 64 := Nat.min_eq_left (by have := chainBits_le k; omega)
  unfold Holds Forest.trunc
  rw [ht]
  exact e

/-- Byte intervals disjoint from the aligned 32-byte hash output retain their bits. -/
theorem writeHash_preserves (s : MachineState) (y : BitVec 256) (base out n : ℕ)
    (v : BitVec n) (hm : MemBits s (W base) v)
    (ho : s.getReg .x12 = W out) (ho8 : out%8=0) (hn8 : n%8=0)
    (hb : base+n < 2^62) (hout : out+32 < 2^62)
    (hd : base+n/8 ≤ out ∨ out+32 ≤ base) :
    MemBits (Riscv.writeHash s y) (W base) v := by
  apply memBits_of_word_frame _ _ _ _ hm
  intro i hi
  apply writeHash_frame
  intro j hj he
  have e := congrArg BitVec.toNat he
  rw [alignToDword_toNat, ho, W_add, W_add,
    W_toNat _ (by omega), W_toNat _ (by omega)] at e
  omega

/-- A chain hash preserves the disclosed values of every later chain. -/
theorem PayloadFrom.writeHash {s : MachineState} {payload : List Bool} (k : Fin 32)
    (hp : PayloadFrom s payload (k.val+1)) (y : BitVec 256)
    (ho : s.getReg .x12 = W (outAddr k)) :
    PayloadFrom (Riscv.writeHash s y) payload (k.val+1) := by
  intro j hj
  have bo := output_bounds k
  have bj := wireOffset_contained j
  have bw := chainBits_le j
  have hn : chainBits j % 8 = 0 := by rcases chainBits_cases j with h | h <;> rw [h] <;> decide
  apply writeHash_preserves s y (wireSlot j) (outAddr k) (chainBits j) _ (hp j hj)
    ho bo.2.2 hn
  · rw [wireSlot_eq j]; omega
  · omega
  · exact unread_disjoint k j (by omega)

/-- A chain hash preserves the committed root slices of every earlier chain. -/
theorem Completed.writeHash {s : MachineState} {tops : Fin 32 → BitVec 256} (k : Fin 32)
    (hp : Completed s tops k) (y : BitVec 256) (ho : s.getReg .x12 = W (outAddr k)) :
    Completed (Riscv.writeHash s y) tops k := by
  intro j hj
  have bo := output_bounds k
  have bj := slot_bounds j
  have hn : rootSliceBits j % 8 = 0 := by unfold rootSliceBits; split_ifs <;> decide
  apply writeHash_preserves s y (rootSliceAddr j) (outAddr k) (rootSliceBits j) _ (hp j hj)
    ho bo.2.2 hn
  · unfold rootSliceAddr rootSliceBits outAddr
    split_ifs <;> omega
  · omega
  · exact completed_disjoint j k hj

end OptimalOTS.RiscvMixedProgram
