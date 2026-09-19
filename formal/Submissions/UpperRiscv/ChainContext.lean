import Submissions.UpperRiscv.MachineFacts
import Submissions.UpperRiscv.Reader

/-!
# The machine context of the chain phase

The facts that hold from the end of the index phase to the root: the payload pointer and bits,
the saved public key, the HASH call number and chain input length, the level-tag registers and
the dispatch halfwords (`Ctx`). Writes into chain slots preserve them (`Ctx.frame`).
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

/-- Chain `k`'s value slot. -/
abbrev slotW (k : ℕ) : Word := W (Flat.slotAddr k)

/-- The first instruction of chain `k`'s block. -/
def blockStart (k : ℕ) : ℕ := 4096 + 4 * (indexLength + blockLength * k)

theorem tableEnd_eq (k : ℕ) : tableEnd k = blockStart (k + 1) := rfl

/-- The chain tops of an assignment. -/
def tops (x : graph.Assignment) (k : Fin 32) : BitVec 128 := Forest.trunc (x (cv k 14).fin)

/-- Facts fixed throughout the chain phase. -/
structure Ctx (s : MachineState) (index : Idx) (payload : List Bool) (pk : PublicKey) : Prop where
  payloadReg : s.getReg .x9 = W payloadAddr
  payloadBits : MemBits s (W payloadAddr) (ofBits 4096 payload)
  pk0 : s.getReg .x30 = pk.extractLsb' 0 64
  pk1 : s.getReg .x31 = pk.extractLsb' 64 64
  call : s.getReg .x5 = Riscv.hashCall
  length : s.getReg .x11 = 192
  levels : ∀ t, t < 15 → (s.getReg (levReg t)).truncate 16 = BitVec.ofNat 16 (Flat.levVal t)
  lanes : ∀ k : Fin 32,
    (s.getHalfword (W (laneAddr k))).toNat = jumpBase k - 8 * (15 - pos index k)

/-- The level-tag registers, the call number, the input length and the payload pointer. -/
def CtxReg (r : Reg) : Prop :=
  r = .x9 ∨ r = .x30 ∨ r = .x31 ∨ r = .x5 ∨ r = .x11 ∨ ∃ t, t < 15 ∧ levReg t = r

/-- A memory frame outside the chain slots `[slotAddr k - 8, slotAddr k + 32)`. -/
def SlotFrame (s t : MachineState) (k : ℕ) : Prop :=
  ∀ addr : Word, (addr.toNat + 8 ≤ Flat.slotAddr k - 8 ∨ Flat.slotAddr k + 32 ≤ addr.toNat) →
    t.getMem addr = s.getMem addr

theorem slotAddr_toNat (k : ℕ) (hk : k < 32) : (slotW k).toNat = Flat.slotAddr k :=
  W_toNat _ (by unfold Flat.slotAddr Flat.slotBase; omega)

theorem laneAddr_bounds (k : ℕ) (hk : k < 32) :
    0x200040 ≤ laneAddr k ∧ laneAddr k + 2 ≤ 0x200080 ∧ laneAddr k % 2 = 0 := by
  unfold laneAddr; omega

theorem Ctx.frame {s t : MachineState} {index : Idx} {payload : List Bool} {pk : PublicKey}
    (ctx : Ctx s index payload pk) (k : ℕ) (hk : k < 32)
    (regs : ∀ r, CtxReg r → t.getReg r = s.getReg r) (mem : SlotFrame s t k) :
    Ctx t index payload pk := by
  have hslot : 0x200088 ≤ Flat.slotAddr k ∧ Flat.slotAddr k ≤ 0x200088 + 24 * 31 := by
    unfold Flat.slotAddr Flat.slotBase; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs .x9 (Or.inl rfl)]; exact ctx.payloadReg
  · apply memBits_of_word_frame s t _ _ ctx.payloadBits
    intro i hi
    apply mem
    right
    rw [alignToDword_toNat, BitVec.toNat_add, W_toNat _ (by norm_num [payloadAddr]),
      BitVec.toNat_ofNat]
    unfold payloadAddr
    omega
  · rw [regs .x30 (Or.inr (Or.inl rfl))]; exact ctx.pk0
  · rw [regs .x31 (Or.inr (Or.inr (Or.inl rfl)))]; exact ctx.pk1
  · rw [regs .x5 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact ctx.call
  · rw [regs .x11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact ctx.length
  · intro t' ht
    rw [regs _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t', ht, rfl⟩)))))]
    exact ctx.levels t' ht
  · intro j
    obtain ⟨l1, l2, l3⟩ := laneAddr_bounds j j.isLt
    have e : t.getHalfword (W (laneAddr j)) = s.getHalfword (W (laneAddr j)) := by
      simp only [MachineState.getHalfword]
      rw [mem]
      left
      rw [alignToDword_toNat, W_toNat _ (by omega)]
      omega
    rw [e]
    exact ctx.lanes j

/-- Chain `k`'s slot represents `v`. -/
def Holds (s : MachineState) (k : ℕ) {w : ℕ} (v : BitVec w) : Prop := MemBits s (slotW k) v

end OptimalOTS.RiscvUpperProgram
