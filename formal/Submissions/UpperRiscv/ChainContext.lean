import Submissions.UpperRiscv.MachineFacts
import Submissions.UpperRiscv.Reader

/-!
# The machine context of the chain phase

The facts that hold from the end of the index phase to the root: the payload pointer, the saved
public key, the HASH call number and chain input length, the checked signature length and the
dispatch halfwords (`Ctx`). Writes into the answer region of a chain preserve them (`Ctx.frame`).
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

/-- Chain `k`'s value slot. -/
abbrev slotW (k : ℕ) : Word := W (slotAddr k)

/-- The code address of block 0's prologue, right after the index phase. -/
def blockZero : ℕ := 4096 + 4 * indexLength

/-- The chain tops of an assignment. -/
def tops (x : graph.Assignment) (k : Fin 28) : BitVec 256 := (x (cv k 31).fin).cast (lenF_fin _)

theorem laneAddr_bounds (q : ℕ) (hq : q < 16) :
    laneBase ≤ laneAddr q ∧ laneAddr q + 2 ≤ laneBase + 32 ∧ laneAddr q % 2 = 0 := by
  unfold laneAddr laneWordAddr laneGroup laneIdx laneBase
  split_ifs <;> omega

theorem outAddr_eq (k : ℕ) : outAddr k = slotAddr k - 8 := by
  unfold outAddr slotAddr payloadAddr; omega

theorem firstChain_lt (q : ℕ) (hq : q < 16) : firstChain q < 28 := by
  unfold firstChain; split_ifs <;> omega

theorem firstChain_eq_zero (q : ℕ) : firstChain q = 0 ↔ q = 0 := by
  unfold firstChain; split_ifs <;> omega

/-- The input pointer before chain `k`: the public-key pointer before chain `0`, then 24 bytes
below the slot. -/
def prevInput (k : ℕ) : ℕ := if k = 0 then hashBase else slotAddr k - 24

theorem slotAddr_toNat (k : ℕ) (hk : k < 28) : (slotW k).toNat = slotAddr k :=
  W_toNat _ (by unfold slotAddr payloadAddr; omega)

theorem slot_bounds (k : ℕ) (hk : k < 28) :
    payloadAddr ≤ slotAddr k ∧ slotAddr k + 24 ≤ payloadAddr + 24 * 28 ∧ slotAddr k % 8 = 0 := by
  unfold slotAddr payloadAddr; omega

/-! ## The dispatch values -/

/-- The coarse digit of block `q`: the digit of chain `2q + 1` for a pair, none for a single. -/
def coarseDigit (index : Idx) (q : ℕ) : ℕ := if q < 12 then digit index.val (2 * q + 1) else 0

/-- The dispatch value of block `q`: `4 · dA + 1024 · dB`. -/
def dispatch (index : Idx) (q : ℕ) : ℕ :=
  4 * digit index.val (firstChain q) + 1024 * coarseDigit index q

theorem digit_lt_32' (i k : ℕ) : digit i k < 32 := by
  have h := digit_lt i k
  have : 2 ^ wid k ≤ 32 := by unfold wid; split_ifs <;> norm_num
  omega

theorem coarseDigit_lt (index : Idx) (q : ℕ) : coarseDigit index q < 16 := by
  unfold coarseDigit
  split_ifs with hq
  · have h := digit_lt index.val (2 * q + 1)
    have : wid (2 * q + 1) = 4 := by unfold wid; split_ifs <;> omega
    rw [this] at h
    exact h
  · omega

theorem dispatch_le (index : Idx) (q : ℕ) : dispatch index q ≤ 15484 := by
  unfold dispatch
  have := digit_lt_32' index.val (firstChain q)
  have := coarseDigit_lt index q
  omega

/-- Facts fixed throughout the chain phase. -/
structure Ctx (s : MachineState) (index : Idx) (pk : PublicKey) : Prop where
  pk0 : s.getReg .x30 = pk.extractLsb' 0 64
  pk1 : s.getReg .x31 = pk.extractLsb' 64 64
  call : s.getReg .x5 = Riscv.hashCall
  length : s.getReg .x11 = 192
  lanes : ∀ q : Fin 16,
    (s.getHalfword (W (laneAddr q))).toNat = laneBaseOf (laneGroup q) - dispatch index q
  /-- The checked signature length, reused by the root phase to build the root input length. -/
  sigLen : s.getReg .x13 = W 5504
  /-- The whole image is in place: the blocks locate their copies from it. -/
  code : Riscv.CodeAt s (W 4096) verifier

/-- The registers of the context. -/
def CtxReg (r : Reg) : Prop :=
  r = .x30 ∨ r = .x31 ∨ r = .x5 ∨ r = .x11 ∨ r = .x13

/-- A memory frame outside the answer region of chain `k`, `[slotAddr k - 8, slotAddr k + 24)`. -/
def SlotFrame (s t : MachineState) (k : ℕ) : Prop :=
  ∀ addr : Word, (addr.toNat + 8 ≤ slotAddr k - 8 ∨ slotAddr k + 24 ≤ addr.toNat) →
    t.getMem addr = s.getMem addr

theorem Ctx.frame {s t : MachineState} {index : Idx} {pk : PublicKey}
    (ctx : Ctx s index pk) (k : ℕ) (hk : k < 28)
    (regs : ∀ r, CtxReg r → t.getReg r = s.getReg r) (mem : SlotFrame s t k)
    (code : t.code = s.code) :
    Ctx t index pk := by
  have hslot := slot_bounds k hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ctx.code.code_eq code⟩
  · rw [regs .x30 (Or.inl rfl)]; exact ctx.pk0
  · rw [regs .x31 (Or.inr (Or.inl rfl))]; exact ctx.pk1
  · rw [regs .x5 (Or.inr (Or.inr (Or.inl rfl)))]; exact ctx.call
  · rw [regs .x11 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact ctx.length
  · intro q
    obtain ⟨l1, l2, l3⟩ := laneAddr_bounds q q.isLt
    have e : t.getHalfword (W (laneAddr q)) = s.getHalfword (W (laneAddr q)) := by
      simp only [MachineState.getHalfword]
      rw [mem]
      left
      rw [alignToDword_toNat, W_toNat _ (by unfold laneBase at l2; omega)]
      unfold laneBase at l1 l2
      unfold slotAddr payloadAddr at hslot ⊢
      omega
    rw [e]
    exact ctx.lanes q
  · rw [regs .x13 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact ctx.sigLen

/-- The values of chains `k` and later are still their disclosed values. -/
def PayloadFrom (s : MachineState) (payload : List Bool) (k : ℕ) : Prop :=
  ∀ j, k ≤ j → j < 28 → MemBits s (slotW j) (ofBits 192 (payload.drop (192 * j)))

/-- Chain `k`'s slot represents `v`. -/
def Holds (s : MachineState) (k : ℕ) {w : ℕ} (v : BitVec w) : Prop := MemBits s (slotW k) v

end OptimalOTS.Riscv2Program
