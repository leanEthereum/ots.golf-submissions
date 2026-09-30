import Submissions.UpperRiscvHint.MixedProgram
import Submissions.UpperRiscvHint.MachineFacts

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program

def wellPlaced (cursor : ℕ) : List (ℕ × Code) → Bool
  | [] => true
  | (off, body) :: rest => decide (cursor ≤ off) && wellPlaced (off+body.length) rest

theorem fragments_placed : wellPlaced 0 fragments = true := by decide +kernel

theorem keys_complete : ∀ q : Fin 16, ∀ d : Fin (copies q),
    (q.val, d.val) ∈ fragmentKeys := by decide +kernel

theorem mem_insertFragment (a b : ℕ × Code) (parts : List (ℕ × Code)) :
    a ∈ insertFragment b parts ↔ a = b ∨ a ∈ parts := by
  induction parts with
  | nil => simp [insertFragment]
  | cons c rest ih =>
    rw [insertFragment]
    split_ifs <;> simp_all [List.mem_cons, or_left_comm]

theorem mem_addStubs (a : ℕ × Code) (stubs : List ℕ) :
    a ∈ addStubs stubs ↔ a ∈ copyFragments ∨ ∃ ip ∈ stubs, a = (ip-copiesIndex,reject) := by
  induction stubs with
  | nil => simp [addStubs]
  | cons ip rest ih =>
    rw [addStubs, mem_insertFragment, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_addGuards (a : ℕ × Code) (banks : List ℕ) (parts : List (ℕ × Code)) :
    a ∈ addGuards banks parts ↔ a ∈ parts ∨
      ∃ bank ∈ banks, a = (guardStart bank-copiesIndex,guardCode) := by
  induction banks with
  | nil => simp [addGuards]
  | cons bank rest ih =>
    rw [addGuards, mem_insertFragment, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_addHelpers (a : ℕ × Code) (helpers parts : List (ℕ × Code)) :
    a ∈ addHelpers helpers parts ↔ a ∈ parts ∨ a ∈ helpers := by
  induction helpers with
  | nil => simp [addHelpers]
  | cons p rest ih =>
    rw [addHelpers, mem_insertFragment, ih]
    simp only [List.mem_cons]
    tauto

/-- Generic placement proof: checking the small fragment metadata is enough; do not
reduce the whole image once for every copy. -/
theorem assemble_located (s : MachineState) (base : ℕ) (parts : List (ℕ × Code)) :
    ∀ cursor, wellPlaced cursor parts = true →
    Riscv.CodeAt s (W (base+4*cursor)) (assemble cursor parts) →
    ∀ off body, (off, body) ∈ parts → Riscv.CodeAt s (W (base+4*off)) body := by
  induction parts with
  | nil => intro cursor placed located off body mem; simp at mem
  | cons part rest ih =>
    rcases part with ⟨pos, code⟩
    intro cursor placed located off body mem
    have hp : cursor ≤ pos ∧ wellPlaced (pos+code.length) rest = true := by
      simpa only [wellPlaced, Bool.and_eq_true, decide_eq_true_eq] using placed
    rw [assemble, List.append_assoc] at located
    have hc := located.append_right
    rw [List.length_replicate, W_add] at hc
    have addr : base+4*cursor+4*(pos-cursor) = base+4*pos := by omega
    rw [addr] at hc
    rcases List.mem_cons.mp mem with same | later
    · cases same
      exact hc.append_left
    · have ht := hc.append_right
      rw [W_add] at ht
      have addr2 : base+4*pos+4*code.length = base+4*(pos+code.length) := by omega
      rw [addr2] at ht
      exact ih (pos+code.length) hp.2 ht off body later

theorem CodeAt.drop {s : MachineState} {pc : Word} {code : List Instr}
    (located : Riscv.CodeAt s pc code) (i : ℕ) :
    Riscv.CodeAt s (pc+BitVec.ofNat 64 (4*i)) (code.drop i) := by
  intro n hn
  have h := located (i+n) (by rw [List.length_drop] at hn; omega)
  rw [List.getElem?_drop, ← h, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem copy_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (q : Fin 16) (d : Fin (copies q)) :
    Riscv.CodeAt s (W (copyStart q d)) (copyCode q d) := by
  have ht := global.append_right (first := indexPhase ++ freeDispatch ++ freeRow ++ prologue 0) (last := tables)
  rw [show (indexPhase ++ freeDispatch ++ freeRow ++ prologue 0).length = copiesIndex by decide,
    W_add] at ht
  have mem : (groupOffset (group q)+256*(15-d.val)+slotOffset q, copyCode q d) ∈ fragments :=
    (mem_addHelpers _ _ _).mpr (Or.inl ((mem_addGuards _ _ _).mpr (Or.inl ((mem_addStubs _ _).mpr (Or.inl
      (List.mem_map.mpr ⟨(q.val,d.val), keys_complete q d, rfl⟩))))))
  have h := assemble_located s copiesStart fragments 0 fragments_placed ht _ _ mem
  exact h

theorem rejectStub_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (ip : ℕ) (hi : ip ∈ rejectStubs) :
    Riscv.CodeAt s (W (4096+4*ip)) reject := by
  have ht := global.append_right (first := indexPhase ++ freeDispatch ++ freeRow ++ prologue 0) (last := tables)
  rw [show (indexPhase ++ freeDispatch ++ freeRow ++ prologue 0).length = copiesIndex by decide,
    W_add] at ht
  have mem : (ip-copiesIndex,reject) ∈ fragments :=
    (mem_addHelpers _ _ _).mpr (Or.inl ((mem_addGuards _ _ _).mpr (Or.inl ((mem_addStubs _ _).mpr (Or.inr ⟨ip,hi,rfl⟩)))))
  have h := assemble_located s copiesStart fragments 0 fragments_placed ht _ _ mem
  have hb : copiesIndex ≤ ip := by
    obtain ⟨bank, hbank, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hbank
    unfold copiesIndex guardStart
    omega
  have he : copiesStart+4*(ip-copiesIndex) = 4096+4*ip := by unfold copiesStart; omega
  simpa only [he] using h

/-- Every length bank other than the honest bank has a reserved rejection row. -/
theorem guard_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (bank : ℕ) (hb : 4 ≤ bank) (hu : bank ≤ 512) :
    Riscv.CodeAt s (W (4096+4*guardStart bank)) guardCode := by
  have ht := global.append_right (first := indexPhase ++ freeDispatch ++ freeRow ++ prologue 0)
    (last := tables)
  rw [show (indexPhase ++ freeDispatch ++ freeRow ++ prologue 0).length = copiesIndex by decide,
    W_add] at ht
  have member : bank ∈ guardBanks := by
    apply List.mem_map.mpr
    exact ⟨bank-4, List.mem_range.mpr (by omega), by omega⟩
  have mem : (guardStart bank-copiesIndex,guardCode) ∈ fragments :=
    (mem_addHelpers _ _ _).mpr (Or.inl ((mem_addGuards _ _ _).mpr (Or.inr ⟨bank,member,rfl⟩)))
  have h := assemble_located s copiesStart fragments 0 fragments_placed ht _ _ mem
  have he : copiesStart+4*(guardStart bank-copiesIndex) = 4096+4*guardStart bank := by
    unfold copiesStart copiesIndex guardStart
    omega
  simpa only [he] using h

theorem helper_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (q : Fin 16) (a b x y : ℕ) (h : ((a,b),(x,y)) ∈ WeightedPairs.swapsOf (capPair q.val))
    (hb : copiesIndex ≤ helperStart q a b) :
    Riscv.CodeAt s (W (4096+4*helperStart q a b)) (helperCode q a b x y) := by
  have ht := global.append_right (first := indexPhase ++ freeDispatch ++ freeRow ++ prologue 0)
    (last := tables)
  rw [show (indexPhase ++ freeDispatch ++ freeRow ++ prologue 0).length = copiesIndex by decide,
    W_add] at ht
  have mem : (helperStart q a b-copiesIndex, helperCode q a b x y) ∈ fragments := by
    apply (mem_addHelpers _ _ _).mpr
    right
    apply List.mem_flatMap.mpr
    refine ⟨q.val, List.mem_range.mpr q.isLt, ?_⟩
    exact List.mem_map.mpr ⟨((a,b),(x,y)), h, rfl⟩
  have located := assemble_located s copiesStart fragments 0 fragments_placed ht _ _ mem
  have he : copiesStart+4*(helperStart q a b-copiesIndex) = 4096+4*helperStart q a b := by
    unfold copiesStart
    omega
  simpa only [he] using located

end OptimalOTS.RiscvMixedProgram
