import Submissions.UpperRiscv.MixedProgram
import Submissions.UpperRiscv.MachineFacts

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program

def wellPlaced (cursor : ℕ) : List (ℕ × Code) → Bool
  | [] => true
  | (off, body) :: rest => decide (cursor ≤ off) && wellPlaced (off+body.length) rest

theorem fragments_placed : wellPlaced copiesAt fragments = true := by decide +kernel

theorem mem_insertFragment (a b : ℕ × Code) (parts : List (ℕ × Code)) :
    a ∈ insertFragment b parts ↔ a = b ∨ a ∈ parts := by
  induction parts with
  | nil => simp [insertFragment]
  | cons c rest ih =>
    rw [insertFragment]
    split_ifs <;> simp_all [List.mem_cons, or_left_comm]

theorem mem_foldr_insert (a : ℕ × Code) (parts : List (ℕ × Code)) :
    a ∈ parts.foldr insertFragment [] ↔ a ∈ parts := by
  induction parts with
  | nil => simp
  | cons b rest ih => rw [List.foldr_cons, mem_insertFragment, ih, List.mem_cons]

theorem mem_fragments (a : ℕ × Code) :
    a ∈ fragments ↔ a ∈ copyFragments ∨ ∃ ip ∈ rejectStubs, a = (ip, reject) := by
  unfold fragments
  rw [mem_foldr_insert, List.mem_append, List.mem_map]
  simp only [eq_comm]

theorem keys_complete (q d : ℕ) (hq : q < 16) (hd : d < 16) : (q, d) ∈ fragmentKeys := by
  unfold fragmentKeys
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  exact ⟨q, hq, d, hd, rfl, rfl⟩

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

theorem tables_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier) :
    Riscv.CodeAt s (W (4096+4*copiesAt)) tables := by
  have ht := global.append_right (first := indexPhase ++ freePrologue ++ freeTable ++ prologue 0)
    (last := tables)
  rw [head_length, W_add] at ht
  exact ht

theorem copy_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (q d : ℕ) (hq : q < 16) (hd : d < 16) :
    Riscv.CodeAt s (W (copyStart q d)) (copyCode q d) := by
  have mem : (bodyAt q d, copyCode q d) ∈ fragments :=
    (mem_fragments _).mpr (Or.inl (List.mem_map.mpr ⟨(q, d), keys_complete q d hq hd, rfl⟩))
  exact assemble_located s 4096 fragments copiesAt fragments_placed (tables_located s global) _ _ mem

theorem rejectStub_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (ip : ℕ) (hi : ip ∈ rejectStubs) :
    Riscv.CodeAt s (W (4096+4*ip)) reject := by
  have mem : (ip, reject) ∈ fragments := (mem_fragments _).mpr (Or.inr ⟨ip, hi, rfl⟩)
  exact assemble_located s 4096 fragments copiesAt fragments_placed (tables_located s global) _ _ mem

theorem indexStub_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier) :
    Riscv.CodeAt s (W (4096+4*indexStub)) reject := by
  have h := global.append_left (first := indexPhase)
    (last := freePrologue ++ freeTable ++ prologue 0 ++ tables)
  have h2 := (CodeAt.drop (by simpa only [List.append_assoc] using h) indexStub)
  have e : indexPhase.drop indexStub = reject ++ [.ADDI .x11 .x0 144] := by decide +kernel
  rw [e] at h2
  have h3 := h2.append_left
  rw [W_add] at h3
  exact h3

theorem freeTable_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier) :
    Riscv.CodeAt s (W (4096+4*freeTableAt)) (freeTable ++ prologue 0) := by
  have e : verifier = (indexPhase ++ freePrologue) ++ ((freeTable ++ prologue 0) ++ tables) := by
    simp only [verifier, List.append_assoc]
  rw [e] at global
  have h := global.append_right.append_left
  have e2 : (indexPhase ++ freePrologue).length = freeTableAt := by decide +kernel
  rw [e2, W_add] at h
  exact h

theorem freePrologue_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier) :
    Riscv.CodeAt s (W (4096+4*38)) (freePrologue ++ freeTable ++ prologue 0) := by
  have e : verifier = indexPhase ++ ((freePrologue ++ freeTable ++ prologue 0) ++ tables) := by
    simp only [verifier, List.append_assoc]
  rw [e] at global
  have h := global.append_right.append_left
  rw [index_length, W_add] at h
  exact h

end OptimalOTS.RiscvMixedProgram
