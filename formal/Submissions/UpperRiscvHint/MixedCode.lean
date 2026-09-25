import Submissions.UpperRiscvHint.MixedProgram
import Submissions.UpperRiscvHint.MachineFacts

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program

/-- Position of a copy in the concrete instruction image. -/
def copyOffset (q d : ℕ) : ℕ :=
  50 + groupOffset (group q) + 256*(copies q-1-d) + slotOffset q

theorem copyStart_eq (q d : ℕ) : copyStart q d = 4096+4*copyOffset q d := by
  unfold copyStart copiesStart copyOffset
  omega

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
    a ∈ addStubs stubs ↔ a ∈ copyFragments ∨ ∃ ip ∈ stubs, a = (ip-50,reject) := by
  induction stubs with
  | nil => simp [addStubs]
  | cons ip rest ih =>
    rw [addStubs, mem_insertFragment, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
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
  have ht := global.append_right (first := indexPhase ++ prologue 0 ++ List.replicate 5 nop) (last := tables)
  rw [show (indexPhase ++ prologue 0 ++ List.replicate 5 nop).length = 50 by decide, W_add] at ht
  have mem : (groupOffset (group q)+256*(15-d.val)+slotOffset q, copyCode q d) ∈ fragments :=
    (mem_addStubs _ _).mpr (Or.inl
      (List.mem_map.mpr ⟨(q.val,d.val), keys_complete q d, rfl⟩))
  have h := assemble_located s copiesStart fragments 0 fragments_placed ht _ _ mem
  exact h

theorem rejectStub_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (ip : ℕ) (hi : ip ∈ rejectStubs) :
    Riscv.CodeAt s (W (4096+4*ip)) reject := by
  have ht := global.append_right (first := indexPhase ++ prologue 0 ++ List.replicate 5 nop) (last := tables)
  rw [show (indexPhase ++ prologue 0 ++ List.replicate 5 nop).length = 50 by decide, W_add] at ht
  have mem : (ip-50,reject) ∈ fragments :=
    (mem_addStubs _ _).mpr (Or.inr ⟨ip,hi,rfl⟩)
  have h := assemble_located s copiesStart fragments 0 fragments_placed ht _ _ mem
  have hb : 50 ≤ ip := by
    simp only [rejectStubs, List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  have he : copiesStart+4*(ip-50) = 4096+4*ip := by unfold copiesStart; omega
  simpa only [he] using h

end OptimalOTS.RiscvMixedProgram
