import Submissions.UpperRiscv.MixedEntry

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
  have ht := global.append_right (first := indexPhase ++ prologue 0) (last := tables)
  rw [show (indexPhase ++ prologue 0).length = 50 by decide, W_add] at ht
  have mem : (groupOffset (group q)+256*(15-d.val)+slotOffset q, copyCode q d) ∈ fragments :=
    List.mem_map.mpr ⟨(q.val,d.val), keys_complete q d, rfl⟩
  have h := assemble_located s copiesStart fragments 0 fragments_placed ht _ _ mem
  exact h

end OptimalOTS.RiscvMixedProgram
