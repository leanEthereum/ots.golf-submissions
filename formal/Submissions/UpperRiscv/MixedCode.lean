import Submissions.UpperRiscv.MixedEntry

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program

/-- Position of a copy in the concrete instruction image. -/
def copyOffset (q d : ℕ) : ℕ :=
  52 + groupOffset (group q) + 128*(copies q-1-d) + 40*withinGroup q

theorem copyStart_eq (q d : ℕ) : copyStart q d = 4096+4*copyOffset q d := by
  unfold copyStart copiesStart copyOffset
  omega

theorem copyCode_length' : ∀ q : Fin 16, ∀ d : Fin (copies q), (copyCode q d).length = copyCapacity q := by
  decide +kernel

theorem group_image' : ∀ g : Fin 6,
    (verifier.drop (52+groupOffset g)).take (groupCode g).length = groupCode g := by
  decide +kernel

theorem copy_group' : ∀ q : Fin 16, ∀ d : Fin (copies q),
    ((groupCode (group q)).drop (128*(copies q-1-d)+40*withinGroup q)).take (copyCapacity q) =
      copyCode q d := by
  decide +kernel

theorem copy_in_group_bounds' : ∀ q : Fin 16, ∀ d : Fin (copies q),
    128*(copies q-1-d)+40*withinGroup q+copyCapacity q ≤ (groupCode (group q)).length := by
  decide +kernel

theorem group_lt' : ∀ q : Fin 16, group q < 6 := by decide +kernel

theorem CodeAt.drop {s : MachineState} {pc : Word} {code : List Instr}
    (located : Riscv.CodeAt s pc code) (i : ℕ) :
    Riscv.CodeAt s (pc+BitVec.ofNat 64 (4*i)) (code.drop i) := by
  intro n hn
  have h := located (i+n) (by rw [List.length_drop] at hn; omega)
  rw [List.getElem?_drop, ← h, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem copy_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (q : Fin 16) (d : Fin (copies q)) :
    Riscv.CodeAt s (W (copyStart q d)) (copyCode q d) := by
  have hg := CodeAt.drop global (52+groupOffset (group q))
  have eg := List.take_append_drop (groupCode (group q)).length
    (verifier.drop (52+groupOffset (group q)))
  rw [group_image' ⟨group q, group_lt' q⟩] at eg
  rw [← eg] at hg
  have hc := CodeAt.drop hg.append_left (128*(copies q-1-d)+40*withinGroup q)
  have ec := List.take_append_drop (copyCapacity q)
    ((groupCode (group q)).drop (128*(copies q-1-d)+40*withinGroup q))
  rw [copy_group' q d] at ec
  rw [← ec] at hc
  have h := hc.append_left
  rw [W_add, W_add] at h
  have e : 4096+4*(52+groupOffset (group q))+4*(128*(copies q-1-d)+40*withinGroup q) =
      copyStart q d := by rw [copyStart_eq]; unfold copyOffset; omega
  rw [e] at h
  exact h

end OptimalOTS.RiscvMixedProgram
