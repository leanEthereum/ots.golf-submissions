import Submissions.UpperRiscvHint.MixedDispatch

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

def leftChain (q : Fin 16) : Chain := ⟨2*q.val+1, by have := q.isLt; omega⟩
def rightChain (q : Fin 16) : Chain := ⟨2*q.val+2, by have := q.isLt; omega⟩
def nextCode (q : ℕ) : Code := if q=15 then root ++ decision else prologue (q+1)
def lengthSetup (q : ℕ) : Code :=
  if q=6 then [.ADDI .x11 .x0 144] else []

theorem hashRow_length (q d : ℕ) : (hashRow q d).length = 2^fineWidth q := by
  simp [hashRow]

set_option maxRecDepth 100000 in
theorem hashRow_drop : ∀ q a d : Fin 16, a.val+d.val ≤ pairCap q →
    (hashRow q d).drop (15-a.val+lead q) = List.replicate (a.val+1-lead q) Instr.ECALL := by
  decide +kernel

theorem prologue_parts (q : Fin 16) : prologue q = lengthSetup q ++ dispatchCode q := by
  unfold prologue lengthSetup dispatchCode dispatchFront prevInput laneAddr
  simp only [show 2*q.val+1 ≠ 0 by omega, if_false, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, List.append_assoc, List.cons_append, List.nil_append]

theorem right_previous (q : Fin 16) : prevInput (rightChain q) = work (leftChain q) := by
  unfold prevInput leftChain rightChain
  rw [if_neg (by omega : 2*q.val+2 ≠ 0)]
  congr 1

theorem remaining_left (index : RawIdx) (q : Fin 16) :
    remaining index (leftChain q) = digit index.val (2*q.val) + 1 - lead q := by
  rw [steps_eq_digit, ← lead_pair q.val 0 (by omega)]
  simp only [leftChain, Nat.add_zero, chainDigit_succ]
  rfl

theorem remaining_right (index : RawIdx) (q : Fin 16) :
    remaining index (rightChain q) = digit index.val (2*q.val+1) + 1 - lead q := by
  rw [steps_eq_digit, ← lead_pair q.val 1 (by omega)]
  simp only [rightChain, show 2*q.val+2 = (2*q.val+1)+1 by omega, chainDigit_succ]

/-- Code reached by the packed two-digit jump, including the second chain and next prologue. -/
theorem landing_located (index : RawIdx) (s : MachineState)
    (global : Riscv.CodeAt s (W 4096) verifier) (q : Fin 16)
    (good : digit index.val (2*q.val)+coarseDigit index q ≤ pairCap q) :
    Riscv.CodeAt s (W (landing0 q+4*lead q-dispatch index q))
      (List.replicate (remaining index (leftChain q)) Instr.ECALL ++
       enter (rightChain q) (prevInput (rightChain q)) ++
       List.replicate (remaining index (rightChain q)) Instr.ECALL ++ nextCode q) := by
  let d := coarseDigit index q
  have hd : d < copies q := coarseDigit_lt_copies index q q.isLt
  have ha := fineDigit_lt index q q.isLt
  have hl := lead_le q
  let off := 2^fineWidth q-1-digit index.val (2*q.val)+lead q
  have hOff : off ≤ 2^fineWidth q := by
    have : digit index.val (2*q.val) < 16 := by simpa [fineWidth] using ha
    dsimp only [off, fineWidth]
    omega
  have hRemain : digit index.val (2*q.val)+1-lead q = remaining index (leftChain q) :=
    (remaining_left index q).symm
  have hSecond : d+1-lead q = remaining index (rightChain q) :=
    (remaining_right index q).symm
  have located := copy_located s global q ⟨d,hd⟩
  have h := CodeAt.drop located off
  change Riscv.CodeAt s (W (copyStart q d)+W (4*off)) ((copyCode q d).drop off) at h
  unfold copyCode at h
  simp only [List.append_assoc] at h
  have hdrop : (hashRow q d).drop off = List.replicate (remaining index (leftChain q)) Instr.ECALL := by
    have hf : digit index.val (2*q.val) < 16 := by simpa [fineWidth] using ha
    have hc : d < 16 := by simpa [copies] using hd
    have ht := hashRow_drop q ⟨digit index.val (2*q.val),hf⟩ ⟨d,hc⟩ good
    rw [← hRemain]
    simpa [fineWidth, off] using ht
  rw [List.drop_append_of_le_length (by rw [hashRow_length]; exact hOff),
    hdrop, hSecond, W_add] at h
  have addr : copyStart q d+4*off = landing0 q+4*lead q-dispatch index q :=
    (pair_landing index q q.isLt).symm
  rw [addr] at h
  rw [right_previous q]
  simpa only [nextCode, rightChain, leftChain, List.append_assoc] using h

end OptimalOTS.RiscvMixedProgram
