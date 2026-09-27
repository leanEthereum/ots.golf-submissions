import Submissions.UpperRiscv.MixedDispatch

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

def leftChain (q : Fin 16) : Fin 33 := ⟨2*q.val+1, by have := q.isLt; omega⟩
def rightChain (q : Fin 16) : Fin 33 := ⟨2*q.val+2, by have := q.isLt; omega⟩
def nextCode (q : ℕ) : Code := if q=15 then root ++ decision else prologue (q+1)
def lengthSetup (q : ℕ) : Code := widthChange (2*q+1) (2*q)

def rowShort (k : ℕ) : ℕ := if shortRow k then 1 else 0

theorem hashRow_length (q d : ℕ) : (hashRow q d).length = 16-rowShort (2*q+1) := by
  simp [hashRow, rowShort]

set_option maxRecDepth 100000 in
theorem hashRow_drop : ∀ q a d : Fin 16, a.val+d.val ≤ pairCap q →
    (hashRow q d).drop (15-a.val) =
      List.replicate (16-rowShort (2*q.val+1)-(15-a.val)) Instr.ECALL := by
  decide +kernel

theorem midWidth' : ∀ q : Fin 16, widthChange (2*q.val+2) (2*q.val+1) = [] := by decide +kernel

theorem prologue_parts (q : Fin 16) : prologue q = lengthSetup q ++
    enter (leftChain q) (prevInput (leftChain q)) ++ dispatchCode q := by
  unfold prologue lengthSetup dispatchCode leftChain prevInput
  simp only [show 2*q.val+1 ≠ 0 by omega, if_false, Nat.add_sub_cancel, List.append_assoc]

theorem right_previous (q : Fin 16) : prevInput (rightChain q) = work (leftChain q) := by
  unfold prevInput leftChain rightChain
  rw [if_neg (by omega : 2*q.val+2 ≠ 0)]
  rfl

theorem shortRow_iff (k : Fin 33) : rowShort k = earlyHash k + (if isCap k then 1 else 0) := by
  revert k; decide +kernel

theorem digitV_left (index : RawIdx) (v : ℕ) (q : Fin 16) :
    digitV index v (leftChain q) = digit index.val (2*q.val) := by
  unfold digitV leftChain; simp

theorem digitV_right (index : RawIdx) (v : ℕ) (q : Fin 16) :
    digitV index v (rightChain q) = coarseDigit index q := by
  unfold digitV rightChain coarseDigit; simp

theorem remaining_left (index : RawIdx) (v : ℕ) (q : Fin 16) (hv : v < 16) :
    remaining index v (leftChain q) = digit index.val (2*q.val)+1-rowShort (leftChain q) := by
  have h := steps_eq_digit index v (leftChain q) hv
  rw [digitV_left] at h
  have hs := shortRow_iff (leftChain q)
  have he := earlyHash_cases (leftChain q)
  unfold remaining
  split_ifs at h hs <;> omega

theorem remaining_right (index : RawIdx) (v : ℕ) (q : Fin 16) (hv : v < 16) :
    remaining index v (rightChain q) = coarseDigit index q+1-rowShort (rightChain q) := by
  have h := steps_eq_digit index v (rightChain q) hv
  rw [digitV_right] at h
  have hs := shortRow_iff (rightChain q)
  have he := earlyHash_cases (rightChain q)
  unfold remaining
  split_ifs at h hs <;> omega

/-- Code reached by the packed two-digit jump, including the second chain and next prologue. -/
theorem landing_located (index : RawIdx) (v : ℕ) (hv : v < 16) (s : MachineState)
    (global : Riscv.CodeAt s (W 4096) verifier) (q : Fin 16)
    (good : digit index.val (2*q.val)+coarseDigit index q ≤ pairCap q) :
    ∃ junk, Riscv.CodeAt s (W (landing0 q-dispatch index q))
      (List.replicate (remaining index v (leftChain q)) Instr.ECALL ++
       enter (rightChain q) (prevInput (rightChain q)) ++
       List.replicate (remaining index v (rightChain q)) Instr.ECALL ++ nextCode q ++ junk) := by
  let d := coarseDigit index q
  have hd : d < 16 := coarseDigit_lt index q
  have ha := fineDigit_lt index q
  have hA := remaining_left index v q hv
  have hB := remaining_right index v q hv
  let off := 15-digit index.val (2*q.val)
  have hOff : off ≤ 16-rowShort (2*q.val+1) := by
    dsimp [off]; unfold rowShort; split_ifs <;> omega
  have located := copy_located s global q d q.isLt hd
  have h := CodeAt.drop located off
  change Riscv.CodeAt s (W (copyStart q d)+W (4*off)) ((copyCode q d).drop off) at h
  unfold copyCode at h
  simp only [List.append_assoc] at h
  rw [midWidth' q, List.nil_append] at h
  have hdrop : (hashRow q d).drop off = List.replicate (remaining index v (leftChain q)) Instr.ECALL := by
    have ht := hashRow_drop q ⟨digit index.val (2*q.val),ha⟩ ⟨d,hd⟩ good
    rw [hA]
    have e : 16-rowShort (2*q.val+1)-(15-digit index.val (2*q.val)) =
        digit index.val (2*q.val)+1-rowShort (leftChain q) := by
      unfold leftChain; unfold rowShort; split_ifs <;> omega
    simpa [off, e] using ht
  have hSecond : d+1-(if shortRow (2*q.val+2) then 1 else 0) = remaining index v (rightChain q) := by
    rw [hB]; rfl
  rw [List.drop_append_of_le_length (by simpa only [hashRow_length] using hOff),
    hdrop, hSecond, W_add] at h
  have e1 : work (2*q.val+1) = prevInput (rightChain q) := (right_previous q).symm
  rw [e1] at h
  have addr : copyStart q d+4*off = landing0 q-dispatch index q := (pair_landing index q).symm
  rw [addr] at h
  refine ⟨[], ?_⟩
  simpa only [nextCode, List.append_assoc, List.append_nil, rightChain] using h

end OptimalOTS.RiscvMixedProgram
