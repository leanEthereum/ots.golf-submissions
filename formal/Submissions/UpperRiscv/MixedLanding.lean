import Submissions.UpperRiscv.MixedChain
import Submissions.UpperRiscv.MixedDispatch

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

def leftChain (q : Fin 16) : Fin 32 := ⟨2*q.val, by have := q.isLt; omega⟩
def rightChain (q : Fin 16) : Fin 32 := ⟨2*q.val+1, by have := q.isLt; omega⟩
def nextCode (q : ℕ) : Code := if q=15 then root ++ decision else prologue (q+1)
def lengthSetup (q : ℕ) : Code :=
  if q=8 then [.ADDI .x11 .x0 192] else []

theorem hashRow_length (q d : ℕ) : (hashRow q d).length =
    2^fineWidth q-earlyHash (2*q) := by
  simp [hashRow, earlyHash]

set_option maxRecDepth 100000 in
theorem hashRow_drop : ∀ q a d : Fin 16, a.val+d.val ≤ pairCap q →
    (hashRow q d).drop (15-a.val) =
      List.replicate (16-earlyHash (2*q.val)-(15-a.val)) Instr.ECALL := by
  decide +kernel

theorem prologue_parts (q : Fin 16) : prologue q = lengthSetup q ++
    enter (leftChain q) (prevInput (leftChain q)) ++ dispatchCode q := by
  unfold prologue lengthSetup dispatchCode leftChain prevInput laneAddr
  have he : (2*q.val=0) ↔ (q.val=0) := by omega
  simp only [he, List.append_assoc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem right_previous (q : Fin 16) : prevInput (rightChain q) = work (leftChain q) := by
  unfold prevInput leftChain rightChain
  rw [if_neg (by omega : 2*q.val+1 ≠ 0), Nat.add_sub_cancel]

theorem Prepared.frame {index : RawIdx} {wire : List Bool} {pk : PublicKey}
    {s t : MachineState} {x : graph.Assignment} {k : Fin 32}
    (prep : Prepared index wire pk s x k) (inv : HashInv index wire pk t x k (work k))
    (mem : t.mem=s.mem) : Prepared index wire pk t x k := by
  refine ⟨inv, ?_⟩
  have h := prep.ready
  split_ifs at *
  · exact holdsAt_frame mem h
  · exact memBits_of_mem_eq mem h

/-- Code reached by the packed two-digit jump, including the second chain and next prologue. -/
theorem landing_located (index : RawIdx) (s : MachineState)
    (global : Riscv.CodeAt s (W 4096) verifier) (q : Fin 16)
    (good : digit index.val (2*q.val)+coarseDigit index q ≤ pairCap q) :
    ∃ junk, Riscv.CodeAt s (W (landing0 q-dispatch index q))
      (List.replicate (remaining index (leftChain q)) Instr.ECALL ++
       enter (rightChain q) (prevInput (rightChain q)) ++
       List.replicate (remaining index (rightChain q)) Instr.ECALL ++ nextCode q ++ junk) := by
  let d := coarseDigit index q
  have hd : d < copies q := coarseDigit_lt_copies index q q.isLt
  have ha := fineDigit_lt index q q.isLt
  have hA := steps_eq_digit index (leftChain q)
  have hB := steps_eq_digit index (rightChain q)
  have bA := earlyHash_cases (leftChain q)
  have bB := earlyHash_cases (rightChain q)
  have hp : 0 < 2^fineWidth q := by positivity
  let off := 2^fineWidth q-1-digit index.val (2*q.val)
  have hOff : off ≤ 2^fineWidth q-earlyHash (leftChain q) := by dsimp [off]; omega
  have hRemain : 2^fineWidth q-earlyHash (leftChain q)-off = remaining index (leftChain q) := by
    unfold remaining
    change 32-RiscvUpperForest.ForestVerifier.pos index (leftChain q) = digit index.val (2*q.val)+1 at hA
    dsimp [off]; omega
  have hSecond : d+1-earlyHash (rightChain q) = remaining index (rightChain q) := by
    unfold remaining
    rw [hB]
    rfl
  have located := copy_located s global q ⟨d,hd⟩
  have h := CodeAt.drop located off
  change Riscv.CodeAt s (W (copyStart q d)+W (4*off)) ((copyCode q d).drop off) at h
  unfold copyCode copyBody at h
  simp only [List.append_assoc] at h
  change Riscv.CodeAt s (W (copyStart q d)+W (4*off))
    ((hashRow q d ++
      (enter (rightChain q) (work (leftChain q)) ++
      (List.replicate (d+1-earlyHash (rightChain q)) Instr.ECALL ++ (nextCode q ++ _)))).drop off) at h
  have hdrop : (hashRow q d).drop off = List.replicate (remaining index (leftChain q)) Instr.ECALL := by
    have hf : digit index.val (2*q.val) < 16 := by simpa [fineWidth] using ha
    have hc : d < 16 := by simpa [copies] using hd
    have ht := hashRow_drop q ⟨digit index.val (2*q.val),hf⟩ ⟨d,hc⟩ good
    simpa [fineWidth, off, leftChain] using ht.trans (congrArg (fun n => List.replicate n Instr.ECALL) hRemain)
  rw [List.drop_append_of_le_length (by simpa only [hashRow_length, leftChain] using hOff),
    hdrop, hSecond, ← right_previous q, W_add] at h
  have addr : copyStart q d+4*off = landing0 q-dispatch index q := (pair_landing index q q.isLt).symm
  rw [addr] at h
  refine ⟨[], ?_⟩
  simpa only [copyBody, List.append_assoc] using h

end OptimalOTS.RiscvMixedProgram
