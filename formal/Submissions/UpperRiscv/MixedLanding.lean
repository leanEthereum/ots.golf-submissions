import Submissions.UpperRiscv.MixedChain
import Submissions.UpperRiscv.MixedDispatch

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

def leftChain (q : Fin 16) : Fin 32 := ⟨2*q.val, by have := q.isLt; omega⟩
def rightChain (q : Fin 16) : Fin 32 := ⟨2*q.val+1, by have := q.isLt; omega⟩
def nextCode (q : ℕ) : Code := if q=15 then root ++ decision else prologue (q+1)
def lengthSetup (q : ℕ) : Code := if q=12 then [.ADDI .x11 .x0 192] else []

theorem prologue_parts (q : Fin 16) : prologue q = lengthSetup q ++
    enter (leftChain q) (prevInput (leftChain q)) ++ dispatchCode q := by
  unfold prologue lengthSetup dispatchCode leftChain prevInput laneAddr
  have he : (2*q.val=0) ↔ (q.val=0) := by omega
  simp only [he, List.append_assoc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem right_previous (q : Fin 16) : prevInput (rightChain q) = work (leftChain q) := by
  unfold prevInput leftChain rightChain
  rw [if_neg (by omega : 2*q.val+1 ≠ 0), Nat.add_sub_cancel]

theorem Prepared.frame {index : Idx} {wire : List Bool} {pk : PublicKey}
    {s t : MachineState} {x : graph.Assignment} {k : Fin 32}
    (prep : Prepared index wire pk s x k) (inv : HashInv index wire pk t x k (work k))
    (mem : t.mem=s.mem) : Prepared index wire pk t x k := by
  refine ⟨inv, ?_⟩
  have h := prep.ready
  split_ifs at *
  · exact holdsAt_frame mem h
  · exact memBits_of_mem_eq mem h

/-- Code reached by the packed two-digit jump, including the second chain and next prologue. -/
theorem landing_located (index : Idx) (s : MachineState)
    (global : Riscv.CodeAt s (W 4096) verifier) (q : Fin 16) :
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
    ((List.replicate (2^fineWidth q-earlyHash (leftChain q)) Instr.ECALL ++
      (enter (rightChain q) (work (leftChain q)) ++
      (List.replicate (d+1-earlyHash (rightChain q)) Instr.ECALL ++ (nextCode q ++ _)))).drop off) at h
  rw [List.drop_append_of_le_length (by simpa only [List.length_replicate] using hOff),
    List.drop_replicate, hRemain, hSecond, ← right_previous q, W_add] at h
  have addr : copyStart q d+4*off = landing0 q-dispatch index q := (pair_landing index q q.isLt).symm
  rw [addr] at h
  refine ⟨List.replicate (copyCapacity q-(copyBody q d).length) nop, ?_⟩
  simpa only [copyBody, List.append_assoc] using h

end OptimalOTS.RiscvMixedProgram
