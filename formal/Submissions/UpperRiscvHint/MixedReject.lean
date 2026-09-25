import Submissions.UpperRiscvHint.MixedLanding

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

def landingIP (q a d : ℕ) : ℕ :=
  50 + groupOffset (group q) + 256*(15-d) + slotOffset q + (15-a)
def rejectJump (ip : ℕ) : Instr :=
  .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((stubFor ip : ℤ)-ip)))

set_option maxRecDepth 100000 in
theorem rejecting_landing_facts : ∀ q a d : Fin 16, pairCap q < a.val+d.val →
    (15-a.val < (hashRow q d).length) ∧
    rowInstr q d (15-a.val) = rejectJump (landingIP q a d) ∧
    stubFor (landingIP q a d) ∈ rejectStubs ∧
    Riscv.admittedInstruction (rejectJump (landingIP q a d)) = true ∧
    W (4096+4*landingIP q a d) +
        signExtend13 (BitVec.ofInt 13 (4*((stubFor (landingIP q a d) : ℤ)-landingIP q a d))) =
      W (4096+4*stubFor (landingIP q a d)) := by
  decide +kernel

theorem landing_reject_refines (index : RawIdx) (q : Fin 16) (s : MachineState)
    (global : Riscv.CodeAt s (W 4096) verifier)
    (pc : s.pc = W (landing0 q-dispatch index q))
    (bad : pairCap q < digit index.val (2*q.val)+coarseDigit index q)
    (fuel : ℕ) (bound : 4 ≤ fuel) :
    Riscv.Refines fuel s (pure (some false)) 4 := by
  let a : Fin 16 := ⟨digit index.val (2*q.val), by
    simpa [fineWidth] using fineDigit_lt index q q.isLt⟩
  let d : Fin 16 := ⟨coarseDigit index q, coarseDigit_lt index q⟩
  let ip := landingIP q a d
  obtain ⟨hlen, hrow, hstub, hadmit, htarget⟩ := rejecting_landing_facts q a d bad
  have loc := copy_located s global q ⟨d.val, by simpa [copies] using d.isLt⟩
  have fetch := loc (15-a.val) (by
    simp only [copyCode, copyBody, List.length_append]; omega)
  have head : (copyCode q d)[15-a.val]? = some (rowInstr q d (15-a.val)) := by
    simp only [copyCode, copyBody, List.append_assoc, List.getElem?_append, hlen, ↓reduceIte]
    simp only [hashRow, List.getElem?_map, List.getElem?_range, hlen,
      show 15-a.val < 2^fineWidth q-(if expands (2*q.val) then 1 else 0) by
        simpa [hashRow] using hlen, ↓reduceIte, Option.map_some]
  have addr : copyStart q d+4*(15-a.val) = landing0 q-dispatch index q := by
    simpa [fineWidth, a, d] using (pair_landing index q q.isLt).symm
  have ipc : 4096+4*ip = landing0 q-dispatch index q := by
    rw [← addr]
    simp only [ip, landingIP, copyStart, copiesStart, copies]
    omega
  rw [head, hrow, W_add, addr, ← pc] at fetch
  have transition : step s = some (s.setPC (W (4096+4*stubFor ip))) := by
    rw [RiscvZkvm.Rv64.step, fetch]
    simp only [rejectJump, execInstrBr, if_true]
    rw [pc, ← ipc]
    exact congrArg (fun p => some (s.setPC p)) htarget
  have locReject : Riscv.CodeAt (s.setPC (W (4096+4*stubFor ip)))
      (W (4096+4*stubFor ip)) reject :=
    (rejectStub_located s global (stubFor ip) hstub).code_eq rfl
  have stop := reject_refines _ (fuel-1) locReject (by omega)
  rw [show fuel=(fuel-1)+1 by omega, show (4 : ℕ)=3+1 by omega]
  exact Riscv.Refines.branch fetch hadmit (fun h => nomatch h) transition stop

end OptimalOTS.RiscvMixedProgram
