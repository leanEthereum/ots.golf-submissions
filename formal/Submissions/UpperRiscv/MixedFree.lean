import Submissions.UpperRiscv.MixedPair
import Submissions.UpperRiscv.MixedFreeArith

/-! The free chain: its first hash, the dispatch on the free digit `v`, and `v` more hashes before
prologue 0; a free digit of 16 or more branches to the rejection after the free jump. -/

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

variable (index : RawIdx) (v : ℕ) (wire : List Bool) (pk : PublicKey) {a : ℕ}

def dispatchFree : Code := [.SUB .x28 .x1 .x29, .JALR .x0 .x28 (imm12 freeImm)]

def freeCost (v c : ℕ) : ℕ := if v < 16 then 6 + v + c else 10

theorem freePrologue_parts : freePrologue = enter 0 (prevInput 0) ++ dispatchFree := rfl

theorem earlyHash_free : earlyHash ((0 : Fin 33) : ℕ) = 1 := by decide

theorem remaining_free (hv : v < 16) : remaining index v 0 = v := by
  have h := steps_eq_digit index v 0 hv
  have hd : digitV index v 0 = v := by simp [digitV]
  have hc : (if isCap (0 : Fin 33) then 0 else 1) = 1 := by decide
  rw [hd, hc] at h
  unfold remaining
  rw [earlyHash_free]
  omega

theorem free_refines (hv : v < 256)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : 5328 ≤ wire.length)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment), v < 16 →
      ChainsInv index v wire pk a u z 1 → Riscv.CodeAt u u.pc (prologue 0) →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z, Payload.graphOff 1)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index v wire pk a s x 0)
    (pc : s.pc = W (4096+4*31))
    (bound : 26 + rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index v (Payload.permute wire) (entryNodes index v 0) x (Payload.graphOff 0) >>=
        fun r => if v < 16 then runNodes' index v (Payload.permute wire) (tableNodes index v 0)
          r.1 r.2 >>= K else pure (some false))
      (freeCost v c) := by
  have global := inv.ctx.code
  have located := freePrologue_located s global
  rw [← pc, freePrologue_parts, List.append_assoc] at located
  have e4 : freeCost v c = 2+2*earlyHash (0 : Fin 33) + (if v < 16 then 2 + v + c else 6) := by
    unfold freeCost
    rw [earlyHash_free]
    split_ifs <;> omega
  rw [e4]
  apply enter_refines index v wire pk 0 (dispatchFree ++ freePad)
    (fun r => if v < 16 then runNodes' index v (Payload.permute wire) (tableNodes index v 0)
      r.1 r.2 >>= K else pure (some false))
    (if v < 16 then 2 + v + c else 6) (20 + rest) hlen ?_ s x fuel inv.ctx inv.input
    (by rw [inv.length]; rfl) inv.payload inv.done inv.tail located
    (by rw [earlyHash_free]; omega)
  intro u z prep locU left hleft
  -- the dispatch
  have ctx := prep.inv.ctx
  let front : Code := [.SUB .x28 .x1 .x29]
  have ready : Riscv.LinearReady u front := by
    simp [front, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  have code : Riscv.CodeAt u u.pc (front ++ ([.JALR .x0 .x28 (imm12 freeImm)] ++ freePad)) := by
    exact locU
  set w := front.foldl execInstrBr u with hw
  have wpc : w.pc = u.pc+4 := rfl
  have wcode : w.code = u.code := rfl
  have wregs : ∀ r, r ≠ .x28 → w.getReg r = u.getReg r := by
    intro r hr; simp [hw, front, execInstrBr, getReg_setReg_ite, hr]
  have w28 : w.getReg .x28 = W 5457 - W (4*v) := by
    simp only [hw, front, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, if_true, ctx.bound, ctx.count]
  have wloc : Riscv.CodeAt w w.pc ([.JALR .x0 .x28 (imm12 freeImm)] ++ freePad) := by
    rw [wpc]; exact code.append_right.code_eq wcode
  have transition := jalr_transition w (imm12 freeImm) wloc.head
  rw [w28, free_target v hv] at transition
  set y := w.setPC (W (4096 + 4*(prologue0At - v))) with hy
  have ymem : y.mem = u.mem := rfl
  have ycode : y.code = u.code := rfl
  have tloc : Riscv.CodeAt y (W (4096+4*(prologue0At - v)))
      ((freeTable ++ prologue 0).drop (255 - v)) := by
    have h := CodeAt.drop (freeTable_located y (ctx.code.code_eq ycode)) (255 - v)
    have e : W (4096+4*freeTableAt) + BitVec.ofNat 64 (4*(255-v)) = W (4096+4*(prologue0At - v)) := by
      rw [show BitVec.ofNat 64 (4*(255-v)) = W (4*(255-v)) from rfl, W_add]
      unfold freeTableAt prologue0At; congr 1; omega
    rw [e] at h
    exact h
  rw [show left = front.length+((left-2)+1) by simp [front]; omega]
  by_cases hs : v < 16
  · simp only [if_pos hs]
    rw [show 2+v+c = front.length+(v+c+1) by simp [front]; omega]
    apply Riscv.Refines.linear front code.append_left ready
    rw [← hw]
    rw [freeTable_low v hs] at tloc
    have prepY : Prepared index v wire pk a y z 0 := by
      apply Prepared.frame index v wire pk prep _ ymem
      exact HashInv.frame index v wire pk prep.inv (work 0)
        (by rw [hy, MachineState.getReg_setPC, wregs .x10 (by decide)]; exact prep.inv.input)
        prep.inv.inputRange (fun r _ h28 => by rw [hy, MachineState.getReg_setPC]; exact wregs r h28)
        rfl rfl
    have run := table_refines index v wire pk 0 (prologue 0) K c rest hlen
      (fun u' z' inv' loc' left' hl' => by
        have e1 : Payload.graphOff (0 : Fin 33) + chainBits 0 = Payload.graphOff 1 := by decide
        rw [e1]
        exact continuation u' z' hs inv' loc' left' hl')
      y z (left-2) prepY (by rw [remaining_free index v hs]; exact tloc)
      (by rw [remaining_free index v hs]; omega)
    rw [remaining_free index v hs] at run
    exact Riscv.Refines.branch wloc.head rfl (fun h => nomatch h) transition
      (by simpa [hy, entryCursor] using run)
  · simp only [if_neg hs]
    rw [show (6 : ℕ) = front.length+(4+1) by simp [front]]
    apply Riscv.Refines.linear front code.append_left ready
    rw [← hw]
    have hi := freeTable_high v (by omega) hv
    have fetch : y.code y.pc = some (.BEQ .x0 .x0
        (BitVec.ofInt 13 (4*((indexStub : ℤ) - (freeTableAt + ((255 - v : ℕ) : ℤ)))))) := by
      have h := tloc 0 (by
        rw [List.length_drop, List.length_append, freeTable_length]; omega)
      rw [List.getElem?_drop, Nat.add_zero, hi] at h
      have e0 : W (4096 + 4*(prologue0At - v)) + BitVec.ofNat 64 (4*0) = y.pc := by
        simp only [Nat.mul_zero]; exact BitVec.add_zero _
      rw [e0] at h
      exact h
    have target := freeBranch_target v (by omega) hv
    have step' : step y = some (y.setPC (W (4096 + 4*indexStub))) := by
      rw [RiscvZkvm.Rv64.step, fetch]
      simp only [execInstrBr, if_true]
      rw [show y.pc = W (4096 + 4*(prologue0At - v)) from rfl, target]
      simp
    have locR : Riscv.CodeAt (y.setPC (W (4096+4*indexStub))) (W (4096+4*indexStub)) reject :=
      (indexStub_located _ (ctx.code.code_eq ycode)).code_eq rfl
    have stop := reject_refines _ (left-2-1) locR (by omega)
    have br := Riscv.Refines.branch fetch (freeBranch_admitted' ⟨v, hv⟩ (by show 16 ≤ v; omega))
      (fun h => nomatch h) step' stop
    exact Riscv.Refines.branch wloc.head rfl (fun h => nomatch h) transition
      (by rw [show left - 2 = (left-2-1)+1 by omega]; exact br)

end OptimalOTS.RiscvMixedProgram
