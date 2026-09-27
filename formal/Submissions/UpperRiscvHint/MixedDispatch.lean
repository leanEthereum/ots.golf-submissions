import Submissions.UpperRiscvHint.MixedChain

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name OracleComp
open Riscv2Program

/-- The prologue's first pointer move and its halfword load. -/
def dispatchFront (q : ℕ) : Code :=
  [.ADDI .x12 .x10 (imm12 ((outAddr (2*q+1) : ℤ) - prevInput (2*q+1))),
   .LHU .x28 .x12 (imm12 ((laneAddr q : ℤ) - outAddr (2*q+1)))]

/-- The pointer moves and the jump of pair `q`, after its length setup. -/
def dispatchCode (q : ℕ) : Code :=
  dispatchFront q ++
  [.ADDI .x10 .x12 (imm12 ((work (2*q+1) : ℤ) - outAddr (2*q+1))),
   .JALR .x0 .x28 (imm12 (jumpImm q))]

theorem dispatchCode_length (q : ℕ) : (dispatchCode q).length = 4 := rfl

theorem pointer_to_out' : ∀ q : Fin 16,
    W (prevInput (2*q.val+1)) + signExtend12 (imm12 ((outAddr (2*q.val+1) : ℤ) - prevInput (2*q.val+1))) =
      W (outAddr (2*q.val+1)) := by
  decide +kernel

theorem lane_offset' : ∀ q : Fin 16,
    W (outAddr (2*q+1)) + signExtend12 (imm12 ((laneAddr q : ℤ)-outAddr (2*q+1))) = W (laneAddr q) := by
  decide +kernel

theorem out_to_work' : ∀ q : Fin 16,
    W (outAddr (2*q.val+1)) + signExtend12 (imm12 ((work (2*q.val+1) : ℤ) - outAddr (2*q.val+1))) =
      W (work (2*q.val+1)) := by
  decide +kernel

theorem lane_access' : ∀ q : Fin 16, isValidHalfwordAccess (W (laneAddr q)) = true := by
  decide +kernel

/-- The effect of the pointer move and the halfword load. -/
structure FrontEffect (index : RawIdx) (q : Fin 16) (s a : MachineState) : Prop where
  pc : a.pc = s.pc + 8
  code : a.code = s.code
  mem : a.mem = s.mem
  regs : ∀ r, r ≠ .x12 → r ≠ .x28 → a.getReg r = s.getReg r
  x12 : a.getReg .x12 = W (outAddr (2*q.val+1))
  x28 : (a.getReg .x28).toNat = baseLane q - dispatch index q

theorem dispatchFront_effect (index : RawIdx) (q : Fin 16) (s : MachineState)
    (input : s.getReg .x10 = W (prevInput (2*q.val+1)))
    (lane : (s.getHalfword (W (laneAddr q))).toNat = baseLane q - dispatch index q) :
    Riscv.LinearReady s (dispatchFront q) ∧
      FrontEffect index q s ((dispatchFront q).foldl execInstrBr s) := by
  have e1 : s.getReg .x10 + signExtend12 (imm12 ((outAddr (2*q.val+1) : ℤ) - prevInput (2*q.val+1))) =
      W (outAddr (2*q.val+1)) := by
    rw [input]; exact pointer_to_out' q
  have ready : Riscv.LinearReady s (dispatchFront q) := by
    simp only [dispatchFront, Riscv.LinearReady, Riscv.linearInstruction,
      Riscv.memoryReady, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, true_and,
      and_true]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true, e1, lane_offset' q]
    exact lane_access' q
  refine ⟨ready, ?_, Riscv.fold_code s _, rfl, ?_, ?_, ?_⟩
  · rw [Riscv.linear_fold_pc s _ ready]; rfl
  · intro r h12 h28
    simp [dispatchFront, execInstrBr, getReg_setReg_ite, h12, h28]
  · simp [dispatchFront, execInstrBr, getReg_setReg_ite, e1]
  · simp only [dispatchFront, List.foldl_cons, List.foldl_nil, execInstrBr,
      MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, if_true, and_self, if_false,
      false_and, e1, lane_offset' q]
    have hh : ((s.setReg .x12 (W (outAddr (2 * q.val + 1)))).setPC (s.pc + 4)).getHalfword
        (W (laneAddr q)) = s.getHalfword (W (laneAddr q)) := by
      simp only [MachineState.getHalfword, MachineState.getMem, MachineState.setReg,
        MachineState.setPC]
    rw [hh]
    change ((s.getHalfword (W (laneAddr q))).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (lt_of_lt_of_le (s.getHalfword _).isLt (by norm_num))]
    exact lane

/-- The prologue's pointer moves, its halfword load, and the jump to the table entry. No hash and
no trap occur on the way. -/
theorem dispatch_refines (index : RawIdx) (q : Fin 16) (s : MachineState) (tail : Code)
    (input : s.getReg .x10 = W (prevInput (2*q.val+1)))
    (lane : (s.getHalfword (W (laneAddr q))).toNat = baseLane q - dispatch index q)
    (located : Riscv.CodeAt s s.pc (dispatchCode q ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : (dispatchCode q).length ≤ fuel)
    (continuation : ∀ t : MachineState, t.pc = W (landing0 q + 4 * lead q - dispatch index q) →
      t.getReg .x10 = W (work (2*q.val+1)) → t.getReg .x12 = W (outAddr (2*q.val+1)) →
      (t.getReg .x28).toNat = baseLane q - dispatch index q →
      (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → t.getReg r = s.getReg r) →
      t.mem = s.mem → t.code = s.code →
      Riscv.Refines (fuel - (dispatchCode q).length) t Q c) :
    Riscv.Refines fuel s Q ((dispatchCode q).length + c) := by
  let move : Instr := .ADDI .x10 .x12 (imm12 ((work (2*q.val+1) : ℤ) - outAddr (2*q.val+1)))
  let jump : Instr := .JALR .x0 .x28 (imm12 (jumpImm q))
  have code : Riscv.CodeAt s s.pc (dispatchFront q ++ ([move] ++ ([jump] ++ tail))) := by
    simpa only [dispatchCode, List.append_assoc, List.cons_append, List.nil_append] using located
  obtain ⟨ready, A⟩ := dispatchFront_effect index q s input lane
  set a := (dispatchFront q).foldl execInstrBr s with ha
  have aloc : Riscv.CodeAt a a.pc ([move] ++ ([jump] ++ tail)) := by
    rw [A.pc]
    exact code.append_right.code_eq A.code
  -- the pointer move and the jump, from `a` or its fall-through copy
  have finish : ∀ b : MachineState, b.code = s.code → b.mem = s.mem →
      (∀ r, b.getReg r = a.getReg r) → Riscv.CodeAt b b.pc ([move] ++ ([jump] ++ tail)) →
      Riscv.Refines (fuel - (dispatchCode q).length + 2) b Q (2 + c) := by
    intro b bcode bmem bregs bloc
    have e2 : b.getReg .x12 + signExtend12 (imm12 ((work (2*q.val+1) : ℤ) - outAddr (2*q.val+1))) =
        W (work (2*q.val+1)) := by
      rw [bregs, A.x12]; exact out_to_work' q
    have bready : Riscv.LinearReady b [move] := by
      simp [move, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
    set u := [move].foldl execInstrBr b with hu
    have upc : u.pc = b.pc + 4 := by rw [hu, Riscv.linear_fold_pc b [move] bready]; rfl
    have ucode : u.code = b.code := Riscv.fold_code b [move]
    have umem : u.mem = b.mem := by rw [hu]; rfl
    have u10 : u.getReg .x10 = W (work (2*q.val+1)) := by
      simp [hu, move, execInstrBr, getReg_setReg_ite, e2]
    have uregs : ∀ r, r ≠ .x10 → u.getReg r = b.getReg r := by
      intro r h10
      simp [hu, move, execInstrBr, getReg_setReg_ite, h10]
    have uloc : Riscv.CodeAt u u.pc ([jump] ++ tail) := by
      rw [upc]; exact bloc.append_right.code_eq ucode
    have u28 : (u.getReg .x28).toNat = baseLane q - dispatch index q := by
      rw [uregs .x28 (by decide), bregs]; exact A.x28
    have target := jump_target index q q.isLt (u.getReg .x28) u28
    have transition := jalr_transition u (imm12 (jumpImm q)) uloc.head
    rw [target] at transition
    let t := u.setPC (W (landing0 q + 4 * lead q - dispatch index q))
    have t12 : t.getReg .x12 = W (outAddr (2*q.val+1)) := by
      show u.getReg .x12 = _; rw [uregs .x12 (by decide), bregs, A.x12]
    have tregs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → t.getReg r = s.getReg r := by
      intro r h10 h12 h28
      show u.getReg r = _
      rw [uregs r h10, bregs, A.regs r h12 h28]
    have cont := continuation t rfl u10 t12 u28 tregs (by show u.mem = _; rw [umem, bmem])
      (by show u.code = _; rw [ucode, bcode])
    rw [show fuel - (dispatchCode q).length + 2 =
      [move].length + ((fuel - (dispatchCode q).length) + 1) by simp; omega,
      show 2 + c = [move].length + (c + 1) by simp; omega]
    apply Riscv.Refines.linear _ bloc.append_left bready
    rw [← hu]
    exact Riscv.Refines.branch uloc.head rfl (fun h => nomatch h) transition cont
  have hlen := dispatchCode_length q
  have flen : (dispatchFront q).length = 2 := rfl
  have rest := finish a A.code A.mem (fun _ => rfl) aloc
  rw [show fuel = (dispatchFront q).length + (fuel - (dispatchCode q).length + 2) by omega,
    show (dispatchCode q).length + c = (dispatchFront q).length + (2 + c) by omega]
  apply Riscv.Refines.linear _ code.append_left ready
  rw [← ha]
  exact rest

/-- The prologue points at chain `2q + 1`, loads the pair's halfword and jumps to its table entry;
chain `2q + 1` is then ready to hash its view value. -/
theorem prologue_refines (index : RawIdx) (wire : List Bool) (pk : PublicKey)
    (q : Fin 16) (k : Chain) (hk : k.val = 2*q.val+1) (s : MachineState) (x : graph.Assignment)
    (ctx : Ctx s index wire pk) (input : s.getReg .x10 = W (prevInput k))
    (len : s.getReg .x11 = W (chainBits k)) (payload : PayloadFrom s wire k)
    (done : Completed s (tops x) k) (tail : Code)
    (located : Riscv.CodeAt s s.pc (dispatchCode q ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : (dispatchCode q).length ≤ fuel)
    (continuation : ∀ u, Prepared index wire pk u x k →
      u.pc = W (landing0 q + 4 * lead q - dispatch index q) →
      Riscv.Refines (fuel - (dispatchCode q).length) u Q c) :
    Riscv.Refines fuel s Q ((dispatchCode q).length + c) := by
  apply dispatch_refines index q s tail (by rw [input, hk]) (ctx.lanes q) located Q c fuel hf
  · intro t tpc t10 t12 t28 tregs tmem tcode
    have tctx : Ctx t index wire pk := ctx.prologue q t10 t12 t28 tregs tmem tcode
    have urange : 32 ≤ work k ∧ work k+24 ≤ 0x78000000 := by
      have h := wireOffset_contained k
      unfold honestViewBits at h
      rw [work_eq_view]; omega
    have prep : Prepared index wire pk t x k := by
      refine ⟨⟨tctx, ?_, urange, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [t10, hk]
      · rw [tregs .x11 (by decide) (by decide) (by decide)]; exact len
      · rw [t12, hk]
      · intro j hj; exact memBits_of_mem_eq tmem (payload j (by omega))
      · intro j hj; exact memBits_of_mem_eq tmem (done j hj)
      · exact memBits_of_mem_eq tmem (payload k le_rfl)
    exact continuation t prep tpc

end OptimalOTS.RiscvMixedProgram
