import Submissions.UpperRiscvHint.MixedChain

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name OracleComp
open Riscv2Program

/-- The prologue's first pointer move and its halfword load. -/
def dispatchFront (q : ℕ) : Code :=
  [.ADDI .x12 .x10 (imm12 ((outAddr (2*q) : ℤ) - prevInput (2*q))),
   .LHU .x28 .x12 (imm12 ((laneAddr q : ℤ) - outAddr (2*q)))]

/-- Pair 0 rejects every view whose length is not the honest one, before any trap is possible:
`BNE` from code index 33 to the rejection stub at 600. -/
def rawCheck (q : ℕ) : Code :=
  if q = 0 then [.BNE .x13 .x6 (BitVec.ofNat 13 (4 * (600 - 33)))] else []

/-- The pointer moves and the jump of pair `q`, after its length setup. -/
def dispatchCode (q : ℕ) : Code :=
  dispatchFront q ++ rawCheck q ++
  [.ADDI .x10 .x12 (imm12 ((work (2*q) : ℤ) - outAddr (2*q))),
   .JALR .x0 .x28 (imm12 (jumpImm q))]

theorem dispatchCode_length (q : ℕ) :
    (dispatchCode q).length = 4 + if q = 0 then 1 else 0 := by
  unfold dispatchCode dispatchFront rawCheck
  split_ifs <;> rfl

theorem pointer_to_out' : ∀ q : Fin 16,
    W (prevInput (2*q.val)) + signExtend12 (imm12 ((outAddr (2*q.val) : ℤ) - prevInput (2*q.val))) =
      W (outAddr (2*q.val)) := by
  decide +kernel

theorem lane_offset' : ∀ q : Fin 16,
    W (outAddr (2*q)) + signExtend12 (imm12 ((laneAddr q : ℤ)-outAddr (2*q))) = W (laneAddr q) := by
  decide +kernel

theorem out_to_work' : ∀ q : Fin 16,
    W (outAddr (2*q.val)) + signExtend12 (imm12 ((work (2*q.val) : ℤ) - outAddr (2*q.val))) =
      W (work (2*q.val)) := by
  decide +kernel

theorem lane_access' : ∀ q : Fin 16, isValidHalfwordAccess (W (laneAddr q)) = true := by
  decide +kernel

/-- The effect of the pointer move and the halfword load. -/
structure FrontEffect (index : RawIdx) (q : Fin 16) (s a : MachineState) : Prop where
  pc : a.pc = s.pc + 8
  code : a.code = s.code
  mem : a.mem = s.mem
  regs : ∀ r, r ≠ .x12 → r ≠ .x28 → a.getReg r = s.getReg r
  x12 : a.getReg .x12 = W (outAddr (2*q.val))
  x28 : (a.getReg .x28).toNat = baseLane q - dispatch index q

theorem dispatchFront_effect (index : RawIdx) (q : Fin 16) (s : MachineState)
    (input : s.getReg .x10 = W (prevInput (2*q.val)))
    (lane : (s.getHalfword (W (laneAddr q))).toNat = baseLane q - dispatch index q) :
    Riscv.LinearReady s (dispatchFront q) ∧
      FrontEffect index q s ((dispatchFront q).foldl execInstrBr s) := by
  have e1 : s.getReg .x10 + signExtend12 (imm12 ((outAddr (2*q.val) : ℤ) - prevInput (2*q.val))) =
      W (outAddr (2*q.val)) := by
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
    have hh : ((s.setReg .x12 (W (outAddr (2 * q.val)))).setPC (s.pc + 4)).getHalfword
        (W (laneAddr q)) = s.getHalfword (W (laneAddr q)) := by
      simp only [MachineState.getHalfword, MachineState.getMem, MachineState.setReg,
        MachineState.setPC]
    rw [hh]
    change ((s.getHalfword (W (laneAddr q))).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (lt_of_lt_of_le (s.getHalfword _).isLt (by norm_num))]
    exact lane

theorem bne_transition (s : MachineState) (r r' : Reg) (off : BitVec 13)
    (fetch : s.code s.pc = some (.BNE r r' off)) :
    step s = some (if s.getReg r = s.getReg r' then s.setPC (s.pc + 4)
      else s.setPC (s.pc + signExtend13 off)) := by
  rw [RiscvZkvm.Rv64.step, fetch]
  by_cases h : s.getReg r = s.getReg r' <;> simp [execInstrBr, h]

/-- The prologue's pointer moves, its halfword load, pair 0's raw-form test on an honest length, and
the jump to the table entry. No hash and no trap occur on the way. -/
theorem dispatch_refines (index : RawIdx) (q : Fin 16) (s : MachineState) (tail : Code)
    (input : s.getReg .x10 = W (prevInput (2*q.val)))
    (lane : (s.getHalfword (W (laneAddr q))).toNat = baseLane q - dispatch index q)
    (short : q.val = 0 → s.getReg .x13 = s.getReg .x6)
    (located : Riscv.CodeAt s s.pc (dispatchCode q ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : (dispatchCode q).length ≤ fuel)
    (continuation : ∀ t : MachineState, t.pc = W (landing0 q + 4 * lead q - dispatch index q) →
      t.getReg .x10 = W (work (2*q.val)) → t.getReg .x12 = W (outAddr (2*q.val)) →
      (t.getReg .x28).toNat = baseLane q - dispatch index q →
      (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → t.getReg r = s.getReg r) →
      t.mem = s.mem → t.code = s.code →
      Riscv.Refines (fuel - (dispatchCode q).length) t Q c) :
    Riscv.Refines fuel s Q ((dispatchCode q).length + c) := by
  let move : Instr := .ADDI .x10 .x12 (imm12 ((work (2*q.val) : ℤ) - outAddr (2*q.val)))
  let jump : Instr := .JALR .x0 .x28 (imm12 (jumpImm q))
  have code : Riscv.CodeAt s s.pc (dispatchFront q ++ (rawCheck q ++ ([move] ++ ([jump] ++ tail)))) := by
    simpa only [dispatchCode, List.append_assoc, List.cons_append, List.nil_append] using located
  obtain ⟨ready, A⟩ := dispatchFront_effect index q s input lane
  set a := (dispatchFront q).foldl execInstrBr s with ha
  have aloc : Riscv.CodeAt a a.pc (rawCheck q ++ ([move] ++ ([jump] ++ tail))) := by
    rw [A.pc]
    exact code.append_right.code_eq A.code
  -- the pointer move and the jump, from `a` or its fall-through copy
  have finish : ∀ b : MachineState, b.code = s.code → b.mem = s.mem →
      (∀ r, b.getReg r = a.getReg r) → Riscv.CodeAt b b.pc ([move] ++ ([jump] ++ tail)) →
      Riscv.Refines (fuel - (dispatchCode q).length + 2) b Q (2 + c) := by
    intro b bcode bmem bregs bloc
    have e2 : b.getReg .x12 + signExtend12 (imm12 ((work (2*q.val) : ℤ) - outAddr (2*q.val))) =
        W (work (2*q.val)) := by
      rw [bregs, A.x12]; exact out_to_work' q
    have bready : Riscv.LinearReady b [move] := by
      simp [move, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
    set u := [move].foldl execInstrBr b with hu
    have upc : u.pc = b.pc + 4 := by rw [hu, Riscv.linear_fold_pc b [move] bready]; rfl
    have ucode : u.code = b.code := Riscv.fold_code b [move]
    have umem : u.mem = b.mem := by rw [hu]; rfl
    have u10 : u.getReg .x10 = W (work (2*q.val)) := by
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
    have t12 : t.getReg .x12 = W (outAddr (2*q.val)) := by
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
  by_cases hq : q.val = 0
  · -- the raw-form test falls through on the honest length
    have hr : rawCheck q = [.BNE .x13 .x6 (BitVec.ofNat 13 (4 * (600 - 33)))] := by
      simp [rawCheck, hq]
    rw [hr] at aloc
    rw [if_pos hq] at hlen
    have fetch : a.code a.pc = some (.BNE .x13 .x6 (BitVec.ofNat 13 (4 * (600 - 33)))) :=
      aloc.head
    have eq : a.getReg .x13 = a.getReg .x6 := by
      rw [A.regs .x13 (by decide) (by decide), A.regs .x6 (by decide) (by decide)]
      exact short hq
    have transition := bne_transition a .x13 .x6 _ fetch
    rw [if_pos eq] at transition
    have rest := finish (a.setPC (a.pc + 4)) (by rw [MachineState.code_setPC]; exact A.code)
      A.mem (fun _ => MachineState.getReg_setPC) aloc.tail
    rw [show fuel = (dispatchFront q).length + ((fuel - (dispatchCode q).length + 2) + 1) by
        omega,
      show (dispatchCode q).length + c = (dispatchFront q).length + ((2 + c) + 1) by omega]
    apply Riscv.Refines.linear _ code.append_left ready
    rw [← ha]
    exact Riscv.Refines.branch fetch rfl (fun h => nomatch h) transition rest
  · have hr : rawCheck q = [] := by simp [rawCheck, hq]
    rw [hr, List.nil_append] at aloc
    rw [if_neg hq] at hlen
    have rest := finish a A.code A.mem (fun _ => rfl) aloc
    rw [show fuel = (dispatchFront q).length + (fuel - (dispatchCode q).length + 2) by omega,
      show (dispatchCode q).length + c = (dispatchFront q).length + (2 + c) by omega]
    apply Riscv.Refines.linear _ code.append_left ready
    rw [← ha]
    exact rest

/-- Pair 0's raw-form test: a view of any other length halts rejecting. -/
theorem dispatch_raw (index : RawIdx) (s : MachineState) (tail : Code)
    (global : Riscv.CodeAt s (W 4096) verifier) (pc : s.pc = W blockZero)
    (input : s.getReg .x10 = W hashBase)
    (lane : (s.getHalfword (W (laneAddr 0))).toNat = baseLane 0 - dispatch index 0)
    (long : s.getReg .x13 ≠ s.getReg .x6)
    (located : Riscv.CodeAt s s.pc (dispatchCode 0 ++ tail)) (fuel : ℕ) (hf : 6 ≤ fuel) :
    Riscv.Refines fuel s (pure (some false)) 6 := by
  let check : Instr := .BNE .x13 .x6 (BitVec.ofNat 13 (4 * (600 - 33)))
  have code := located
  rw [dispatchCode, show rawCheck 0 = [check] from rfl, List.append_assoc,
    List.append_assoc] at code
  obtain ⟨ready, A⟩ := dispatchFront_effect index 0 s (by rw [input]; simp [prevInput]) lane
  set a := (dispatchFront ((0 : Fin 16) : ℕ)).foldl execInstrBr s with ha
  have fetch : a.code a.pc = some check := by
    rw [A.pc]; exact (code.append_right.code_eq A.code).head
  have ne : ¬ a.getReg .x13 = a.getReg .x6 := by
    rw [A.regs .x13 (by decide) (by decide), A.regs .x6 (by decide) (by decide)]
    exact long
  have transition := bne_transition a .x13 .x6 _ fetch
  rw [if_neg ne] at transition
  have target : a.pc + signExtend13 (BitVec.ofNat 13 (4 * (600 - 33))) = W (4096 + 4 * 600) := by
    rw [A.pc, pc, signExtend13_nonnegative _ (by norm_num)]
    decide
  rw [target] at transition
  have locReject : Riscv.CodeAt (a.setPC (W (4096 + 4 * 600))) (W (4096 + 4 * 600)) reject :=
    rejectStub_located _ (global.code_eq (by rw [MachineState.code_setPC]; exact A.code)) 600
      (by decide)
  have stop := reject_refines _ (fuel - 3) locReject (by omega)
  rw [show fuel = (dispatchFront 0).length + ((fuel - 3) + 1) by
      rw [show (dispatchFront 0).length = 2 from rfl]; omega,
    show (6 : ℕ) = (dispatchFront 0).length + (3 + 1) from rfl]
  apply Riscv.Refines.linear _ code.append_left ready
  exact Riscv.Refines.branch (s := a) fetch rfl (fun h => nomatch h) transition stop

/-- The prologue points at chain `2q`, loads the pair's halfword and jumps to its table entry;
chain `2q` is then ready to hash its view value. -/
theorem prologue_refines (index : RawIdx) (wire : List Bool) (pk : PublicKey)
    (q : Fin 16) (k : Fin 32) (hk : k.val = 2*q.val) (s : MachineState) (x : graph.Assignment)
    (ctx : Ctx s index wire pk) (input : s.getReg .x10 = W (prevInput k))
    (len : s.getReg .x11 = W (chainBits k)) (payload : PayloadFrom s wire k)
    (done : Completed s (tops x) k) (tail : Code)
    (short : wire.length = honestViewBits)
    (located : Riscv.CodeAt s s.pc (dispatchCode q ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : (dispatchCode q).length ≤ fuel)
    (continuation : ∀ u, Prepared index wire pk u x k →
      u.pc = W (landing0 q + 4 * lead q - dispatch index q) →
      Riscv.Refines (fuel - (dispatchCode q).length) u Q c) :
    Riscv.Refines fuel s Q ((dispatchCode q).length + c) := by
  apply dispatch_refines index q s tail (by rw [input, hk]) (ctx.lanes q) ?_ located Q c fuel hf
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
  · intro _
    rw [ctx.viewLen, ctx.lenWord, short]
    rfl

end OptimalOTS.RiscvMixedProgram
