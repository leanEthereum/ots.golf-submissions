import Submissions.UpperRiscv.ChainSteps

/-!
# One chain block

The prologue lands on the step of the disclosed position; the steps from there to the end of the
table hash the chain up to its top. The specification's nodes below the disclosed position are
pure and read the disclosed word.
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (payload : List Bool) (pk : PublicKey)

/-! ## Code shapes -/

/-- The three nodes of level `t` of chain `k`. -/
def tripleN (k : Fin 32) (t : ℕ) : List Name :=
  if h : t < 15 then [ci k ⟨t, h⟩, ch k ⟨t, h⟩, cv k ⟨t, h⟩] else []

theorem chainNodes_eq (k : Fin 32) :
    chainNodes k = src k :: (List.range 15).flatMap (tripleN k) := by
  simp only [chainNodes, tripleN, List.finRange, List.range]
  rfl

theorem range_split (p : ℕ) (hp : p ≤ 15) :
    List.range 15 = List.range p ++ List.range' p (15 - p) := by
  have h := @List.range'_append_1 0 p (15 - p)
  rw [Nat.zero_add, Nat.add_sub_cancel' hp] at h
  rw [List.range_eq_range', List.range_eq_range', h]

theorem steps_length (l : List ℕ) : (l.flatMap chainStep).length = 2 * l.length := by
  rw [List.length_flatMap]
  simp [chainStep, List.map_const', List.sum_replicate]
  omega

theorem chainTable_split (p : ℕ) (hp : p ≤ 15) :
    chainTable = (List.range p).flatMap chainStep ++ (List.range' p (15 - p)).flatMap chainStep := by
  rw [chainTable, range_split p hp, List.flatMap_append]

theorem chainTable_length : chainTable.length = 30 := by
  rw [chainTable, steps_length, List.length_range]

theorem chainBlock_length (k : ℕ) : (chainBlock k).length = 39 := by
  rw [chainBlock, List.length_append, chainPrologue_parts, List.length_append,
    prologueLinear_length, chainTable_length]
  rfl

/-- Landing inside a located block. -/
theorem CodeAt.drop {s : MachineState} {pc : Word} {code : List Instr}
    (located : Riscv.CodeAt s pc code) (i : ℕ) :
    Riscv.CodeAt s (pc + BitVec.ofNat 64 (4 * i)) (code.drop i) := by
  intro n hn
  have h := located (i + n) (by rw [List.length_drop] at hn; omega)
  rw [List.getElem?_drop, ← h, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

/-! ## The steps from the disclosed position -/

/-- Levels `t` to `14` of chain `k`. -/
theorem steps_refines (k : Fin 32) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' cursor : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      StepInv index payload pk u y k 15 → Holds u k (y (cv k 14).fin) →
      Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor)) c) :
    ∀ (n t : ℕ), 15 - t = n → t ≤ 15 → pos index k ≤ t →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      StepInv index payload pk s x k t → Holds s k (x (valueNode k t).fin) →
      Riscv.CodeAt s s.pc ((List.range' t (15 - t)).flatMap chainStep ++ tail) →
      2 * (15 - t) + rest' ≤ fuel →
      Riscv.Refines fuel s
        (runNodes' index payload ((List.range' t (15 - t)).flatMap (tripleN k)) x cursor >>= K)
        (2 * (15 - t) + c) := by
  intro n
  induction n with
  | zero =>
    intro t ht _ _ s x fuel inv held located bound
    have h15 : t = 15 := by omega
    subst h15
    simp only [Nat.sub_self, List.range'_zero, List.flatMap_nil, List.nil_append, runNodes',
      pure_bind, Nat.mul_zero, Nat.zero_add] at located bound ⊢
    have hv : valueNode k 15 = cv k 14 := by simp [valueNode]
    rw [hv] at held
    exact continuation s x inv held located fuel bound
  | succ n ih =>
    intro t hn ht hp s x fuel inv held located bound
    have ht' : t < 15 := by omega
    have hsucc : 15 - t = (15 - (t + 1)) + 1 := by omega
    rw [hsucc] at located bound ⊢
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc] at located
    rw [List.range'_succ, List.flatMap_cons, runNodes'_append, bind_assoc]
    have triple : tripleN k t = [ci k ⟨t, ht'⟩, ch k ⟨t, ht'⟩, cv k ⟨t, ht'⟩] := by
      simp [tripleN, ht']
    rw [triple]
    rw [show 2 * (15 - (t + 1) + 1) + c = 2 + (2 * (15 - (t + 1)) + c) by omega]
    apply step_refines index payload pk k ⟨t, ht'⟩ hp
      (tail := (List.range' (t + 1) (15 - (t + 1))).flatMap chainStep ++ tail)
      (fun r => runNodes' index payload ((List.range' (t + 1) (15 - (t + 1))).flatMap (tripleN k))
        r.1 r.2 >>= K)
      (2 * (15 - (t + 1)) + c) (2 * (15 - (t + 1)) + rest') cursor s x fuel inv
      (by rwa [prev_eq_valueNode]) located (by omega)
    intro u y inv' held' located' left hleft
    exact ih (t + 1) (by omega) (by omega) (by omega) u _ left inv'
      (by rw [show t + 1 = (⟨t, ht'⟩ : Fin 15).val + 1 from rfl, valueNode_succ]; exact held')
      located' (by omega)

/-! ## The specification before the disclosed level -/

/-- Before its disclosed level, a chain's nodes are pure: zeros, then the disclosed word. -/
theorem prefix_run (k : Fin 32) :
    ∀ (q : ℕ), q ≤ pos index k → ∀ (x : graph.Assignment) (cursor : ℕ),
    ∃ x' : graph.Assignment,
      runNodes' index payload (src k :: (List.range q).flatMap (tripleN k)) x cursor =
        pure (x', if q = pos index k then cursor + 128 else cursor) ∧
      (∀ k' : Fin 32, k' ≠ k → x' (cv k' 14).fin = x (cv k' 14).fin) ∧
      (q = pos index k → x' (valueNode k q).fin =
        ofBits (graph.len (valueNode k q).fin)
          ((payload.drop cursor).take (graph.len (valueNode k q).fin))) := by
  intro q
  induction q with
  | zero =>
    intro _ x cursor
    have run : runNodes' index payload (src k :: (List.range 0).flatMap (tripleN k)) x cursor =
        cursorStep index payload x cursor (src k) := by
      simp only [List.range_zero, List.flatMap_nil, runNodes', Prod.mk.eta, bind_pure]
    rw [run, cursorStep_src, valueNode_zero]
    by_cases h0 : pos index k = 0
    · rw [if_pos h0, if_pos h0.symm]
      refine ⟨_, rfl, ?_, ?_⟩
      · intro k' _
        exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
      · intro _
        rw [Function.update_self]
    · rw [if_neg h0, if_neg (fun h => h0 h.symm)]
      refine ⟨_, rfl, ?_, ?_⟩
      · intro k' _
        exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
      · intro h
        exact absurd h.symm h0
  | succ q ih =>
    intro hq x cursor
    obtain ⟨x₁, run₁, frame₁, _⟩ := ih (by omega) x cursor
    have hq15 : q < 15 := by
      have := pos_le index k
      omega
    have hq' : ¬ (q = pos index k) := by omega
    have hnot : ¬ (pos index k ≤ q) := fun h => by omega
    rw [if_neg hq'] at run₁
    have triple : tripleN k q = [ci k ⟨q, hq15⟩, ch k ⟨q, hq15⟩, cv k ⟨q, hq15⟩] := by
      simp [tripleN, hq15]
    have run : runNodes' index payload (src k :: (List.range (q + 1)).flatMap (tripleN k)) x cursor =
        runNodes' index payload [ci k ⟨q, hq15⟩, ch k ⟨q, hq15⟩, cv k ⟨q, hq15⟩] x₁ cursor := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, triple, ← List.cons_append,
        runNodes'_append, run₁, pure_bind]
    rw [run]
    simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hnot, pure_bind,
      Prod.mk.eta, bind_pure]
    have hv : valueNode k (q + 1) = cv k ⟨q, hq15⟩ := valueNode_succ k ⟨q, hq15⟩
    rw [hv]
    by_cases hd : pos index k = q + 1
    · rw [if_pos hd, if_pos hd.symm]
      refine ⟨_, rfl, ?_, ?_⟩
      · intro k' hk'
        rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk' (Name.cv.inj h).1)),
          Function.update_of_ne (fin_ne_of_ne (by simp)),
          Function.update_of_ne (fin_ne_of_ne (by simp))]
        exact frame₁ k' hk'
      · intro _
        rw [Function.update_self]
    · rw [if_neg hd, if_neg (fun h => hd h.symm)]
      refine ⟨_, rfl, ?_, ?_⟩
      · intro k' hk'
        rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk' (Name.cv.inj h).1)),
          Function.update_of_ne (fin_ne_of_ne (by simp)),
          Function.update_of_ne (fin_ne_of_ne (by simp))]
        exact frame₁ k' hk'
      · intro h
        exact absurd h.symm hd

/-! ## The prologue and the jump -/

/-- Machine facts holding between chain blocks: chains before `k` are complete and their tops,
with the headers between them, form the prefix of the root input. -/
structure ChainsInv (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop where
  ctx : Ctx s index payload pk
  slot : s.getReg .x12 = W (prevSlot k)
  pc : s.pc = W (blockStart k)
  done : 1 ≤ k → MemBits s (W Flat.slotBase) (rootAcc (topFun (tops x)) (k - 1))

/-- An even address is unchanged by clearing its low bit. -/
theorem and_not_one_of_even (a : Word) (h : a.toNat % 2 = 0) : a &&& ~~~(1#64) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases hi0 : i = 0
  · subst hi0
    have h0 : a.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]
      simp [h]
    rw [h0]
    decide
  · simp [hi0, hi]

theorem jump_offset_range : ∀ k : Fin 32,
    -2048 ≤ ((tableEnd k : ℤ) - (jumpBase k : ℤ)) ∧ ((tableEnd k : ℤ) - (jumpBase k : ℤ)) < 2048 := by
  decide

theorem tableEnd_bounds (k : ℕ) (hk : k < 32) : 4096 ≤ tableEnd k ∧ tableEnd k < 10000 := by
  unfold tableEnd indexLength blockLength; omega

theorem jumpBase_bounds (k : ℕ) : 5000 ≤ jumpBase k ∧ jumpBase k < 9000 := by
  unfold jumpBase Flat.jumpBase0 Flat.jumpBase1; split_ifs <;> omega

/-- The computed jump lands on step `p` of chain `k`'s table. -/
theorem jump_target (k : Fin 32) (p : ℕ) (hp : p ≤ 15) (v : Word)
    (hv : v.toNat = jumpBase k - 8 * (15 - p)) :
    (v + signExtend12 (imm12 ((tableEnd k : ℤ) - (jumpBase k : ℤ)))) &&& ~~~(1#64) =
      W (blockStart k + 4 * (9 + 2 * p)) := by
  obtain ⟨r1, r2⟩ := jump_offset_range k
  have hj := jumpBase_bounds k
  have ht := tableEnd_bounds k k.isLt
  have hv' : v = W (jumpBase k - 8 * (15 - p)) := by
    apply BitVec.eq_of_toNat_eq
    rw [hv, W_toNat _ (by omega)]
  rw [hv', W_add_imm _ _ r1 r2 (by omega) (by omega)]
  have e : (((jumpBase k - 8 * (15 - p) : ℕ) : ℤ) + ((tableEnd k : ℤ) - (jumpBase k : ℤ))).toNat =
      blockStart k + 4 * (9 + 2 * p) := by
    have : tableEnd k = blockStart k + 156 := by
      unfold tableEnd blockStart indexLength blockLength; ring
    omega
  rw [e]
  apply and_not_one_of_even
  rw [W_toNat _ (by unfold blockStart indexLength blockLength; omega)]
  unfold blockStart
  omega

theorem jalr_transition (s : MachineState) (i : BitVec 12)
    (fetch : s.code s.pc = some (.JALR .x0 .x28 i)) :
    RiscvZkvm.Rv64.step s = some (s.setPC ((s.getReg .x28 + signExtend12 i) &&& ~~~(1#64))) := by
  rw [RiscvZkvm.Rv64.step, fetch]
  rfl

theorem notCtx_of_prologue (r : Reg) (h : CtxReg r) :
    r ≠ .x10 ∧ r ≠ .x12 ∧ r ≠ .x26 ∧ r ≠ .x27 ∧ r ≠ .x28 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | ⟨t, ht, rfl⟩
  all_goals try (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide)
  interval_cases t <;> (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- The disclosed word of chain `k`, read from the payload. -/
theorem payload_words (s : MachineState) (k : ℕ) (hk : k < 32)
    (bits : MemBits s (W payloadAddr) (ofBits 4096 payload)) :
    s.getMem (W (payloadAddr + 16 * k)) = (ofBits 128 (payload.drop (128 * k))).extractLsb' 0 64 ∧
    s.getMem (W (payloadAddr + 16 * k + 8)) = (ofBits 128 (payload.drop (128 * k))).extractLsb' 64 64 := by
  have h := memBits_extract (start := 128 * k) (len := 128) bits (by omega) (by omega)
  rw [ofBits_extract payload (by omega), show 128 * k / 8 = 16 * k by omega, W_add] at h
  have al : alignToDword (W (payloadAddr + 16 * k)) = W (payloadAddr + 16 * k) :=
    aligned_W _ (by unfold payloadAddr; omega) (by unfold payloadAddr; omega)
  have al8 : alignToDword (W (payloadAddr + 16 * k + 8)) = W (payloadAddr + 16 * k + 8) :=
    aligned_W _ (by unfold payloadAddr; omega) (by unfold payloadAddr; omega)
  constructor
  · exact getMem_of_memBits (by decide) al h
  · have h2 := memBits_extract (start := 64) (len := 64) h (by decide) (by decide)
    rw [show (64 : ℕ) / 8 = 8 by norm_num, W_add] at h2
    have := getMem_of_memBits (by decide) al8 h2
    rw [this]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]

/-- Chain `k`'s prologue: the slot receives the disclosed word, the HASH pointers and the header
are set, and control jumps to the step of the disclosed position, at nine cycles. -/
theorem prologue_refines (k : Fin 32) (rest : Code) (s : MachineState)
    (x : graph.Assignment) (inv : ChainsInv index payload pk s x k.val)
    (located : Riscv.CodeAt s s.pc (chainPrologue k ++ rest))
    {fuel : ℕ} {q : OracleComp Spec (Option Bool)} {c : ℕ}
    (continuation : ∀ u : MachineState,
      StepInv index payload pk u x k (pos index k) →
      Holds u k (ofBits 128 (payload.drop (128 * k.val))) → u.code = s.code →
      Riscv.Refines fuel u q c) :
    Riscv.Refines (9 + fuel) s q (9 + c) := by
  have hs := slot_bounds k k.isLt
  have hl := laneAddr_bounds k k.isLt
  rw [chainPrologue_parts, List.append_assoc] at located
  -- readiness of the straight-line part
  have ready : Riscv.LinearReady s (prologueLinear k) := by
    have e : prologueLinear k =
        [.ADDI .x12 .x12 (BitVec.ofNat 12 (if k.val = 0 then 136 else 24)),
          .ADDI .x10 .x12 (imm12 (-8))] ++ (copy128 .x9 (16 * k.val) .x12 0 ++
        [.SD .x12 .x12 (imm12 (-8)),
          .LHU .x28 .x12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ)))]) := by
      simp [prologueLinear]
    rw [e]
    set b2 := [Instr.ADDI .x12 .x12 (BitVec.ofNat 12 (if k.val = 0 then 136 else 24)),
      Instr.ADDI .x10 .x12 (imm12 (-8))].foldl execInstrBr s with hb2
    have b2x12 : b2.getReg .x12 = slotW k := by
      rw [hb2]
      simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ite]
      simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
        show ¬ (Reg.x12 = Reg.x10) by decide, if_false, inv.slot,
        signExtend12_nat _ (show (if k.val = 0 then 136 else 24) < 2048 by split_ifs <;> norm_num),
        W_add, prevSlot_step k k.isLt]
    have b2x9 : b2.getReg .x9 = W payloadAddr := by
      rw [hb2]
      simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ite]
      simp only [show ¬ (Reg.x9 = Reg.x10) by decide, show ¬ (Reg.x9 = Reg.x12) by decide,
        false_and, if_false, inv.ctx.payloadReg]
    refine Riscv.LinearReady.append ⟨rfl, trivial, rfl, trivial, trivial⟩ ?_
    rw [← hb2]
    refine (copy128_ready b2 .x9 .x12 (16 * k.val) 0 (by decide) (by decide) (by decide)
      ?_ ?_ ?_ ?_).append ?_
    · rw [b2x9, signExtend12_nat _ (by omega), W_add]
      exact dword_ok _ (by unfold payloadAddr; omega) (by unfold payloadAddr; omega)
        (by unfold payloadAddr; omega)
    · rw [b2x9, signExtend12_nat _ (by omega), W_add]
      exact dword_ok _ (by unfold payloadAddr; omega) (by unfold payloadAddr; omega)
        (by unfold payloadAddr; omega)
    · rw [b2x12, signExtend12_nat _ (by norm_num), W_add]
      exact dword_ok _ (by omega) (by omega) (by omega)
    · rw [b2x12, signExtend12_nat _ (by norm_num), W_add]
      exact dword_ok _ (by omega) (by omega) (by omega)
    · have b6x12 : ((copy128 .x9 (16 * k.val) .x12 0).foldl execInstrBr b2).getReg .x12 =
          slotW k := by
        rw [copy128_reg _ _ _ _ _ _ (by decide) (by decide), b2x12]
      refine ⟨rfl, ?_, rfl, ?_, trivial⟩
      · show isValidDwordAccess (_ + _) = true
        rw [b6x12, W_sub8 _ (by omega) (by omega)]
        exact dword_ok _ (by omega) (by omega) (by omega)
      · show isValidHalfwordAccess (_ + _) = true
        simp only [execInstrBr, MachineState.getReg_setPC, getReg_store, b6x12]
        rw [lane_offset k k.isLt]
        exact half_ok _ (by omega) (by omega) hl.2.2
  have E := prologueLinear_effect s k k.isLt inv.slot inv.ctx.payloadReg
  set b := (prologueLinear k).foldl execInstrBr s with hb
  have bLocated : Riscv.CodeAt b b.pc
      ([Instr.JALR .x0 .x28 (imm12 ((tableEnd k : ℤ) - (jumpBase k : ℤ)))] ++ rest) := by
    rw [Riscv.linear_fold_pc s _ ready, prologueLinear_length]
    have h := located.append_right
    rw [prologueLinear_length] at h
    exact h.code_eq (Riscv.fold_code s _)
  rw [show 9 + fuel = (prologueLinear k).length + (fuel + 1) by rw [prologueLinear_length]; omega,
    show 9 + c = (prologueLinear k).length + (c + 1) by rw [prologueLinear_length]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hb]
  have fetchJ := bLocated.head
  apply Riscv.Refines.branch fetchJ rfl (fun h => nomatch h) (jalr_transition b _ fetchJ)
  have hx28 : (b.getReg .x28).toNat = jumpBase k - 8 * (15 - pos index k) := by
    rw [E.target, BitVec.toNat_setWidth, inv.ctx.lanes k, Nat.mod_eq_of_lt]
    have := jumpBase_bounds k
    omega
  rw [jump_target k (pos index k) (pos_le index k) _ hx28]
  set u := b.setPC (W (blockStart k + 4 * (9 + 2 * pos index k))) with hu
  have uRegs : ∀ r, u.getReg r = b.getReg r := fun r => by rw [hu]; simp
  have uMem : ∀ addr, u.getMem addr = b.getMem addr := fun addr => by rw [hu]; simp
  have frame : SlotFrame s u k := by
    intro addr haddr
    rw [uMem]
    apply E.frame
    · intro e; rw [e, W_toNat _ (by omega)] at haddr; omega
    · intro e; rw [e, W_toNat _ (by omega)] at haddr; omega
    · intro e; rw [e, W_toNat _ (by omega)] at haddr; omega
  apply continuation u ?_ ?_ (by rw [hu]; simp [E.code])
  · refine ⟨inv.ctx.frame k k.isLt (fun r hr => ?_) frame, ?_, ?_, ?_, rfl, ?_⟩
    · obtain ⟨h10, h12, h26, h27, h28⟩ := notCtx_of_prologue r hr
      rw [uRegs, E.regs r h10 h12 h26 h27 h28]
    · rw [uRegs, E.slot]
    · rw [uRegs, E.input]
    · refine ⟨0, by norm_num, ?_, fun _ => rfl⟩
      rw [uMem, E.header]
      simp [hdrW]
    · intro hk1
      exact rootAcc_frame k.isLt hk1 frame (inv.done hk1)
  · obtain ⟨w0, w1⟩ := payload_words payload s k k.isLt inv.ctx.payloadBits
    apply memBits_of_twoWords (aligned_W _ hs.2.2 (by omega))
    · rw [uMem, E.word0, w0]
    · rw [show slotW k + 8 = W (Flat.slotAddr k + 8) from W_add _ _, uMem, E.word1, w1]

end OptimalOTS.RiscvUpperProgram
