import Submissions.UpperRiscv.ChainPrologue

/-!
# The hash steps of a chain

Step `t` of chain `k` stores the level tag of `t` in the header's top halfword and hashes the
192-bit header and value in place, exactly as the specification evaluates the nodes
`ci k t`, `ch k t`, `cv k t`.
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (payload : List Bool) (pk : PublicKey)

/-! ## Small facts -/

theorem fin_ne_of_ne {m n : Name} (h : m ≠ n) : m.fin ≠ n.fin :=
  fun e => h (Name.fin_injective e)

theorem mem_support_hash {n : ℕ} (u : BitVec n) (y : BitVec hashBits) :
    y ∈ support (hash u) := by
  have h : support (hash u) = Set.univ := by simp [OptimalOTS.hash]
  rw [h]
  exact Set.mem_univ y

theorem writeHash_regs (w : MachineState) (a : BitVec hashBits) (r : Reg) :
    (Riscv.writeHash w a).getReg r = w.getReg r := by
  simp [Riscv.writeHash]

theorem writeHash_code (w : MachineState) (a : BitVec hashBits) :
    (Riscv.writeHash w a).code = w.code := by
  simp [Riscv.writeHash]

theorem writeHash_pc (w : MachineState) (a : BitVec hashBits) :
    (Riscv.writeHash w a).pc = w.pc + 4 := rfl

/-- The header of chain `k` with level tag `L`. -/
abbrev hdrW (k L : ℕ) : Word := W (Flat.slotAddr k + L * 2 ^ 48)

theorem hdr_eq_hdrW (k : Fin 32) (t : Fin 15) : Forest.hdr k t = hdrW k (Flat.levVal t) := rfl

/-- The node holding chain `k`'s value at position `t ≤ 15`. -/
def valueNode (k : Fin 32) (t : ℕ) : Name :=
  if t = 0 then src k else if h : t ≤ 15 then cv k ⟨t - 1, by omega⟩ else rh

theorem valueNode_zero (k : Fin 32) : valueNode k 0 = src k := by simp [valueNode]

theorem valueNode_succ (k : Fin 32) (t : Fin 15) : valueNode k (t.val + 1) = cv k t := by
  have h : t.val + 1 ≤ 15 := by omega
  simp only [valueNode, Nat.succ_ne_zero, if_false, dif_pos h, Nat.add_sub_cancel]

theorem prev_eq_valueNode (k : Fin 32) (t : Fin 15) : prev k t = valueNode k t.val := by
  unfold prev valueNode
  by_cases h0 : t.val = 0
  · rw [dif_pos h0, if_pos h0]
  · rw [dif_neg h0, if_neg h0, dif_pos (by omega)]

theorem valueNode_len (k : Fin 32) (t : ℕ) (ht : t ≤ 15) : graph.len (valueNode k t).fin = 128 := by
  unfold valueNode
  split_ifs <;> first | exact graph_len_fin _ | omega

/-- A represented graph value yields its low 128 bits. -/
theorem Holds.trunc {s : MachineState} {k : ℕ} {n : Name} {x : graph.Assignment}
    (held : Holds s k (x n.fin)) : Holds s k (Forest.trunc (x n.fin)) := by
  have bound : 0 + 128 ≤ graph.len n.fin := by
    rw [graph_len_fin]
    cases n <;> simp [Name.len]
  have h := memBits_extract (start := 0) (len := 128) held (by decide) bound
  have he : (x n.fin).extractLsb' 0 128 = Forest.trunc (x n.fin) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [Forest.trunc, hi]
  rw [show slotW k + BitVec.ofNat 64 (0 / 8) = slotW k from BitVec.add_zero _, he] at h
  exact h

/-! ## Invariant within a chain -/

/-- Machine facts holding before step `t` of chain `k`. -/
structure StepInv (s : MachineState) (x : graph.Assignment) (k : Fin 32) (t : ℕ) : Prop where
  ctx : Ctx s index payload pk
  slot : s.getReg .x12 = slotW k
  input : s.getReg .x10 = W (Flat.slotAddr k - 8)
  header : ∃ L, L < 2 ^ 16 ∧ s.getMem (W (Flat.slotAddr k - 8)) = hdrW k L ∧ (t = 15 → L = 0)
  pc : s.pc = W (blockStart k + 4 * (9 + 2 * t))
  done : 1 ≤ k.val → MemBits s (W Flat.slotBase) (rootAcc (topFun (tops x)) (k.val - 1))

/-- The three specification steps of level `t` of an evaluated chain, as one hash. -/
def tripleUpdate (x : graph.Assignment) (k : Fin 32) (t : Fin 15) (y : BitVec hashBits) :
    graph.Assignment :=
  Function.update (Function.update (Function.update x (ci k t).fin
      ((Forest.trunc (x (prev k t).fin) ++ hdr k t).cast (graph_len_fin (ci k t)).symm))
    (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm))
    (cv k t).fin ((Forest.trunc (y.cast (graph_len_fin (ch k t)).symm)).cast
      (graph_len_fin (cv k t)).symm)

theorem triple_run (k : Fin 32) (t : Fin 15) (ht : pos index k ≤ t.val)
    (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index payload [ci k t, ch k t, cv k t] x cursor =
      hash ((Forest.trunc (x (prev k t).fin) ++ hdr k t).cast
          (graph_len_fin (ci k t)).symm) >>= fun y => pure (tripleUpdate x k t y, cursor) := by
  have hnd : ¬ (pos index k = t.val + 1) := fun h => by omega
  simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_pos ht, if_neg hnd,
    pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def, Function.update_self,
    tripleUpdate]

theorem tripleUpdate_cv (x : graph.Assignment) (k : Fin 32) (t : Fin 15) (y : BitVec hashBits) :
    tripleUpdate x k t y (cv k t).fin =
      (Forest.trunc (y.cast (graph_len_fin (ch k t)).symm)).cast (graph_len_fin (cv k t)).symm := by
  simp only [tripleUpdate, Function.update_self]

theorem tripleUpdate_ch (x : graph.Assignment) (k : Fin 32) (t : Fin 15) (y : BitVec hashBits) :
    tripleUpdate x k t y (ch k t).fin = y.cast (graph_len_fin (ch k t)).symm := by
  simp only [tripleUpdate]
  rw [Function.update_of_ne (fin_ne_of_ne (by simp)), Function.update_self]

theorem tripleUpdate_other (x : graph.Assignment) (k : Fin 32) (t : Fin 15) (y : BitVec hashBits)
    (n : Name) (h1 : n ≠ ci k t) (h2 : n ≠ ch k t) (h3 : n ≠ cv k t) :
    tripleUpdate x k t y n.fin = x n.fin := by
  simp only [tripleUpdate]
  rw [Function.update_of_ne (fin_ne_of_ne h3), Function.update_of_ne (fin_ne_of_ne h2),
    Function.update_of_ne (fin_ne_of_ne h1)]

/-- The root prefix only reads the tops of the chains up to `j`. -/
theorem rootAcc_congr {c c' : ℕ → BitVec 128} :
    ∀ j, (∀ i, i ≤ j → c i = c' i) → rootAcc c j = rootAcc c' j
  | 0, h => by simp only [rootAcc]; exact h 0 le_rfl
  | j + 1, h => by
    simp only [rootAcc]
    rw [h (j + 1) le_rfl, rootAcc_congr j (fun i hi => h i (by omega))]

theorem tops_congr_prefix {x y : graph.Assignment} (k : ℕ)
    (h : ∀ k' : Fin 32, k'.val < k → x (cv k' 14).fin = y (cv k' 14).fin) :
    rootAcc (topFun (tops x)) (k - 1) = rootAcc (topFun (tops y)) (k - 1) ∨ k = 0 := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · exact Or.inr h0
  · left
    apply rootAcc_congr
    intro i hi
    unfold topFun tops
    split_ifs with hi32
    · rw [h ⟨i, hi32⟩ (by simp; omega)]
    · rfl

theorem minus2 : signExtend12 (BitVec.ofNat 12 4094) = BitVec.ofInt 64 (-2) := by decide

theorem slot_minus2 (k : ℕ) (hk : k < 32) :
    slotW k + signExtend12 (BitVec.ofNat 12 4094) = W (Flat.slotAddr k - 8 + 6) := by
  have hs := slot_bounds k hk
  have e : BitVec.ofNat 12 4094 = imm12 (-2) := by decide
  rw [e, W_add_imm _ _ (by norm_num) (by norm_num) (by omega) (by omega)]
  congr 1
  omega

/-- The header after a level-tag store. -/
theorem header_store (k : ℕ) (hk : k < 32) (L L' : ℕ) (hL : L < 2 ^ 16) (hL' : L' < 2 ^ 16) :
    replaceHalfword (hdrW k L) 3 (BitVec.ofNat 16 L') = hdrW k L' := by
  have hs := slot_bounds k hk
  rw [hdrW, hdrW, W_hdr _ _ (by omega) hL, W_hdr _ _ (by omega) hL', replaceHalfword_append]

/-- The prefix of the root input lies below chain `k`'s header. -/
theorem rootAcc_frame {s t : MachineState} {k : ℕ} (hk : k < 32) (hk1 : 1 ≤ k)
    {c : ℕ → BitVec 128} (frame : SlotFrame s t k)
    (held : MemBits s (W Flat.slotBase) (rootAcc c (k - 1))) :
    MemBits t (W Flat.slotBase) (rootAcc c (k - 1)) := by
  apply memBits_of_word_frame s t _ _ held
  intro i hi
  apply frame
  left
  have hs := slot_bounds k hk
  rw [alignToDword_toNat, BitVec.toNat_add, W_toNat _ (by norm_num [Flat.slotBase]),
    BitVec.toNat_ofNat]
  unfold Flat.slotAddr at hs ⊢
  unfold Flat.slotBase at hs ⊢
  omega

/-- Level `t` of chain `k`: the tag store and the hash, at two cycles. -/
theorem step_refines (k : Fin 32) (t : Fin 15) (ht : pos index k ≤ t.val)
    (tail : Code) (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool))
    (c budget cursor : ℕ) (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : StepInv index payload pk s x k t) (held : Holds s k (x (prev k t).fin))
    (located : Riscv.CodeAt s s.pc (chainStep t ++ tail)) (bound : 2 + budget ≤ fuel)
    (continuation : ∀ (u : MachineState) (y : BitVec hashBits),
      StepInv index payload pk u (tripleUpdate x k t y) k (t.val + 1) →
      Holds u k (tripleUpdate x k t y (cv k t).fin) → Riscv.CodeAt u u.pc tail →
      ∀ left, budget ≤ left → Riscv.Refines left u (K (tripleUpdate x k t y, cursor)) c) :
    Riscv.Refines fuel s (runNodes' index payload [ci k t, ch k t, cv k t] x cursor >>= K)
      (2 + c) := by
  rw [triple_run index payload k t ht]
  simp only [bind_assoc, pure_bind]
  have hs := slot_bounds k k.isLt
  obtain ⟨L, hL, hhdr, -⟩ := inv.header
  -- the tag store
  have fetchSH : s.code s.pc = some (.SH .x12 (levReg t) (BitVec.ofNat 12 4094)) := located.head
  have addrSH : s.getReg .x12 + signExtend12 (BitVec.ofNat 12 4094) = W (Flat.slotAddr k - 8 + 6) := by
    rw [inv.slot]; exact slot_minus2 k k.isLt
  have readySH : Riscv.memoryReady s (.SH .x12 (levReg t) (BitVec.ofNat 12 4094)) := by
    show isValidHalfwordAccess _ = true
    rw [addrSH]
    exact half_ok _ (by omega) (by omega) (by omega)
  set w := execInstrBr s (.SH .x12 (levReg t) (BitVec.ofNat 12 4094)) with hw
  have wEq : w = (s.setMem (W (Flat.slotAddr k - 8))
      (hdrW k (Flat.levVal t))).setPC (s.pc + 4) := by
    rw [hw]
    show (s.setHalfword (s.getReg .x12 + signExtend12 (BitVec.ofNat 12 4094))
      ((s.getReg (levReg t)).truncate 16)).setPC (s.pc + 4) = _
    rw [addrSH, setHalfword_top s _ (by omega) (by omega), hhdr, inv.ctx.levels t t.isLt,
      header_store k k.isLt L _ hL (Flat.levVal_lt t)]
  have wRegs : ∀ r, w.getReg r = s.getReg r := by
    intro r; rw [wEq]; simp
  have wMem : ∀ addr, w.getMem addr =
      if addr = W (Flat.slotAddr k - 8) then hdrW k (Flat.levVal t) else s.getMem addr := by
    intro addr; rw [wEq, MachineState.getMem_setPC, getMem_setMem_ite]
  have wPc : w.pc = s.pc + 4 := by rw [wEq]; rfl
  have wCodeEq : w.code = s.code := by rw [wEq]; simp
  have wCode : Riscv.CodeAt w w.pc ([Instr.ECALL] ++ tail) := by
    rw [wPc]
    exact located.tail.code_eq wCodeEq
  have wFetch : w.code w.pc = some .ECALL := wCode.head
  have wCall : w.getReg .x5 = Riscv.hashCall := by rw [wRegs]; exact inv.ctx.call
  have wLen : w.getReg .x11 = 192 := by rw [wRegs]; exact inv.ctx.length
  have wIn : w.getReg .x10 = W (Flat.slotAddr k - 8) := by rw [wRegs]; exact inv.input
  have wOut : w.getReg .x12 = slotW k := by rw [wRegs]; exact inv.slot
  have wValid : Riscv.hashArgumentsValid w = true := by
    have r1 : isValidOutputRange (W (Flat.slotAddr k - 8)) 24 = true :=
      range_ok _ _ (by omega) (by omega) (by norm_num) (by norm_num)
    have r2 := hashOutput_ok (Flat.slotAddr k) (by omega) (by omega) hs.2.2
    have e24 : ((192 : Word).toNat + 7) / 8 = 24 := rfl
    unfold Riscv.hashArgumentsValid
    rw [wIn, wOut, wLen, e24, r1, Bool.true_and]
    exact r2
  -- the query is the specification's chain input
  have valueW : MemBits w (slotW k) (Forest.trunc (x (prev k t).fin)) := by
    apply memBits_of_word_frame s w _ _ held.trunc
    intro i hi
    rw [wMem, if_neg]
    intro e
    have e' := congrArg BitVec.toNat e
    rw [alignToDword_toNat, BitVec.toNat_add, slotAddr_toNat k k.isLt, BitVec.toNat_ofNat,
      W_toNat _ (by omega)] at e'
    omega
  have hdrM : MemBits w (W (Flat.slotAddr k - 8)) (hdr k t) := by
    have h := memBits_word w (W (Flat.slotAddr k - 8)) (aligned_W _ (by omega) (by omega))
    rw [wMem, if_pos rfl] at h
    rw [hdr_eq_hdrW]
    exact h
  have inputM : MemBits w (W (Flat.slotAddr k - 8)) (Forest.trunc (x (prev k t).fin) ++ hdr k t) := by
    apply memBits_append (by decide) hdrM
    rw [show (64 : ℕ) / 8 = 8 by norm_num, W_add, show Flat.slotAddr k - 8 + 8 = Flat.slotAddr k by omega]
    exact valueW
  have wInput : Riscv.hashInput w = ⟨graph.len (ci k t).fin,
      (Forest.trunc (x (prev k t).fin) ++ hdr k t).cast (graph_len_fin (ci k t)).symm⟩ := by
    apply hashInput_of_memBits wIn
    · rw [wLen, graph_len_fin]; rfl
    · exact (memBits_cast _ _ _ _).mpr inputM
  have blocks : blockCost (graph.len (ci k t).fin) = 1 := by
    rw [graph_len_fin]; show blockCost 192 = 1; decide
  -- compose: tag store, hash, continuation
  rw [show fuel = 1 + ((fuel - 2) + 1) by omega, show 2 + c = 1 + (1 + c) by omega]
  apply Riscv.Refines.steps (Riscv.PureSteps.cons fetchSH rfl (fun h => by cases h)
    (Riscv.linear_step s _ rfl readySH fetchSH) (Riscv.PureSteps.refl _))
  have step := Riscv.Refines.hash (fuel := fuel - 2) wFetch wCall wValid
    (k := fun y => K (tripleUpdate x k t y, cursor)) (c := c) ?_
  · rw [wInput, blocks] at step
    exact step
  intro y
  set v := Riscv.writeHash w y with hv
  have vRegs : ∀ r, v.getReg r = s.getReg r := by
    intro r; rw [hv, writeHash_regs, wRegs]
  have outFrame : ∀ addr, (∀ j, j < 4 → addr ≠ slotW k + BitVec.ofNat 64 (8 * j)) →
      v.getMem addr = w.getMem addr := by
    intro addr outside
    rw [hv, writeHash_frame _ _ _ (by rw [wOut]; exact outside)]
  have frame : SlotFrame s v k := by
    intro addr haddr
    rw [outFrame, wMem, if_neg]
    · intro e; rw [e, W_toNat _ (by omega)] at haddr; omega
    · intro j hj e
      rw [e, BitVec.toNat_add, slotAddr_toNat k k.isLt, BitVec.toNat_ofNat] at haddr
      omega
  have vPc : v.pc = s.pc + 8 := by
    rw [hv, writeHash_pc, wPc, BitVec.add_assoc]; rfl
  have vCode : v.code = s.code := by rw [hv, writeHash_code, wCodeEq]
  have vLocated : Riscv.CodeAt v v.pc tail := by
    rw [vPc]
    have h : Riscv.CodeAt s s.pc (chainStep t ++ tail) := located
    have h2 := h.append_right
    rw [show (chainStep t).length = 2 from rfl] at h2
    exact h2.code_eq vCode
  have answer : Holds v k ((y.cast (graph_len_fin (ch k t)).symm : BitVec (graph.len (ch k t).fin))) := by
    unfold Holds
    apply (memBits_cast _ _ _ _).mpr
    have h := writeHash_memBits w y (by rw [wOut]; exact aligned_W _ hs.2.2 (by omega))
    rw [wOut] at h
    exact h
  have chHeld : Holds v k (tripleUpdate x k t y (ch k t).fin) := by
    rw [tripleUpdate_ch]; exact answer
  have cvHeld : Holds v k (tripleUpdate x k t y (cv k t).fin) := by
    rw [tripleUpdate_cv]
    unfold Holds
    apply (memBits_cast _ _ _ _).mpr
    have h := chHeld.trunc
    rwa [tripleUpdate_ch] at h
  apply continuation v y ?_ cvHeld vLocated (fuel - 2) (by omega)
  refine ⟨inv.ctx.frame k k.isLt (fun r _ => vRegs r) frame,
    by rw [vRegs]; exact inv.slot, by rw [vRegs]; exact inv.input, ?_, ?_, ?_⟩
  · refine ⟨Flat.levVal t, Flat.levVal_lt t, ?_, ?_⟩
    · rw [outFrame, wMem, if_pos rfl]
      intro j hj e
      have e' := congrArg BitVec.toNat e
      rw [W_toNat _ (by omega), BitVec.toNat_add, slotAddr_toNat k k.isLt, BitVec.toNat_ofNat] at e'
      omega
    · intro h15
      have : t.val = 14 := by omega
      rw [show (t : ℕ) = 14 from this]
      rfl
  · rw [vPc, inv.pc, show (8 : Word) = W 8 from rfl, W_add]
    congr 1
  · intro hk1
    have e : rootAcc (topFun (tops (tripleUpdate x k t y))) (k.val - 1) =
        rootAcc (topFun (tops x)) (k.val - 1) := by
      apply rootAcc_congr
      intro i hi
      unfold topFun tops
      split_ifs with hi32
      · rw [tripleUpdate_other x k t y (cv ⟨i, hi32⟩ 14) (by simp) (by simp)]
        intro e
        have := congrArg Fin.val (Name.cv.inj e).1
        simp at this
        omega
      · rfl
    rw [e]
    exact rootAcc_frame k.isLt hk1 frame (inv.done hk1)

end OptimalOTS.RiscvUpperProgram
