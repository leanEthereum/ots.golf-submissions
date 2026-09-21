import Submissions.UpperRiscv.ChainSteps

/-!
# One chain block

The prologue lands on the hash step of the disclosed position; the steps from there to the end of
the table hash the chain up to its top. The specification's nodes below the disclosed position
are pure zeros.
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (payload : List Bool) (pk : PublicKey)

/-! ## Code shapes -/

/-- The three nodes of level `t` of chain `k`. -/
def tripleN (k : Fin 28) (t : ℕ) : List Name :=
  if h : t < 32 then [ci k ⟨t, h⟩, ch k ⟨t, h⟩, cv k ⟨t, h⟩] else []

theorem chainNodes_eq (k : Fin 28) :
    chainNodes k = src k :: (List.range 32).flatMap (tripleN k) := by
  simp only [chainNodes, tripleN, List.finRange, List.range]
  rfl

theorem range_split (p : ℕ) (hp : p ≤ 32) :
    List.range 32 = List.range p ++ List.range' p (32 - p) := by
  have h := @List.range'_append_1 0 p (32 - p)
  rw [Nat.zero_add, Nat.add_sub_cancel' hp] at h
  rw [List.range_eq_range', List.range_eq_range', h]

theorem chainBlock_length (k : ℕ) : (chainBlock k).length = blockLength k := by
  simp [chainBlock, chainPrologue, blockLength]; omega

/-- Landing inside a located block. -/
theorem CodeAt.drop {s : MachineState} {pc : Word} {code : List Instr}
    (located : Riscv.CodeAt s pc code) (i : ℕ) :
    Riscv.CodeAt s (pc + BitVec.ofNat 64 (4 * i)) (code.drop i) := by
  intro n hn
  have h := located (i + n) (by rw [List.length_drop] at hn; omega)
  rw [List.getElem?_drop, ← h, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

/-- A chain's table has room for its hash steps. -/
theorem levels_ge (k : Fin 28) : 32 - RiscvUpperForest.ForestVerifier.pos index k ≤ levels k := by
  have hp : RiscvUpperForest.ForestVerifier.pos index k = 31 - digit index.val (slotOf k.val) :=
    Forest.fixedPositions_val index k
  have hd := digit_lt index.val (slotOf k.val)
  rw [wid_slotOf k.isLt] at hd
  unfold levels
  by_cases hk : k.val < 16
  · rw [if_pos hk]
    rw [if_pos hk] at hd
    norm_num at hd
    omega
  · rw [if_neg hk]
    rw [if_neg hk] at hd
    norm_num at hd
    omega

/-- The code from the landing point: the remaining hash steps. -/
theorem landing_code {s : MachineState} (k : Fin 28) (tail : Code)
    (located : Riscv.CodeAt s s.pc (chainBlock k ++ tail)) (p : ℕ) (hp : 32 - p ≤ levels k) :
    Riscv.CodeAt s (s.pc + BitVec.ofNat 64 (4 * (4 + (levels k - (32 - p)))))
      (List.replicate (32 - p) .ECALL ++ tail) := by
  have h := CodeAt.drop located (4 + (levels k - (32 - p)))
  have e : (chainBlock k ++ tail).drop (4 + (levels k - (32 - p))) =
      List.replicate (32 - p) .ECALL ++ tail := by
    rw [chainBlock, List.append_assoc, ← List.drop_drop,
      List.drop_left' (show (chainPrologue k).length = 4 from rfl),
      List.drop_append_of_le_length (by simp), List.drop_replicate]
    congr 2
    omega
  rw [e] at h
  exact h

/-! ## The specification before the disclosed level -/

/-- Before its disclosed level, a chain's nodes are pure zeros. -/
theorem prefix_run (k : Fin 28) :
    ∀ (q : ℕ), q ≤ RiscvUpperForest.ForestVerifier.pos index k → ∀ (x : graph.Assignment) (cursor : ℕ),
    ∃ x' : graph.Assignment,
      runNodes' index payload (src k :: (List.range q).flatMap (tripleN k)) x cursor =
        pure (x', cursor) ∧
      (∀ k' : Fin 28, k' ≠ k → x' (cv k' 31).fin = x (cv k' 31).fin) := by
  intro q
  induction q with
  | zero =>
    intro _ x cursor
    have run : runNodes' index payload (src k :: (List.range 0).flatMap (tripleN k)) x cursor =
        cursorStep index payload x cursor (src k) := by
      simp only [List.range_zero, List.flatMap_nil, runNodes', Prod.mk.eta, bind_pure]
    rw [run, cursorStep_src]
    refine ⟨_, rfl, ?_⟩
    intro k' _
    exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
  | succ q ih =>
    intro hq x cursor
    obtain ⟨x₁, run₁, frame₁⟩ := ih (by omega) x cursor
    have hq32 : q < 32 := by
      have := pos_le index k
      omega
    have hne : ¬ (RiscvUpperForest.ForestVerifier.pos index k = q) := by omega
    have hlt : ¬ (RiscvUpperForest.ForestVerifier.pos index k < q) := by omega
    have hle : ¬ (RiscvUpperForest.ForestVerifier.pos index k ≤ q) := by omega
    have triple : tripleN k q = [ci k ⟨q, hq32⟩, ch k ⟨q, hq32⟩, cv k ⟨q, hq32⟩] := by
      simp [tripleN, hq32]
    have run : runNodes' index payload (src k :: (List.range (q + 1)).flatMap (tripleN k)) x cursor =
        runNodes' index payload [ci k ⟨q, hq32⟩, ch k ⟨q, hq32⟩, cv k ⟨q, hq32⟩] x₁ cursor := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, triple, ← List.cons_append,
        runNodes'_append, run₁, pure_bind]
    rw [run]
    simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hne, if_neg hlt,
      if_neg hle, pure_bind, Prod.mk.eta, bind_pure]
    refine ⟨_, rfl, ?_⟩
    intro k' hk'
    rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk' (Name.cv.inj h).1)),
      Function.update_of_ne (fin_ne_of_ne (by simp)),
      Function.update_of_ne (fin_ne_of_ne (by simp))]
    exact frame₁ k' hk'

/-! ## The invariant between chains -/

/-- Machine facts holding between chain blocks: chains before `k` are complete, the low 192
bits of their tops form the prefix of the root input, and the full top of chain `k - 1` still
lies below its slot. -/
structure ChainsInv (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop where
  ctx : Ctx s index pk
  input : s.getReg .x10 = W (prevInput k)
  out : 1 ≤ k → s.getReg .x12 = W (slotAddr (k - 1) - 8)
  pc : s.pc = W (blockStart k)
  payload : PayloadFrom s payload k
  done : 2 ≤ k → MemBits s (W regionAddr) (lowCat (topFun (tops x)) (k - 2))
  top : 1 ≤ k → MemBits s (W (slotAddr (k - 1) - 8)) (topFun (tops x) (k - 1))

/-- The root prefix grows by the low 192 bits of the next top. -/
theorem lowCat_extend (s : MachineState) (j : ℕ) (hj : j + 1 < 28) (c : ℕ → BitVec 256)
    (prev : MemBits s (W regionAddr) (lowCat c j))
    (next : MemBits s (W (slotAddr (j + 1) - 8)) (lo192 (c (j + 1)))) :
    MemBits s (W regionAddr) (lowCat c (j + 1)) := by
  rw [lowCat]
  apply (memBits_cast _ _ _ _).mpr
  apply memBits_append (by omega) prev
  have base : W regionAddr + BitVec.ofNat 64 (192 * (j + 1) / 8) = W (slotAddr (j + 1) - 8) := by
    rw [W_add]
    congr 1
    unfold slotAddr payloadAddr regionAddr
    omega
  rw [base]
  exact next

/-- The root prefix before chain `k`, from the invariant. -/
theorem lowCat_of_inv {s : MachineState} {x : graph.Assignment} {k : ℕ} (hk : k < 28)
    (inv : ChainsInv index payload pk s x k) (hk1 : 1 ≤ k) :
    MemBits s (W regionAddr) (lowCat (topFun (tops x)) (k - 1)) := by
  have next := lo_of_answer (inv.top hk1)
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · obtain rfl : k = 1 := by omega
    simp only [Nat.sub_self, lowCat] at next ⊢
    have e : W (slotAddr 0 - 8) = W regionAddr := by
      unfold slotAddr payloadAddr regionAddr; rfl
    rw [e] at next
    exact next
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show j + 2 - 1 = j + 1 by omega]
    have hd := inv.done h2
    rw [show j + 2 - 2 = j by omega] at hd
    apply lowCat_extend s j (by omega) _ hd
    rw [show j + 2 - 1 = j + 1 by omega] at next
    exact next

/-- The value read at a disclosed node is the specification's decoded value. -/
theorem read_value (k : ℕ) (n : Name) (hn : graph.len n.fin = 192) (cursor : ℕ)
    (t : MachineState) (held : Holds t k (ofBits 192 (payload.drop cursor))) :
    Holds t k (ofBits (graph.len n.fin) ((payload.drop cursor).take (graph.len n.fin))) := by
  unfold Holds
  rw [hn]
  have take : ofBits 192 ((payload.drop cursor).take 192) = ofBits 192 (payload.drop cursor) := by
    simpa only [List.drop_zero] using
      ofBits_drop_take (payload.drop cursor) (cap := 192) (start := 0) (len := 192) (by decide)
  rw [take]
  exact held

/-! ## The steps from the disclosed position -/

/-- What the slot holds before level `t`, or the full top after the last level. -/
def HoldsAt (s : MachineState) (x : graph.Assignment) (k : Fin 28) (t : ℕ) : Prop :=
  if h : t < 32 then
    Holds s k ((Forest.trunc (x (prev k ⟨t, h⟩).fin)).cast (graph_len_fin (ci k ⟨t, h⟩)).symm)
  else MemBits s (W (slotAddr k - 8)) (tops x k)

theorem prev_succ (k : Fin 28) (t : Fin 32) (ht : t.val < 31) :
    prev k ⟨t.val + 1, by omega⟩ = cv k t := by
  simp [prev]

/-- The answer of level `t` is what the next level needs. -/
theorem holdsAt_succ {u : MachineState} {x : graph.Assignment} {k : Fin 28} {t : Fin 32}
    {v : BitVec (graph.len (ci k t).fin)} {y : BitVec hashBits}
    (answer : MemBits u (W (slotAddr k - 8)) y) :
    HoldsAt u (tripleUpdate x k t v y) k (t.val + 1) := by
  unfold HoldsAt
  by_cases h : t.val + 1 < 32
  · rw [dif_pos h]
    have e : prev k ⟨t.val + 1, h⟩ = cv k t := prev_succ k t (by omega)
    unfold Holds
    apply (memBits_cast _ _ _ _).mpr
    rw [e, trunc_tripleUpdate_cv]
    exact holds_of_answer k.isLt answer
  · rw [dif_neg h]
    have ht : t = 31 := Fin.ext (by have := t.isLt; omega)
    subst ht
    unfold tops
    rw [tripleUpdate_cv]
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    exact answer

/-- Levels `t` to `31` of chain `k`, above the disclosed level. -/
theorem steps_refines (k : Fin 28) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' cursor : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      StepInv index payload pk u y k 32 → MemBits u (W (slotAddr k - 8)) (tops y k) →
      Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor)) c) :
    ∀ (n t : ℕ), 32 - t = n → t ≤ 32 → RiscvUpperForest.ForestVerifier.pos index k < t →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      StepInv index payload pk s x k t → HoldsAt s x k t →
      Riscv.CodeAt s s.pc (List.replicate (32 - t) .ECALL ++ tail) →
      (32 - t) + rest' ≤ fuel →
      Riscv.Refines fuel s
        (runNodes' index payload ((List.range' t (32 - t)).flatMap (tripleN k)) x cursor >>= K)
        ((32 - t) + c) := by
  intro n
  induction n with
  | zero =>
    intro t ht _ _ s x fuel inv held located bound
    have h32 : t = 32 := by omega
    subst h32
    simp only [Nat.sub_self, List.range'_zero, List.flatMap_nil, List.nil_append, runNodes',
      pure_bind, List.replicate_zero, Nat.zero_add] at located bound ⊢
    unfold HoldsAt at held
    rw [dif_neg (by omega)] at held
    exact continuation s x inv held located fuel bound
  | succ n ih =>
    intro t hn ht hp s x fuel inv held located bound
    have ht' : t < 32 := by omega
    have hsucc : 32 - t = (32 - (t + 1)) + 1 := by omega
    rw [hsucc] at located bound ⊢
    rw [List.range'_succ, List.flatMap_cons, runNodes'_append, bind_assoc]
    have triple : tripleN k t = [ci k ⟨t, ht'⟩, ch k ⟨t, ht'⟩, cv k ⟨t, ht'⟩] := by
      simp [tripleN, ht']
    rw [triple]
    rw [List.replicate_succ, List.cons_append] at located
    rw [show 32 - (t + 1) + 1 + c = 1 + (32 - (t + 1) + c) by omega]
    unfold HoldsAt at held
    rw [dif_pos ht'] at held
    apply step_refines index payload pk k ⟨t, ht'⟩
      (tail := List.replicate (32 - (t + 1)) .ECALL ++ tail)
      (fun r => runNodes' index payload ((List.range' (t + 1) (32 - (t + 1))).flatMap (tripleN k))
        r.1 r.2 >>= K)
      (32 - (t + 1) + c) (32 - (t + 1) + rest') cursor cursor s x fuel _
      (triple_run_step index payload k ⟨t, ht'⟩ hp x cursor) inv held located (by omega)
    intro u y inv' answer located' left hleft
    exact ih (t + 1) (by omega) (by omega) (by omega) u _ left inv' (holdsAt_succ answer)
      located' (by omega)

/-! ## The prologue and the jump -/

/-- Chain `k`'s prologue: the pointers are set and control jumps to the step of the disclosed
position, at four cycles. -/
theorem prologue_refines (k : Fin 28) (rest : Code) (s : MachineState)
    (x : graph.Assignment) (inv : ChainsInv index payload pk s x k.val)
    (located : Riscv.CodeAt s s.pc (chainPrologue k ++ rest))
    {fuel : ℕ} {q : OracleComp Spec (Option Bool)} {c : ℕ}
    (continuation : ∀ u : MachineState,
      StepInv index payload pk u x k (RiscvUpperForest.ForestVerifier.pos index k) →
      Holds u k (ofBits 192 (payload.drop (192 * k.val))) → u.code = s.code →
      Riscv.Refines fuel u q c) :
    Riscv.Refines (4 + fuel) s q (4 + c) := by
  have hs := slot_bounds k k.isLt
  rw [chainPrologue_parts, List.append_assoc] at located
  have ready := prologueLinear_ready s k k.isLt inv.input
  have E := prologueLinear_effect s k k.isLt inv.input
  set b := (prologueLinear k).foldl execInstrBr s with hb
  have bLocated : Riscv.CodeAt b b.pc
      ([Instr.JALR .x0 .x28 (imm12 ((tableEnd k : ℤ) - 4 - jumpBase))] ++ rest) := by
    rw [Riscv.linear_fold_pc s _ ready, prologueLinear_length]
    have h := located.append_right
    rw [prologueLinear_length] at h
    exact h.code_eq (Riscv.fold_code s _)
  rw [show 4 + fuel = (prologueLinear k).length + (fuel + 1) by rw [prologueLinear_length]; omega,
    show 4 + c = (prologueLinear k).length + (c + 1) by rw [prologueLinear_length]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hb]
  have fetchJ := bLocated.head
  apply Riscv.Refines.branch fetchJ rfl (fun h => nomatch h) (jalr_transition b _ fetchJ)
  have hx28 : (b.getReg .x28).toNat = jumpBase - 4 * (31 - RiscvUpperForest.ForestVerifier.pos index k) := by
    rw [E.target, BitVec.toNat_setWidth, inv.ctx.lanes k, Nat.mod_eq_of_lt]
    have := jumpBase_bounds
    omega
  rw [jump_target k k.isLt (RiscvUpperForest.ForestVerifier.pos index k) (pos_le index k) _ hx28]
  set u := b.setPC (W (tableEnd k - 4 * (32 - RiscvUpperForest.ForestVerifier.pos index k))) with hu
  have uRegs : ∀ r, u.getReg r = b.getReg r := fun r => by rw [hu]; simp
  have uMem : ∀ addr, u.getMem addr = b.getMem addr := fun addr => by rw [hu]; simp
  have frame : SlotFrame s u k := by
    intro addr _
    rw [uMem, E.mem]
  apply continuation u ?_ ?_ (by rw [hu]; simp [E.code])
  · refine ⟨inv.ctx.frame k k.isLt (fun r hr => ?_) frame, ?_, ?_, rfl, ?_, ?_⟩
    · obtain ⟨h10, h12, h28⟩ := notCtx_of_prologue r hr
      rw [uRegs, E.regs r h10 h12 h28]
    · rw [uRegs, E.input]
    · rw [uRegs, E.out]
    · intro j hj hj28
      apply memBits_of_mem_eq (show u.mem = s.mem from funext fun a => (uMem a).trans (E.mem a))
      exact inv.payload j (by omega) hj28
    · intro hk1
      apply memBits_of_mem_eq (show u.mem = s.mem from funext fun a => (uMem a).trans (E.mem a))
      exact lowCat_of_inv index payload pk k.isLt inv hk1
  · apply memBits_of_mem_eq (show u.mem = s.mem from funext fun a => (uMem a).trans (E.mem a))
    exact inv.payload k le_rfl k.isLt

/-! ## The whole chain -/

/-- One chain: its prologue, then the levels from its disclosed position, at
`4 + (32 - p)` cycles. -/
theorem chain_refines (k : Fin 28) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y (k.val + 1) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 192 * k.val + 192)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index payload pk s x k.val)
    (located : Riscv.CodeAt s s.pc (chainBlock k ++ tail))
    (bound : 4 + (32 - RiscvUpperForest.ForestVerifier.pos index k) + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (chainNodes k) x (192 * k.val) >>= K)
      (4 + (32 - RiscvUpperForest.ForestVerifier.pos index k) + c) := by
  have hp := pos_le index k
  have hs := slot_bounds k k.isLt
  set p := RiscvUpperForest.ForestVerifier.pos index k with hpdef
  have hp32 : p < 32 := by omega
  -- the specification up to the disclosed level is pure
  obtain ⟨x', run, frame⟩ := prefix_run index payload k p le_rfl x (192 * k.val)
  have nodes : chainNodes k = (src k :: (List.range p).flatMap (tripleN k)) ++
      (tripleN k p ++ (List.range' (p + 1) (32 - (p + 1))).flatMap (tripleN k)) := by
    rw [chainNodes_eq, range_split p (by omega), List.flatMap_append, List.cons_append,
      show 32 - p = (32 - (p + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]
  rw [nodes, runNodes'_append, run, bind_assoc, pure_bind]
  dsimp only
  -- the prologue
  rw [chainBlock, List.append_assoc] at located
  rw [show fuel = 4 + (fuel - 4) by omega,
    show 4 + (32 - p) + c = 4 + ((32 - p) + c) by omega]
  apply prologue_refines index payload pk k (List.replicate (levels k) .ECALL ++ tail) s x inv located
  intro u inv' held code
  have locatedU : Riscv.CodeAt u u.pc (List.replicate (32 - p) .ECALL ++ tail) := by
    have h := landing_code k tail (by rw [chainBlock, List.append_assoc]; exact located) p
      (levels_ge index k)
    rw [inv.pc, W_add] at h
    have e : blockStart k + 4 * (4 + (levels k - (32 - p))) = tableEnd k - 4 * (32 - p) := by
      rw [tableEnd_eq, blockStart_succ]
      have := levels_ge index k
      unfold blockLength
      omega
    rw [e, ← inv'.pc] at h
    exact h.code_eq code
  -- the disclosed level
  have inv'' : StepInv index payload pk u x' k p := by
    refine ⟨inv'.ctx, inv'.input, inv'.out, inv'.pc, inv'.payload, ?_⟩
    intro hk1
    have e : lowCat (topFun (tops x')) (k.val - 1) = lowCat (topFun (tops x)) (k.val - 1) := by
      apply lowCat_congr
      intro i hi
      unfold topFun tops
      split_ifs with hi28
      · rw [frame ⟨i, hi28⟩ (by intro e; have := congrArg Fin.val e; simp at this; omega)]
      · rfl
    rw [e]
    exact inv'.done hk1
  have triple : tripleN k p = [ci k ⟨p, hp32⟩, ch k ⟨p, hp32⟩, cv k ⟨p, hp32⟩] := by
    simp [tripleN, hp32]
  rw [triple, runNodes'_append, bind_assoc]
  rw [show 32 - p = (32 - (p + 1)) + 1 by omega] at locatedU ⊢
  rw [List.replicate_succ, List.cons_append] at locatedU
  rw [show 32 - (p + 1) + 1 + c = 1 + (32 - (p + 1) + c) by omega]
  have held' : Holds u k (ofBits (graph.len (ci k ⟨p, hp32⟩).fin)
      ((payload.drop (192 * k.val)).take (graph.len (ci k ⟨p, hp32⟩).fin))) :=
    read_value payload k _ (graph_len_fin _) _ u held
  apply step_refines index payload pk k ⟨p, hp32⟩
    (tail := List.replicate (32 - (p + 1)) .ECALL ++ tail)
    (fun r => runNodes' index payload ((List.range' (p + 1) (32 - (p + 1))).flatMap (tripleN k))
      r.1 r.2 >>= K)
    (32 - (p + 1) + c) (32 - (p + 1) + rest') (192 * k.val) (192 * k.val + 192) u x' (fuel - 4) _
    (triple_run_read index payload k ⟨p, hp32⟩ rfl x' (192 * k.val)) inv'' held' locatedU
    (by omega)
  intro v y invV answer locatedV left hleft
  -- the remaining levels
  apply steps_refines index payload pk k tail K c rest' (192 * k.val + 192) ?_
    (32 - (p + 1)) (p + 1) rfl (by omega) (by omega) v _ left invV (holdsAt_succ answer)
    locatedV hleft
  intro w z invW topW locatedW left' hleft'
  apply continuation w z ?_ locatedW left' hleft'
  refine ⟨invW.ctx, ?_, ?_, ?_, invW.payload, ?_, ?_⟩
  · rw [invW.input]
    unfold prevInput
    rw [if_neg (by omega)]
    show W _ = W _
    congr 1
    try (unfold slotAddr; omega)
  · intro _
    rw [invW.out, show k.val + 1 - 1 = k.val by omega]
  · rw [invW.pc, Nat.sub_self, Nat.mul_zero, Nat.sub_zero, tableEnd_eq]
  · intro h2
    rw [show k.val + 1 - 2 = k.val - 1 by omega]
    exact invW.done (by omega)
  · intro _
    rw [show k.val + 1 - 1 = k.val by omega]
    unfold topFun
    rw [dif_pos k.isLt]
    exact topW

end OptimalOTS.Riscv2Program
