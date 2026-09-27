import Submissions.UpperRiscvHint.MixedFree

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open scoped Classical
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] stagedRun stagedCost freeRun

theorem image_code : image.code = verifier := rfl

/-! ## The first hashing pair -/

def busyAux (index : RawIdx) : ℕ → ℕ → ℕ
  | 0, q => q
  | n+1, q => if pairWeight index q = 0 then busyAux index n (q+1) else q

/-- The first pair whose table landing leads to a hash: the first cap pair with a nonzero digit,
else pair 6, whose first chain is a normal chain. -/
def firstBusy (index : RawIdx) : ℕ := busyAux index 6 0

theorem busyAux_spec (index : RawIdx) : ∀ n q,
    q ≤ busyAux index n q ∧ busyAux index n q ≤ q + n ∧
      (∀ j, q ≤ j → j < busyAux index n q → pairWeight index j = 0) ∧
      (busyAux index n q < q + n → pairWeight index (busyAux index n q) ≠ 0) := by
  intro n
  induction n with
  | zero => intro q; simp only [busyAux]; exact ⟨le_rfl, le_rfl, fun j h1 h2 => by omega, by omega⟩
  | succ n ih =>
    intro q
    by_cases h : pairWeight index q = 0
    · rw [busyAux, if_pos h]
      obtain ⟨a, b, c, d⟩ := ih (q+1)
      refine ⟨by omega, by omega, ?_, fun hl => d (by omega)⟩
      intro j hj hj'
      by_cases hjq : j = q
      · subst hjq; exact h
      · exact c j (by omega) hj'
    · rw [busyAux, if_neg h]
      exact ⟨le_rfl, by omega, fun j hj hj' => by omega, fun _ => h⟩

/-- The machine's oracle behavior on a view, in its order of checks: the index query; a free count
of at least 16, which rejects; on an admitted residue the staged run, decided on the root; on a
wrong residue with a positive free count, a trap at the free chain's first hash; otherwise the
first hashing pair's landing, which rejects on its cap or traps at its first hash. -/
noncomputable def trapVerify (pk : PublicKey) (m : Message) (view : List Bool) :
    OracleComp Spec (Option Bool) := do
  let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits view))
  let index := rawIdx answer
  if 16 ≤ viewDigit view then pure (some false)
  else if freeDigit index.val = viewDigit view then freeDecision index (viewPayload view) pk
  else if viewDigit view ≠ 0 then pure none
  else if PairAllowed index.val (firstBusy index) then pure none
  else pure (some false)

/-! ## A wrong residue -/

/-- An `ECALL` with a residue other than the HASH call number traps: as HALT, `x10` holds a chain
address, which is no decision. -/
theorem ecall_traps (t : MachineState) (f : ℕ) (fetch : t.code t.pc = some .ECALL)
    (x5 : t.getReg .x5 ≠ Riscv.hashCall) (k : Chain) (x10 : t.getReg .x10 = W (work k)) :
    Riscv.execute (f+1) t = pure none := by
  have hb := work_bounds k
  have hw : (W (work k)).toNat = work k := W_toNat _ (by omega)
  by_cases halt : t.getReg .x5 = 0
  · apply Riscv.execute_badHalt f t fetch halt
    · rw [x10]; intro h; have := congrArg BitVec.toNat h; rw [hw] at this; simp at this; omega
    · rw [x10]; intro h; have := congrArg BitVec.toNat h; rw [hw] at this; simp at this; omega
  · exact Riscv.execute_badCall f t fetch halt x5

/-- The machine before pair `q`'s prologue while no chain has hashed. -/
structure Walk (index : RawIdx) (q : ℕ) (s : MachineState) : Prop where
  global : Riscv.CodeAt s (W 4096) verifier
  located : ∃ junk, Riscv.CodeAt s s.pc (prologue q ++ junk)
  x10 : s.getReg .x10 = W (prevInput (2*q+1))
  x5 : s.getReg .x5 ≠ Riscv.hashCall
  lanes : ∀ q' : Fin 16, (s.getHalfword (W (laneAddr q'))).toNat = baseLane q' - dispatch index q'

theorem pairCap_eq : ∀ q : Fin 16, pairCap q = PairCode.cap q := by decide

/-- A cap pair with two zero digits lands on its pointer move and reaches the next prologue
without a hash. -/
theorem walk_zero (index : RawIdx) (q : Fin 16) (hq : q.val < 6)
    (zero : pairWeight index q = 0) (s : MachineState) (w : Walk index q s)
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : (dispatchCode q).length + 2 ≤ fuel)
    (continuation : ∀ u, Walk index (q.val+1) u →
      Riscv.Refines (fuel - (dispatchCode q).length - 2) u Q c) :
    Riscv.Refines fuel s Q ((dispatchCode q).length + (2 + c)) := by
  obtain ⟨junk, loc⟩ := w.located
  have hl : lengthSetup q = [] := by simp only [lengthSetup]; rw [if_neg (by omega)]
  rw [prologue_parts, hl, List.nil_append] at loc
  apply dispatch_refines index q s junk w.x10 (w.lanes q) loc Q (2+c) fuel (by omega)
  intro t tpc t10 t12 t28 tregs tmem tcode
  have tglobal : Riscv.CodeAt t (W 4096) verifier := w.global.code_eq tcode
  unfold pairWeight at zero
  have good : digit index.val (2*q.val)+coarseDigit index q ≤ pairCap q := by
    unfold coarseDigit pairCap; omega
  have land := landing_located index t tglobal q good
  rw [← tpc] at land
  have hl1 : lead q = 1 := by unfold lead; rw [if_pos (Or.inl hq)]
  have rA : remaining index (leftChain q) = 0 := by rw [remaining_left, hl1]; omega
  have rB : remaining index (rightChain q) = 0 := by rw [remaining_right, hl1]; omega
  rw [rA, rB] at land
  simp only [List.replicate_zero, List.nil_append] at land
  have hp : t.getReg .x10 = W (prevInput (rightChain q)) := by rw [t10, right_previous]; rfl
  have E := enter_effect t (rightChain q) hp
  rw [show fuel - (dispatchCode q).length =
    (enter (rightChain q) (prevInput (rightChain q))).length +
      (fuel - (dispatchCode q).length - 2) by change _ = 2 + _; omega]
  apply Riscv.Refines.linear (enter (rightChain q) (prevInput (rightChain q))) land.append_left
    (enter_ready _ _ _)
  apply continuation
  refine ⟨tglobal.code_eq E.code, ⟨[], ?_⟩, ?_, ?_, ?_⟩
  · rw [E.pc]
    have h := land.append_right.code_eq E.code
    simp only [nextCode, if_neg (show q.val ≠ 15 by omega), List.append_nil] at h ⊢
    exact h
  · rw [E.input]
    unfold prevInput rightChain
    rw [if_neg (by omega)]
    congr 2
  · rw [E.regs .x5 (by decide) (by decide), tregs .x5 (by decide) (by decide) (by decide)]
    exact w.x5
  · intro q'
    have hm : ((enter (rightChain q) (prevInput (rightChain q))).foldl execInstrBr t).mem = s.mem := by
      rw [E.mem, tmem]
    simpa only [MachineState.getHalfword, MachineState.getMem, hm] using w.lanes q'

/-- The first hashing pair: its landing rejects on the cap, or its first hash traps. -/
theorem walk_busy (index : RawIdx) (q : Fin 16) (hq : q.val ≤ 6)
    (busy : q.val < 6 → pairWeight index q ≠ 0) (s : MachineState) (w : Walk index q s)
    (fuel : ℕ) (hf : 10 ≤ fuel) :
    Riscv.Refines fuel s
      (if PairAllowed index.val q then pure none else pure (some false)) 10 := by
  obtain ⟨junk, loc⟩ := w.located
  rw [prologue_parts, List.append_assoc] at loc
  have ready := lengthSetup_ready s q
  set s1 := (lengthSetup q).foldl execInstrBr s with hs1
  have s1regs : ∀ r, r ≠ .x11 → s1.getReg r = s.getReg r := by
    intro r hr
    rw [hs1]; unfold lengthSetup
    split_ifs <;> simp [execInstrBr, getReg_setReg_ite, hr]
  have s1mem : s1.mem = s.mem := by rw [hs1]; unfold lengthSetup; split_ifs <;> rfl
  have s1code : s1.code = s.code := Riscv.fold_code s _
  have hL : (lengthSetup q).length ≤ 1 := by unfold lengthSetup; split_ifs <;> simp
  have s1loc : Riscv.CodeAt s1 s1.pc (dispatchCode q ++ junk) := by
    rw [show s1.pc = s.pc + W (4*(lengthSetup q).length) from Riscv.linear_fold_pc s _ ready]
    exact loc.append_right.code_eq s1code
  have hd := dispatchCode_length q
  apply Riscv.Refines.mono (c := (lengthSetup q).length + ((dispatchCode q).length + 4)) _
    (by omega)
  rw [show fuel = (lengthSetup q).length + (fuel - (lengthSetup q).length) by omega]
  apply Riscv.Refines.linear _ loc.append_left ready
  rw [← hs1]
  apply dispatch_refines index q s1 junk (by rw [s1regs .x10 (by decide)]; exact w.x10)
    (by simpa only [MachineState.getHalfword, MachineState.getMem, s1mem] using w.lanes q)
    s1loc _ 4 _ (by omega)
  intro t tpc t10 t12 t28 tregs tmem tcode
  have tglobal : Riscv.CodeAt t (W 4096) verifier := w.global.code_eq (tcode.trans s1code)
  have t5 : t.getReg .x5 ≠ Riscv.hashCall := by
    rw [tregs .x5 (by decide) (by decide) (by decide), s1regs .x5 (by decide)]; exact w.x5
  obtain ⟨f, hf'⟩ : ∃ f, fuel - (lengthSetup q).length - (dispatchCode q).length = f + 3 :=
    ⟨fuel - (lengthSetup q).length - (dispatchCode q).length - 3, by omega⟩
  rw [hf']
  by_cases good : PairAllowed index.val q
  · rw [if_pos good]
    have good' : digit index.val (2*q.val)+coarseDigit index q ≤ pairCap q := by
      unfold PairAllowed at good; unfold coarseDigit; rw [pairCap_eq]; exact good
    have land := landing_located index t tglobal q good'
    rw [← tpc] at land
    by_cases hA : remaining index (leftChain q) = 0
    · -- a cap pair whose first digit is zero: its second chain hashes first
      have hq6 : q.val < 6 := by
        by_contra h
        rw [remaining_left] at hA; unfold lead at hA; rw [if_neg (by omega)] at hA; omega
      have hl1 : lead q = 1 := by unfold lead; rw [if_pos (Or.inl hq6)]
      have hB : remaining index (rightChain q) ≠ 0 := by
        have hb := busy hq6
        unfold pairWeight at hb
        rw [remaining_left, hl1] at hA
        rw [remaining_right, hl1]; omega
      obtain ⟨nB, hnB⟩ : ∃ nB, remaining index (rightChain q) = nB + 1 :=
        ⟨remaining index (rightChain q) - 1, by omega⟩
      rw [hA, hnB, List.replicate_zero, List.nil_append, List.replicate_succ] at land
      simp only [List.append_assoc, List.cons_append] at land
      have hp : t.getReg .x10 = W (prevInput (rightChain q)) := by rw [t10, right_previous]; rfl
      have E := enter_effect t (rightChain q) hp
      rw [show f + 3 = (enter (rightChain q) (prevInput (rightChain q))).length + (f + 1) by
          simp [enter]; omega,
        show (4 : ℕ) = (enter (rightChain q) (prevInput (rightChain q))).length + 2 by simp [enter]]
      apply Riscv.Refines.linear (enter (rightChain q) (prevInput (rightChain q)))
        land.append_left (enter_ready _ _ _)
      apply Riscv.Refines.trap
      have loc' : Riscv.CodeAt ((enter (rightChain q) (prevInput (rightChain q))).foldl execInstrBr t)
          ((enter (rightChain q) (prevInput (rightChain q))).foldl execInstrBr t).pc
          (Instr.ECALL :: (List.replicate nB Instr.ECALL ++ nextCode q)) := by
        rw [E.pc]; exact land.append_right.code_eq E.code
      apply ecall_traps _ f loc'.head
        (by rw [E.regs .x5 (by decide) (by decide)]; exact t5) (rightChain q) E.input
    · obtain ⟨nA, hnA⟩ : ∃ nA, remaining index (leftChain q) = nA + 1 :=
        ⟨remaining index (leftChain q) - 1, by omega⟩
      rw [hnA, List.replicate_succ, List.cons_append, List.cons_append] at land
      apply Riscv.Refines.trap
      rw [show f + 3 = (f + 2) + 1 by rfl]
      exact ecall_traps t (f+2) land.head t5 (leftChain q) t10
  · rw [if_neg good]
    have bad : pairCap q < digit index.val (2*q.val)+coarseDigit index q := by
      unfold PairAllowed at good; unfold coarseDigit; rw [pairCap_eq]; omega
    exact landing_reject_refines index q t tglobal tpc bad (f+3) (by omega)

/-- On a wrong residue with free count 0 the machine passes the zero cap pairs and stops at the
first hashing pair. -/
theorem walk_refines (index : RawIdx) : ∀ n q, firstBusy index - q = n → q ≤ firstBusy index →
    ∀ s fuel, Walk index q s → 6*n + 10 ≤ fuel →
    Riscv.Refines fuel s
      (if PairAllowed index.val (firstBusy index) then pure none else pure (some false))
      (6*n + 10) := by
  obtain ⟨_, hle, zeros, busy⟩ := busyAux_spec index 6 0
  change firstBusy index ≤ 0 + 6 at hle
  intro n
  induction n with
  | zero =>
    intro q hn hq s fuel w hf
    have e : q = firstBusy index := by omega
    subst e
    exact walk_busy index ⟨firstBusy index, by omega⟩ (by dsimp only; omega)
      (fun h => busy (by dsimp only at h; change firstBusy index < 0 + 6; omega)) s w fuel hf
  | succ n ih =>
    intro q hn hq s fuel w hf
    have hq6 : q < 6 := by omega
    let Q16 : Fin 16 := ⟨q, by omega⟩
    have hd : (dispatchCode Q16).length = 4 := dispatchCode_length _
    apply Riscv.Refines.mono (c := (dispatchCode Q16).length + (2 + (6*n + 10))) _ (by omega)
    exact walk_zero index Q16 hq6 (zeros q (by omega) (by change q < firstBusy index; omega))
      s w _ _ fuel (by omega)
      (fun u wu => ih (q+1) (by omega) (by omega) u _ wu (by omega))

/-! ## The whole image -/

/-- An admitted residue fixes the digit sum: the free count completes it to 145. -/
theorem free_sum (index : RawIdx) (c : ℕ) (hc : c < 16) (rank : freeDigit index.val = c)
    (caps : ∀ q : Fin 16, PairAllowed index.val q) : digitSum index.val + c = 145 := by
  have h := staged_caps_sum_le index.val caps
  unfold freeDigit at rank
  omega

set_option maxRecDepth 100000 in
/-- Every execution on every view refines `trapVerify`, and every accepting path costs at most
318 cycles. -/
theorem image_refines_trap (pk : PublicKey) (m : Message) (view : List Bool) (n : ℕ)
    (hn : 1337 ≤ n) :
    Riscv.Refines n (RiscvHint.loadView image pk m view) (trapVerify pk m view) 318 := by
  have initial := Riscv.CodeAt.initial image pk m view image_valid
  rw [image_code] at initial
  have global : Riscv.CodeAt (S0 pk m view) (W 4096) verifier :=
    initial.code_eq (by simp [RiscvHint.loadView, Riscv.initialState]; rfl)
  have pc0 : (S0 pk m view).pc = W 4096 := S0_pc pk m view
  have located : Riscv.CodeAt (S0 pk m view) (S0 pk m view).pc
      (indexPhase ++ (freeDispatch ++ (freeRow ++ (prologue 0 ++ tables)))) := by
    rw [pc0]
    simpa only [verifier, List.append_assoc] using global
  unfold trapVerify
  rw [show (318 : ℕ) = 284 + 34 from rfl]
  apply indexPhase_refines pk m view _ (n - 34) n _ _ located (by rw [indexPhase_length]; omega)
  intro answer left hleft
  set index := rawIdx answer
  set s := afterIndex pk m view answer
  set c := viewDigit view with hc
  have sglobal : Riscv.CodeAt s (W 4096) verifier :=
    global.code_eq (afterIndex_code pk m view answer)
  have spc : s.pc = W freeStart := afterIndex_pc pk m view answer
  have sloc : Riscv.CodeAt s s.pc (freeDispatch ++ (freeRow ++ (prologue 0 ++ tables))) := by
    rw [spc]
    exact (front_located s sglobal)
  have x10 : s.getReg .x10 = W hashBase := (afterIndex_setupRegs pk m view answer).2
  have x11 : s.getReg .x11 = W 192 := (afterIndex_setupRegs pk m view answer).1
  have x1 : s.getReg .x1 = W freeBase := afterIndex_x1 pk m view answer
  have x6 : s.getReg .x6 = W (4 * c) := afterIndex_x6 pk m view answer
  have c64 : c < 64 := viewDigit_lt view
  dsimp only
  apply freeDispatch_refines s _ c c64 x10 x1 x6 sloc _ 280 left (by omega)
  intro t tpc t10 t12 tregs tmem tcode
  have tglobal : Riscv.CodeAt t (W 4096) verifier := sglobal.code_eq tcode
  by_cases big : 16 ≤ c
  · -- the raw form: a rejection stub before any possible trap
    rw [if_pos big]
    exact (free_reject_refines t tglobal c big c64 tpc _ (by omega)).mono (by omega)
  rw [if_neg big]
  have c16 : c < 16 := by omega
  by_cases rank : freeDigit index.val = c
  · -- an admitted residue: the free chain, all pairs, the root and the decision
    rw [if_pos rank]
    have sctx := afterIndex_ctx pk m view answer global rank
    have tctx : Ctx t index view pk :=
      sctx.free t12 (fun r hr => tregs r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl <;> decide)) tmem tcode
    have t11 : t.getReg .x11 = W 192 := by rw [tregs .x11 (by decide) (by decide) (by decide), x11]
    have tpay : PayloadFrom t view 0 := fun j hj =>
      memBits_of_mem_eq tmem (afterIndex_payloadFrom pk m view answer j hj)
    have fits := stagedCost_le index
    have run := free_refines index view pk c c16 rank t tctx tpc t10 t12 t11 tpay (left - 4)
      (by omega)
    by_cases caps : ∀ q : Fin 16, PairAllowed index.val q
    · have cost := stagedCost_allowed index caps
      have sum := free_sum index c c16 rank caps
      exact run.mono (by omega)
    · -- a forbidden pair: the machine never accepts, so no cycle bound is needed
      exact run.anyCost (freeDecision_rejects index _ pk caps)
  · rw [if_neg rank]
    have t5 : t.getReg .x5 ≠ Riscv.hashCall := by
      rw [tregs .x5 (by decide) (by decide) (by decide), afterIndex_x5, Ne, residue_iff]
      exact rank
    by_cases c0 : c ≠ 0
    · -- a positive free count: the free chain's first hash traps on the residue
      rw [if_pos c0]
      apply Riscv.Refines.trap
      have loc := freeLanding_located t tglobal c (by omega)
      rw [freeRow_hashes ⟨c, c16⟩, ← tpc] at loc
      obtain ⟨c', hc'⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      dsimp only at loc
      rw [hc', List.replicate_succ, List.cons_append] at loc
      obtain ⟨f, hf⟩ : ∃ f, left - 4 = f + 1 := ⟨left - 5, by omega⟩
      rw [hf]
      exact ecall_traps t f loc.head t5 0 t10
    · -- free count 0: the zero cap pairs, then the first hashing pair
      rw [if_neg c0]
      have hc0 : c = 0 := by omega
      have loc := freeLanding_located t tglobal 0 (by omega)
      rw [freeRow_hashes ⟨0, by omega⟩] at loc
      rw [hc0] at tpc
      rw [← tpc] at loc
      have w : Walk index 0 t := by
        refine ⟨tglobal, ⟨tables, by simpa using loc⟩, by rw [t10]; rfl, t5, ?_⟩
        intro q'
        simpa only [MachineState.getHalfword, MachineState.getMem, tmem] using
          afterIndex_lanes pk m view answer q'
      have hb : firstBusy index ≤ 6 := (busyAux_spec index 6 0).2.1
      exact (walk_refines index _ 0 rfl (by omega) t (left - 4) w (by omega)).mono (by omega)

end OptimalOTS.RiscvMixedProgram
