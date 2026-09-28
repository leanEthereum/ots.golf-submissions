import Submissions.UpperRiscvHint.MixedPair
import Submissions.UpperRiscvHint.StagedVerifier
import Submissions.UpperRiscvHint.MixedIndexArith
import Submissions.UpperRiscvHint.Valid

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

set_option allowUnsafeReducibility true in
attribute [local irreducible] OptimalOTS.RiscvMixedProgram.tables OptimalOTS.RiscvMixedProgram.verifier

/-! Arithmetic of the capped-pair verifier's cycles after the free chain. -/
namespace OptimalOTS.CappedCost

/-- Per-pair cycles besides one hash per digit unit: the length setup before pair 6, the prologue,
the pointer move, and the extra hash of each normal chain. -/
def overhead (q : ℕ) : ℕ := (if q < 6 ∨ 15 ≤ q then 6 else 8) + if q = 6 then 1 else 0

def rejectCost (q : ℕ) : ℕ := 8 + if q = 6 then 1 else 0

def cost (w : ℕ → ℕ) : (n q : ℕ) → ℕ
  | 0, _ => 20
  | n+1, q => if w q ≤ PairCode.cap q then
      overhead q + w q + cost w n (q+1)
    else rejectCost q

/-- Every path fits in 33 cycles per pair plus the root and the decision. -/
theorem cost_le (w : ℕ → ℕ) : ∀ n q, cost w n q ≤ 33 * n + 20 := by
  intro n
  induction n with
  | zero => intro q; simp [cost]
  | succ n ih =>
    intro q
    have h := ih (q+1)
    rw [cost]
    split_ifs with hw
    · unfold overhead; unfold PairCode.cap at hw; split_ifs <;> omega
    · unfold rejectCost; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
/-- When all sixteen pairs pass, the pairs, the root and the decision cost 135 cycles besides the
digit sum. -/
theorem cost_allowed (w : ℕ → ℕ) (hw : ∀ q < 16, w q ≤ PairCode.cap q) :
    cost w 16 0 = 135 + ∑ q ∈ Finset.range 16, w q := by
  have h0 := hw 0 (by omega); have h1 := hw 1 (by omega); have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega); have h4 := hw 4 (by omega); have h5 := hw 5 (by omega)
  have h6 := hw 6 (by omega); have h7 := hw 7 (by omega); have h8 := hw 8 (by omega)
  have h9 := hw 9 (by omega); have h10 := hw 10 (by omega); have h11 := hw 11 (by omega)
  have h12 := hw 12 (by omega); have h13 := hw 13 (by omega); have h14 := hw 14 (by omega)
  have h15 := hw 15 (by omega)
  simp only [cost, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    if_true, overhead, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  omega

end OptimalOTS.CappedCost

namespace OptimalOTS.RiscvMixedProgram

def pairWeight (index : RawIdx) (q : ℕ) : ℕ :=
  digit index.val (2*q) + digit index.val (2*q+1)

theorem pairCost_overhead (index : RawIdx) (q : Fin 16) :
    pairCost index q = CappedCost.overhead q.val + pairWeight index q.val := by
  have h : (lengthSetup q).length + 8 = CappedCost.overhead q.val + 2 * lead q := by
    revert q
    decide +kernel
  rw [pairCost_eq, remaining_left, remaining_right]
  have hl := lead_le q
  unfold pairWeight
  omega

theorem badPairCost_eq (q : Fin 16) : badPairCost q = CappedCost.rejectCost q.val := by
  unfold badPairCost
  rw [dispatchCode_length]
  revert q
  decide +kernel

theorem stagedCost_eq (index : RawIdx) (n q : ℕ) (hq : q+n ≤ 16) :
    stagedCost index n q = CappedCost.cost (pairWeight index) n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [stagedCost, dif_pos (show q < 16 by omega), CappedCost.cost]
    change (if pairWeight index q ≤ PairCode.cap q then
      pairCost index ⟨q, by omega⟩ + stagedCost index n (q+1) else badPairCost ⟨q, by omega⟩) = _
    split_ifs
    · rw [pairCost_overhead, ih (q+1) (by omega)]
    · exact badPairCost_eq _

theorem stagedCost_le (index : RawIdx) : stagedCost index 16 0 ≤ 548 := by
  rw [stagedCost_eq index 16 0 (by decide)]
  exact CappedCost.cost_le _ 16 0

/-- When every pair passes, the pairs, the root and the decision cost 135 cycles besides the
digit sum. -/
theorem stagedCost_allowed (index : RawIdx) (caps : ∀ q : Fin 16, PairAllowed index.val q) :
    stagedCost index 16 0 = 135 + digitSum index.val := by
  rw [stagedCost_eq index 16 0 (by decide), CappedCost.cost_allowed]
  · unfold digitSum
    have h := sum_digit_pairs (digit index.val) 16
    rw [show 2 * 16 = 32 from rfl] at h
    rw [h]
    rfl
  · intro q hq
    exact caps ⟨q, hq⟩

end OptimalOTS.RiscvMixedProgram

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (wire : List Bool) (pk : PublicKey)

def blockCodeAt (q : ℕ) : Code := if q < 16 then prologue q else root ++ decision

theorem nextCode_eq (q : Fin 16) : nextCode q = blockCodeAt (q.val+1) := by
  have h := q.isLt
  unfold nextCode blockCodeAt
  split_ifs <;> first | rfl | omega

/-- Trace refinement of the staged run: a forbidden landing rejects before any hash of its pair,
and a completed run ends in the machine's decision on the root. -/
theorem stagedRun_refines :
    ∀ (n q : ℕ), 16-q=n → q ≤ 16 →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      ChainsInv index wire pk s x (2*q+1) →
      (q = 0 → s.pc = W freeLanding) →
      (∃ junk, Riscv.CodeAt s s.pc (blockCodeAt q ++ junk)) →
      stagedCost index n q ≤ fuel →
      Riscv.Refines fuel s
        ((fun o => o.elim (some false) (decisionOutcome · pk)) <$>
          stagedRun index (viewPayload wire) n q x (cursor (2*q+1)))
        (stagedCost index n q) := by
  intro n
  induction n with
  | zero =>
    intro q hq _ s x fuel inv _ located bound
    have hq16 : q=16 := by omega
    subst q
    obtain ⟨junk, located⟩ := located
    unfold blockCodeAt at located
    rw [if_neg (by omega)] at located
    simp only [stagedCost, stagedRun, map_bind, map_pure, Option.elim] at bound ⊢
    exact rootDecision_refines index (viewPayload wire) wire pk s x fuel
      (final_root index wire pk inv) located.append_left (by omega)
  | succ n ih =>
    intro q hq hq' s x fuel inv start located bound
    have hq16 : q < 16 := by omega
    let Q : Fin 16 := ⟨q,hq16⟩
    rw [stagedRun, dif_pos hq16]
    rw [stagedCost, dif_pos hq16] at bound ⊢
    unfold blockCodeAt at located
    rw [if_pos hq16] at located
    by_cases good : PairAllowed index.val q
    · simp only [if_pos good, map_bind] at bound ⊢
      apply pair_refines index wire pk Q good
        (fun r => (fun o => o.elim (some false) (decisionOutcome · pk)) <$>
          stagedRun index (viewPayload wire) n (q+1) r.1 r.2)
        (stagedCost index n (q+1)) (stagedCost index n (q+1)) ?_
        s x fuel inv start located bound
      intro u z invU locU left hleft
      apply ih (q+1) (by omega) (by omega) u z left invU (by omega) ?_ hleft
      simpa only [nextCode_eq Q] using locU
    · simp only [if_neg good, map_pure, Option.elim] at bound ⊢
      exact pair_bad_refines index wire pk Q (by
        change ¬ (digit index.val (2*q)+coarseDigit index q ≤ pairCap q) at good
        dsimp only [Q]
        omega) s x fuel inv start located bound

end OptimalOTS.RiscvMixedProgram

/-!
# The free dispatch and the free chain

After the index phase the machine points `x10` and `x12` at the free chain's cell and jumps
`c` cells before pair 0's prologue. The masked tag in `x6` includes the length bank
and complemented count. A cell with `c ≥ 16`
jumps to a rejection stub. The other cells hash the free chain `c` times; on an admitted residue
this is the free chain of the staged run, and the pairs follow from pair 0's prologue.
-/

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

/-! ## The free row -/

theorem front_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier) :
    Riscv.CodeAt s (W (4096 + 4*32)) (freeDispatch ++ (freeRow ++ (prologue 0 ++ tables))) := by
  have g : Riscv.CodeAt s (W 4096)
      (indexPhase ++ (freeDispatch ++ (freeRow ++ (prologue 0 ++ tables)))) := by
    simpa only [verifier, List.append_assoc] using global
  have h := g.append_right
  rwa [index_length, W_add] at h

/-- The cells reached for free count `c`, followed by pair 0's prologue. -/
theorem freeLanding_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (c : ℕ) (hc : c ≤ 63) :
    Riscv.CodeAt s (W (freeLanding - 4*c)) (freeRow.drop (64 - c) ++ (prologue 0 ++ tables)) := by
  have h := (front_located s global).append_right
  rw [show (freeDispatch.length) = 133 from rfl, W_add] at h
  have h' := CodeAt.drop h (64 - c)
  rw [List.drop_append_of_le_length (by simp only [freeRow, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]; omega),
    W_add] at h'
  have e : 4096 + 4*32 + 4*133 + 4*(64 - c) = freeLanding - 4*c := by unfold freeLanding; omega
  rwa [e] at h'

set_option maxRecDepth 100000 in
theorem freeRow_hashes : ∀ c : Fin 16,
    freeRow.drop (64 - c.val) = List.replicate c.val Instr.ECALL := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem free_reject_facts : ∀ c : Fin 64, 16 ≤ c.val →
    freeRow.drop (64 - c.val) = rejectJump (229 - c.val) :: freeRow.drop (65 - c.val) ∧
    stubFor (229 - c.val) ∈ rejectStubs ∧
    Riscv.admittedInstruction (rejectJump (229 - c.val)) = true ∧
    W (freeLanding - 4*c.val) +
        signExtend13 (BitVec.ofInt 13 (4*((stubFor (229 - c.val) : ℤ) - (229 - c.val : ℕ)))) =
      W (4096 + 4*stubFor (229 - c.val)) := by
  decide +kernel

/-- A free count of at least 16 lands on a jump to a rejection stub. -/
theorem free_reject_refines (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (c : ℕ) (hc16 : 16 ≤ c) (hc : c < 64) (pc : s.pc = W (freeLanding - 4*c))
    (fuel : ℕ) (bound : 4 ≤ fuel) :
    Riscv.Refines fuel s (pure (some false)) 4 := by
  obtain ⟨hdrop, hstub, hadmit, htarget⟩ := free_reject_facts ⟨c, hc⟩ hc16
  have loc := freeLanding_located s global c (by omega)
  dsimp only at hdrop hstub hadmit htarget
  rw [hdrop, List.cons_append, ← pc] at loc
  have fetch := loc.head
  have transition : step s = some (s.setPC (W (4096+4*stubFor (229 - c)))) := by
    rw [RiscvZkvm.Rv64.step, fetch]
    simp only [rejectJump, execInstrBr, if_true]
    rw [pc]
    exact congrArg (fun p => some (s.setPC p)) htarget
  have locReject : Riscv.CodeAt (s.setPC (W (4096+4*stubFor (229 - c))))
      (W (4096+4*stubFor (229 - c))) reject :=
    (rejectStub_located s global _ hstub).code_eq rfl
  have stop := reject_refines _ (fuel-1) locReject (by omega)
  rw [show fuel=(fuel-1)+1 by omega, show (4 : ℕ)=3+1 by omega]
  exact Riscv.Refines.branch fetch hadmit (fun h => nomatch h) transition stop

/-! ## The free dispatch -/

/-- A context survives a move of `x12` to the free chain, which is no pair's chain. -/
theorem Ctx.free {s t : MachineState} {index : RawIdx} {view : List Bool} {pk : PublicKey}
    (ctx : Ctx s index view pk) (t12 : t.getReg .x12 = W (outAddr 0))
    (regs : ∀ r, r = .x30 ∨ r = .x31 ∨ r = .x5 → t.getReg r = s.getReg r)
    (mem : t.mem = s.mem) (code : t.code = s.code) : Ctx t index view pk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [code]; exact ctx.null, ctx.code.code_eq code⟩
  · rw [regs .x30 (by simp)]; exact ctx.pk0
  · rw [regs .x31 (by simp)]; exact ctx.pk1
  · rw [regs .x5 (by simp)]; exact ctx.call
  · intro q
    simpa only [MachineState.getHalfword, MachineState.getMem, mem] using ctx.lanes q
  · intro q h
    have hq := q.isLt
    rw [t12] at h
    rcases h with h | ⟨h, _⟩
    · have := outAddr_inj (by omega) (by omega) h; omega
    · have := outAddr_inj (by omega) (by omega) h; omega
  · intro k hk hk' h
    rw [t12] at h
    have := outAddr_inj (by omega) hk' h; omega

theorem free_target (c : ℕ) (hc : c < 32) :
    (W freeBase + W (4*(31-c)) + signExtend12 (imm12 ((freeLanding : ℤ) - freeBase - 124))) &&& ~~~(1#64) =
      W (freeLanding - 4*c) := by
  rw [W_add, W_add_imm _ _ (by unfold freeLanding freeBase; omega)
    (by unfold freeLanding freeBase; omega) (by unfold freeLanding freeBase; omega)
    (by unfold freeBase; omega)]
  have e : (((freeBase + 4*(31-c) : ℕ) : ℤ) + ((freeLanding : ℤ) - freeBase - 124)).toNat =
      freeLanding - 4*c := by unfold freeLanding freeBase; omega
  rw [e]
  apply and_not_one_of_even
  rw [W_toNat _ (by unfold freeLanding; omega)]
  unfold freeLanding; omega

def dispatchTarget (tag : ℕ) : Word :=
  (W tag + signExtend12 (imm12 ((freeLanding : ℤ) - freeBase - 124))) &&& ~~~(1#64)

theorem setPC_mem (s : MachineState) (pc : Word) : (s.setPC pc).mem = s.mem := rfl

theorem maskedJump_refines (s : MachineState) (tag : ℕ)
    (x6 : s.getReg .x6 = W tag)
    (fetch : s.code s.pc = some (.JALR .x0 .x6
      (imm12 ((freeLanding : ℤ) - freeBase - 124))))
    (Q : OracleComp Spec (Option Bool)) (cost fuel : ℕ)
    (continuation : Riscv.Refines fuel (s.setPC (dispatchTarget tag)) Q cost) :
    Riscv.Refines (fuel+1) s Q (cost+1) := by
  have transition : RiscvZkvm.Rv64.step s = some (s.setPC (dispatchTarget tag)) := by
    rw [RiscvZkvm.Rv64.step, fetch]
    change some (s.setPC ((s.getReg .x6 + signExtend12
      (imm12 ((freeLanding : ℤ) - freeBase - 124))) &&& ~~~(1#64))) = _
    rw [x6]
    rfl
  exact Riscv.Refines.branch fetch rfl (fun h => nomatch h) transition continuation

/-- Direct masked dispatch: the padding after the jump is never executed. -/
theorem freeDispatch_refines (s : MachineState) (tail : Code) (tag : ℕ)
    (x10 : s.getReg .x10 = W hashBase) (x6 : s.getReg .x6 = W tag)
    (located : Riscv.CodeAt s s.pc (freeDispatch ++ tail))
    (Q : OracleComp Spec (Option Bool)) (cost fuel : ℕ) (hf : 3 ≤ fuel)
    (continuation : ∀ t : MachineState, t.pc = dispatchTarget tag →
      t.getReg .x10 = W (work 0) → t.getReg .x12 = W (outAddr 0) →
      (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → t.getReg r = s.getReg r) →
      t.mem = s.mem → t.code = s.code → Riscv.Refines (fuel - 3) t Q cost) :
    Riscv.Refines fuel s Q (3 + cost) := by
  let lin : Code := enter 0 hashBase
  let jump : Instr := .JALR .x0 .x6 (imm12 ((freeLanding : ℤ) - freeBase - 124))
  have code : Riscv.CodeAt s s.pc (lin ++ ([jump] ++ (List.replicate 130 nop ++ tail))) := by
    simpa only [freeDispatch, lin, jump, List.append_assoc, List.cons_append, List.nil_append]
      using located
  have E : EntryEffect s (lin.foldl execInstrBr s) 0 :=
    enter_effect s 0 (by rw [x10]; rfl)
  have ready : Riscv.LinearReady s lin := enter_ready s 0 hashBase
  generalize hu : lin.foldl execInstrBr s = u at E
  have upc : u.pc = s.pc + BitVec.ofNat 64 (4 * lin.length) := by
    rw [← hu]; exact Riscv.linear_fold_pc s _ ready
  have ucode : u.code = s.code := by
    rw [← hu]; exact Riscv.fold_code s _
  have uregs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → u.getReg r = s.getReg r := by
    intro r h10 h12 _
    exact E.regs r h10 h12
  have u6 : u.getReg .x6 = W tag := by rw [E.regs .x6 (by decide) (by decide), x6]
  have uloc : Riscv.CodeAt u u.pc ([jump] ++ (List.replicate 130 nop ++ tail)) := by
    rw [upc]; exact code.append_right.code_eq ucode
  generalize htarget : dispatchTarget tag = target at continuation
  let t := u.setPC target
  have t10 : t.getReg .x10 = W (work 0) := by
    simpa only [t, MachineState.getReg_setPC, Fin.val_zero] using E.input
  have t12 : t.getReg .x12 = W (outAddr 0) := by
    simpa only [t, MachineState.getReg_setPC, Fin.val_zero] using E.out
  have tregs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → t.getReg r = s.getReg r := by
    simpa only [t, MachineState.getReg_setPC] using uregs
  have tmem : t.mem = s.mem := (setPC_mem u target).trans E.mem
  have tcode : t.code = s.code := MachineState.code_setPC.trans ucode
  have cont := continuation t rfl t10 t12 tregs tmem tcode
  rw [show fuel = lin.length + ((fuel - 3) + 1) by simp [lin, enter]; omega,
    show 3 + cost = lin.length + (cost + 1) by simp [lin, enter]; omega]
  apply Riscv.Refines.linear _ code.append_left ready
  rw [hu]
  apply maskedJump_refines u tag u6 uloc.head Q cost (fuel - 3)
  simpa only [htarget] using cont

theorem dispatchTarget_honest (view : List Bool) (bank : viewBank view = 3) :
    dispatchTarget (viewTag view) = W (freeLanding - 4*viewDigit view) := by
  unfold dispatchTarget viewTag
  rw [bank, show (2048 * 3 : ℕ) = freeBase from rfl, ← W_add]
  exact free_target _ (viewDigit_lt view)

/-! ## The staged run's rejections -/

theorem stagedRun_rejects (index : RawIdx) (payload : List Bool)
    (n q : ℕ) (bad : ∃ j, q ≤ j ∧ j < q+n ∧ ¬ PairAllowed index.val j)
    (x : graph.Assignment) (cursor : ℕ) :
    ∀ o ∈ support (stagedRun index payload n q x cursor), o = none := by
  induction n generalizing q x cursor with
  | zero => obtain ⟨j, hj, hj', _⟩ := bad; omega
  | succ n ih =>
    rw [stagedRun]
    by_cases hq : q < 16
    · rw [dif_pos hq]
      intro o ho
      split_ifs at ho with allowed
      · rw [support_bind] at ho
        simp only [Set.mem_iUnion] at ho
        obtain ⟨r', _, ho⟩ := ho
        apply ih (q+1) ?_ r'.1 r'.2 o ho
        obtain ⟨j, hj, hj', bad⟩ := bad
        have hne : j ≠ q := by intro h; apply bad; simpa only [h] using allowed
        exact ⟨j, by omega, by omega, bad⟩
      · simpa only [support_pure, Set.mem_singleton_iff] using ho
    · rw [dif_neg hq]
      intro o ho
      simpa only [support_pure, Set.mem_singleton_iff] using ho

/-- The machine's verdict on the staged run. -/
noncomputable def freeDecision (index : RawIdx) (payload : List Bool) (pk : PublicKey) :
    OracleComp Spec (Option Bool) :=
  (fun o => o.elim (some false) (decisionOutcome · pk)) <$> freeRun index payload (fun _ => 0)

/-- With a forbidden pair the staged run never accepts. -/
theorem freeDecision_rejects (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (bad : ¬ ∀ q : Fin 16, PairAllowed index.val q) :
    some true ∉ support (freeDecision index payload pk) := by
  intro h
  push_neg at bad
  obtain ⟨j, hj⟩ := bad
  unfold freeDecision freeRun at h
  rw [support_map, support_bind] at h
  simp only [Set.mem_iUnion, Set.mem_image] at h
  obtain ⟨o, ⟨r, _, ho⟩, he⟩ := h
  rw [stagedRun_rejects index payload 16 0 ⟨j.val, by omega, by omega, hj⟩ r.1 r.2 o ho] at he
  simp at he

/-! ## The free chain on an admitted residue -/

theorem remaining_free (index : RawIdx) (c : ℕ) (hc : c < 16) (rank : freeDigit index.val = c) :
    remaining index 0 = c := by
  rw [steps_eq_digit]
  simp only [chainDigit, Fin.val_zero, if_true, show (0 : ℕ) < 13 by omega, true_or]
  omega

/-- On an admitted residue the free row hashes the free chain, and the pairs follow. -/
theorem free_refines (index : RawIdx) (view : List Bool) (pk : PublicKey) (c : ℕ) (hc : c < 16)
    (rank : freeDigit index.val = c) (t : MachineState)
    (ctx : Ctx t index view pk) (pc : t.pc = W (freeLanding - 4*c))
    (x10 : t.getReg .x10 = W (work 0)) (x12 : t.getReg .x12 = W (outAddr 0))
    (x11 : t.getReg .x11 = W 192) (payload : PayloadFrom t view 0) (fuel : ℕ)
    (bound : c + stagedCost index 16 0 ≤ fuel) :
    Riscv.Refines fuel t (freeDecision index (viewPayload view) pk)
      (c + stagedCost index 16 0) := by
  have hr := remaining_free index c hc rank
  have hP : t.pc + W (4 * remaining index 0) = W freeLanding := by
    rw [pc, hr, W_add, Nat.sub_add_cancel (by unfold freeLanding; omega)]
  have loc := freeLanding_located t ctx.code c (by omega)
  rw [freeRow_hashes ⟨c, hc⟩, ← pc] at loc
  dsimp only at loc
  rw [← hr] at loc bound ⊢
  have urange : 32 ≤ work 0 ∧ work 0 + 24 ≤ 0x78000000 := by decide
  have prep : Prepared index view pk t (fun _ => 0) 0 :=
    ⟨⟨ctx, x10, urange, x11, x12, fun j hj => payload j (by omega), fun j hj => absurd hj (by omega)⟩,
      payload 0 le_rfl⟩
  unfold freeDecision freeRun
  rw [map_bind]
  apply table_refines index view pk 0 (prologue 0 ++ tables)
    (fun r => (fun o => o.elim (some false) (decisionOutcome · pk)) <$>
      stagedRun index (viewPayload view) 16 0 r.1 r.2)
    (stagedCost index 16 0) (stagedCost index 16 0) (W freeLanding) ?_ t (fun _ => 0) fuel prep loc
    hP bound
  intro u z inv locU upc left hleft
  have e : cursor ((0 : Chain).val) + chainBits 0 = cursor (2*0+1) := by decide
  dsimp only
  rw [e]
  exact stagedRun_refines index view pk 16 0 rfl (by omega) u z left inv (fun _ => upc)
    ⟨tables, by simpa only [blockCodeAt, if_pos (show 0 < 16 by omega)] using locU⟩ hleft

end OptimalOTS.RiscvMixedProgram
