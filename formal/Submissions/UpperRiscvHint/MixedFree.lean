import Submissions.UpperRiscvHint.MixedPair
import Submissions.UpperRiscvHint.CheckedRun
import Submissions.UpperRiscvHint.MixedIndexArith
import Submissions.UpperRiscvHint.Valid

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

set_option allowUnsafeReducibility true in
attribute [local irreducible] OptimalOTS.RiscvMixedProgram.tables OptimalOTS.RiscvMixedProgram.verifier

namespace OptimalOTS.CappedCost

/-- Ordinary instructions of pair `q` beyond its weight: cap pairs 5 (the shifted weight carries
the sixth), pair 15 six, normal pairs eight, and pair 6's width switch. -/
def overhead (q : ℕ) : ℕ := (if q < 6 then 5 else if 15 ≤ q then 6 else 8) + if q = 6 then 1 else 0

def cost (w : ℕ → ℕ) : (n q : ℕ) → ℕ
  | 0, _ => 21
  | n+1, q => overhead q + w q + cost w n (q+1)

theorem cost_le (w : ℕ → ℕ) (hw : ∀ q, overhead q + w q ≤ 32) : ∀ n q, cost w n q ≤ 32*n+21 := by
  intro n
  induction n with
  | zero => intro q; simp [cost]
  | succ n ih =>
    intro q
    have h := ih (q+1)
    have hq := hw q
    rw [cost]
    omega

theorem cost_allowed (w : ℕ → ℕ) : cost w 16 0 = 130 + ∑ q ∈ Finset.range 16, w q := by
  simp only [cost,overhead,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num
  omega

end OptimalOTS.CappedCost

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

def pairWeight (index : ChainIndex) (q : ℕ) : ℕ := PairCode.weight q (rawPair index.val q)

theorem helper_le' : ∀ q : Fin 16, ∀ p : PairCode.Pair, PairCode.helper q p ≤ 1 := by decide +kernel

theorem skip_recode' : ∀ q : Fin 16, ∀ p : PairCode.Pair,
    PairCode.skip q p = 1 → (PairCode.recode q p).2 = 0 ∧ PairCode.kind q = true := by decide +kernel

theorem noskip_save' : ∀ q : Fin 16, ∀ p : PairCode.Pair,
    PairCode.skip q p ≠ 1 → PairCode.skipSave q p = 0 := by decide +kernel

theorem skip_save' : ∀ q : Fin 16, ∀ p : PairCode.Pair,
    PairCode.skip q p = 1 → PairCode.skipSave q p = 1 + PairCode.helper q p := by decide +kernel

theorem overhead_facts : ∀ q : Fin 16,
    (lengthSetup q).length + 8 = CappedCost.overhead q.val + 2 * lead q +
      (if PairCode.kind q.val then 1 else 0) ∧
    (PairCode.kind q.val = true → lead q = 1) := by
  decide +kernel

theorem pairCost_overhead (index : ChainIndex) (q : Fin 16) :
    pairCost index q = CappedCost.overhead q.val + pairWeight index q.val := by
  obtain ⟨hov, hlead⟩ := overhead_facts q
  have hl := lead_le q
  have hdec := PairCode.decoder_cost_exact q.val (rawPair index.val q)
  have hh := helper_le' q (rawPair index.val q)
  rw [pairCost_eq, remaining_left]
  unfold rightCost pairWeight pairFee
  by_cases hs : skipFlag index q = true
  · have hs1 := (skipFlag_iff index q).mp hs
    obtain ⟨hy, hk⟩ := skip_recode' q _ hs1
    have hss := skip_save' q _ hs1
    rw [hk] at hov hdec
    rw [hlead hk] at hov ⊢
    rw [if_pos hs]
    simp only [if_true] at hov hdec
    split_ifs <;> omega
  · have hs1 : PairCode.skip q.val (rawPair index.val q) ≠ 1 := fun e => hs ((skipFlag_iff index q).mpr e)
    have hss := noskip_save' q _ hs1
    rw [if_neg hs, remaining_right]
    split_ifs at hov hdec <;> omega

theorem stagedCost_eq (index : ChainIndex) (n q : ℕ) (hq : q+n ≤ 16) :
    stagedCost index n q = CappedCost.cost (pairWeight index) n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [stagedCost,dif_pos (show q<16 by omega),CappedCost.cost,pairCost_overhead,
      ih (q+1) (by omega)]

theorem overhead_weight_le : ∀ q : Fin 16, ∀ p : PairCode.Pair,
    CappedCost.overhead q.val + PairCode.weight q p ≤ 32 := by decide +kernel

theorem stagedCost_le (index : ChainIndex) : stagedCost index 16 0 ≤ 533 := by
  rw [stagedCost_eq index 16 0 (by decide)]
  refine CappedCost.cost_le _ (fun q => ?_) 16 0
  by_cases hq : q < 16
  · exact overhead_weight_le ⟨q, hq⟩ (rawPair index.val q)
  · unfold CappedCost.overhead pairWeight
    have := PairCode.weight_le q (rawPair index.val q)
    split_ifs <;> omega

theorem stagedCost_allowed (index : ChainIndex) :
    stagedCost index 16 0 = 130 + digitSum index.val := by
  rw [stagedCost_eq index 16 0 (by decide),CappedCost.cost_allowed,← Fin.sum_univ_eq_sum_range]
  rfl

/-- The running checksum after the first `q` pairs. -/
def creditAt (index : ChainIndex) (base : Word) (q : ℕ) : Word :=
  base + W (∑ j ∈ Finset.range q, pairCorrection index j)

theorem creditAt_zero (index : ChainIndex) (base : Word) : creditAt index base 0 = base := by
  simp [creditAt,W]

theorem creditAt_succ (index : ChainIndex) (base : Word) (q : ℕ) :
    creditAt index base (q+1) = creditAt index base q + W (pairCorrection index q) := by
  simp only [creditAt,Finset.sum_range_succ,← W_add,BitVec.add_assoc]

theorem creditAt_final (index : ChainIndex) (base : Word) :
    creditAt index base 16 = base + W (4*(rawDigitSum index.val+6-digitSum index.val)) := by
  unfold creditAt
  apply congrArg (fun n : ℕ => base + W n)
  have pc : ∀ q : Fin 16, pairCorrection index q =
      4*((digit index.val (2*q.val) + (15-digit index.val (2*q.val+1)) +
        (if PairCode.kind q.val then 1 else 0)) - PairCode.weight q.val (rawPair index.val q)) :=
    fun q => rfl
  rw [rawDigitSum_pairs,digitSum,← Fin.sum_univ_eq_sum_range, ← kind_count,
    ← Finset.sum_add_distrib, Finset.sum_congr rfl fun q _ => pc q, ← Finset.mul_sum]
  apply congrArg (fun n : ℕ => 4*n)
  apply Finset.sum_tsub_distrib
  intro q _
  have h := WeightedPairs.weight_le_raw (PairCode.kind q.val) (PairCode.complement (rawPair index.val q))
  have hs : 16-(digit index.val (2*q.val+1)+1) = 15-digit index.val (2*q.val+1) := by omega
  simpa only [PairCode.weight,PairCode.complement,rawPair,Fin.val_rev,hs] using h

/-- Pair `q` starts one chain back exactly when pair `q - 1` skipped its right chain. -/
def entrySkip (index : ChainIndex) (q : ℕ) : Bool := if q = 0 then false else skipFlag index (q-1)

theorem entrySkip_range (index : ChainIndex) (q : ℕ) (hq : q < 16) (h : entrySkip index q = true) :
    1 ≤ q ∧ q ≤ 6 := by
  unfold entrySkip at h
  by_cases h0 : q = 0
  · rw [if_pos h0] at h; exact absurd h (by decide)
  · rw [if_neg h0] at h
    have h6 : q - 1 < 6 := skipFlag_cap index ⟨q-1, by omega⟩ h
    exact ⟨by omega, by omega⟩

theorem entrySkip_final (index : ChainIndex) : entrySkip index 16 = false := by
  unfold entrySkip skipFlag isSkip capPair WeightedPairs.capPos
  simp

def blockCodeAt (index : ChainIndex) (q : ℕ) : Code :=
  if q < 16 then entryCode (entrySkip index q) q else root ++ decision

theorem exitCode_eq (index : ChainIndex) (q : Fin 16) :
    exitCode index q = blockCodeAt index (q.val+1) := by
  have h := q.isLt
  unfold exitCode blockCodeAt entrySkip entryCode
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  by_cases hs : skipFlag index q = true
  · have hc := skipFlag_cap index q hs
    rw [if_pos hs, if_pos (by omega), if_pos hs]; rfl
  · rw [if_neg hs]
    unfold nextCode
    split_ifs <;> first | rfl | omega

/-- Every pair advances the explicit checksum invariant; the root alone tests its residue. -/
theorem checkedRun_refines (index : ChainIndex) (wire : List Bool) (pk : PublicKey)
    (base : Word) (ok : Bool)
    (check : ok = decide (rv64_remu (creditAt index base 16) (W 257) = Riscv.hashCall)) :
    ∀ (n q : ℕ), 16-q=n → q ≤ 16 →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      EntryInv (credit := creditAt index base q) index wire pk (entrySkip index q) s x (2*q+1) →
      (q = 0 → s.pc = W freeLanding) →
      (∃ junk, Riscv.CodeAt s s.pc (blockCodeAt index q ++ junk)) →
      stagedCost index n q ≤ fuel →
      Riscv.Refines fuel s
        (checkedRun index (viewPayload wire) pk ok n q x (cursor (2*q+1)))
        (stagedCost index n q) := by
  intro n
  induction n with
  | zero =>
    intro q hq _ s x fuel inv _ located bound
    have hq16 : q=16 := by omega
    subst q
    obtain ⟨junk,located⟩ := located
    unfold blockCodeAt at located
    rw [if_neg (by omega)] at located
    simp only [stagedCost] at bound ⊢
    rw [entrySkip_final] at inv
    have inv := inv.chains index wire pk (by omega)
    rw [checkedRun,check]
    by_cases valid : rv64_remu (creditAt index base 16) (W 257) = Riscv.hashCall
    · rw [decide_eq_true valid,if_pos rfl]
      exact rootDecision_refines index (viewPayload wire) wire pk s x fuel valid
        (final_root index wire pk inv) located.append_left (by omega)
    · rw [decide_eq_false valid,if_neg Bool.false_ne_true]
      exact rootReject_refines index wire pk s x fuel valid
        (final_root index wire pk inv) located.append_left (by omega)
  | succ n ih =>
    intro q hq hq' s x fuel inv start located bound
    have hq16 : q<16 := by omega
    let Q : Fin 16 := ⟨q,hq16⟩
    rw [checkedRun,dif_pos hq16]
    rw [stagedCost,dif_pos hq16] at bound ⊢
    unfold blockCodeAt at located
    rw [if_pos hq16] at located
    apply pair_refines index wire pk Q
      (fun r => checkedRun index (viewPayload wire) pk ok n (q+1) r.1 r.2)
      (stagedCost index n (q+1)) (stagedCost index n (q+1)) ?_ (entrySkip index q)
      (entrySkip_range index q hq16) s x fuel inv start located bound
    intro u z invU locU left hleft
    dsimp only [Q] at invU
    have hflag : skipFlag index Q = entrySkip index (q+1) := by
      unfold entrySkip; simp [Q]
    have invU' : EntryInv (credit := creditAt index base (q+1)) index wire pk (entrySkip index (q+1))
        u z (2*(q+1)+1) := by
      rw [creditAt_succ, ← hflag]
      convert invU using 1 <;> omega
    apply ih (q+1) (by omega) (by omega) u z left invU' (by omega) ?_ hleft
    simpa only [exitCode_eq index Q] using locU

end OptimalOTS.RiscvMixedProgram

/-!
# The free dispatch and the free chain

After the index phase the machine points `x10` and `x12` at the free chain's cell and jumps
`c` cells before pair 0's prologue. The masked tag in `x6` includes the length bank
and complemented count. A cell with `c ≥ 19`
jumps to a rejection stub. The other cells hash the free chain `c` times; on an admitted residue
this is the free chain of the staged run, and the pairs follow from pair 0's prologue.
-/

namespace OptimalOTS.RiscvMixedProgram
variable {credit : BitVec 64}
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

/-! ## The free row -/

theorem front_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier) :
    Riscv.CodeAt s (W (4096 + 4*31)) (freeDispatch ++ (freeRow ++ (prologue 0 ++ tables))) := by
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
  rw [show (freeDispatch.length) = 134 from rfl, W_add] at h
  have h' := CodeAt.drop h (64 - c)
  rw [List.drop_append_of_le_length (by simp only [freeRow, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]; omega),
    W_add] at h'
  have e : 4096 + 4*31 + 4*134 + 4*(64 - c) = freeLanding - 4*c := by unfold freeLanding; omega
  rwa [e] at h'

set_option maxRecDepth 100000 in
theorem freeRow_hashes : ∀ c : Fin 19,
    freeRow.drop (64 - c.val) = List.replicate c.val Instr.ECALL := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem free_reject_facts : ∀ c : Fin 64, 19 ≤ c.val →
    freeRow.drop (64 - c.val) = rejectJump (229 - c.val) :: freeRow.drop (65 - c.val) ∧
    stubFor (229 - c.val) ∈ rejectStubs ∧
    Riscv.admittedInstruction (rejectJump (229 - c.val)) = true ∧
    W (freeLanding - 4*c.val) +
        signExtend13 (BitVec.ofInt 13 (4*((stubFor (229 - c.val) : ℤ) - (229 - c.val : ℕ)))) =
      W (4096 + 4*stubFor (229 - c.val)) := by
  decide +kernel

/-- A free count of at least 19 lands on a jump to a rejection stub. -/
theorem free_reject_refines (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (c : ℕ) (hc16 : 19 ≤ c) (hc : c < 64) (pc : s.pc = W (freeLanding - 4*c))
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
theorem Ctx.free {s t : MachineState} {index : ChainIndex} {view : List Bool} {pk : PublicKey}
    (ctx : Ctx (credit := credit) s index view pk) (t12 : t.getReg .x12 = W (outAddr 0))
    (regs : ∀ r, r = .x30 ∨ r = .x31 ∨ r = .x5 ∨ r = .x2 ∨ r = .x27 → t.getReg r = s.getReg r)
    (mem : t.mem = s.mem) (code : t.code = s.code) : Ctx (credit := credit) t index view pk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [code]; exact ctx.null, ctx.code.code_eq code, ?_, ?_⟩
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
  · rw [regs .x2 (by simp)]; exact ctx.modulus
  · rw [regs .x27 (by simp)]; exact ctx.checksum

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
  have code : Riscv.CodeAt s s.pc (lin ++ ([jump] ++ (List.replicate 131 nop ++ tail))) := by
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
  have uloc : Riscv.CodeAt u u.pc ([jump] ++ (List.replicate 131 nop ++ tail)) := by
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

theorem remaining_free (index : ChainIndex) : remaining index 0 = index.free.val := by
  rw [steps_eq_digit]
  simp only [chainDigit,Fin.val_zero,if_true,show (0:ℕ)<13 by omega,true_or]
  omega

/-- Any admitted view count runs its chosen free chain before the delayed checksum. -/
theorem free_refines (index : ChainIndex) (view : List Bool) (pk : PublicKey) (c : ℕ) (hc : c < 19)
    (count : index.free.val = c) (ok : Bool)
    (check : ok = decide (rv64_remu (creditAt index credit 16) (W 257) = Riscv.hashCall))
    (t : MachineState) (ctx : Ctx (credit := credit) t index view pk)
    (pc : t.pc = W (freeLanding - 4*c))
    (x10 : t.getReg .x10 = W (work 0)) (x12 : t.getReg .x12 = W (outAddr 0))
    (x11 : t.getReg .x11 = W 192) (payload : PayloadFrom t view 0) (fuel : ℕ)
    (bound : c + stagedCost index 16 0 ≤ fuel) :
    Riscv.Refines fuel t (checkedFreeDecision index (viewPayload view) pk ok)
      (c + stagedCost index 16 0) := by
  have hr : remaining index 0 = c := (remaining_free index).trans count
  have hP : t.pc + W (4 * remaining index 0) = W freeLanding := by
    rw [pc,hr,W_add,Nat.sub_add_cancel (by unfold freeLanding; omega)]
  have loc := freeLanding_located t ctx.code c (by omega)
  rw [freeRow_hashes ⟨c,hc⟩,← pc] at loc
  dsimp only at loc
  rw [← hr] at loc bound ⊢
  have urange : 32 ≤ work 0 ∧ work 0+24 ≤ 0x78000000 := by decide
  have prep : Prepared (credit := credit) index view pk t (fun _ => 0) 0 :=
    ⟨⟨ctx,x10,urange,x11,x12,fun j hj => payload j (by omega),fun j hj => absurd hj (by omega)⟩,
      payload 0 le_rfl⟩
  unfold checkedFreeDecision
  apply table_refines index view pk 0 (prologue 0 ++ tables)
    (fun r => checkedRun index (viewPayload view) pk ok 16 0 r.1 r.2)
    (stagedCost index 16 0) (stagedCost index 16 0) (W freeLanding) ?_ t (fun _ => 0) fuel prep loc hP bound
  intro u z inv locU upc left hleft
  have e : cursor ((0 : Chain).val)+chainBits 0 = cursor (2*0+1) := by decide
  dsimp only
  rw [e]
  apply checkedRun_refines index view pk credit ok check 16 0 rfl (by omega) u z left
    (by simpa only [creditAt_zero,Fin.val_zero,Nat.mul_zero,Nat.zero_add,entrySkip,if_true]
      using inv.entry index view pk) (fun _ => upc)
    ⟨tables,by simpa only [blockCodeAt,entrySkip,entryCode,if_pos (show 0<16 by omega),
      if_true, Bool.false_eq_true, if_false] using locU⟩ hleft

end OptimalOTS.RiscvMixedProgram
