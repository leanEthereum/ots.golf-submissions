import Submissions.UpperRiscvHint.MaskedDispatch

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open scoped Classical
open Riscv2Program
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] stagedRun stagedCost freeRun

theorem image_code : image.code = verifier := rfl

/-- The free count is supplied by the view until the final checksum validates it. -/
def executionIndex (answer : BitVec hashBits) (view : List Bool) : ChainIndex :=
  { rawIdx answer with free := ⟨viewDigit view,viewDigit_lt view⟩ }

@[simp] theorem executionIndex_val (answer : BitVec hashBits) (view : List Bool) :
    (executionIndex answer view).val = pack answer := rfl

@[simp] theorem executionIndex_free (answer : BitVec hashBits) (view : List Bool) :
    (executionIndex answer view).free.val = viewDigit view := rfl

@[simp] theorem rawIdx_val (answer : BitVec hashBits) : (rawIdx answer).val = pack answer := rfl

@[simp] theorem rawIdx_free (answer : BitVec hashBits) :
    (rawIdx answer).free.val = min (freeDigit (pack answer)) 31 := rfl

theorem executionIndex_canonical (answer : BitVec hashBits) (view : List Bool)
    (rank : freeDigit (pack answer) = viewDigit view) : executionIndex answer view = rawIdx answer := by
  apply ChainIndex.ext (i := executionIndex answer view) (j := rawIdx answer)
  · rw [executionIndex_val,rawIdx_val]
  · apply Fin.ext
    rw [executionIndex_free,rawIdx_free,rank,Nat.min_eq_left (by have := viewDigit_lt view; omega)]

theorem Ctx.reindex {credit : Word} {s : MachineState} {i j : ChainIndex}
    {view : List Bool} {pk : PublicKey} (ctx : Ctx (credit := credit) s i view pk)
    (same : j.val = i.val) : Ctx (credit := credit) s j view pk := by
  refine ⟨ctx.pk0,ctx.pk1,ctx.call,?_,?_,ctx.base,ctx.null,ctx.code,ctx.modulus,ctx.checksum⟩
  · intro q
    simpa only [dispatch,coarseDigit,same] using ctx.lanes q
  · intro q h
    simpa only [dispatch,coarseDigit,same] using ctx.row q h

/-- The exact oracle behavior includes chains on bad-rank views, before the root-boundary trap. -/
noncomputable def trapVerify (pk : PublicKey) (m : Message) (view : List Bool) :
    OracleComp Spec (Option Bool) := do
  let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits view))
  let index := executionIndex answer view
  if viewBank view < 3 then pure none
  else if 3 < viewBank view then pure (some false)
  else if 19 ≤ viewDigit view then pure (some false)
  else checkedFreeDecision index (viewPayload view) pk (decide (freeDigit index.val = viewDigit view))

/-- The checksum has no higher alias at an admitted free count. -/
theorem free_sum (index : ChainIndex) (c : ℕ) (hc : c < 19) (rank : freeDigit index.val = c) :
    digitSum index.val+c=147 := by
  have h := digitSum_le index.val
  unfold freeDigit at rank
  omega

set_option maxRecDepth 100000 in
/-- Every execution on every view refines `trapVerify`, and every accepting path costs at most
311 cycles. -/
theorem image_refines_trap (pk : PublicKey) (m : Message) (view : List Bool) (n : ℕ)
    (hn : 1337 ≤ n) :
    Riscv.Refines n (RiscvHint.loadView image pk m view) (trapVerify pk m view) 311 := by
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
  rw [show (311 : ℕ) = 280 + 31 from rfl]
  apply indexPhase_refines pk m view _ (n - 31) n _ _ located (by rw [indexPhase_length]; omega)
  intro answer left hleft
  set index := executionIndex answer view
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
  have x6 : s.getReg .x6 = W (viewTag view) := afterIndex_x6 pk m view answer
  have c32 : c < 32 := viewDigit_lt view
  have c64 : c < 64 := by omega
  dsimp only
  apply freeDispatch_refines s _ (viewTag view) x10 x6 sloc _ 277 left (by omega)
  intro t tpc t10 t12 tregs tmem tcode
  have tglobal : Riscv.CodeAt t (W 4096) verifier := sglobal.code_eq tcode
  by_cases low : viewBank view < 3
  · rw [if_pos low]
    exact smallBank_refines pk m view t (tcode.trans (afterIndex_code pk m view answer)) tpc low _ _
  rw [if_neg low]
  by_cases high : 3 < viewBank view
  · rw [if_pos high]
    rw [viewTag, dispatchTarget_guard _ _ (by omega) (viewBank_le view) c32] at tpc
    exact (guard_refines t tglobal (viewBank view) (31-c) (by omega)
      (viewBank_le view) (by omega) tpc _ (by omega)).mono (by omega)
  rw [if_neg high]
  have bank : viewBank view = 3 := by omega
  rw [dispatchTarget_honest view bank] at tpc
  change t.pc = W (freeLanding - 4*c) at tpc
  by_cases big : 19 ≤ c
  · -- the raw form: a rejection stub before any possible trap
    rw [if_pos big]
    exact (free_reject_refines t tglobal c big c64 tpc _ (by omega)).mono (by omega)
  rw [if_neg big]
  have c16 : c < 19 := by omega
  let base := initialCredit pk m view answer
  have sctx : Ctx (credit := base) s index view pk := by
    have h := afterIndex_ctx pk m view answer global
    exact h.reindex (j := index) ((executionIndex_val answer view).trans (rawIdx_val answer).symm)
  have tctx : Ctx (credit := base) t index view pk :=
    sctx.free t12 (fun r hr => tregs r
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) tmem tcode
  have t11 : t.getReg .x11 = W 192 := by rw [tregs .x11 (by decide) (by decide) (by decide),x11]
  have tpay : PayloadFrom t view 0 := fun j hj =>
    memBits_of_mem_eq tmem (afterIndex_payloadFrom pk m view answer j hj)
  have fits := stagedCost_le index
  have check : decide (freeDigit index.val = c) =
      decide (rv64_remu (creditAt index base 16) (W 257) = Riscv.hashCall) := by
    rw [creditAt_final]
    exact Bool.decide_congr (residue_iff pk m view answer bank).symm
  have run := free_refines index view pk c c16 (executionIndex_free answer view) _ check t tctx tpc t10 t12 t11 tpay (left-3)
    (by omega)
  by_cases rank : freeDigit index.val = c
  · have cost := stagedCost_allowed index
    have sum := free_sum index c c16 rank
    exact run.mono (by omega)
  · rw [decide_eq_false rank] at run ⊢
    exact run.anyCost (checkedFreeDecision_false index _ pk)

end OptimalOTS.RiscvMixedProgram
