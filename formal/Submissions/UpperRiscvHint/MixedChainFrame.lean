import Submissions.UpperRiscvHint.MixedChainSteps
import Submissions.UpperRiscvHint.MixedRootMemory

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph

def CtxReg (r : Reg) : Prop :=
  r = .x30 ∨ r = .x31 ∨ r = .x5 ∨ r = .x1 ∨ r = .x10 ∨ r = .x12 ∨ r = .x28

theorem Ctx.frame {s t : MachineState} {index : RawIdx} {view : List Bool} {pk : PublicKey}
    (ctx : Ctx s index view pk)
    (regs : ∀ r, CtxReg r → t.getReg r = s.getReg r) (mem : t.mem = s.mem)
    (code : t.code = s.code) : Ctx t index view pk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [code]; exact ctx.null, ctx.code.code_eq code⟩
  · rw [regs .x30 (by simp [CtxReg])]; exact ctx.pk0
  · rw [regs .x31 (by simp [CtxReg])]; exact ctx.pk1
  · rw [regs .x5 (by simp [CtxReg])]; exact ctx.call
  · intro q
    simpa only [MachineState.getHalfword, MachineState.getMem, mem] using ctx.lanes q
  · intro q h
    rw [regs .x10 (by simp [CtxReg]), regs .x12 (by simp [CtxReg])] at h
    rw [regs .x28 (by simp [CtxReg])]
    exact ctx.row q h
  · rw [regs .x1 (by simp [CtxReg])]; exact ctx.base

/-- Moving the pointers from chain `2q + 1` to chain `2q + 2` keeps pair `q`'s halfword in `x28`. -/
theorem Ctx.enter {s t : MachineState} {index : RawIdx} {view : List Bool} {pk : PublicKey}
    (ctx : Ctx s index view pk) (q : Fin 16)
    (s10 : s.getReg .x10 = W (work (2*q.val+1))) (s12 : s.getReg .x12 = W (outAddr (2*q.val+1)))
    (t10 : t.getReg .x10 = W (work (2*q.val+2)))
    (t12 : t.getReg .x12 = W (outAddr (2*q.val+2)))
    (regs : ∀ r, r ≠ .x10 → r ≠ .x12 → t.getReg r = s.getReg r) (mem : t.mem = s.mem)
    (code : t.code = s.code) : Ctx t index view pk := by
  have hq := q.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [code]; exact ctx.null, ctx.code.code_eq code⟩
  · rw [regs .x30 (by decide) (by decide)]; exact ctx.pk0
  · rw [regs .x31 (by decide) (by decide)]; exact ctx.pk1
  · rw [regs .x5 (by decide) (by decide)]; exact ctx.call
  · intro q
    simpa only [MachineState.getHalfword, MachineState.getMem, mem] using ctx.lanes q
  · intro q' h
    have hq' := q'.isLt
    rw [regs .x28 (by decide) (by decide)]
    rw [t12] at h
    rcases h with h | ⟨h, _⟩
    · have e := outAddr_inj (by omega) (by omega) h
      have : q' = q := Fin.ext (by omega)
      subst this
      exact ctx.row q' (Or.inr ⟨s12, s10⟩)
    · have e := outAddr_inj (by omega) (by omega) h
      omega
  · rw [regs .x1 (by decide) (by decide)]; exact ctx.base

/-- The prologue of pair `q` points at chain `2q + 1` and loads the pair's halfword into `x28`. -/
theorem Ctx.prologue {s t : MachineState} {index : RawIdx} {view : List Bool} {pk : PublicKey}
    (ctx : Ctx s index view pk) (q : Fin 16)
    (t10 : t.getReg .x10 = W (work (2*q.val+1))) (t12 : t.getReg .x12 = W (outAddr (2*q.val+1)))
    (t28 : (t.getReg .x28).toNat = baseLane q - dispatch index q)
    (regs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → t.getReg r = s.getReg r)
    (mem : t.mem = s.mem) (code : t.code = s.code) : Ctx t index view pk := by
  have hq := q.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [code]; exact ctx.null, ctx.code.code_eq code⟩
  · rw [regs .x30 (by decide) (by decide) (by decide)]; exact ctx.pk0
  · rw [regs .x31 (by decide) (by decide) (by decide)]; exact ctx.pk1
  · rw [regs .x5 (by decide) (by decide) (by decide)]; exact ctx.call
  · intro q
    simpa only [MachineState.getHalfword, MachineState.getMem, mem] using ctx.lanes q
  · intro q' h
    have hq' := q'.isLt
    rw [t12] at h
    rcases h with h | ⟨h, _⟩
    · have e := outAddr_inj (by omega) (by omega) h
      omega
    · have e := outAddr_inj (by omega) (by omega) h
      have : q' = q := Fin.ext (by omega)
      subst this
      exact t28
  · rw [regs .x1 (by decide) (by decide) (by decide)]; exact ctx.base

variable (index : RawIdx) (wire : List Bool) (pk : PublicKey)

theorem holdsAt_frame {s t : MachineState} {x : graph.Assignment} {k : Chain} {level : ℕ}
    (mem : t.mem = s.mem) (held : HoldsAt s x k level) : HoldsAt t x k level := by
  unfold HoldsAt at *
  split_ifs at * <;> exact memBits_of_mem_eq mem held

/-- Hash-input width in `x11` at the boundary before chain `k`: the previous chain's width. -/
def prevBits (k : ℕ) : ℕ := if k ≤ 13 then 192 else 144

/-- State at a boundary between complete chains. -/
structure ChainsInv (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop where
  ctx : Ctx s index wire pk
  input : s.getReg .x10 = W (prevInput k)
  out : 1 ≤ k → s.getReg .x12 = W (outAddr (k-1))
  length : s.getReg .x11 = W (prevBits k)
  payload : PayloadFrom s wire k
  done : Completed s (tops x) k

theorem HashInv.complete {s : MachineState} {x : graph.Assignment} {k : Chain}
    (inv : HashInv index wire pk s x k (work k))
    (answer : MemBits s (W (outAddr k)) (tops x k)) :
    ChainsInv index wire pk s x (k.val+1) := by
  refine ⟨inv.ctx, ?_, ?_, ?_, inv.payload, ?_⟩
  · rw [inv.input]
    unfold prevInput
    rw [if_neg (by omega), Nat.add_sub_cancel]
  · intro _
    rw [Nat.add_sub_cancel]; exact inv.out
  · rw [inv.length]
    congr 1
  · intro j hj
    by_cases he : j = k
    · subst j; exact answer
    · exact inv.done j (by have hne : j.val ≠ k.val := fun h => he (Fin.ext h); omega)

theorem final_root {s : MachineState} {x : graph.Assignment}
    (inv : ChainsInv index wire pk s x 33) : RootInv index wire pk s x :=
  ⟨inv.ctx, inv.input, inv.out (by decide), completed_root s (tops x) inv.done⟩

end OptimalOTS.RiscvMixedProgram
