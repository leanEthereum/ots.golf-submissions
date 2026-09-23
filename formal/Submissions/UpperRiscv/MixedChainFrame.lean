import Submissions.UpperRiscv.MixedChainSteps
import Submissions.UpperRiscv.MixedRootMemory

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph

def CtxReg (r : Reg) : Prop := r = .x30 ∨ r = .x31 ∨ r = .x5 ∨ r = .x13

theorem Ctx.frame {s t : MachineState} {index : Idx} {pk : PublicKey} (ctx : Ctx s index pk)
    (regs : ∀ r, CtxReg r → t.getReg r = s.getReg r) (mem : t.mem = s.mem)
    (code : t.code = s.code) : Ctx t index pk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ctx.code.code_eq code⟩
  · rw [regs .x30 (by simp [CtxReg])]; exact ctx.pk0
  · rw [regs .x31 (by simp [CtxReg])]; exact ctx.pk1
  · rw [regs .x5 (by simp [CtxReg])]; exact ctx.call
  · intro q
    simpa only [MachineState.getHalfword, MachineState.getMem, mem] using ctx.lanes q
  · rw [regs .x13 (by simp [CtxReg])]; exact ctx.sigLen

variable (index : Idx) (wire : List Bool) (pk : PublicKey)

theorem HashInv.frame {s t : MachineState} {x : graph.Assignment} {k : Fin 32} {base : ℕ}
    (inv : HashInv index wire pk s x k base) (next : ℕ) (hp : t.getReg .x10 = W next)
    (hb : 32 ≤ next ∧ next+24 ≤ 0x78000000)
    (regs : ∀ r, r ≠ .x10 → r ≠ .x28 → t.getReg r = s.getReg r)
    (mem : t.mem = s.mem) (code : t.code = s.code) : HashInv index wire pk t x k next := by
  refine ⟨inv.ctx.frame (fun r hr => ?_) mem code, hp, hb, ?_, ?_, ?_, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl <;> exact regs _ (by decide) (by decide)
  · rw [regs .x11 (by decide) (by decide)]; exact inv.length
  · rw [regs .x12 (by decide) (by decide)]; exact inv.out
  · intro j hj; exact memBits_of_mem_eq mem (inv.payload j hj)
  · intro j hj; exact memBits_of_mem_eq mem (inv.done j hj)

theorem holdsAt_frame {s t : MachineState} {x : graph.Assignment} {k : Fin 32} {level : ℕ}
    (mem : t.mem = s.mem) (held : HoldsAt s x k level) : HoldsAt t x k level := by
  unfold HoldsAt at *
  split_ifs at * <;> exact memBits_of_mem_eq mem held

def prevBits (k : ℕ) : ℕ := if k ≤ 24 then 160 else 192

/-- State at a boundary between complete chains. -/
structure ChainsInv (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop where
  ctx : Ctx s index pk
  input : s.getReg .x10 = W (prevInput k)
  out : 1 ≤ k → s.getReg .x12 = W (outAddr (k-1))
  length : s.getReg .x11 = W (prevBits k)
  payload : PayloadFrom s wire k
  done : Completed s (tops x) k

theorem rootSlice_of_memAnswer {s : MachineState} (k : Fin 32) {y : BitVec 256}
    (answer : MemBits s (W (outAddr k)) y) :
    MemBits s (W (rootSliceAddr k)) (rootSlice k y) := by
  have h := memBits_extract answer (rootSlice_aligned k) (rootSlice_contained k)
  rw [W_add, ← rootSlice_address k] at h
  exact h

theorem HashInv.complete {s : MachineState} {x : graph.Assignment} {k : Fin 32}
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
    · subst j; exact rootSlice_of_memAnswer k answer
    · exact inv.done j (by have hne : j.val ≠ k.val := fun h => he (Fin.ext h); omega)

theorem initial_chains (pk : PublicKey) (m : Message) (bits : List Bool) (answer : BitVec hashBits)
    (hi : Accepted (pack answer)) (hlen : bits.length = 5504)
    (located : Riscv.CodeAt (S0 pk m bits) (W 4096) verifier) (x : graph.Assignment) :
    ChainsInv (acceptedIdx answer hi) (bits.drop 128) pk (afterIndex pk m bits answer) x 0 := by
  refine ⟨afterIndex_ctx pk m bits answer hi hlen located,
    (afterIndex_setupRegs pk m bits answer).2, ?_, (afterIndex_setupRegs pk m bits answer).1,
    afterIndex_payloadFrom pk m bits answer, ?_⟩
  · intro h; omega
  · intro j hj; omega

/-- After the last chain (hashed in place at the start of the root input), `x10` is the root
input. -/
theorem prevInput_32 : prevInput 32 = rootAddr := by decide +kernel

theorem final_root {s : MachineState} {x : graph.Assignment}
    (inv : ChainsInv index wire pk s x 32) : RootInv index pk s x := by
  refine ⟨inv.ctx, ?_, inv.out (by decide), completed_root s (tops x) inv.done⟩
  rw [inv.input, prevInput_32]

end OptimalOTS.RiscvMixedProgram
