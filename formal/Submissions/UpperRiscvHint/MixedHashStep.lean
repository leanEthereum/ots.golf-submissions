import Submissions.UpperRiscvHint.MixedChainSemantics
import Submissions.UpperRiscvHint.MixedEntry

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest Forest.Name OracleComp

/-- A chain hash preserves the dispatch table and all fixed registers. -/
theorem Ctx.writeHash {s : MachineState} {index : RawIdx} {pk : PublicKey}
    (ctx : Ctx s index pk) (k : Fin 32) (y : BitVec hashBits)
    (ho : s.getReg .x12 = W (outAddr k)) : Ctx (Riscv.writeHash s y) index pk := by
  have b := output_bounds k
  refine ⟨?_, ?_, ?_, ?_, ?_, ctx.code.code_eq (writeHash_code s y)⟩
  · rw [writeHash_regs]; exact ctx.pk0
  · rw [writeHash_regs]; exact ctx.pk1
  · rw [writeHash_regs]; exact ctx.call
  · intro q
    have he : (Riscv.writeHash s y).getHalfword (W (laneAddr q)) = s.getHalfword (W (laneAddr q)) := by
      simp only [MachineState.getHalfword]
      rw [writeHash_frame]
      intro j hj he
      have e := congrArg BitVec.toNat he
      have hq := q.isLt
      rw [alignToDword_toNat, ho, W_add,
        W_toNat _ (by unfold laneAddr laneBase; omega), W_toNat _ (by omega)] at e
      unfold laneAddr laneBase at e
      omega
    rw [he]; exact ctx.lanes q
  · rw [writeHash_regs]; exact ctx.sigLen

/-- Each admitted chain input costs one oracle compression, at either state width. -/
theorem chain_blockCost (k : Fin 32) : blockCost (chainBits k) = 1 := by
  rcases chainBits_cases k with h | h <;> rw [h] <;> decide

/-- A chain hash is valid for the packed initial input as well as the expanded state. -/
theorem chain_hashValid (s : MachineState) (k : Fin 32) (base : ℕ)
    (hp : s.getReg .x10 = W base) (ho : s.getReg .x12 = W (outAddr k))
    (hn : s.getReg .x11 = W (chainBits k)) (hb : 32 ≤ base ∧ base+24 ≤ 0x78000000) :
    Riscv.hashArgumentsValid s = true := by
  have bo := output_bounds k
  have hlen := chainBits_le k
  have hmin := chainBits_ge k
  have r1 : isValidOutputRange (W base) ((chainBits k+7)/8) = true :=
    range_ok _ _ hb.1 (by omega) (by omega) (by omega)
  have r2 := hashOutput_ok (outAddr k) (by omega) (by omega) bo.2.2
  unfold Riscv.hashArgumentsValid
  rw [hp, ho, hn, W_toNat _ (by omega), r1, Bool.true_and]
  exact r2

/-- One actual machine HASH refines one specification query; the result is universally quantified. -/
theorem chain_hash_refines (s : MachineState) (k : Fin 32) (base : ℕ)
    (v : BitVec (chainBits k)) (K : BitVec hashBits → OracleComp Spec (Option Bool))
    (c fuel : ℕ) (hf : 1 ≤ fuel)
    (hp : s.getReg .x10 = W base) (ho : s.getReg .x12 = W (outAddr k))
    (hn : s.getReg .x11 = W (chainBits k)) (hc : s.getReg .x5 = Riscv.hashCall)
    (hb : 32 ≤ base ∧ base+24 ≤ 0x78000000) (hm : MemBits s (W base) v)
    (fetch : s.code s.pc = some .ECALL)
    (continuation : ∀ y, Riscv.Refines (fuel-1) (Riscv.writeHash s y) (K y) c) :
    Riscv.Refines fuel s (hash v >>= K) (1+c) := by
  have hv := chain_hashValid s k base hp ho hn hb
  have hin : Riscv.hashInput s = ⟨chainBits k, v⟩ := by
    apply hashInput_of_memBits hp
    · rw [hn, W_toNat _ (by have := chainBits_le k; omega)]
    · exact hm
  have h := Riscv.Refines.hash (fuel := fuel-1) fetch hc hv continuation
  rw [hin, chain_blockCost k] at h
  simpa only [Nat.sub_add_cancel hf] using h

end OptimalOTS.RiscvMixedProgram
