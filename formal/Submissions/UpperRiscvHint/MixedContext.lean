import OptimalOTS.RiscvHint
import Submissions.UpperRiscvHint.MixedIndexLanes

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W Code laneBase hashBase)
open OptimalOTS.Dag

/-- The free dispatch, after the index phase. -/
def freeStart : ℕ := 4096 + 4*32
def laneGroup (q : ℕ) : ℕ := q/4
def laneIdx (q : ℕ) : ℕ := q%4
def laneAddr (q : ℕ) : ℕ := laneBase+2*q
def coarseDigit (index : RawIdx) (q : ℕ) : ℕ := digit index.val (2*q+1)
def dispatch (index : RawIdx) (q : ℕ) : ℕ :=
  4*digit index.val (2*q) + 1024*coarseDigit index q

theorem coarseDigit_lt (index : RawIdx) (q : ℕ) : coarseDigit index q < 16 := by
  have h := digit_lt index.val (2*q+1)
  have : 2 ^ wid (2*q+1) ≤ 16 := by
    unfold wid
    split_ifs <;> norm_num
  unfold coarseDigit; omega

theorem dispatch_le (index : RawIdx) (q : ℕ) : dispatch index q ≤ 15420 := by
  unfold dispatch
  have hf := digit_lt index.val (2*q)
  have hw : 2 ^ wid (2*q) ≤ 16 := by unfold wid; split_ifs <;> norm_num
  have := coarseDigit_lt index q
  omega

/-- Register and dispatch facts shared by all chain phases. -/
structure Ctx (s : MachineState) (index : RawIdx) (view : List Bool) (pk : PublicKey) : Prop where
  pk0 : s.getReg .x30 = pk.extractLsb' 0 64
  pk1 : s.getReg .x31 = pk.extractLsb' 64 64
  call : s.getReg .x5 = Riscv.hashCall
  lanes : ∀ q : Fin 16,
    (s.getHalfword (W (laneAddr q))).toNat = baseLane q - dispatch index q
  /-- `x28` holds pair `q`'s dispatch halfword while `x12` addresses chain `2q + 2`, or chain
  `2q + 1` with `x10` at its value; the prologue loads it between those two pointer moves. -/
  row : ∀ q : Fin 16, (s.getReg .x12 = W (outAddr (2*q.val+2)) ∨
      (s.getReg .x12 = W (outAddr (2*q.val+1)) ∧ s.getReg .x10 = W (work (2*q.val+1)))) →
    (s.getReg .x28).toNat = baseLane q - dispatch index q
  /-- Pair 0's link, from which the root length is computed. It is set by pair 0's jump, before
  `x12` addresses any chain after the free chain. -/
  base : ∀ k, 1 ≤ k → k < 33 → s.getReg .x12 = W (outAddr k) → s.getReg .x1 = W rootBase
  /-- No code at address 0: the decision's `JALR x0 x0 0` traps. -/
  null : s.code 0 = none
  code : Riscv.CodeAt s (W 4096) verifier

end OptimalOTS.RiscvMixedProgram
