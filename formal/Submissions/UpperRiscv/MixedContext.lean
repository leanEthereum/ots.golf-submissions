import Submissions.UpperRiscv.MixedIndexLanes
import Submissions.UpperRiscv.Reader

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W Code laneBase hashBase)
open OptimalOTS.Dag
open Forest Forest.Name

abbrev target : ℕ := OptimalOTS.target
def blockZero : ℕ := 4096 + 4*45
def laneGroup (q : ℕ) : ℕ := q/4
def laneIdx (q : ℕ) : ℕ := q%4
def laneAddr (q : ℕ) : ℕ := laneBase+2*q
def firstChain (q : ℕ) : ℕ := 2*q
def coarseDigit (index : Idx) (q : ℕ) : ℕ := digit index.val (2*q+1)
def dispatch (index : Idx) (q : ℕ) : ℕ :=
  4*digit index.val (2*q) + 512*coarseDigit index q

theorem firstChain_lt (q : ℕ) (hq : q < 16) : firstChain q < 32 := by
  unfold firstChain; omega

theorem digit_lt_32' (i k : ℕ) : digit i k < 32 := by
  have h := digit_lt i k
  have : 2 ^ wid k ≤ 32 := by unfold wid; split_ifs <;> norm_num
  omega

theorem coarseDigit_lt (index : Idx) (q : ℕ) : coarseDigit index q < 16 := by
  have h := digit_lt index.val (2*q+1)
  have : 2 ^ wid (2*q+1) ≤ 16 := by
    unfold wid
    split_ifs <;> norm_num
  unfold coarseDigit; omega

theorem dispatch_le (index : Idx) (q : ℕ) : dispatch index q ≤ 7804 := by
  unfold dispatch
  have := digit_lt_32' index.val (2*q)
  have := coarseDigit_lt index q
  omega

/-- Register and dispatch facts shared by the wide and narrow chain phases. -/
structure Ctx (s : MachineState) (index : Idx) (pk : PublicKey) : Prop where
  pk0 : s.getReg .x30 = pk.extractLsb' 0 64
  pk1 : s.getReg .x31 = pk.extractLsb' 64 64
  call : s.getReg .x5 = Riscv.hashCall
  lanes : ∀ q : Fin 16,
    (s.getHalfword (W (laneAddr q))).toNat = baseLane q - dispatch index q
  sigLen : s.getReg .x13 = W 5504
  code : Riscv.CodeAt s (W 4096) verifier

end OptimalOTS.RiscvMixedProgram
