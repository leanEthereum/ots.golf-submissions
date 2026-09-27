import Submissions.UpperRiscv.MixedIndexLanes

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W Code laneBase hashBase)
open OptimalOTS.Dag

abbrev target : ℕ := OptimalOTS.target
/-- The free chain's prologue, after the index phase. -/
def blockZero : ℕ := 4096 + 4*38
def laneGroup (q : ℕ) : ℕ := q/4
def laneIdx (q : ℕ) : ℕ := q%4
/-- The index digit of pair `q`'s first chain; `2q+1` is its second chain's digit. -/
def firstChain (q : ℕ) : ℕ := 2*q
def coarseDigit (index : RawIdx) (q : ℕ) : ℕ := digit index.val (2*q+1)
def dispatch (index : RawIdx) (q : ℕ) : ℕ :=
  4*digit index.val (2*q) + 1024*coarseDigit index q

theorem firstChain_lt (q : ℕ) (hq : q < 16) : firstChain q < 32 := by
  unfold firstChain; omega

theorem digit_lt_32' (i k : ℕ) : digit i k < 32 := by
  have h := digit_lt i k
  have : 2 ^ wid k ≤ 32 := by unfold wid; split_ifs <;> norm_num
  omega

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

/-- Register and dispatch facts shared by every chain phase. `a` is the loader's length
register `a3 = min |σ| 5505`, compared against the bound `5465` in `x1` by the decision. -/
structure Ctx (s : MachineState) (index : RawIdx) (v : ℕ) (pk : PublicKey) (a : ℕ) : Prop where
  pk0 : s.getReg .x30 = pk.extractLsb' 0 64
  pk1 : s.getReg .x31 = pk.extractLsb' 64 64
  call : s.getReg .x5 = Riscv.hashCall
  lanes : ∀ q : Fin 16,
    (s.getHalfword (W (laneAddr q))).toNat = baseLane q - dispatch index q
  sigLen : s.getReg .x13 = W a
  short : a ≤ 5505
  bound : s.getReg .x1 = W 5465
  count : s.getReg .x29 = W (4 * v)
  code : Riscv.CodeAt s (W 4096) verifier

end OptimalOTS.RiscvMixedProgram
