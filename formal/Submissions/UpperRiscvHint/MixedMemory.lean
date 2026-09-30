import Submissions.UpperRiscvHint.MixedLayout

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

/-- Every chain from `k` on still has its view value at its working address. -/
def PayloadFrom (s : MachineState) (view : List Bool) (k : ℕ) : Prop :=
  ∀ j : Chain, k ≤ j.val →
    MemBits s (W (work j)) (ofBits (wireBits j) (view.drop (wireOffset j)))

/-- Every chain below `k` has its committed top at its top address. -/
def Completed (s : MachineState) (tops : (k : Chain) → BitVec (topBits k)) (k : ℕ) : Prop :=
  ∀ j : Chain, j.val < k → MemBits s (W (topAddr j)) (tops j)

/-- Restrict a represented disclosure to the chain's hash-input width. -/
theorem memBits_input {s : MachineState} (k : Chain) (view : List Bool)
    (h : MemBits s (W (work k)) (ofBits (wireBits k) (view.drop (wireOffset k)))) :
    MemBits s (W (work k)) (ofBits (chainBits k) (view.drop (wireOffset k))) := by
  intro i hi
  have hw : i < wireBits k := lt_of_lt_of_le hi (chainBits_le_wireBits k)
  have hm := h i hw
  simpa only [ofBits, BitVec.getLsbD_ofNat, hi, hw, decide_true, Bool.true_and] using hm

/-- A hash writes the chain's top into its answer buffer. -/
theorem top_of_answer {s : MachineState} (k : Chain) {y : BitVec 256}
    (answer : MemBits s (W (outAddr k)) y) : MemBits s (W (topAddr k)) (topOf k y) := by
  have h := memBits_extract answer (start := topOff k) (len := topBits k)
    (by unfold topOff; split_ifs <;> rfl) (topOff_add_le k)
  rw [W_add] at h
  exact h

/-- Byte intervals disjoint from the aligned 32-byte hash output retain their bits. -/
theorem writeHash_preserves (s : MachineState) (y : BitVec 256) (base out n : ℕ)
    (v : BitVec n) (hm : MemBits s (W base) v)
    (ho : s.getReg .x12 = W out) (ho8 : out%8=0)
    (hb : base+n < 2^62) (hout : out+32 < 2^62)
    (hd : base+(n+7)/8 ≤ out ∨ out+32 ≤ base) :
    MemBits (Riscv.writeHash s y) (W base) v := by
  apply memBits_of_word_frame _ _ _ _ hm
  intro i hi
  apply writeHash_frame
  intro j hj he
  have e := congrArg BitVec.toNat he
  rw [alignToDword_toNat, ho, W_add, W_add,
    W_toNat _ (by omega), W_toNat _ (by omega)] at e
  omega

/-- A chain hash preserves the disclosed values of every later chain. -/
theorem PayloadFrom.writeHash {s : MachineState} {payload : List Bool} (k : Chain)
    (hp : PayloadFrom s payload (k.val+1)) (y : BitVec 256)
    (ho : s.getReg .x12 = W (outAddr k)) :
    PayloadFrom (Riscv.writeHash s y) payload (k.val+1) := by
  intro j hj
  have bo := output_bounds k
  have bj := wireOffset_contained j
  have bw := wireBits_le j
  apply writeHash_preserves s y (work j) (outAddr k) (wireBits j) _ (hp j hj)
    ho bo.2.2
  · rw [work_eq_view j]; unfold honestViewBits at bj; omega
  · omega
  · exact unread_disjoint k j (by omega)

/-- A chain hash preserves the committed tops of every earlier chain. -/
theorem Completed.writeHash {s : MachineState} {tops : (k : Chain) → BitVec (topBits k)}
    (k : Chain) (hp : Completed s tops k) (y : BitVec 256)
    (ho : s.getReg .x12 = W (outAddr k)) :
    Completed (Riscv.writeHash s y) tops k := by
  intro j hj
  have bo := output_bounds k
  have bj := output_bounds j
  have hl := topBits_le j
  have ht : topOff j ≤ 112 := by unfold topOff; split_ifs <;> decide
  apply writeHash_preserves s y (topAddr j) (outAddr k) (topBits j) _ (hp j hj)
    ho bo.2.2 (by unfold topAddr; omega) (by omega)
  exact completed_disjoint j k hj

end OptimalOTS.RiscvMixedProgram
