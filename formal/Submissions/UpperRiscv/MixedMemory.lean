import Submissions.UpperRiscv.MixedLayout
import Submissions.UpperRiscv.MixedRoot

/-! Memory invariants between chains: unread values, committed root slots, and the seven bytes
past the region. -/

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

/-- The top of chain `k` in an assignment. -/
def tops (x : graph.Assignment) (k : Fin 33) : BitVec (topBits k) :=
  (x (Name.tp k).fin).cast (lenF_fin _)

/-- Chains from `k` on still find their signature values. -/
def PayloadFrom (s : MachineState) (payload : List Bool) (k : ℕ) : Prop :=
  ∀ j : Fin 33, k ≤ j.val →
    MemBits s (W (valueAddr j)) (ofBits (chainBits j) (payload.drop (wireOffset j)))

/-- Chains below `k` have committed their tops to their root slots. -/
def Completed (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop :=
  ∀ j : Fin 33, j.val < k → MemBits s (W (slotAddr j)) (tops x j)

theorem topSlice_of_answer (s : MachineState) (k : Fin 33) (y : BitVec 256)
    (answer : MemBits s (W (outAddr k)) y) : MemBits s (W (slotAddr k)) (topSlice k y) := by
  have h := memBits_extract answer (by unfold topOff; omega) (topOff_add_le k)
  rw [W_add, ← slot_eq k] at h
  exact h

/-- Byte intervals disjoint from the aligned 32-byte hash output retain their bits. -/
theorem writeHash_preserves (s : MachineState) (y : BitVec 256) (base out n : ℕ)
    (v : BitVec n) (hm : MemBits s (W base) v)
    (ho : s.getReg .x12 = W out) (ho8 : out%8=0) (hn8 : n%8=0)
    (hb : base+n < 2^62) (hout : out+32 < 2^62)
    (hd : base+n/8 ≤ out ∨ out+32 ≤ base) :
    MemBits (Riscv.writeHash s y) (W base) v := by
  apply memBits_of_word_frame _ _ _ _ hm
  intro i hi
  apply writeHash_frame
  intro j hj he
  have e := congrArg BitVec.toNat he
  rw [alignToDword_toNat, ho, W_add, W_add,
    W_toNat _ (by omega), W_toNat _ (by omega)] at e
  omega

/-- A chain hash preserves the values of every later chain. -/
theorem PayloadFrom.writeHash {s : MachineState} {payload : List Bool} (k : Fin 33)
    (hp : PayloadFrom s payload (k.val+1)) (y : BitVec 256)
    (ho : s.getReg .x12 = W (outAddr k)) :
    PayloadFrom (Riscv.writeHash s y) payload (k.val+1) := by
  intro j hj
  have bo := output_bounds k
  have bv := value_bounds j
  have hc := chainBits_bytes j
  apply writeHash_preserves s y (valueAddr j) (outAddr k) (chainBits j) _ (hp j hj)
    ho bo.2.2 (by omega)
  · unfold tailAddr regionAddr at bv; omega
  · unfold laneBase at bo; omega
  · have := unread_disjoint k j (by omega); omega

/-- A chain hash preserves the committed root slots of every earlier chain. -/
theorem Completed.writeHash {s : MachineState} {x : graph.Assignment} (k : Fin 33)
    (hp : Completed s x k) (y : BitVec 256) (ho : s.getReg .x12 = W (outAddr k)) :
    Completed (Riscv.writeHash s y) x k := by
  intro j hj
  have bo := output_bounds k
  have bj := output_bounds j
  have hs := slot_eq j
  have ht := topOff_add_le j
  apply writeHash_preserves s y (slotAddr j) (outAddr k) (topBits j) _ (hp j hj)
    ho bo.2.2 (topBits_aligned' j)
  · unfold laneBase at bj; omega
  · unfold laneBase at bo; omega
  · exact completed_disjoint j k hj

/-- The seven bytes past the region survive every chain hash. -/
theorem tail_writeHash {s : MachineState} (v : BitVec 56) (hm : MemBits s (W tailAddr) v)
    (k : Fin 33) (y : BitVec 256) (ho : s.getReg .x12 = W (outAddr k)) :
    MemBits (Riscv.writeHash s y) (W tailAddr) v := by
  have bo := output_bounds k
  apply writeHash_preserves s y tailAddr (outAddr k) 56 v hm ho bo.2.2 (by norm_num)
  · decide
  · unfold laneBase at bo; omega
  · have := tail_disjoint k; omega

theorem posW_slotW_aligned' : ∀ j : Fin 33, posW slotW j.val % 8 = 0 := by decide +kernel

theorem slot_cover : ∀ n i, i < posW slotW n → ∃ j < n, posW slotW j ≤ i ∧ i < posW slotW j + slotW j := by
  intro n
  induction n with
  | zero => intro i hi; simp [posW_zero] at hi
  | succ n ih =>
    intro i hi
    rw [posW_succ] at hi
    by_cases h : i < posW slotW n
    · obtain ⟨j, hj, h1, h2⟩ := ih i h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨n, by omega, by omega, hi⟩

/-- The committed slots form the root region. -/
theorem memBits_region (s : MachineState) (c : (k : Fin 33) → BitVec (topBits k))
    (h : ∀ k, MemBits s (W (slotAddr k)) (c k)) : MemBits s (W regionAddr) (rootRegion c) := by
  intro i hi
  obtain ⟨j, hj, h1, h2⟩ := slot_cover 33 i (by rw [posW_slotW_33]; exact hi)
  set p := posW slotW j with hp
  have ha := posW_slotW_aligned' ⟨j, hj⟩
  have hw : slotW j = topBits (slotChain j) := by rw [slotW, if_pos hj]
  have hpos : slotPos (slotChain j) = p := by rw [slotPos, slotOf_slotChain hj]
  have hm := h (slotChain j) (i - p) (by rw [← hw]; omega)
  have haddr : W (slotAddr (slotChain j)) + BitVec.ofNat 64 ((i - p) / 8) =
      W regionAddr + BitVec.ofNat 64 (i / 8) := by
    rw [slotAddr, hpos]
    unfold W
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    dsimp only at ha
    omega
  rw [haddr, show (i - p) % 8 = i % 8 by dsimp only at ha; omega] at hm
  rw [hm]
  have ht : (rootRegion c).getLsbD i = (ofDigitsW slotW (slotDigit c) 33).testBit i := by
    rw [BitVec.getLsbD, rootRegion_toNat]
  rw [ht]
  have hd : digitW slotW (ofDigitsW slotW (slotDigit c) 33) j = slotDigit c j :=
    digitW_ofDigitsW slotW _ (slotDigit_lt c) 33 j hj
  have hbit : (ofDigitsW slotW (slotDigit c) 33).testBit i =
      (digitW slotW (ofDigitsW slotW (slotDigit c) 33) j).testBit (i - p) := by
    unfold digitW
    rw [Nat.testBit_mod_two_pow, ← hp, Nat.testBit_div_two_pow]
    rw [show i - p + p = i by omega]
    simp [show i - p < slotW j by omega]
  rw [hbit, hd, slotDigit, if_pos hj, BitVec.getLsbD]

end OptimalOTS.RiscvMixedProgram
