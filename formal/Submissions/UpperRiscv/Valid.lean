import OptimalOTS.Dag
import Submissions.UpperRiscv.Count
import Submissions.UpperRiscv.Digits

/-!
# Accepted indices

The index is the 128-bit number packing the 28 chain digits: five-bit digits for the first
sixteen chains (bits `5 k, …, 5 k + 4`), four-bit digits for the other twelve (bits
`80 + 4 (k - 16), …`). An index is accepted when its digits sum to `target = 216`. The accepted
indices are counted exactly by `compW wid 28 216`; there are more than `729 * 2 ^ 105` of them,
the exact threshold at which the signing loop still fails with probability at most `2 ^ -128`.

The machine reads digit `k` from byte `k` of the 256-bit index answer; `pack` is that reading.
-/

namespace OptimalOTS

open OptimalOTS.Dag

/-- The digit sum of every accepted index. -/
def target : ℕ := 216

/-- Digit widths: five bits for the first sixteen chains, four for the next twelve, none beyond. -/
def wid (k : ℕ) : ℕ := if k < 16 then 5 else if k < 28 then 4 else 0

/-- Position of digit `k` in the packed index. -/
abbrev pos : ℕ → ℕ := posW wid

theorem pos_28 : pos 28 = 128 := by decide

theorem pos_of_le {k : ℕ} (hk : 28 ≤ k) : pos k = 128 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h | h
    · show posW wid (k + 1) = 128
      have := ih (by omega)
      rw [posW_succ, show posW wid k = 128 from this]
      simp [wid, show ¬ k < 16 by omega, show ¬ k < 28 by omega]
    · rw [← h]; exact pos_28

/-- Digit `k` of `i`. -/
abbrev digit : ℕ → ℕ → ℕ := digitW wid

theorem digit_lt (i k : ℕ) : digit i k < 2 ^ wid k := digitW_lt wid i k

/-- The number whose `n` low digits are `c 0, …, c (n - 1)`. -/
abbrev ofDigits : (ℕ → ℕ) → ℕ → ℕ := ofDigitsW wid

theorem ofDigits_lt (c : ℕ → ℕ) (hc : ∀ k, c k < 2 ^ wid k) (n : ℕ) :
    ofDigits c n < 2 ^ pos n := ofDigitsW_lt wid c hc n

theorem digit_ofDigits (c : ℕ → ℕ) (hc : ∀ k, c k < 2 ^ wid k) (n j : ℕ) (hj : j < n) :
    digit (ofDigits c n) j = c j := digitW_ofDigitsW wid c hc n j hj

theorem ofDigits_digit (i n : ℕ) (hi : i < 2 ^ pos n) : ofDigits (digit i) n = i :=
  ofDigitsW_digitW wid i n hi

/-- An index is accepted when its 28 digits sum to `target`. -/
def Accepted (i : ℕ) : Prop := ∑ k ∈ Finset.range 28, digit i k = target

instance : DecidablePred Accepted := fun i => by unfold Accepted; infer_instance

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- The accepted indices below `2 ^ idxBits`. -/
def validSet : Finset ℕ := (Finset.range (2 ^ idxBits)).filter Accepted

/-- A valid index. -/
abbrev Idx : Type := {i : ℕ // i ∈ validSet}

/-- The number of valid indices. -/
def numValid : ℕ := (validSet).card

theorem mem_validSet {i : ℕ} : i ∈ validSet ↔ i < 2 ^ idxBits ∧ Accepted i := by
  simp [validSet]

theorem mem_validSet_lt {i : ℕ} (h : i ∈ validSet) : i < 2 ^ idxBits :=
  (mem_validSet.mp h).1

theorem mem_validSet_accepted {i : ℕ} (h : i ∈ validSet) : Accepted i :=
  (mem_validSet.mp h).2

theorem Idx.isLt (i : Idx) : i.val < 2 ^ idxBits := mem_validSet_lt i.2

theorem numValid_le : numValid ≤ 2 ^ idxBits := by
  unfold numValid validSet
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])

/-! ## Counting the accepted indices -/

/-- The digit tuples counted by `compW wid 28 target`. -/
def tuples : Finset ((k : Fin 28) → Fin (2 ^ wid k)) :=
  Finset.univ.filter fun c => ∑ k, (c k).val = target

theorem tuples_card : tuples.card = Forest.compW wid 28 target := Forest.card_compW wid 28 target

/-- The digits of an index. -/
def digitsOf (i : ℕ) (k : Fin 28) : Fin (2 ^ wid k) := ⟨digit i k, digit_lt i k⟩

/-- The digit function of a tuple, extended by zero. -/
def digitFun (c : (k : Fin 28) → Fin (2 ^ wid k)) (k : ℕ) : ℕ :=
  if h : k < 28 then (c ⟨k, h⟩).val else 0

theorem digitFun_lt (c : (k : Fin 28) → Fin (2 ^ wid k)) (k : ℕ) : digitFun c k < 2 ^ wid k := by
  unfold digitFun
  split_ifs with h
  · exact (c ⟨k, h⟩).isLt
  · positivity

/-- The index with the given digits. -/
def indexOf (c : (k : Fin 28) → Fin (2 ^ wid k)) : ℕ := ofDigits (digitFun c) 28

theorem digit_indexOf (c : (k : Fin 28) → Fin (2 ^ wid k)) (k : Fin 28) :
    digit (indexOf c) k = (c k).val := by
  rw [indexOf, digit_ofDigits _ (digitFun_lt c) 28 k k.isLt, digitFun, dif_pos k.isLt]

theorem idxBits_eq : 2 ^ idxBits = 2 ^ pos 28 := by rw [pos_28]; norm_num [idxBits]

attribute [local irreducible] validSet tuples

theorem card_validSet : (validSet).card = Forest.compW wid 28 target := by
  rw [← tuples_card]
  refine Finset.card_bij' (fun i _ => digitsOf i) (fun c _ => indexOf c) ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨_, sum⟩ := mem_validSet.mp hi
    simp only [tuples, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← sum, ← Fin.sum_univ_eq_sum_range]
    rfl
  · intro c hc
    simp only [tuples, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine mem_validSet.mpr ⟨?_, ?_⟩
    · rw [idxBits_eq]
      exact ofDigits_lt _ (digitFun_lt c) 28
    · show ∑ k ∈ Finset.range 28, digit (indexOf c) k = target
      rw [← hc, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun k _ => digit_indexOf c k
  · intro i hi
    obtain ⟨lt, _⟩ := mem_validSet.mp hi
    show ofDigits (digitFun (digitsOf i)) 28 = i
    have agree : ∀ k ∈ Finset.range 28,
        digitFun (digitsOf i) k * 2 ^ pos k = digit i k * 2 ^ pos k := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [digitFun, dif_pos hk', digitsOf]
    show ∑ k ∈ Finset.range 28, digitFun (digitsOf i) k * 2 ^ pos k = i
    rw [Finset.sum_congr rfl agree]
    rw [idxBits_eq] at lt
    exact ofDigits_digit i 28 lt
  · intro c _
    funext k
    apply Fin.ext
    show digit (indexOf c) k = (c k).val
    rw [digit_indexOf]

/-- The availability threshold: a fresh index is accepted with probability at least
`729 / 2 ^ 23`, which is what the `2 ^ 20` signing trials need. -/
theorem numValid_avail : 729 * 2 ^ 105 ≤ numValid := by
  rw [numValid, card_validSet]
  show 729 * 2 ^ 105 ≤ Forest.compW wid 28 216
  rw [← Forest.compTableW_getD wid 216 28 216 le_rfl]
  decide +kernel

/-! ## The machine's reading of the digits -/

/-- Digit `k` as the machine reads it: the low `wid k` bits of byte `k` of the index answer. -/
def byteDigit (y : BitVec hashBits) (k : ℕ) : ℕ := y.toNat / 2 ^ (8 * k) % 2 ^ wid k

theorem byteDigit_lt (y : BitVec hashBits) (k : ℕ) : byteDigit y k < 2 ^ wid k :=
  Nat.mod_lt _ (by positivity)

/-- The packed index of an answer. -/
def pack (y : BitVec hashBits) : ℕ := ofDigits (byteDigit y) 28

theorem pack_lt (y : BitVec hashBits) : pack y < 2 ^ idxBits := by
  rw [idxBits_eq]
  exact ofDigits_lt _ (byteDigit_lt y) 28

theorem digit_pack (y : BitVec hashBits) {k : ℕ} (hk : k < 28) : digit (pack y) k = byteDigit y k :=
  digit_ofDigits _ (byteDigit_lt y) 28 k hk

theorem pack_lt_pos (y : BitVec hashBits) : pack y < 2 ^ pos 28 :=
  ofDigits_lt _ (byteDigit_lt y) 28

theorem pack_lt' (y : BitVec hashBits) : pack y < 2 ^ 128 := by
  rw [← pos_28]; exact pack_lt_pos y

attribute [irreducible] pack

/-- Fewer than half of the indices are accepted. -/
theorem compW_target_le : Forest.compW wid 28 target ≤ 2 ^ 127 := by
  rw [← Forest.compTableW_getD wid target 28 target le_rfl]
  decide +kernel

theorem numValid_le_half : numValid ≤ 2 ^ 127 := by
  rw [numValid, card_validSet]
  exact compW_target_le

theorem two_numValid_le : 2 * numValid ≤ 2 ^ 128 := by
  have := numValid_le_half
  omega

end OptimalOTS
