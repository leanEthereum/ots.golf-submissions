import OptimalOTS.Dag
import Submissions.UpperRiscv.Count
import Submissions.UpperRiscv.Digits

/-!
# Accepted indices

The index is the 128-bit number packing the 28 chain digits: for `p < 12`, a five-bit digit for
chain `2p` and a four-bit digit for chain `2p + 1` (bits `9p, …, 9p + 8`), then five-bit digits
for chains `24 … 27`. An index is accepted when its digits sum to `target = 215`. The accepted
indices are counted exactly by `compW wid 28 215`; there are more than `712 * 2 ^ 105` of them,
the exact threshold at which the signing loop still fails with probability at most `2 ^ -128`.

The machine reads digit `k` from bits `fieldPos k, …` of the 256-bit index answer; `pack` is
that reading.
-/

namespace OptimalOTS

open OptimalOTS.Dag

/-- The digit sum of every accepted index. -/
def target : ℕ := 215

/-- Digit widths: chains `2p` and `2p + 1` (`p < 12`) form a pair of a five-bit and a four-bit
digit; chains `24 … 27` are five-bit; none beyond. -/
def wid (k : ℕ) : ℕ := if k < 24 then (if k % 2 = 0 then 5 else 4) else if k < 28 then 5 else 0

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
      simp [wid, show ¬ k < 24 by omega, show ¬ k < 28 by omega]
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
`712 / 2 ^ 23`, which is what the `2 ^ 20` signing trials need. -/
theorem numValid_avail : 712 * 2 ^ 105 ≤ numValid := by
  rw [numValid, card_validSet]
  show 712 * 2 ^ 105 ≤ Forest.compW wid 28 215
  rw [← Forest.compTableW_getD wid 215 28 215 le_rfl]
  decide +kernel

/-! ## The machine's reading of the digits -/

/-- The answer is read as 29 cells in bit order, each some unread low bits (`jw k`) below digit
`k` (`wid k` bits). Lane `p` (16 bits) of words 0–2 holds the pair of chains `2p` and `2p + 1`:
`junk₂ ‖ d₂ₚ ‖ junk₃ ‖ d₂ₚ₊₁ ‖ junk₂`; lane `12 + s` of word 3 holds chain `24 + s`:
`junk₂ ‖ d ‖ junk₉`. The junk of a cell also absorbs the trailing junk of the lane before it,
and cell 28 is the unread rest. -/
def jw (k : ℕ) : ℕ :=
  if k = 0 then 2 else if k < 24 then (if k % 2 = 0 then 4 else 3)
  else if k = 24 then 4 else if k < 28 then 11 else if k = 28 then 9 else 0

/-- Cell widths. -/
def cw (k : ℕ) : ℕ := jw k + wid k

/-- The bit position of digit `k` in the answer. -/
def fieldPos (k : ℕ) : ℕ := posW cw k + jw k

/-- Digit `k` as the machine reads it: the `wid k` bits of the index answer from `fieldPos k`. -/
def fieldDigit (y : BitVec hashBits) (k : ℕ) : ℕ := y.toNat / 2 ^ fieldPos k % 2 ^ wid k

theorem fieldDigit_lt (y : BitVec hashBits) (k : ℕ) : fieldDigit y k < 2 ^ wid k :=
  Nat.mod_lt _ (by positivity)

/-- The packed index of an answer. -/
def pack (y : BitVec hashBits) : ℕ := ofDigits (fieldDigit y) 28

theorem pack_lt (y : BitVec hashBits) : pack y < 2 ^ idxBits := by
  rw [idxBits_eq]
  exact ofDigits_lt _ (fieldDigit_lt y) 28

theorem digit_pack (y : BitVec hashBits) {k : ℕ} (hk : k < 28) :
    digit (pack y) k = fieldDigit y k :=
  digit_ofDigits _ (fieldDigit_lt y) 28 k hk

theorem pack_lt_pos (y : BitVec hashBits) : pack y < 2 ^ pos 28 :=
  ofDigits_lt _ (fieldDigit_lt y) 28

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
