import Submissions.UpperRiscv.Parameters
import Submissions.UpperRiscv.Count
import Submissions.UpperRiscv.Digits

/-!
# Accepted indices

The index packs 32 chain digits into 128 bits: sixteen pairs of four-bit digits. An index is accepted when its digits sum to 157.
The accepted indices exceed the availability threshold `750 * 2 ^ 105`.

The machine reads digit `k` from bits `fieldPos k, …` of the 256-bit index answer; `pack` is
that reading.
-/

namespace OptimalOTS

open OptimalOTS.Dag

/-- The digit sum of every accepted index. -/
def target : ℕ := 157

/-- Thirty-two four-bit digits. -/
def wid (k : ℕ) : ℕ := if k < 32 then 4 else 0

/-- Position of digit `k` in the packed index. -/
abbrev pos : ℕ → ℕ := posW wid

theorem pos_32 : pos 32 = 128 := by decide

theorem pos_of_le {k : ℕ} (hk : 32 ≤ k) : pos k = 128 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h | h
    · show posW wid (k + 1) = 128
      have := ih (by omega)
      rw [posW_succ, show posW wid k = 128 from this]
      simp [wid, show ¬ k < 4 by omega, show ¬ k < 32 by omega]
    · rw [← h]; exact pos_32

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

/-- An index is accepted when its 32 digits sum to `target`. -/
def Accepted (i : ℕ) : Prop := ∑ k ∈ Finset.range 32, digit i k = target

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

/-- The digit tuples counted by `compW wid 32 target`. -/
def tuples : Finset ((k : Fin 32) → Fin (2 ^ wid k)) :=
  Finset.univ.filter fun c => ∑ k, (c k).val = target

theorem tuples_card : tuples.card = Forest.compW wid 32 target := Forest.card_compW wid 32 target

/-- The digits of an index. -/
def digitsOf (i : ℕ) (k : Fin 32) : Fin (2 ^ wid k) := ⟨digit i k, digit_lt i k⟩

/-- The digit function of a tuple, extended by zero. -/
def digitFun (c : (k : Fin 32) → Fin (2 ^ wid k)) (k : ℕ) : ℕ :=
  if h : k < 32 then (c ⟨k, h⟩).val else 0

theorem digitFun_lt (c : (k : Fin 32) → Fin (2 ^ wid k)) (k : ℕ) : digitFun c k < 2 ^ wid k := by
  unfold digitFun
  split_ifs with h
  · exact (c ⟨k, h⟩).isLt
  · positivity

/-- The index with the given digits. -/
def indexOf (c : (k : Fin 32) → Fin (2 ^ wid k)) : ℕ := ofDigits (digitFun c) 32

theorem digit_indexOf (c : (k : Fin 32) → Fin (2 ^ wid k)) (k : Fin 32) :
    digit (indexOf c) k = (c k).val := by
  rw [indexOf, digit_ofDigits _ (digitFun_lt c) 32 k k.isLt, digitFun, dif_pos k.isLt]

theorem idxBits_eq : 2 ^ idxBits = 2 ^ pos 32 := by rw [pos_32]; norm_num [idxBits]

attribute [local irreducible] validSet tuples

theorem card_validSet : (validSet).card = Forest.compW wid 32 target := by
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
      exact ofDigits_lt _ (digitFun_lt c) 32
    · show ∑ k ∈ Finset.range 32, digit (indexOf c) k = target
      rw [← hc, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun k _ => digit_indexOf c k
  · intro i hi
    obtain ⟨lt, _⟩ := mem_validSet.mp hi
    show ofDigits (digitFun (digitsOf i)) 32 = i
    have agree : ∀ k ∈ Finset.range 32,
        digitFun (digitsOf i) k * 2 ^ pos k = digit i k * 2 ^ pos k := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [digitFun, dif_pos hk', digitsOf]
    show ∑ k ∈ Finset.range 32, digitFun (digitsOf i) k * 2 ^ pos k = i
    rw [Finset.sum_congr rfl agree]
    rw [idxBits_eq] at lt
    exact ofDigits_digit i 32 lt
  · intro c _
    funext k
    apply Fin.ext
    show digit (indexOf c) k = (c k).val
    rw [digit_indexOf]

/-- The availability threshold: a fresh index is accepted with probability at least
`750 / 2 ^ 23`, which leaves the `2 ^ 20` signing trials room for the bad records. -/
theorem numValid_avail : 750 * 2 ^ 105 ≤ numValid := by
  rw [numValid, card_validSet]
  show 750 * 2 ^ 105 ≤ Forest.compW wid 32 157
  rw [← Forest.compTableW_getD wid 157 32 157 le_rfl]
  decide +kernel

/-! ## The machine's reading of the digits -/

/-- Unread bits preceding each digit. Sixteen 16-bit lanes each hold a pair,
with the fine digit at bit 2 and the coarse digit at bit 9. Cell 32 is trailing junk. -/
def jw (k : ℕ) : ℕ :=
  if k = 0 then 2 else if k < 32 then
    (if k % 2 = 1 then 3 else 5)
  else if k = 32 then 3 else 0

/-- Cell widths. -/
def cw (k : ℕ) : ℕ := jw k + wid k

/-- The bit position of digit `k` in the answer. -/
def fieldPos (k : ℕ) : ℕ := posW cw k + jw k

/-- Digit `k` as the machine reads it: the `wid k` bits of the index answer from `fieldPos k`. -/
def fieldDigit (y : BitVec hashBits) (k : ℕ) : ℕ := y.toNat / 2 ^ fieldPos k % 2 ^ wid k

theorem fieldDigit_lt (y : BitVec hashBits) (k : ℕ) : fieldDigit y k < 2 ^ wid k :=
  Nat.mod_lt _ (by positivity)

/-- The packed index of an answer. -/
def pack (y : BitVec hashBits) : ℕ := ofDigits (fieldDigit y) 32

theorem pack_lt (y : BitVec hashBits) : pack y < 2 ^ idxBits := by
  rw [idxBits_eq]
  exact ofDigits_lt _ (fieldDigit_lt y) 32

theorem digit_pack (y : BitVec hashBits) {k : ℕ} (hk : k < 32) :
    digit (pack y) k = fieldDigit y k :=
  digit_ofDigits _ (fieldDigit_lt y) 32 k hk

theorem pack_lt_pos (y : BitVec hashBits) : pack y < 2 ^ pos 32 :=
  ofDigits_lt _ (fieldDigit_lt y) 32

theorem pack_lt' (y : BitVec hashBits) : pack y < 2 ^ 128 := by
  rw [← pos_32]; exact pack_lt_pos y

attribute [irreducible] pack

/-- Fewer than half of the indices are accepted. -/
theorem compW_target_le : Forest.compW wid 32 target ≤ 2 ^ 127 := by
  rw [← Forest.compTableW_getD wid target 32 target le_rfl]
  decide +kernel

theorem numValid_le_half : numValid ≤ 2 ^ 127 := by
  rw [numValid, card_validSet]
  exact compW_target_le

theorem two_numValid_le : 2 * numValid ≤ 2 ^ 128 := by
  have := numValid_le_half
  omega

end OptimalOTS
