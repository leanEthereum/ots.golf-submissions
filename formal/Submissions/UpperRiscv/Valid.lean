import OptimalOTS.Dag
import Submissions.UpperRiscv.Count
import Submissions.UpperRiscv.Digits

/-!
# Accepted indices

The index is the 128-bit number packing 32 byte-slot digits, of which 28 are nonzero: five-bit
digits for the first sixteen chains, four-bit digits for slots `16 … 23` and for the four even
slots `24, 26, 28, 30`; slots `25, 27, 29, 31` have width zero and are always `0`. An index is
accepted when its digits sum to `target = 215`. The accepted indices are counted exactly by
`compW wid 32 215`; there are more than `712 * 2 ^ 105` of them, the exact threshold at which the
signing loop still fails with probability at most `2 ^ -128`.

The machine reads slot `k` from byte `k` of the 256-bit index answer; `pack` is that reading.
Chain `k` uses slot `slotOf k`, so the last four chains sit in the even bytes `24, 26, 28, 30`
and a single lane word carries all four.
-/

namespace OptimalOTS

open OptimalOTS.Dag

/-- The digit sum of every accepted index. -/
def target : ℕ := 215

/-- Digit widths by byte slot: five bits for the first sixteen, four for slots `16 … 23`, four
for the even slots `24, 26, 28, 30`, none elsewhere. -/
def wid (k : ℕ) : ℕ :=
  if k < 16 then 5 else if k < 24 then 4 else if k < 32 then (if k % 2 = 0 then 4 else 0) else 0

/-- The byte slot of chain `k`: the identity below `24`, then every other byte. -/
def slotOf (k : ℕ) : ℕ := k + (k - 24)

theorem slotOf_of_lt {k : ℕ} (hk : k < 24) : slotOf k = k := by unfold slotOf; omega

theorem slotOf_lt {k : ℕ} (hk : k < 28) : slotOf k < 31 := by unfold slotOf; omega

/-! The four slots of the chains `24 … 27` as literals. Tactics get the value of `slotOf` at a
numeral from these lemmas: `simp only` runs without the default simprocs, so it does not reduce
the arithmetic of `slotOf`'s body under a function application, and `omega` compares atoms
structurally, not up to definitional unfolding. -/

theorem slotOf_24 : slotOf 24 = 24 := by unfold slotOf; omega

theorem slotOf_25 : slotOf 25 = 26 := by unfold slotOf; omega

theorem slotOf_26 : slotOf 26 = 28 := by unfold slotOf; omega

theorem slotOf_27 : slotOf 27 = 30 := by unfold slotOf; omega

theorem wid_slotOf {k : ℕ} (hk : k < 28) : wid (slotOf k) = if k < 16 then 5 else 4 := by
  unfold wid slotOf; split_ifs <;> omega

/-- The slots skipped by `slotOf` have width zero. -/
theorem wid_odd_of_ge {k : ℕ} (h : 24 ≤ k) (h2 : k % 2 = 1) : wid k = 0 := by
  unfold wid; split_ifs <;> omega

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
      simp [wid, show ¬ k < 16 by omega, show ¬ k < 24 by omega, show ¬ k < 32 by omega]
    · rw [← h]; exact pos_32

/-- Digit `k` of `i`. -/
abbrev digit : ℕ → ℕ → ℕ := digitW wid

theorem digit_lt (i k : ℕ) : digit i k < 2 ^ wid k := digitW_lt wid i k

/-- The digits of the skipped slots vanish. -/
theorem digit_eq_zero_odd (i : ℕ) {k : ℕ} (h : 24 ≤ k) (h2 : k % 2 = 1) : digit i k = 0 := by
  have hd := digit_lt i k
  rw [wid_odd_of_ge h h2, pow_zero, Nat.lt_one_iff] at hd
  exact hd

/-- `slotOf` enumerates the 28 slots outside `{25, 27, 29, 31}`. -/
theorem sum_split_slots (f : ℕ → ℕ) (h25 : f 25 = 0) (h27 : f 27 = 0) (h29 : f 29 = 0)
    (h31 : f 31 = 0) :
    ∑ k ∈ Finset.range 28, f (slotOf k) = ∑ k ∈ Finset.range 32, f k := by
  -- The 24 slots below `24` agree pointwise, with no enumeration at all.
  have head : ∑ x ∈ Finset.range 24, f (slotOf x) = ∑ x ∈ Finset.range 24, f x :=
    Finset.sum_congr rfl fun k hk => by simp only [slotOf_of_lt (Finset.mem_range.mp hk)]
  -- Peel the eight-slot tail of the right sum; the explicit arguments pin each rewrite to it.
  rw [Finset.sum_range_succ f 31, Finset.sum_range_succ f 30, Finset.sum_range_succ f 29,
    Finset.sum_range_succ f 28, Finset.sum_range_succ f 27, Finset.sum_range_succ f 26,
    Finset.sum_range_succ f 25, Finset.sum_range_succ f 24]
  -- Peel the four-slot tail of the left sum and match the heads.
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, head]
  -- `simp only` beta-reduces before matching, so the four slot values land whatever shape the
  -- peeled summands have.
  simp only [slotOf_24, slotOf_25, slotOf_26, slotOf_27]
  omega

/-- Summing over the 28 chain slots is summing over all 32 slots. -/
theorem sum_slotOf (i : ℕ) :
    ∑ k ∈ Finset.range 28, digit i (slotOf k) = ∑ k ∈ Finset.range 32, digit i k :=
  sum_split_slots (digit i) (digit_eq_zero_odd i (by norm_num) (by norm_num))
    (digit_eq_zero_odd i (by norm_num) (by norm_num))
    (digit_eq_zero_odd i (by norm_num) (by norm_num))
    (digit_eq_zero_odd i (by norm_num) (by norm_num))

/-- The number whose `n` low digits are `c 0, …, c (n - 1)`. -/
abbrev ofDigits : (ℕ → ℕ) → ℕ → ℕ := ofDigitsW wid

theorem ofDigits_lt (c : ℕ → ℕ) (hc : ∀ k, c k < 2 ^ wid k) (n : ℕ) :
    ofDigits c n < 2 ^ pos n := ofDigitsW_lt wid c hc n

theorem digit_ofDigits (c : ℕ → ℕ) (hc : ∀ k, c k < 2 ^ wid k) (n j : ℕ) (hj : j < n) :
    digit (ofDigits c n) j = c j := digitW_ofDigitsW wid c hc n j hj

theorem ofDigits_digit (i n : ℕ) (hi : i < 2 ^ pos n) : ofDigits (digit i) n = i :=
  ofDigitsW_digitW wid i n hi

/-- An index is accepted when its 32 slot digits sum to `target`. -/
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
`712 / 2 ^ 23`, which is what the `2 ^ 20` signing trials need. -/
theorem numValid_avail : 712 * 2 ^ 105 ≤ numValid := by
  rw [numValid, card_validSet]
  show 712 * 2 ^ 105 ≤ Forest.compW wid 32 215
  rw [← Forest.compTableW_getD wid 215 32 215 le_rfl]
  decide +kernel

/-! ## The machine's reading of the digits -/

/-- Slot `k` as the machine reads it: the low `wid k` bits of byte `k` of the index answer. -/
def byteDigit (y : BitVec hashBits) (k : ℕ) : ℕ := y.toNat / 2 ^ (8 * k) % 2 ^ wid k

theorem byteDigit_lt (y : BitVec hashBits) (k : ℕ) : byteDigit y k < 2 ^ wid k :=
  Nat.mod_lt _ (by positivity)

/-- The packed index of an answer. -/
def pack (y : BitVec hashBits) : ℕ := ofDigits (byteDigit y) 32

theorem pack_lt (y : BitVec hashBits) : pack y < 2 ^ idxBits := by
  rw [idxBits_eq]
  exact ofDigits_lt _ (byteDigit_lt y) 32

theorem digit_pack (y : BitVec hashBits) {k : ℕ} (hk : k < 32) : digit (pack y) k = byteDigit y k :=
  digit_ofDigits _ (byteDigit_lt y) 32 k hk

theorem pack_lt_pos (y : BitVec hashBits) : pack y < 2 ^ pos 32 :=
  ofDigits_lt _ (byteDigit_lt y) 32

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
