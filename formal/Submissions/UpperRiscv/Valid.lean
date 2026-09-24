import Submissions.UpperRiscv.Parameters
import Submissions.UpperRiscv.PairCount
import Submissions.UpperRiscv.Digits

/-!
# Accepted indices

The index packs 32 chain digits into 128 bits: sixteen pairs of four-bit digits. An index is
accepted when its digits sum to 158 and each pair satisfies its local cap.
The accepted indices exceed the availability threshold `89 * 2 ^ 108`.

The machine reads digit `k` from bits `fieldPos k, …` of the 256-bit index answer; `pack` is
that reading.
-/

namespace OptimalOTS

open OptimalOTS.Dag

/-- The digit sum of every accepted index. -/
def target : ℕ := 158

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

/-- The local cap checked by the landing cell for pair `q`. -/
def PairAllowed (i q : ℕ) : Prop :=
  digit i (2*q) + digit i (2*q+1) ≤ PairCode.cap q

instance : DecidableRel PairAllowed := fun _ _ => by unfold PairAllowed; infer_instance

/-- Accepted indices form a capped subset of one fixed-rank antichain. -/
def Accepted (i : ℕ) : Prop :=
  (∑ k ∈ Finset.range 32, digit i k = target) ∧ ∀ q : Fin 16, PairAllowed i q.val

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

/-- Any decoded index, including those rejected by the verifier. -/
abbrev RawIdx := Fin (2 ^ idxBits)

def Idx.toRaw (i : Idx) : RawIdx := ⟨i.val, i.isLt⟩

instance : Coe Idx RawIdx := ⟨Idx.toRaw⟩

@[simp] theorem Idx.toRaw_val (i : Idx) : (i : RawIdx).val = i.val := rfl

theorem Idx.toRaw_injective : Function.Injective Idx.toRaw := by
  intro i j h
  exact Subtype.ext (congrArg Fin.val h)

theorem numValid_le : numValid ≤ 2 ^ idxBits := by
  unfold numValid validSet
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])

/-! ## Counting the accepted indices -/

abbrev PairTuple := Fin 16 → PairCode.Pair

theorem digit_lt_16 (i k : ℕ) : digit i k < 16 := by
  have h := digit_lt i k
  have hw : 2 ^ wid k ≤ 16 := by unfold wid; split_ifs <;> norm_num
  omega

/-- The sixteen pairs of an index. -/
def digitsOf (i : ℕ) (q : Fin 16) : PairCode.Pair :=
  (⟨digit i (2*q.val), digit_lt_16 _ _⟩,
   ⟨digit i (2*q.val+1), digit_lt_16 _ _⟩)

/-- The flattened pair digits, extended by zero. -/
def digitFun (c : PairTuple) (k : ℕ) : ℕ :=
  if h : k < 32 then
    if k % 2 = 0 then (c ⟨k/2, by omega⟩).1.val else (c ⟨k/2, by omega⟩).2.val
  else 0

theorem digitFun_lt (c : PairTuple) (k : ℕ) : digitFun c k < 2 ^ wid k := by
  unfold digitFun
  split_ifs with h he
  · simpa [wid, h] using (c ⟨k/2, by omega⟩).1.isLt
  · simpa [wid, h] using (c ⟨k/2, by omega⟩).2.isLt
  · positivity

def indexOf (c : PairTuple) : ℕ := ofDigits (digitFun c) 32

theorem digit_indexOf_fst (c : PairTuple) (q : Fin 16) :
    digit (indexOf c) (2*q.val) = (c q).1.val := by
  have hq := q.isLt
  rw [indexOf, digit_ofDigits _ (digitFun_lt c) 32 _ (by omega)]
  simp [digitFun, show 2*q.val < 32 by omega, Nat.mul_div_right]

theorem digit_indexOf_snd (c : PairTuple) (q : Fin 16) :
    digit (indexOf c) (2*q.val+1) = (c q).2.val := by
  have hq := q.isLt
  rw [indexOf, digit_ofDigits _ (digitFun_lt c) 32 _ (by omega)]
  simp [digitFun, show 2*q.val+1 < 32 by omega, Nat.add_div, Nat.mul_div_right]

theorem sum_digit_pairs (f : ℕ → ℕ) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n), f k) =
      ∑ q ∈ Finset.range n, (f (2*q) + f (2*q+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    simp only [Finset.sum_range_succ, ih]
    omega

theorem idxBits_eq : 2 ^ idxBits = 2 ^ pos 32 := by rw [pos_32]; norm_num [idxBits]

attribute [local irreducible] validSet PairCode.tuples

theorem card_validSet : (validSet).card = PairCode.count 16 target := by
  rw [← PairCode.tuples_card]
  refine Finset.card_bij' (fun i _ => digitsOf i) (fun c _ => indexOf c) ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨_, hsum, hcap⟩ := mem_validSet.mp hi
    simp only [PairCode.tuples, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hcap, ?_⟩
    rw [← hsum, show 32 = 2*16 from rfl, sum_digit_pairs,
      ← Fin.sum_univ_eq_sum_range]
    rfl
  · intro c hc
    simp only [PairCode.tuples, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine mem_validSet.mpr ⟨?_, ?_⟩
    · rw [idxBits_eq]
      exact ofDigits_lt _ (digitFun_lt c) 32
    · refine ⟨?_, ?_⟩
      · rw [show 32 = 2*16 from rfl, sum_digit_pairs, ← Fin.sum_univ_eq_sum_range]
        simpa only [digit_indexOf_fst, digit_indexOf_snd, PairCode.weight] using hc.2
      · intro q
        simpa only [PairAllowed, digit_indexOf_fst, digit_indexOf_snd, PairCode.weight] using hc.1 q
  · intro i hi
    obtain ⟨lt, _⟩ := mem_validSet.mp hi
    show ofDigits (digitFun (digitsOf i)) 32 = i
    have agree : ∀ k ∈ Finset.range 32,
        digitFun (digitsOf i) k * 2 ^ pos k = digit i k * 2 ^ pos k := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [digitFun, dif_pos hk']
      split_ifs with he
      · have heq : 2*(k/2) = k := by omega
        simp only [digitsOf, heq]
      · have heq : 2*(k/2)+1 = k := by omega
        simp only [digitsOf, heq]
    show ∑ k ∈ Finset.range 32, digitFun (digitsOf i) k * 2 ^ pos k = i
    rw [Finset.sum_congr rfl agree]
    rw [idxBits_eq] at lt
    exact ofDigits_digit i 32 lt
  · intro c _
    funext q
    apply Prod.ext
    · apply Fin.ext; exact digit_indexOf_fst c q
    · apply Fin.ext; exact digit_indexOf_snd c q

/-- A fresh index succeeds with probability at least `89 / 2 ^ 20`. -/
theorem numValid_avail : 89 * 2 ^ 108 ≤ numValid := by
  rw [numValid, card_validSet]
  exact PairCode.count_lower

/-! ## The machine's reading of the digits -/

/-- Unread bits preceding each digit. Sixteen 16-bit lanes each hold a pair,
with the fine digit at bit 2 and the coarse digit at bit 10. Cell 32 is trailing junk. -/
def jw (k : ℕ) : ℕ :=
  if k = 0 then 2 else if k < 32 then
    4
  else if k = 32 then 2 else 0

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
theorem compW_target_le : PairCode.count 16 target ≤ 2 ^ 127 := by
  rw [target, PairCode.exact_count]
  norm_num

theorem numValid_le_half : numValid ≤ 2 ^ 127 := by
  rw [numValid, card_validSet]
  exact compW_target_le

theorem two_numValid_le : 2 * numValid ≤ 2 ^ 128 := by
  have := numValid_le_half
  omega

end OptimalOTS
