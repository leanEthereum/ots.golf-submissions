import OptimalOTS.Dag
import Submissions.UpperRiscvHint.PairCount
import Submissions.UpperRiscvHint.Digits

/-! Scheme-local signature parameters. A 128-bit nonce preserves the nonce/index
space equality used by the adaptive chosen-message security proof. -/

namespace OptimalOTS

open OracleSpec OracleComp
open OptimalOTS.Dag

def nonceBits : ℕ := 128
abbrev Nonce := BitVec nonceBits
abbrev Signature := Nonce × List Bool

def idxCost : ℕ := blockCost (pkBits + msgBits + nonceBits)
def trials : ℕ := signBudget / idxCost

/-- The same unrestricted two-stage attacker interface, with this scheme's signature type. -/
structure Adversary where
  State : Type
  choose : PublicKey → OracleComp Spec (Message × State)
  forge : State → Option Signature → OracleComp Spec (Message × Signature)

end OptimalOTS

/-!
# Accepted indices

The index packs sixteen raw nibble pairs into 128 bits. The coarse nibble is
complemented before the weighted pair recoding; pairs 0–5 use the skip-aware cap alphabet.
Accept shifted weighted sums in [129,147], and fill the remaining rank with a free digit 0
through 18.
The exact accepted count exceeds `89 * 2^108`.

The machine reads digit `k` from bits `fieldPos k, …` of the 256-bit index answer; `pack` is
that reading.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace OptimalOTS

open OptimalOTS.Dag

/-- The digit sum of an accepted index plus its free count. -/
def target : ℕ := 147

/-- Thirty-two four-bit digits. -/
def wid (k : ℕ) : ℕ := if k < 32 then 4 else 0

/-- Position of digit `k` in the packed index. -/
abbrev pos : ℕ → ℕ := posW wid

theorem pos_32 : pos 32 = 128 := by decide

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

theorem digit_lt_16 (i k : ℕ) : digit i k < 16 := by
  have h := digit_lt i k
  have hw : 2 ^ wid k ≤ 16 := by unfold wid; split_ifs <;> norm_num
  omega

/-- Raw pair of adjacent nibbles, before complementing the coarse nibble. -/
def rawPair (i q : ℕ) : PairCode.Pair :=
  (⟨digit i (2*q), digit_lt_16 _ _⟩, ⟨digit i (2*q+1), digit_lt_16 _ _⟩)

/-- Every raw pair has a valid weighted decoding. -/
def PairAllowed (i q : ℕ) : Prop := PairCode.weight q (rawPair i q) ≤ PairCode.cap q

instance : DecidableRel PairAllowed := fun _ _ => by unfold PairAllowed; infer_instance

theorem pairAllowed_all (i q : ℕ) : PairAllowed i q := PairCode.weight_le _ _

/-- Actual chain digit after the injective pair recoding. -/
def stepDigit (i k : ℕ) : ℕ :=
  if k % 2 = 0 then (PairCode.recode (k/2) (rawPair i (k/2))).1
  else (PairCode.recode (k/2) (rawPair i (k/2))).2

@[simp] theorem stepDigit_even (i q : ℕ) :
    stepDigit i (2*q) = (PairCode.recode q (rawPair i q)).1 := by simp [stepDigit]

@[simp] theorem stepDigit_odd (i q : ℕ) :
    stepDigit i (2*q+1) = (PairCode.recode q (rawPair i q)).2 := by
  have hd : (2*q+1)/2 = q := by omega
  simp [stepDigit, hd, Nat.add_mod]

theorem stepDigit_le (i k : ℕ) : stepDigit i k ≤ 22 := by
  have h := PairCode.recode_bounds (k/2) (rawPair i (k/2))
  unfold stepDigit
  split_ifs <;> omega

/-- The shifted weighted sum, including each decoder's two-instruction fee and each skip. -/
def digitSum (i : ℕ) : ℕ := ∑ q : Fin 16, PairCode.weight q (rawPair i q)

/-- Number of redirected pairs. -/
def helperCount (i : ℕ) : ℕ := ∑ q : Fin 16, PairCode.helper q (rawPair i q)

/-- Instructions removed by skipped pointer pairs. -/
def skipCount (i : ℕ) : ℕ := ∑ q : Fin 16, PairCode.skipSave q (rawPair i q)

theorem digitSum_le (i : ℕ) : digitSum i ≤ 384 := by
  calc digitSum i ≤ ∑ _q : Fin 16, 24 :=
        Finset.sum_le_sum fun q _ => PairCode.weight_le q (rawPair i q)
       _ = 384 := by simp

/-- The free count: `target - S` on the window. For `c < 257`,
`(S + c) % 257 = target` exactly when `c = freeDigit i`. -/
def freeDigit (i : ℕ) : ℕ := (661 - digitSum i) % 257

/-- Accepted indices: shifted weighted sum 129 through 147. Pair validity is automatic. -/
def Accepted (i : ℕ) : Prop :=
  (129 ≤ digitSum i ∧ digitSum i ≤ target) ∧ ∀ q : Fin 16, PairAllowed i q.val

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

/-- Interpreter input: the packed index and the free-chain count. The machine
can supply an arbitrary view count; accepted signatures use `ofRaw`. -/
structure ChainIndex where
  raw : RawIdx
  free : Fin 32
  deriving DecidableEq

def ChainIndex.val (i : ChainIndex) : ℕ := i.raw.val

theorem ChainIndex.isLt (i : ChainIndex) : i.val < 2 ^ idxBits := i.raw.isLt

def ChainIndex.ofRaw (i : RawIdx) : ChainIndex :=
  ⟨i, ⟨min (freeDigit i.val) 31, by omega⟩⟩

instance : Coe RawIdx ChainIndex := ⟨ChainIndex.ofRaw⟩
instance : Coe Idx ChainIndex := ⟨fun i => ChainIndex.ofRaw i.toRaw⟩

@[simp] theorem ChainIndex.ofRaw_val (i : RawIdx) : (ChainIndex.ofRaw i).val = i.val := rfl
@[simp] theorem Idx.toChain_val (i : Idx) : (i : ChainIndex).val = i.val := rfl
@[simp] theorem Idx.toChain_free (i : Idx) :
    (i : ChainIndex).free.val = min (freeDigit i.val) 31 := rfl

theorem ChainIndex.ext {i j : ChainIndex} (hv : i.val = j.val) (hf : i.free = j.free) : i = j := by
  cases i with
  | mk a b =>
    cases j with
    | mk c d =>
      have h : a = c := Fin.ext hv
      cases h
      cases hf
      rfl

theorem numValid_le : numValid ≤ 2 ^ idxBits := by
  unfold numValid validSet
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])

/-! ## Counting the accepted indices -/

abbrev PairTuple := Fin 16 → PairCode.Pair

/-- The sixteen pairs of an index. -/
def digitsOf (i : ℕ) (q : Fin 16) : PairCode.Pair := rawPair i q

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

theorem digitSum_eq_weights (i : ℕ) :
    digitSum i = ∑ q : Fin 16, WeightedPairs.pairWeight (WeightedPairs.capPos q.val)
      (stepDigit i (2*q.val)) (stepDigit i (2*q.val+1)) := by
  simp only [digitSum, stepDigit_even, stepDigit_odd, PairCode.weight_recode, PairCode.kind]

theorem kind_count : (∑ q : Fin 16, if PairCode.kind q.val then 1 else 0) = 6 := by
  decide +kernel

theorem digitSum_cost (i : ℕ) :
    digitSum i + skipCount i = (∑ k ∈ Finset.range 32, stepDigit i k) + 2*helperCount i + 6 := by
  rw [show 32 = 2*16 from rfl, sum_digit_pairs, ← Fin.sum_univ_eq_sum_range, ← kind_count]
  simp only [digitSum, skipCount, ← Finset.sum_add_distrib, PairCode.decoder_cost_exact,
    stepDigit_even, stepDigit_odd, helperCount, Finset.mul_sum]

theorem skipCount_le (i : ℕ) : skipCount i ≤ 6 + helperCount i := by
  have h : skipCount i ≤ ∑ q : Fin 16, ((if PairCode.kind q.val then 1 else 0) +
      PairCode.helper q.val (rawPair i q)) :=
    Finset.sum_le_sum fun q _ => PairCode.skipSave_le q.val (rawPair i q)
  rw [Finset.sum_add_distrib, kind_count] at h
  exact h

theorem idxBits_eq : 2 ^ idxBits = 2 ^ pos 32 := by rw [pos_32]; norm_num [idxBits]

attribute [local irreducible] validSet PairCode.tuples

/-- Accepted indices with digit sum `s`. -/
def validAt (s : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ idxBits)).filter fun i => digitSum i = s ∧ ∀ q : Fin 16, PairAllowed i q.val

theorem card_validAt (s : ℕ) : (validAt s).card = PairCode.count 16 s := by
  rw [← PairCode.tuples_card]
  refine Finset.card_bij' (fun i _ => digitsOf i) (fun c _ => indexOf c) ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨_, hsum, _⟩ := Finset.mem_filter.mp hi
    simpa only [PairCode.tuples, Finset.mem_filter, Finset.mem_univ, true_and,
      digitsOf, digitSum] using hsum
  · intro c hc
    simp only [PairCode.tuples, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine Finset.mem_filter.mpr ⟨?_, ?_, fun q => pairAllowed_all _ _⟩
    · rw [Finset.mem_range, idxBits_eq]
      exact ofDigits_lt _ (digitFun_lt c) 32
    · have hpair : ∀ q : Fin 16, rawPair (indexOf c) q = c q := by
        intro q
        apply Prod.ext
        · exact Fin.ext (digit_indexOf_fst c q)
        · exact Fin.ext (digit_indexOf_snd c q)
      simpa only [digitSum, hpair] using hc
  · intro i hi
    have lt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    show ofDigits (digitFun (digitsOf i)) 32 = i
    have agree : ∀ k ∈ Finset.range 32,
        digitFun (digitsOf i) k * 2 ^ pos k = digit i k * 2 ^ pos k := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [digitFun, dif_pos hk']
      split_ifs with he
      · have heq : 2*(k/2) = k := by omega
        simp only [digitsOf, rawPair, heq]
      · have heq : 2*(k/2)+1 = k := by omega
        simp only [digitsOf, rawPair, heq]
    show ∑ k ∈ Finset.range 32, digitFun (digitsOf i) k * 2 ^ pos k = i
    rw [Finset.sum_congr rfl agree]
    rw [idxBits_eq] at lt
    exact ofDigits_digit i 32 lt
  · intro c _
    funext q
    apply Prod.ext
    · apply Fin.ext; exact digit_indexOf_fst c q
    · apply Fin.ext; exact digit_indexOf_snd c q

theorem card_validSet :
    (validSet).card = ∑ s ∈ Finset.range 19, PairCode.count 16 (129 + s) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun i => digitSum i - 129) (t := Finset.range 19)]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [← card_validAt]
    apply congrArg Finset.card
    ext i
    have hs' := Finset.mem_range.mp hs
    simp only [validSet, validAt, Accepted, target, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, ⟨lo, hi'⟩, caps⟩, e⟩
      exact ⟨hi, by omega, caps⟩
    · rintro ⟨hi, e, caps⟩
      exact ⟨⟨hi, ⟨by omega, by omega⟩, caps⟩, by omega⟩
  · intro i hi
    obtain ⟨_, ⟨lo, hi'⟩, _⟩ := mem_validSet.mp hi
    simp only [Finset.coe_range, Set.mem_Iio]
    unfold target at hi'
    omega

/-- A fresh index succeeds with probability at least `89 / 2 ^ 20`. -/
theorem numValid_avail : 89 * 2 ^ 108 ≤ numValid := by
  rw [numValid, card_validSet]
  exact PairCode.window_lower

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

attribute [irreducible] pack

/-- Fewer than half of the indices are accepted. -/
theorem numValid_le_half : numValid ≤ 2 ^ 127 := by
  rw [numValid, card_validSet]
  exact PairCode.window_le_half

theorem two_numValid_le : 2 * numValid ≤ 2 ^ 128 := by
  have := numValid_le_half
  omega

end OptimalOTS
