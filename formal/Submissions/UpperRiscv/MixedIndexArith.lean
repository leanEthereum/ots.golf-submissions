import Submissions.UpperRiscv.MixedIndexLanes
import Submissions.UpperRiscv.MixedLanes

/-!
# The arithmetic of the index check

The four dispatch words sum with exactly three 64-bit wraps. Reduction modulo 255 checks the
digit-sum ranks 158 and 413. The pair restrictions in the chain phase subsequently exclude
413. Each stored lane holds `base − (4 · dA + 1024 · dB)` (`lane_halfword`).
-/

namespace OptimalOTS.RiscvMixedProgram

open Riscv2Program (W wordReg laneValue broadcast W_toNat fld)

open OptimalOTS.Dag
open RiscvZkvm.Rv64

theorem wid_le (k : ℕ) : wid k ≤ 5 := by unfold wid; split_ifs <;> omega

theorem fld_lt (u p b : ℕ) : fld u p b < 2 ^ b := Nat.mod_lt _ (by positivity)

theorem fineFld_le (g u l : ℕ) : fineFld g u l ≤ 15 := by
  have h := fld_lt u (16*l+2) (fineBits g l)
  have hw : 2 ^ fineBits g l ≤ 16 := by norm_num [fineBits]
  unfold fineFld
  omega

theorem coarseFld_le (g u l : ℕ) : coarseFld g u l ≤ 15 := by
  have h := fld_lt u (16*l+10) (coarseBits g l)
  have hw : 2 ^ coarseBits g l ≤ 16 := by norm_num [coarseBits]
  unfold coarseFld
  omega

/-- One lane of a masked word is below `15421`. -/
theorem laneEntry_le (g u l : ℕ) : 4 * fineFld g u l + 1024 * coarseFld g u l ≤ 15420 := by
  have := fineFld_le g u l; have := coarseFld_le g u l; omega

theorem laneNat_le (u g : ℕ) : laneNat u g ≤ 15420 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) := by
  unfold laneNat
  have := laneEntry_le g u 0
  have := laneEntry_le g u 1
  have := laneEntry_le g u 2
  have := laneEntry_le g u 3
  omega

/-- The mask registers hold the two masks. -/
def MasksLoaded (a : MachineState) : Prop := ∀ g, g < 4 → a.getReg (maskReg g) = W (maskNat g)

theorem laneOf_toNat (a : MachineState) (hm : MasksLoaded a) (g : ℕ) (hg : g < 4) :
    (laneOf a g).toNat = laneNat (a.getReg (wordReg g)).toNat g := by
  unfold laneOf
  rw [hm g hg]
  exact laneValue_toNat _ _

theorem laneSum_toNat (a : MachineState) (hm : MasksLoaded a) :
    ∀ n, n ≤ 4 → (laneSum a n).toNat =
      ∑ g ∈ Finset.range n, laneNat (a.getReg (wordReg g)).toNat g := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hb : ∀ n, ∑ g ∈ Finset.range n, laneNat (a.getReg (wordReg g)).toNat g ≤
        n * (15420 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by
      intro n
      calc ∑ g ∈ Finset.range n, laneNat (a.getReg (wordReg g)).toNat g
          ≤ ∑ _g ∈ Finset.range n, 15420 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) :=
            Finset.sum_le_sum fun g _ => laneNat_le _ _
        _ = n * (15420 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by simp
    rw [laneSum, BitVec.toNat_add, ih (by omega), laneOf_toNat a hm n (by omega),
      Finset.sum_range_succ, Nat.mod_eq_of_lt]
    have h1 := hb n
    have h2 := laneNat_le (a.getReg (wordReg n)).toNat n
    have : n * (15420 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) ≤
        3 * (15420 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- The word values of a state. -/
def wordsOf (a : MachineState) (g : ℕ) : ℕ := (a.getReg (wordReg g)).toNat

/-- The fine fields of lane `l` over the four words, and the coarse fields over the three pair
words. -/
def fineTotal (u : ℕ → ℕ) (l : ℕ) : ℕ := ∑ g ∈ Finset.range 4, fineFld g (u g) l

def coarseTotal (u : ℕ → ℕ) (l : ℕ) : ℕ := ∑ g ∈ Finset.range 4, coarseFld g (u g) l

theorem fineTotal_lt (u : ℕ → ℕ) (l : ℕ) : fineTotal u l < 64 := by
  unfold fineTotal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have := fineFld_le 0 (u 0) l; have := fineFld_le 1 (u 1) l
  have := fineFld_le 2 (u 2) l; have := fineFld_le 3 (u 3) l
  omega

theorem coarseTotal_lt (u : ℕ → ℕ) (l : ℕ) : coarseTotal u l < 64 := by
  unfold coarseTotal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have := coarseFld_le 0 (u 0) l; have := coarseFld_le 1 (u 1) l; have := coarseFld_le 2 (u 2) l; have := coarseFld_le 3 (u 3) l
  omega

/-- The lane sum is the pre-fold value of the fine and coarse totals. -/
theorem laneSum_lanes (u : ℕ → ℕ) :
    ∑ g ∈ Finset.range 4, laneNat (u g) g =
      preFold (fineTotal u 0) (fineTotal u 1) (fineTotal u 2) (fineTotal u 3)
        (coarseTotal u 0) (coarseTotal u 1) (coarseTotal u 2) (coarseTotal u 3) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, laneNat, preFold, fineTotal, coarseTotal]
  ring

theorem broadcast_toNat (B : ℕ) (hB : B < 2 ^ 16) :
    (W (broadcast B)).toNat = broadcast B := by
  apply W_toNat
  unfold broadcast
  omega

/-- The fold of the lane sum, lane by lane. -/
theorem fold_laneSum (a : MachineState) (hm : MasksLoaded a) (hfm : a.getReg .x1 = W (broadcast 0x1fc)) :
    (foldValue (laneSum a 4) (a.getReg .x1)).toNat =
      4 * (fineTotal (wordsOf a) 0 + coarseTotal (wordsOf a) 0) +
      2 ^ 16 * (4 * (fineTotal (wordsOf a) 1 + coarseTotal (wordsOf a) 1)) +
      2 ^ 32 * (4 * (fineTotal (wordsOf a) 2 + coarseTotal (wordsOf a) 2)) +
      2 ^ 48 * (4 * (fineTotal (wordsOf a) 3 + coarseTotal (wordsOf a) 3)) := by
  have hL : (laneSum a 4).toNat = preFold (fineTotal (wordsOf a) 0) (fineTotal (wordsOf a) 1)
      (fineTotal (wordsOf a) 2) (fineTotal (wordsOf a) 3) (coarseTotal (wordsOf a) 0)
      (coarseTotal (wordsOf a) 1) (coarseTotal (wordsOf a) 2) (coarseTotal (wordsOf a) 3) := by
    rw [laneSum_toNat a hm 4 le_rfl]
    exact laneSum_lanes (wordsOf a)
  have f0 := fineTotal_lt (wordsOf a) 0; have f1 := fineTotal_lt (wordsOf a) 1
  have f2 := fineTotal_lt (wordsOf a) 2; have f3 := fineTotal_lt (wordsOf a) 3
  have c0 := coarseTotal_lt (wordsOf a) 0; have c1 := coarseTotal_lt (wordsOf a) 1
  have c2 := coarseTotal_lt (wordsOf a) 2; have c3 := coarseTotal_lt (wordsOf a) 3
  have hfold := fold_toNat _ _ _ _ _ _ _ _ f0 f1 f2 f3 c0 c1 c2 c3
  have hmask : (W (broadcast 0x1fc)).toNat = broadcast 0x1fc :=
    broadcast_toNat _ (by norm_num)
  unfold foldValue
  rw [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, hfm, hmask, hL]
  exact hfold

/-- Word `g` of the index answer. -/
def wordOf (answer : BitVec hashBits) (g : ℕ) : Word := answer.extractLsb' (64 * g) 64

theorem fld_extract (answer : BitVec hashBits) (w p b : ℕ) (hpb : p + b ≤ 64) :
    fld (wordOf answer w).toNat p b = answer.toNat / 2 ^ (64 * w + p) % 2 ^ b := by
  unfold fld wordOf
  rw [show (BitVec.extractLsb' (64 * w) 64 answer).toNat = answer.toNat / 2 ^ (64 * w) % 2 ^ 64 by
      simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow],
    show (2 : ℕ) ^ 64 = 2 ^ p * 2 ^ (64 - p) by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)),
    Nat.div_div_eq_div_mul, ← pow_add]

/-- The chain whose digit is the fine field of lane `l` of word `g`. -/
def fineChain (g l : ℕ) : ℕ := 2 * (4 * g + l)

/-- The chain whose digit is the coarse field of lane `l` of pair word `g`. -/
def coarseChain (g l : ℕ) : ℕ := 2 * (4 * g + l) + 1

theorem fieldPos_fine (g l : ℕ) (hg : g < 4) (hl : l < 4) :
    fieldPos (fineChain g l) = 64 * g + (16 * l + 2) ∧ wid (fineChain g l) = fineBits g l := by
  interval_cases g <;> interval_cases l <;> decide

theorem fieldPos_coarse (g l : ℕ) (hg : g < 4) (hl : l < 4) :
    fieldPos (coarseChain g l) = 64 * g + (16 * l + 10) ∧ wid (coarseChain g l) = coarseBits g l := by
  interval_cases g <;> interval_cases l <;> decide

/-- The fine field of lane `l` of word `g` is the digit of chain `fineChain g l`. -/
theorem fine_word (answer : BitVec hashBits) (g l : ℕ) (hg : g < 4) (hl : l < 4) :
    fineFld g (wordOf answer g).toNat l = fieldDigit answer (fineChain g l) := by
  obtain ⟨hp, hw⟩ := fieldPos_fine g l hg hl
  unfold fineFld fieldDigit
  rw [fld_extract _ _ _ _ (by unfold fineBits; omega), hp, hw]

theorem coarse_word (answer : BitVec hashBits) (g l : ℕ) (hg : g < 4) (hl : l < 4) :
    coarseFld g (wordOf answer g).toNat l = fieldDigit answer (coarseChain g l) := by
  obtain ⟨hp, hw⟩ := fieldPos_coarse g l hg hl
  unfold coarseFld fieldDigit
  rw [fld_extract _ _ _ _ (by unfold coarseBits; omega), hp, hw]

/-- The words of the answer are in the index registers. -/
def WordsLoaded (a : MachineState) (answer : BitVec hashBits) : Prop :=
  ∀ g, g < 4 → a.getReg (wordReg g) = wordOf answer g

theorem field_sum (answer : BitVec hashBits) :
    ∑ l ∈ Finset.range 4, (fineTotal (fun g => (wordOf answer g).toNat) l +
      coarseTotal (fun g => (wordOf answer g).toNat) l) =
      ∑ k ∈ Finset.range 32, fieldDigit answer k := by
  simp only [fineTotal, coarseTotal, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [fine_word answer 0 0 (by norm_num) (by norm_num),
    fine_word answer 0 1 (by norm_num) (by norm_num),
    fine_word answer 0 2 (by norm_num) (by norm_num),
    fine_word answer 0 3 (by norm_num) (by norm_num),
    fine_word answer 1 0 (by norm_num) (by norm_num),
    fine_word answer 1 1 (by norm_num) (by norm_num),
    fine_word answer 1 2 (by norm_num) (by norm_num),
    fine_word answer 1 3 (by norm_num) (by norm_num),
    fine_word answer 2 0 (by norm_num) (by norm_num),
    fine_word answer 2 1 (by norm_num) (by norm_num),
    fine_word answer 2 2 (by norm_num) (by norm_num),
    fine_word answer 2 3 (by norm_num) (by norm_num),
    fine_word answer 3 0 (by norm_num) (by norm_num),
    fine_word answer 3 1 (by norm_num) (by norm_num),
    fine_word answer 3 2 (by norm_num) (by norm_num),
    fine_word answer 3 3 (by norm_num) (by norm_num),
    coarse_word answer 0 0 (by norm_num) (by norm_num),
    coarse_word answer 0 1 (by norm_num) (by norm_num),
    coarse_word answer 0 2 (by norm_num) (by norm_num),
    coarse_word answer 0 3 (by norm_num) (by norm_num),
    coarse_word answer 1 0 (by norm_num) (by norm_num),
    coarse_word answer 1 1 (by norm_num) (by norm_num),
    coarse_word answer 1 2 (by norm_num) (by norm_num),
    coarse_word answer 1 3 (by norm_num) (by norm_num),
    coarse_word answer 2 0 (by norm_num) (by norm_num),
    coarse_word answer 2 1 (by norm_num) (by norm_num),
    coarse_word answer 2 2 (by norm_num) (by norm_num),
    coarse_word answer 2 3 (by norm_num) (by norm_num),
    coarse_word answer 3 0 (by norm_num) (by norm_num),
    coarse_word answer 3 1 (by norm_num) (by norm_num),
    coarse_word answer 3 2 (by norm_num) (by norm_num),
    coarse_word answer 3 3 (by norm_num) (by norm_num)]
  norm_num [fineChain, coarseChain]
  ring

theorem remainder_fold_answer (a : MachineState) (hm : MasksLoaded a) (answer : BitVec hashBits)
    (hw : WordsLoaded a answer) (hfm : a.getReg .x1 = W (broadcast 0x1fc)) :
    (foldValue (laneSum a 4) (a.getReg .x1)).toNat % 65535 =
      4 * ∑ k ∈ Finset.range 32, fieldDigit answer k := by
  rw [fold_laneSum a hm hfm]
  have hf : ∀ l, fineTotal (wordsOf a) l = fineTotal (fun g => (wordOf answer g).toNat) l := by
    intro l
    unfold fineTotal
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [wordsOf, hw g (Finset.mem_range.mp hg)]
  have hc : ∀ l, coarseTotal (wordsOf a) l = coarseTotal (fun g => (wordOf answer g).toNat) l := by
    intro l
    unfold coarseTotal
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [wordsOf, hw g (Finset.mem_range.mp hg)]
  have bound : ∀ l, 4*(fineTotal (wordsOf a) l + coarseTotal (wordsOf a) l) ≤ 764 := by
    intro l
    have := fineTotal_lt (wordsOf a) l
    have := coarseTotal_lt (wordsOf a) l
    omega
  rw [lane_remainder _ _ _ _ (by have := bound 0; have := bound 1; have := bound 2; have := bound 3; omega),
    ← field_sum answer]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf, hc]
  ring

/-- The cheap address checksum deliberately keeps two ranks. The pair tables eliminate 413. -/
def IndexRank (i : ℕ) : Prop :=
  (∑ k ∈ Finset.range 32, digit i k) = 158 ∨
  (∑ k ∈ Finset.range 32, digit i k) = 413

instance : DecidablePred IndexRank := fun _ => inferInstanceAs (Decidable (_ ∨ _))

theorem accepted_indexRank {i : ℕ} (hi : Accepted i) : IndexRank i :=
  Or.inl hi.1

theorem digit_sum_pairs (i : ℕ) :
    (∑ k ∈ Finset.range 32, digit i k) =
      ∑ q ∈ Finset.range 16, (digit i (2*q) + digit i (2*q+1)) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

theorem caps_sum_le {i : ℕ} (hc : ∀ q : Fin 16, PairAllowed i q.val) :
    (∑ k ∈ Finset.range 32, digit i k) ≤ 412 := by
  rw [digit_sum_pairs]
  calc
    _ ≤ ∑ q ∈ Finset.range 16, PairCode.cap q := by
      apply Finset.sum_le_sum
      intro q hq
      exact hc ⟨q, Finset.mem_range.mp hq⟩
    _ = 412 := by decide +kernel

theorem accepted_iff_rank_caps (i : ℕ) :
    Accepted i ↔ IndexRank i ∧ ∀ q : Fin 16, PairAllowed i q.val := by
  constructor
  · intro h
    exact ⟨accepted_indexRank h, h.2⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc⟩
    have bound := caps_sum_le hc
    rcases hr with h | h
    · exact h
    · omega

theorem indexRank_iff (answer : BitVec hashBits) :
    IndexRank (pack answer) ↔
      (∑ k ∈ Finset.range 32, fieldDigit answer k) = 158 ∨
      (∑ k ∈ Finset.range 32, fieldDigit answer k) = 413 := by
  unfold IndexRank
  rw [Finset.sum_congr rfl fun k hk => digit_pack answer (Finset.mem_range.mp hk)]

theorem addressSum_eq (a : MachineState)
    (hb : ∀ g, g < 4 → a.getReg (baseReg g) = W (baseWord g)) :
    addressSum a 4 = W (4 * baseWord 0) - laneSum a 4 := by
  have h : ∀ g, g < 4 → a.getReg (baseReg g) = W (baseWord 0) := by
    intro g hg
    rw [hb g hg]
    interval_cases g <;> decide +kernel
  have eb : W (4 * baseWord 0) =
      W (baseWord 0) + W (baseWord 0) + W (baseWord 0) + W (baseWord 0) := by
    decide +kernel
  simp only [addressSum, laneSum, h 0 (by norm_num), h 1 (by norm_num),
    h 2 (by norm_num), h 3 (by norm_num), eb]
  abel

theorem addressSum_toNat (a : MachineState) (hm : MasksLoaded a)
    (hb : ∀ g, g < 4 → a.getReg (baseReg g) = W (baseWord g)) :
    (addressSum a 4).toNat =
      4 * baseWord 0 - 3 * 2 ^ 64 - (laneSum a 4).toNat := by
  have bound : (laneSum a 4).toNat ≤ 4 * 4340410370284600380 := by
    rw [laneSum_toNat a hm 4 le_rfl]
    have h := Finset.sum_le_sum (s := Finset.range 4) (fun g _ => laneNat_le (a.getReg (wordReg g)).toNat g)
    norm_num at h ⊢
    exact h
  rw [addressSum_eq a hb]
  have eb : (W (4 * baseWord 0)).toNat = 4 * baseWord 0 - 3 * 2 ^ 64 := by
    decide +kernel
  rw [BitVec.toNat_sub_of_le, eb]
  rw [BitVec.le_def, eb]
  have en : baseWord 0 = 18445835621712285080 := by decide +kernel
  rw [en]
  omega

theorem raw_sum_mod (a : MachineState) (hm : MasksLoaded a) (answer : BitVec hashBits)
    (hw : WordsLoaded a answer) :
    (laneSum a 4).toNat % 255 =
      (4 * ∑ k ∈ Finset.range 32, fieldDigit answer k) % 255 := by
  rw [laneSum_toNat a hm 4 le_rfl]
  have he : (∑ g ∈ Finset.range 4, laneNat (a.getReg (wordReg g)).toNat g) =
      ∑ g ∈ Finset.range 4, laneNat (wordOf answer g).toNat g := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [hw g (Finset.mem_range.mp hg)]
  rw [he, laneSum_lanes, ← field_sum answer]
  simp only [preFold, Finset.sum_range_succ, Finset.sum_range_zero]
  omega

theorem address_remainder_iff (a : MachineState) (hm : MasksLoaded a)
    (answer : BitVec hashBits) (hw : WordsLoaded a answer)
    (hb : ∀ g, g < 4 → a.getReg (baseReg g) = W (baseWord g)) :
    (addressSum a 4).toNat % 255 = 0 ↔ IndexRank (pack answer) := by
  have congruence := raw_sum_mod a hm answer hw
  have bound : (laneSum a 4).toNat ≤ 4 * 4340410370284600380 := by
    rw [laneSum_toNat a hm 4 le_rfl]
    have h := Finset.sum_le_sum (s := Finset.range 4) (fun g _ => laneNat_le (a.getReg (wordReg g)).toNat g)
    norm_num at h ⊢
    exact h
  have total : (∑ k ∈ Finset.range 32, fieldDigit answer k) ≤ 480 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range 32, 15 := by
        apply Finset.sum_le_sum
        intro k hk
        have h := fieldDigit_lt answer k
        have hk' := Finset.mem_range.mp hk
        simp only [wid, if_pos hk', Nat.reducePow] at h
        omega
      _ = 480 := by norm_num
  rw [addressSum_toNat a hm hb, indexRank_iff]
  have en : baseWord 0 = 18445835621712285080 := by decide +kernel
  rw [en]
  omega

end OptimalOTS.RiscvMixedProgram
