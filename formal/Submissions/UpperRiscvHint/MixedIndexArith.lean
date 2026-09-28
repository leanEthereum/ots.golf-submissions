import Submissions.UpperRiscvHint.MixedIndexLanes
import Submissions.UpperRiscvHint.MixedProgram
import Submissions.UpperRiscvHint.Lanes

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (broadcast and_split and_split_at and_field fld laneValue)

def fineBits (_g _l : ℕ) : ℕ := 4
def coarseBits (_g _l : ℕ) : ℕ := 4
def fineFld (g u l : ℕ) : ℕ := fld u (16*l+2) (fineBits g l)
def coarseFld (g u l : ℕ) : ℕ := fld u (16*l+10) (coarseBits g l)
def maskNat (_g : ℕ) : ℕ := broadcast 0x3c3c
def laneNat (u g : ℕ) : ℕ :=
  (4*fineFld g u 0+1024*coarseFld g u 0) + 2^16*(4*fineFld g u 1+1024*coarseFld g u 1) +
  2^32*(4*fineFld g u 2+1024*coarseFld g u 2) + 2^48*(4*fineFld g u 3+1024*coarseFld g u 3)

theorem and_pair (y a b : ℕ) (ha : a ≤ 8) :
    y &&& (4*(2^a-1)+1024*(2^b-1)) = 4*(y/4%2^a)+1024*(y/1024%2^b) := by
  have hb : 4*(2^a-1) < 2^10 := by
    have : 2^a ≤ (2:ℕ)^8 := Nat.pow_le_pow_right (by omega) ha
    omega
  rw [show (1024:ℕ)=2^10 by norm_num, and_split_at _ _ _ 10 hb, and_field,
    Nat.and_two_pow_sub_one_eq_mod]
  have h : y % 2^10 / 4 % 2^a = y/4%2^a := by
    rw [show (2:ℕ)^10 = 4*2^8 by norm_num, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 ha)]
  rw [h]

private theorem mod_f5 (u : ℕ) : u%65536/4%32=u/4%32 := by omega
private theorem mod_f4 (u : ℕ) : u%65536/4%16=u/4%16 := by omega
private theorem mod_c3 (u : ℕ) : u%65536/1024%8=u/1024%8 := by omega
private theorem mod_c4 (u : ℕ) : u%65536/1024%16=u/1024%16 := by omega
private theorem mod_fold (u : ℕ) : u%65536/4%128=u/4%128 := by omega

theorem and_mask (u g : ℕ) : u &&& maskNat g = laneNat u g := by
  unfold maskNat laneNat fineFld coarseFld fineBits coarseBits fld
  have hm : broadcast 0x3c3c = (4*(2^4-1)+1024*(2^4-1)) + 2^16*((4*(2^4-1)+1024*(2^4-1)) +
      2^16*((4*(2^4-1)+1024*(2^4-1)) + 2^16*(4*(2^4-1)+1024*(2^4-1)))) := by
    norm_num [broadcast]
  rw [hm, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num)]
  simp only [and_pair _ 5 3 (by omega), and_pair _ 4 4 (by omega)]
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  simp only [mod_f5, mod_f4, mod_c3, mod_c4, Nat.div_div_eq_div_mul]
  norm_num only [Nat.reduceMul]
  ring

theorem maskNat_toNat (g : ℕ) : (BitVec.ofNat 64 (maskNat g)).toNat = maskNat g := by
  norm_num [maskNat, broadcast]

theorem laneValue_toNat (u : Word) (g : ℕ) :
    (laneValue u (BitVec.ofNat 64 (maskNat g))).toNat = laneNat u.toNat g := by
  rw [laneValue, BitVec.toNat_and, maskNat_toNat, and_mask]

def preFold (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ) : ℕ :=
  (4*s0+1024*t0)+2^16*(4*s1+1024*t1)+2^32*(4*s2+1024*t2)+2^48*(4*s3+1024*t3)

end OptimalOTS.RiscvMixedProgram

/-!
# The arithmetic of the index check

The four dispatch words sum with exactly three 64-bit wraps. Adding four times the
complemented free count (31-c), the sum's residue modulo 255 checks that the digit sum plus the count is 145 modulo 255. Each stored lane holds `base − (4 · dA + 1024 · dB)` (`lane_halfword`).
-/

namespace OptimalOTS.RiscvMixedProgram

open Riscv2Program (W wordReg laneValue broadcast W_toNat fld)

open OptimalOTS.Dag
open RiscvZkvm.Rv64

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

/-- The fine fields of lane `l` over the four words, and the coarse fields over the three pair
words. -/
def fineTotal (u : ℕ → ℕ) (l : ℕ) : ℕ := ∑ g ∈ Finset.range 4, fineFld g (u g) l

def coarseTotal (u : ℕ → ℕ) (l : ℕ) : ℕ := ∑ g ∈ Finset.range 4, coarseFld g (u g) l

/-- The lane sum is the pre-fold value of the fine and coarse totals. -/
theorem laneSum_lanes (u : ℕ → ℕ) :
    ∑ g ∈ Finset.range 4, laneNat (u g) g =
      preFold (fineTotal u 0) (fineTotal u 1) (fineTotal u 2) (fineTotal u 3)
        (coarseTotal u 0) (coarseTotal u 1) (coarseTotal u 2) (coarseTotal u 3) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, laneNat, preFold, fineTotal, coarseTotal]
  ring

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
  have en : baseWord 0 = 18445833920962121929 := by decide +kernel
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

theorem digitSum_pack (answer : BitVec hashBits) :
    digitSum (pack answer) = ∑ k ∈ Finset.range 32, fieldDigit answer k := by
  unfold digitSum
  exact Finset.sum_congr rfl fun k hk => digit_pack answer (Finset.mem_range.mp hk)

/-- The address sum plus four times the complemented count has residue 1 exactly when the count is the
index's free digit, that is when the digit sum plus the count is 145 modulo 255. -/
theorem free_remainder_iff (a : MachineState) (hm : MasksLoaded a)
    (answer : BitVec hashBits) (hw : WordsLoaded a answer)
    (hb : ∀ g, g < 4 → a.getReg (baseReg g) = W (baseWord g)) (c : ℕ) (hc : c < 32) :
    (addressSum a 4 + W (6144 + 4 * (31-c))).toNat % 255 = 1 ↔ freeDigit (pack answer) = c := by
  have congruence := raw_sum_mod a hm answer hw
  have bound : (laneSum a 4).toNat ≤ 4 * 4340410370284600380 := by
    rw [laneSum_toNat a hm 4 le_rfl]
    have h := Finset.sum_le_sum (s := Finset.range 4)
      (fun g _ => laneNat_le (a.getReg (wordReg g)).toNat g)
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
  have hs := addressSum_toNat a hm hb
  have en : baseWord 0 = 18445833920962121929 := by decide +kernel
  rw [en] at hs
  have hc' : (W (6144 + 4 * (31-c))).toNat = 6144 + 4 * (31-c) := W_toNat _ (by omega)
  rw [BitVec.toNat_add, hc', hs, Nat.mod_eq_of_lt (show
    4 * 18445833920962121929 - 3 * 2 ^ 64 - (laneSum a 4).toNat + (6144 + 4 * (31-c)) < 2^64 by omega),
    freeDigit, digitSum_pack]
  omega

end OptimalOTS.RiscvMixedProgram
