import Submissions.UpperLeanIsa.FourMachineLayout
import Submissions.UpperLeanIsa.LengthGate128

/-! Lemmas for reusing the validated signature length as a landing frame.
The packed machine uses the eight-unit checksum shift; the frame constants
below are retained as auxiliary cell algebra. -/

namespace OptimalOTS.HLFour.LengthFrame

open LeanerVM.Parameters

/-- The already certified discrete logarithm of the full signature length. -/
def lengthExp : ℕ := 1434881718044321323

/-- Fourteen separated frames use C1,...,C13 and the public length word. -/
def exponent (f : ℕ) : ℕ :=
  if f = 0 then 1152921504606846976
  else if f = 1 then lengthExp
  else f * 1152921504606846976

theorem length_value : gpow lengthExp = (5504 : K) :=
  OptimalOTS.HLG3.LengthGate.log5504

theorem bounds : ∀ f < 14, 2 ^ 33 ≤ exponent f ∧ exponent f ≤ eLen := by
  decide

theorem separated : ∀ f < 14, ∀ j < 14, j < f →
    exponent j + 2 ^ 33 ≤ exponent f := by
  decide

theorem length_frame : ofK (gpow (exponent 1)) = OptimalOTS.HLG3.natV 5504 := by
  change ofK (gpow lengthExp) = ofK (BitVec.ofNat 64 5504)
  rw [length_value]
  rfl

/-- The eight binding groups each contribute at least one hash. -/
abbrev deduction := bindingDeduction

theorem deduction_sum : (∑ u ∈ Finset.range 13, deduction u) = 8 := by decide

theorem zero_band : ∀ u < 13, deduction u = 1 → pn u 0 = 0 := by decide

theorem last_band : ∀ u < 13, deduction u = 0 → pn u 17 = 0 := by decide

theorem band_lower {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    deduction u ≤ band u v := by
  by_cases hd : deduction u = 0
  · rw [hd]; omega
  have hd1 : deduction u = 1 := by unfold deduction bindingDeduction at hd ⊢; split_ifs at hd ⊢ <;> omega
  rw [hd1]
  have h := (band_spec hu hv).2.2
  by_contra hn
  have hb : band u v = 0 := by omega
  rw [hb, A_succ, zero_band u hu hd1] at h
  simp [A, psum] at h

theorem band_shift_le {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    band u v - deduction u ≤ 16 := by
  have hb := band_lt_17 hu hv
  by_cases hd : deduction u = 0
  · rw [hd, Nat.sub_zero]
    by_contra hn
    have he : band u v = 17 := by omega
    obtain ⟨_, hlo, hhi⟩ := band_spec hu hv
    rw [he] at hlo hhi
    rw [A_succ, last_band u hu hd, Nat.add_zero] at hhi
    omega
  · have hd1 : deduction u = 1 := by unfold deduction bindingDeduction at hd ⊢; split_ifs at hd ⊢ <;> omega
    omega

theorem cost_lower {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    deduction u ≤ cost T u v := by
  rw [hT.cost_eq u hu v hv]
  exact band_lower hu hv

theorem cost_shift_le {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    cost T u v - deduction u ≤ 16 := by
  rw [hT.cost_eq u hu v hv]
  exact band_shift_le hu hv

theorem shifted_sum (C : ℕ → ℕ) (hC : ∀ u < 13, deduction u ≤ C u) :
    (∑ u ∈ Finset.range 13, (C u - deduction u)) + 8 = ∑ u ∈ Finset.range 13, C u := by
  rw [← deduction_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  exact Nat.sub_add_cancel (hC u (Finset.mem_range.mp hu))

/-- Subtracting one from each of eight positive binding-group costs changes the
target from 85 to 77 and preserves exact checking by the existing product gate. -/
theorem shifted_checksum {s c : ℕ} (hc : 8 ≤ c) (hbound : s + c ≤ 300) :
    LeanIsaFieldRescale.initialProduct 77 s *
      LeanIsaFieldRescale.costFactor (c - 8) = gpow LeanIsaFieldRescale.sentinel ↔
      s + c = 85 := by
  rw [LeanIsaFieldRescale.checksum_exact (by decide) (by omega)]
  omega

theorem shifted_product (s c : ℕ) :
    LeanIsaFieldRescale.initialProduct 77 s * LeanIsaFieldRescale.costFactor c =
    LeanIsaFieldRescale.initialProduct 85 s * LeanIsaFieldRescale.costFactor (c + 8) := by
  have he : LeanIsaFieldRescale.costFactor 85 =
      LeanIsaFieldRescale.costFactor 77 * LeanIsaFieldRescale.costFactor 8 :=
    (LeanIsaFieldRescale.factor_add 77 8).symm
  have h77 : LeanIsaFieldRescale.costFactor 77 ≠ 0 := pow_ne_zero _ g_ne_zero
  have h8 : LeanIsaFieldRescale.costFactor 8 ≠ 0 := pow_ne_zero _ g_ne_zero
  simp only [LeanIsaFieldRescale.initialProduct, he, ← LeanIsaFieldRescale.factor_add c 8]
  field_simp


end OptimalOTS.HLFour.LengthFrame
