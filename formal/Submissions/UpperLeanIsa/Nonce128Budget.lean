import Submissions.UpperLeanIsa.TierKernel

/-! Standalone algebra for the 128-bit signing nonce. The same inequalities are
implemented for general schedules in TierKernel; LayerScheme and the fused
machine now use the full nonce and the 5504-bit wire format. -/

namespace OptimalOTS.LeanIsaBaseline.Layer.Tier.Nonce128

/-- The proposed budget term with nonce-row size 2^128 and knee one. -/
noncomputable def budget (hp k1 : ℝ) (b : ℕ) : ℝ :=
  k1 * b + hp / (4 * 2^128) * ((b - 1 : ℕ) : ℝ)^2

theorem budget_charge {hp k1 : ℝ} (hh : 0 ≤ hp) (hk : hp ≤ 2*k1)
    {b : ℕ} (hb : 2 ≤ b) :
    budget hp k1 (b-2) + (1 + ((b-2 : ℕ) : ℝ) / 2^128) * hp ≤
      budget hp k1 b := by
  by_cases hb2 : b = 2
  · subst b
    norm_num [budget]
    linarith
  · have hb3 : 3 ≤ b := by omega
    have he1 : ((b-1 : ℕ) : ℝ) = (b : ℝ)-1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have he2 : ((b-2 : ℕ) : ℝ) = (b : ℝ)-2 := by
      rw [Nat.cast_sub hb, Nat.cast_ofNat]
    have he3 : ((b-2-1 : ℕ) : ℝ) = (b : ℝ)-3 := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      norm_num
    unfold budget
    rw [he1, he2, he3]
    nlinarith

/-- With 2^128 nonces and a 2^127 attack budget, the algebraic slope becomes
5/8 of `hp`, assuming the linear term is `hp/2`. -/
theorem budget_le {hp : ℝ} (hh : 0 ≤ hp)
    (hs : (5/8 : ℝ)*hp ≤ 1/2^127) {b : ℕ} (hb : b ≤ 2^127) :
    budget hp (hp/2) b ≤ (b : ℝ)/2^127 := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hbR : (b : ℝ) ≤ 2^127 := by exact_mod_cast hb
  have hx0 : (0 : ℝ) ≤ ((b-1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxb : ((b-1 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.sub_le b 1
  have hsq : ((b-1 : ℕ) : ℝ)^2 ≤ (2^127 : ℝ)*b := by
    calc _ ≤ (b : ℝ)^2 := pow_le_pow_left₀ hx0 hxb 2
      _ ≤ (2^127 : ℝ)*b := by nlinarith
  have hq : hp / (4*2^128) * ((b-1 : ℕ) : ℝ)^2 ≤ hp/8*b := by
    calc _ ≤ hp/(4*2^128) * ((2^127 : ℝ)*b) :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg hh (by positivity))
      _ = hp/8*b := by ring
  calc budget hp (hp/2) b ≤ (5/8*hp)*b := by unfold budget; nlinarith
    _ ≤ (1/2^127 : ℝ)*b := mul_le_mul_of_nonneg_right hs hb0
    _ = (b : ℝ)/2^127 := by ring

end OptimalOTS.LeanIsaBaseline.Layer.Tier.Nonce128
