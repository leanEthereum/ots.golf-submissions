import OptimalOTS.LeanIsa

/-!
The algebraic core of the field-rescaled checksum, using the pinned leanISA generator.
-/

namespace LeanIsaFieldRescale

open LeanerVM.Parameters

def stride : ℕ := 1152921504606846976
def sentinel : ℕ := 262143

def costFactor (c : ℕ) : K := gpow (stride * c)

theorem factor_add (a b : ℕ) :
    costFactor a * costFactor b = costFactor (a + b) := by
  simp only [costFactor, gpow, Nat.mul_add, pow_add]

/-- In GF(2^64), the inverse fourth Frobenius sends g to g^(2^60). -/
theorem factor_sixteen : costFactor 16 = g := by
  have he : stride * 16 % (2 ^ 64 - 1) = 1 := by norm_num [stride]
  calc
    costFactor 16 = gpow ((stride * 16) % (2 ^ 64 - 1)) := by
      rw [costFactor, ← orderOf_g]
      exact (pow_mod_orderOf g (stride * 16)).symm
    _ = g := by rw [he]; exact pow_one g

theorem factor_pow_sixteen (n : ℕ) : (costFactor n) ^ 16 = gpow n := by
  have hm : stride * n * 16 = stride * 16 * n := by ring
  simp only [costFactor, gpow, ← pow_mul]
  rw [hm, pow_mul, show g ^ (stride * 16) = g from factor_sixteen]

theorem factor_injective {a b : ℕ} (ha : a ≤ 300) (hb : b ≤ 300)
    (h : costFactor a = costFactor b) : a = b := by
  have hh := congrArg (fun x : K => x ^ 16) h
  rw [factor_pow_sixteen, factor_pow_sixteen] at hh
  exact gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) hh

/-- The free block seeds this value; the final product is pinned to the halt address. -/
def initialProduct (layer s : ℕ) : K :=
    gpow sentinel / costFactor layer * costFactor s

theorem checksum_exact {layer s c : ℕ} (hLayer : layer ≤ 300) (hSum : s + c ≤ 300) :
    initialProduct layer s * costFactor c = gpow sentinel ↔ s + c = layer := by
  have hn : gpow sentinel ≠ 0 := pow_ne_zero _ g_ne_zero
  have hl : costFactor layer ≠ 0 := pow_ne_zero _ g_ne_zero
  rw [initialProduct, mul_assoc, factor_add]
  constructor
  · intro h
    have he : costFactor (s + c) = costFactor layer := by
      field_simp at h
      exact h
    exact factor_injective hSum hLayer he
  · intro h
    rw [h]
    exact div_mul_cancel₀ _ hl

end LeanIsaFieldRescale
