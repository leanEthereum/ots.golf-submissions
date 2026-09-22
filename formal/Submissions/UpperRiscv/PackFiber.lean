import Submissions.UpperRiscv.Valid

/-!
# The fibers of `pack`

`pack` reads `wid k` bits of an answer from bit `fieldPos k`. The answer is a sequence of 33
cells (`cw`) in bit order, each some unread low bits (`jw k`) below digit `k`; the unread bits
form another 128-bit number, and `y ↦ (pack y, junk y)` is a bijection: every packed index has
exactly `2 ^ 128` answers (`card_pack_mem`, in `PackCount.lean`).
-/

namespace OptimalOTS

theorem posW_cw_33 : posW cw 33 = 256 := by decide

theorem posW_jw_33 : posW jw 33 = 128 := by decide

theorem jw_of_ge {k : ℕ} (hk : 33 ≤ k) : jw k = 0 := by
  simp [jw, show k ≠ 0 by omega, show ¬ k < 32 by omega, show k ≠ 32 by omega]

theorem wid_of_ge {k : ℕ} (hk : 32 ≤ k) : wid k = 0 := by
  simp [wid, show ¬ k < 4 by omega, show ¬ k < 32 by omega]

theorem cw_of_ge {k : ℕ} (hk : 33 ≤ k) : cw k = 0 := by
  unfold cw
  rw [jw_of_ge hk, wid_of_ge (by omega)]

/-- Cell `k` of an answer. -/
def cellOf (y : BitVec hashBits) (k : ℕ) : ℕ := digitW cw y.toNat k

theorem cellOf_lt (y : BitVec hashBits) (k : ℕ) : cellOf y k < 2 ^ cw k := digitW_lt cw _ k

/-- The digit of a cell: its bits above the unread ones. -/
theorem fieldDigit_eq (y : BitVec hashBits) (k : ℕ) :
    cellOf y k / 2 ^ jw k = fieldDigit y k := by
  unfold cellOf digitW fieldDigit fieldPos cw
  rw [pow_add 2 (jw k) (wid k), Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add]

/-- The unread bits of each cell. -/
def junkDigit (y : BitVec hashBits) (k : ℕ) : ℕ := cellOf y k % 2 ^ jw k

theorem junkDigit_lt (y : BitVec hashBits) (k : ℕ) : junkDigit y k < 2 ^ jw k :=
  Nat.mod_lt _ (by positivity)

theorem cellOf_eq (y : BitVec hashBits) (k : ℕ) :
    cellOf y k = junkDigit y k + 2 ^ jw k * fieldDigit y k := by
  rw [← fieldDigit_eq]
  exact (Nat.mod_add_div _ _).symm

/-- The unread bits, packed. -/
def junk (y : BitVec hashBits) : ℕ := ofDigitsW jw (junkDigit y) 33

theorem junk_lt (y : BitVec hashBits) : junk y < 2 ^ 128 := by
  rw [← posW_jw_33]
  exact ofDigitsW_lt jw _ (junkDigit_lt y) 33

/-- The answer with packed index `i` and unread bits `j`. -/
def unpack (i j : ℕ) : BitVec hashBits :=
  BitVec.ofNat hashBits (ofDigitsW cw (fun k => digitW jw j k + 2 ^ jw k * digit i k) 33)

theorem unpack_digit_lt (i j k : ℕ) : digitW jw j k + 2 ^ jw k * digit i k < 2 ^ cw k := by
  have h1 := digitW_lt jw j k
  have h2 := digit_lt i k
  unfold cw
  calc digitW jw j k + 2 ^ jw k * digit i k
      < 2 ^ jw k + 2 ^ jw k * digit i k := by omega
    _ = 2 ^ jw k * (digit i k + 1) := by ring
    _ ≤ 2 ^ jw k * 2 ^ wid k := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (jw k + wid k) := (pow_add 2 _ _).symm

theorem hashBits_eq : hashBits = 256 := rfl

theorem toNat_unpack (i j : ℕ) :
    (unpack i j).toNat = ofDigitsW cw (fun k => digitW jw j k + 2 ^ jw k * digit i k) 33 := by
  unfold unpack
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [hashBits_eq, ← posW_cw_33]
  exact ofDigitsW_lt cw _ (unpack_digit_lt i j) 33

theorem cellOf_unpack (i j : ℕ) {k : ℕ} (hk : k < 33) :
    cellOf (unpack i j) k = digitW jw j k + 2 ^ jw k * digit i k := by
  unfold cellOf
  rw [toNat_unpack]
  exact digitW_ofDigitsW cw _ (unpack_digit_lt i j) 33 k hk

theorem fieldDigit_unpack {i : ℕ} (j : ℕ) (hi : i < 2 ^ 128) (k : ℕ) :
    fieldDigit (unpack i j) k = digit i k := by
  by_cases hk : k < 33
  · rw [← fieldDigit_eq, cellOf_unpack i j hk, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (digitW_lt jw j k), zero_add]
  · have h1 : digit i k = 0 :=
      digitW_eq_zero_of_lt wid (n := 32) (by show i < 2 ^ pos 32; rw [pos_32]; exact hi)
        (by omega)
    rw [h1]
    unfold fieldDigit
    rw [wid_of_ge (by omega), pow_zero, Nat.mod_one]

theorem pack_unpack {i : ℕ} (j : ℕ) (hi : i < 2 ^ 128) : pack (unpack i j) = i := by
  unfold pack
  rw [show fieldDigit (unpack i j) = digit i from funext (fieldDigit_unpack j hi)]
  exact ofDigits_digit i 32 (by rw [pos_32]; exact hi)

theorem junk_unpack (i : ℕ) {j : ℕ} (hj : j < 2 ^ 128) : junk (unpack i j) = j := by
  unfold junk
  have e : ∀ k, junkDigit (unpack i j) k = digitW jw j k := by
    intro k
    by_cases hk : k < 33
    · unfold junkDigit
      rw [cellOf_unpack i j hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (digitW_lt jw j k)]
    · have h2 : digitW jw j k = 0 :=
        digitW_eq_zero_of_lt jw (n := 33) (by rw [posW_jw_33]; exact hj) (by omega)
      rw [h2]
      unfold junkDigit
      rw [jw_of_ge (by omega), pow_zero, Nat.mod_one]
  rw [show junkDigit (unpack i j) = digitW jw j from funext e]
  exact ofDigitsW_digitW jw j 33 (by rw [posW_jw_33]; exact hj)

theorem unpack_pack_junk (y : BitVec hashBits) : unpack (pack y) (junk y) = y := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_unpack]
  have e : ∀ k, digitW jw (junk y) k + 2 ^ jw k * digit (pack y) k = cellOf y k := by
    intro k
    by_cases hk : k < 33
    · rw [show digitW jw (junk y) k = junkDigit y k from
          digitW_ofDigitsW jw _ (junkDigit_lt y) 33 k hk]
      by_cases hk' : k < 32
      · rw [digit_pack y hk', cellOf_eq]
      · have h1 : digit (pack y) k = 0 :=
          digitW_eq_zero_of_lt wid (n := 32) (pack_lt_pos y) (by omega)
        have h2 : fieldDigit y k = 0 := by
          unfold fieldDigit
          rw [wid_of_ge (by omega), pow_zero, Nat.mod_one]
        rw [h1, cellOf_eq, h2]
    · have h1 : digit (pack y) k = 0 :=
        digitW_eq_zero_of_lt wid (n := 32) (pack_lt_pos y) (by omega)
      have h2 : digitW jw (junk y) k = 0 :=
        digitW_eq_zero_of_lt jw (n := 33) (by rw [posW_jw_33]; exact junk_lt y) (by omega)
      have h3 : cellOf y k = 0 := by
        have := cellOf_lt y k
        rw [cw_of_ge (by omega), pow_zero] at this
        omega
      simp [h1, h2, h3]
  simp only [e]
  exact ofDigitsW_digitW cw y.toNat 33 (by rw [posW_cw_33, ← hashBits_eq]; exact y.isLt)

end OptimalOTS
