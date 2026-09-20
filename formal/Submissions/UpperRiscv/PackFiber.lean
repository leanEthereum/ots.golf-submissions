import Submissions.UpperRiscv.Valid

/-!
# The fibers of `pack`

`pack` reads the low `wid k` bits of byte `k` of an answer. The unread bits (`junk`) form
another 128-bit number, and `y ↦ (pack y, junk y)` is a bijection: every packed index has exactly
`2 ^ 128` answers (`card_pack_mem`).
-/

namespace OptimalOTS


/-- The unread bits of each byte. -/
def jw (k : ℕ) : ℕ := if k < 32 then 8 - wid k else 0

/-- Byte widths. -/
def bw (k : ℕ) : ℕ := if k < 32 then 8 else 0

theorem posW_bw_32 : posW bw 32 = 256 := by decide

theorem posW_jw_32 : posW jw 32 = 128 := by decide

theorem posW_bw_of_le {k : ℕ} (hk : 32 ≤ k) : posW bw k = 256 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h | h
    · rw [posW_succ, ih (by omega)]; simp [bw, show ¬ k < 32 by omega]
    · rw [← h]; exact posW_bw_32

theorem wid_add_jw {k : ℕ} (hk : k < 32) : wid k + jw k = 8 := by
  simp only [wid, jw, hk, if_true]
  split_ifs <;> omega

theorem wid_of_ge {k : ℕ} (hk : 32 ≤ k) : wid k = 0 := by
  simp [wid, show ¬ k < 16 by omega, show ¬ k < 28 by omega]

theorem wid_le_eight (k : ℕ) : wid k ≤ 8 := by unfold wid; split_ifs <;> omega

/-- Byte `k` of an answer. -/
def byteOf (y : BitVec hashBits) (k : ℕ) : ℕ := digitW bw y.toNat k

theorem posW_bw (k : ℕ) (hk : k ≤ 32) : posW bw k = 8 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [posW_succ, ih (by omega)]; simp [bw, show k < 32 by omega]; ring

theorem byteDigit_eq (y : BitVec hashBits) {k : ℕ} (hk : k < 32) :
    byteDigit y k = byteOf y k % 2 ^ wid k := by
  unfold byteDigit byteOf digitW
  rw [posW_bw k hk.le, show bw k = 8 by simp [bw, hk]]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (wid_le_eight k))]

/-- The unread bits, packed. -/
def junk (y : BitVec hashBits) : ℕ := ofDigitsW jw (fun k => byteOf y k / 2 ^ wid k) 32

theorem junk_digit_lt (y : BitVec hashBits) (k : ℕ) : byteOf y k / 2 ^ wid k < 2 ^ jw k := by
  by_cases hk : k < 32
  · have hb : byteOf y k < 2 ^ 8 := by
      have := digitW_lt bw y.toNat k
      simpa [byteOf, bw, hk] using this
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, add_comm, wid_add_jw hk]
    exact hb
  · have hb : byteOf y k < 1 := by
      have := digitW_lt bw y.toNat k
      simpa [byteOf, bw, hk] using this
    simp only [jw, hk, if_false, pow_zero]
    have : byteOf y k = 0 := by omega
    rw [this, Nat.zero_div]
    exact Nat.one_pos

theorem junk_lt (y : BitVec hashBits) : junk y < 2 ^ 128 := by
  rw [← posW_jw_32]
  exact ofDigitsW_lt jw _ (junk_digit_lt y) 32

/-- The answer with packed index `i` and unread bits `j`. -/
def unpack (i j : ℕ) : BitVec hashBits :=
  BitVec.ofNat hashBits (ofDigitsW bw (fun k => digit i k + 2 ^ wid k * digitW jw j k) 32)

theorem unpack_digit_lt {i j : ℕ} (hi : i < 2 ^ 128) (hj : j < 2 ^ 128) (k : ℕ) :
    digit i k + 2 ^ wid k * digitW jw j k < 2 ^ bw k := by
  by_cases hk : k < 32
  · have h1 := digit_lt i k
    have h2 := digitW_lt jw j k
    simp only [bw, hk, if_true]
    calc digit i k + 2 ^ wid k * digitW jw j k
        < 2 ^ wid k + 2 ^ wid k * digitW jw j k := by omega
      _ = 2 ^ wid k * (digitW jw j k + 1) := by ring
      _ ≤ 2 ^ wid k * 2 ^ jw k := Nat.mul_le_mul_left _ h2
      _ = 2 ^ 8 := by rw [← pow_add, wid_add_jw hk]
  · have h1 : digit i k = 0 :=
      digitW_eq_zero_of_lt wid (n := 28) (by show i < 2 ^ pos 28; rw [pos_28]; exact hi) (by omega)
    have h2 : digitW jw j k = 0 :=
      digitW_eq_zero_of_lt jw (n := 32) (by rw [posW_jw_32]; exact hj) (by omega)
    simp [bw, hk, h1, h2]

theorem hashBits_eq : hashBits = 256 := rfl

theorem toNat_unpack {i j : ℕ} (hi : i < 2 ^ 128) (hj : j < 2 ^ 128) :
    (unpack i j).toNat = ofDigitsW bw (fun k => digit i k + 2 ^ wid k * digitW jw j k) 32 := by
  unfold unpack
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [hashBits_eq, ← posW_bw_32]
  exact ofDigitsW_lt bw _ (unpack_digit_lt hi hj) 32

theorem byteOf_unpack {i j : ℕ} (hi : i < 2 ^ 128) (hj : j < 2 ^ 128) {k : ℕ} (hk : k < 32) :
    byteOf (unpack i j) k = digit i k + 2 ^ wid k * digitW jw j k := by
  unfold byteOf
  rw [toNat_unpack hi hj]
  exact digitW_ofDigitsW bw _ (unpack_digit_lt hi hj) 32 k hk

theorem pack_unpack {i j : ℕ} (hi : i < 2 ^ 128) (hj : j < 2 ^ 128) : pack (unpack i j) = i := by
  unfold pack
  have e : ∀ k, byteDigit (unpack i j) k = digit i k := by
    intro k
    by_cases hk : k < 32
    · rw [byteDigit_eq _ hk, byteOf_unpack hi hj hk, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (digit_lt i k)]
    · have h1 : digit i k = 0 :=
        digitW_eq_zero_of_lt wid (n := 28) (by show i < 2 ^ pos 28; rw [pos_28]; exact hi) (by omega)
      rw [h1]
      unfold byteDigit
      rw [wid_of_ge (by omega)]
      simp [Nat.mod_one]
  rw [show byteDigit (unpack i j) = digit i from funext e]
  exact ofDigits_digit i 28 (by rw [pos_28]; exact hi)

theorem junk_unpack {i j : ℕ} (hi : i < 2 ^ 128) (hj : j < 2 ^ 128) : junk (unpack i j) = j := by
  unfold junk
  have e : ∀ k, byteOf (unpack i j) k / 2 ^ wid k = digitW jw j k := by
    intro k
    by_cases hk : k < 32
    · rw [byteOf_unpack hi hj hk, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (digit_lt i k), zero_add]
    · have h2 : digitW jw j k = 0 :=
        digitW_eq_zero_of_lt jw (n := 32) (by rw [posW_jw_32]; exact hj) (by omega)
      rw [h2]
      have hb : byteOf (unpack i j) k < 1 := by
        have := digitW_lt bw (unpack i j).toNat k
        simpa [byteOf, bw, hk] using this
      have : byteOf (unpack i j) k = 0 := by omega
      rw [this, Nat.zero_div]
  simp only [e]
  exact ofDigitsW_digitW jw j 32 (by rw [posW_jw_32]; exact hj)

theorem unpack_pack_junk (y : BitVec hashBits) : unpack (pack y) (junk y) = y := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_unpack (pack_lt' y) (junk_lt y)]
  have e : ∀ k, digit (pack y) k + 2 ^ wid k * digitW jw (junk y) k = byteOf y k := by
    intro k
    by_cases hk : k < 32
    · rw [show digitW jw (junk y) k = byteOf y k / 2 ^ wid k from
          digitW_ofDigitsW jw _ (junk_digit_lt y) 32 k hk]
      by_cases hk' : k < 28
      · rw [digit_pack y hk', byteDigit_eq y hk]
        exact Nat.mod_add_div _ _
      · have h1 : digit (pack y) k = 0 :=
          digitW_eq_zero_of_lt wid (n := 28) (pack_lt_pos y) (by omega)
        rw [h1, show wid k = 0 by simp [wid, show ¬ k < 16 by omega, hk']]
        simp
    · have h1 : digit (pack y) k = 0 := digitW_eq_zero_of_lt wid (n := 28) (pack_lt_pos y) (by omega)
      have h2 : digitW jw (junk y) k = 0 :=
        digitW_eq_zero_of_lt jw (n := 32) (by rw [posW_jw_32]; exact junk_lt y) (by omega)
      have hb : byteOf y k < 1 := by
        have := digitW_lt bw y.toNat k
        simpa [byteOf, bw, hk] using this
      rw [h1, h2]
      omega
  simp only [e]
  exact ofDigitsW_digitW bw y.toNat 32 (by rw [posW_bw_32, ← hashBits_eq]; exact y.isLt)


end OptimalOTS
