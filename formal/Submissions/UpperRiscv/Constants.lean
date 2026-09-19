import Mathlib

/-!
# Constants shared by the scheme and the machine image

The hash inputs of the scheme carry the addresses and level tags that the machine writes, so the
two sides share these numbers.

* Chain `k`'s 128-bit value lives at `slotAddr k = slotBase + 24 k`, preceded by an 8-byte header.
* The header of the hash step at level `t` of chain `k` is `slotAddr k + levVal t * 2 ^ 48`: the
  slot address in its low 48 bits and a level tag in its high 16 bits. The machine keeps the level
  tags in registers; `jumpBase0` and `jumpBase1` are also the jump bases of the chain dispatch.
-/

namespace OptimalOTS.Flat

/-- Address of chain `0`'s value slot. -/
def slotBase : ℕ := 0x200088

/-- Address of chain `k`'s value slot. -/
def slotAddr (k : ℕ) : ℕ := slotBase + 24 * k

/-- Jump base of the dispatch of chains `0` to `15`. -/
def jumpBase0 : ℕ := 5730

/-- Jump base of the dispatch of chains `16` to `31`. -/
def jumpBase1 : ℕ := 8226

/-- The level tags, as held (in their low 16 bits) by the registers of the chain steps. -/
def levList : List ℕ := [1, 192, 64, 120, 4224, jumpBase0, jumpBase1, 2, 3, 4, 5, 6, 7, 8, 0]

/-- The level tag of level `t`; the last level has tag `0`. -/
def levVal (t : ℕ) : ℕ := levList.getD t 0

theorem levVal_lt (t : ℕ) : levVal t < 2 ^ 16 := by
  unfold levVal
  rcases Nat.lt_or_ge t 15 with h | h
  · interval_cases t <;> decide
  · rw [List.getD_eq_default _ _ (by simp [levList]; omega)]
    norm_num

theorem levVal_injective {t t' : ℕ} (ht : t < 15) (ht' : t' < 15) (h : levVal t = levVal t') :
    t = t' := by
  interval_cases t <;> interval_cases t' <;> first | rfl | (revert h; decide)

theorem levVal_14 : levVal 14 = 0 := rfl

/-- The header of the hash step at level `t` of chain `k`. -/
def hdrNat (k t : ℕ) : ℕ := slotAddr k + levVal t * 2 ^ 48

theorem slotAddr_lt (k : ℕ) (hk : k < 32) : slotAddr k < 2 ^ 48 := by
  unfold slotAddr slotBase; omega

theorem hdrNat_lt (k t : ℕ) (hk : k < 32) : hdrNat k t < 2 ^ 64 := by
  have h1 := slotAddr_lt k hk
  have h2 := levVal_lt t
  unfold hdrNat
  have : levVal t * 2 ^ 48 ≤ (2 ^ 16 - 1) * 2 ^ 48 := Nat.mul_le_mul_right _ (by omega)
  norm_num at this ⊢
  omega

theorem hdrNat_injective {k t k' t' : ℕ} (hk : k < 32) (hk' : k' < 32) (ht : t < 15)
    (ht' : t' < 15) (h : hdrNat k t = hdrNat k' t') : k = k' ∧ t = t' := by
  have a1 := slotAddr_lt k hk
  have a2 := slotAddr_lt k' hk'
  unfold hdrNat at h
  have hl : levVal t = levVal t' := by
    have e1 : (slotAddr k + levVal t * 2 ^ 48) / 2 ^ 48 = levVal t := by
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt a1, Nat.zero_add]
    have e2 : (slotAddr k' + levVal t' * 2 ^ 48) / 2 ^ 48 = levVal t' := by
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt a2, Nat.zero_add]
    rw [← e1, ← e2, h]
  refine ⟨?_, levVal_injective ht ht' hl⟩
  rw [hl] at h
  unfold slotAddr at h
  omega

end OptimalOTS.Flat
