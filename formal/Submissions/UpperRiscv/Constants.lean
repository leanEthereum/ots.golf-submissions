import Mathlib

/-!
# Constants shared by the scheme and the machine image

The hash inputs of the scheme carry the addresses and level tags that the machine writes, so the
two sides share these numbers.

* Chain `k`'s 128-bit value lives at `slotAddr k = slotBase + 24 k`, preceded by an 8-byte header.
* The header of the hash step at level `t` of chain `k` is `slotAddr k + levVal k t * 2 ^ 32`: the
  slot address in its low 32 bits and a 32-bit level tag in its high 32 bits. The machine writes
  the tag with one word store from a register whose low 32 bits are already known: the HASH call
  number, the input length, the payload cursor, the checked signature length, the stack top, the
  four lane constants, the sum comparator, one loaded constant, and (per chain) the two HASH
  pointers and the code address of the chain's step table. `jumpBase0` and `jumpBase1` are also
  the jump bases of the chain dispatch.
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

/-- The code address of the first step of chain `k`'s table: the return address of the
prologue's `JALR`, which the machine keeps in `x14` during the chain. -/
def tableStart (k : ℕ) : ℕ := 4412 + 156 * k

/-- The low 32 bits of a 16-bit value broadcast to the four lanes of a word. -/
def lanes32 (v : ℕ) : ℕ := v + v * 2 ^ 16

/-- The level tag of level `t` of chain `k`: the low 32 bits of the register the chain step
stores. Levels `11`, `12` and `13` use the chain's slot pointer, its HASH input pointer and its
table address; the last level has tag `0`. -/
def levVal (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 192
  | 2 => 0x400040
  | 3 => lanes32 120
  | 4 => 4224
  | 5 => lanes32 jumpBase0
  | 6 => lanes32 jumpBase1
  | 7 => lanes32 1
  | 8 => 0x1000000
  | 9 => 1256
  | 10 => 2
  | 11 => slotAddr k
  | 12 => slotAddr k - 8
  | 13 => tableStart k
  | _ => 0

theorem levVal_ge (k n : ℕ) : levVal k (n + 14) = 0 := rfl

theorem levVal_14 (k : ℕ) : levVal k 14 = 0 := rfl

/-- Levels other than `11`, `12` and `13` have the same tag in every chain. -/
theorem levVal_const (k t : ℕ) (h11 : t ≠ 11) (h12 : t ≠ 12) (h13 : t ≠ 13) :
    levVal k t = levVal 0 t := by
  rcases Nat.lt_or_ge t 14 with h | h
  · interval_cases t <;> first | rfl | exact absurd rfl ‹_›
  · obtain ⟨n, rfl⟩ : ∃ n, t = n + 14 := ⟨t - 14, by omega⟩
    rw [levVal_ge, levVal_ge]

theorem slotAddr_lt (k : ℕ) (hk : k < 32) : slotAddr k < 2 ^ 32 := by
  unfold slotAddr slotBase; omega

theorem tableStart_lt (k : ℕ) (hk : k < 32) : tableStart k < 2 ^ 32 := by
  unfold tableStart; omega

theorem levVal_lt (k t : ℕ) (hk : k < 32) : levVal k t < 2 ^ 32 := by
  have hs := slotAddr_lt k hk
  have ht := tableStart_lt k hk
  rcases Nat.lt_or_ge t 14 with h | h
  · interval_cases t <;> simp only [levVal] <;>
      first | omega | norm_num [lanes32, jumpBase0, jumpBase1]
  · obtain ⟨n, rfl⟩ : ∃ n, t = n + 14 := ⟨t - 14, by omega⟩
    rw [levVal_ge]
    norm_num

/-- Within a chain, the fifteen level tags are distinct. -/
theorem levVal_injective (k : ℕ) (hk : k < 32) {t t' : ℕ} (ht : t < 15) (ht' : t' < 15)
    (h : levVal k t = levVal k t') : t = t' := by
  have hs : 0x200088 ≤ slotAddr k ∧ slotAddr k ≤ 0x200088 + 24 * 31 := by
    unfold slotAddr slotBase; omega
  have hb : 4412 ≤ tableStart k ∧ tableStart k ≤ 4412 + 156 * 31 := by
    unfold tableStart; omega
  interval_cases t <;> interval_cases t' <;> first
    | rfl
    | (exfalso; simp only [levVal] at h
       try norm_num [lanes32, jumpBase0, jumpBase1] at h
       try omega)

/-- The header of the hash step at level `t` of chain `k`. -/
def hdrNat (k t : ℕ) : ℕ := slotAddr k + levVal k t * 2 ^ 32

theorem hdrNat_lt (k t : ℕ) (hk : k < 32) : hdrNat k t < 2 ^ 64 := by
  have h1 := slotAddr_lt k hk
  have h2 := levVal_lt k t hk
  unfold hdrNat
  have : levVal k t * 2 ^ 32 ≤ (2 ^ 32 - 1) * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
  norm_num at this ⊢
  omega

theorem hdrNat_injective {k t k' t' : ℕ} (hk : k < 32) (hk' : k' < 32) (ht : t < 15)
    (ht' : t' < 15) (h : hdrNat k t = hdrNat k' t') : k = k' ∧ t = t' := by
  have a1 := slotAddr_lt k hk
  have a2 := slotAddr_lt k' hk'
  unfold hdrNat at h
  have hl : levVal k t = levVal k' t' := by
    have e1 : (slotAddr k + levVal k t * 2 ^ 32) / 2 ^ 32 = levVal k t := by
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt a1, Nat.zero_add]
    have e2 : (slotAddr k' + levVal k' t' * 2 ^ 32) / 2 ^ 32 = levVal k' t' := by
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt a2, Nat.zero_add]
    rw [← e1, ← e2, h]
  have hkk : k = k' := by
    rw [hl] at h
    unfold slotAddr at h
    omega
  subst hkk
  exact ⟨rfl, levVal_injective k hk ht ht' hl⟩

end OptimalOTS.Flat
