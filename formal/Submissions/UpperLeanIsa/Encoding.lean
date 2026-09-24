import OptimalOTS.Model
import Submissions.UpperLeanIsa.Checksum

/-! Mixed 7/6-bit Winternitz encoding: 41 message fields and two checksum digits.
Field `k` is the bit range `[fieldOff k, fieldOff k + fieldWidth k)` of the message. A 6-bit
field (and each checksum digit) is stored with offset 64, so every digit is `< 128` and every
chain keeps 127 steps. The checksum prevents changing a message by advancing every disclosed
chain. -/

namespace OptimalOTS.LeanIsaBaseline

open Checksum

/-- Widths `[7]*8 ++ [6]*12 ++ [7]*2 ++ [6]*19` for the 41 message fields; the two checksum
digits count as 6-bit fields. -/
def fieldWidth (k : ℕ) : ℕ :=
  if k < 8 then 7 else if k < 20 then 6 else if k < 22 then 7 else 6

/-- Bit offset of field `k`: the total width of the fields after it (big-endian). -/
def fieldOff (k : ℕ) : ℕ :=
  if k < 8 then 200 + 7 * (7 - k) else if k < 20 then 128 + 6 * (19 - k)
  else if k < 22 then 114 + 7 * (21 - k) else 6 * (40 - k)

/-- The digit offset: `0` for 7-bit fields, `64` for 6-bit fields and the checksum digits. -/
def digitOff (k : ℕ) : ℕ := if fieldWidth k = 7 then 0 else 64

def messageDigits (m : Message) : List ℕ :=
  (List.range 41).map fun k => digitOff k + m.toNat / 2 ^ fieldOff k % 2 ^ fieldWidth k

/-- The checksum digits are `64 + C / 64` and `64 + C % 64` for `C = Σ (127 − eₖ)`. -/
def digits (m : Message) : List ℕ :=
  messageDigits m ++
    [64 + wotsChecksumValue 128 (messageDigits m) / 64,
     64 + wotsChecksumValue 128 (messageDigits m) % 64]

theorem fieldOff_succ {k : ℕ} (hk : k < 40) :
    fieldOff k = fieldOff (k + 1) + fieldWidth (k + 1) := by
  unfold fieldOff fieldWidth
  split_ifs <;> omega

theorem fieldOff_last : fieldOff 40 = 0 := rfl

theorem fieldOff_zero_add : fieldOff 0 + fieldWidth 0 = 256 := rfl

theorem digitOff_add_pow_le (k : ℕ) : digitOff k + 2 ^ fieldWidth k ≤ 128 := by
  unfold digitOff fieldWidth
  split_ifs <;> simp_all

theorem messageDigits_length (m : Message) : (messageDigits m).length = 41 := by
  simp [messageDigits]

theorem messageDigits_lt (m : Message) : ∀ d ∈ messageDigits m, d < 128 := by
  intro d hd
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hd
  have := Nat.mod_lt (m.toNat / 2 ^ fieldOff k) (Nat.two_pow_pos (fieldWidth k))
  have := digitOff_add_pow_le k
  omega

theorem getElem_messageDigits (m : Message) (k : ℕ) (hk : k < (messageDigits m).length) :
    (messageDigits m)[k] = digitOff k + m.toNat / 2 ^ fieldOff k % 2 ^ fieldWidth k := by
  simp [messageDigits]

/-- The low `fieldOff k + fieldWidth k` bits are the fields `k, …, 40`, each at its offset. -/
theorem mod_eq_sum_fields (n : ℕ) : ∀ t, t ≤ 40 →
    n % 2 ^ (fieldOff (40 - t) + fieldWidth (40 - t)) =
      ∑ i ∈ Finset.range (t + 1),
        2 ^ fieldOff (40 - i) * (n / 2 ^ fieldOff (40 - i) % 2 ^ fieldWidth (40 - i)) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [fieldOff_last]
  | succ t ih =>
    intro ht
    have hoff : fieldOff (40 - (t + 1)) = fieldOff (40 - t) + fieldWidth (40 - t) := by
      have h := fieldOff_succ (k := 40 - (t + 1)) (by omega)
      rwa [show 40 - (t + 1) + 1 = 40 - t by omega] at h
    rw [Finset.sum_range_succ, ← ih (by omega), ← hoff, pow_add, Nat.mod_mul]

theorem toNat_eq_sum_fields (m : Message) :
    m.toNat = ∑ k ∈ Finset.range 41,
      2 ^ fieldOff k * (m.toNat / 2 ^ fieldOff k % 2 ^ fieldWidth k) := by
  have h := mod_eq_sum_fields m.toNat 40 le_rfl
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [Nat.sub_self, fieldOff_zero_add, Nat.mod_eq_of_lt hm] at h
  refine h.trans ((Finset.sum_congr rfl fun i _ => ?_).trans (Finset.sum_range_reflect
    (fun k => 2 ^ fieldOff k * (m.toNat / 2 ^ fieldOff k % 2 ^ fieldWidth k)) 41))
  simp only [show 41 - 1 - i = 40 - i by omega]

theorem messageDigits_injective : Function.Injective messageDigits := by
  intro a b h
  apply BitVec.eq_of_toNat_eq
  rw [toNat_eq_sum_fields a, toNat_eq_sum_fields b]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 41 := Finset.mem_range.mp hk
  have hl : k < (messageDigits a).length := by rw [messageDigits_length]; exact hk'
  have he := getElem_messageDigits a k hl
  rw [List.getElem_of_eq h, getElem_messageDigits] at he
  rw [Nat.add_left_cancel he.symm]

theorem wotsChecksumValue_messageDigits_le (m : Message) :
    wotsChecksumValue 128 (messageDigits m) ≤ 3223 := by
  have h : wotsChecksumValue 128 (messageDigits m) ≤
      ∑ k ∈ Finset.range 41, (127 - digitOff k) := by
    rw [wotsChecksumValue, messageDigits, List.map_map, ← List.sum_toFinset _ List.nodup_range]
    · rw [List.toFinset_range]
      exact Finset.sum_le_sum fun k _ => by simp only [Function.comp_apply]; omega
  exact h.trans (by decide)

theorem digits_length (m : Message) : (digits m).length = 43 := by
  simp [digits, messageDigits_length]

theorem digits_lt (m : Message) : ∀ d ∈ digits m, d < 128 := by
  intro d hd
  have hC := wotsChecksumValue_messageDigits_le m
  rcases List.mem_append.mp hd with hd | hd
  · exact messageDigits_lt m d hd
  · generalize wotsChecksumValue 128 (messageDigits m) = C at hC hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> omega

/-- Pointwise-`≤` digit vectors come from the same message. -/
theorem digits_le_imp_eq {a b : Message}
    (h : List.Forall₂ (· ≤ ·) (digits a) (digits b)) : a = b := by
  obtain ⟨hMsg, hCs⟩ := Forall₂.append_inv h
    ((messageDigits_length a).trans (messageDigits_length b).symm)
  simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at hCs
  have hGE := wotsChecksumValue_antitone hMsg (messageDigits_lt a) (messageDigits_lt b)
  have hEq : wotsChecksumValue 128 (messageDigits a) = wotsChecksumValue 128 (messageDigits b) := by
    have := Nat.div_add_mod (wotsChecksumValue 128 (messageDigits a)) 64
    have := Nat.div_add_mod (wotsChecksumValue 128 (messageDigits b)) 64
    omega
  exact messageDigits_injective (Forall₂.eq_of_sum_eq hMsg
    (wotsChecksum_eq_imp_sum_eq hMsg (messageDigits_lt a) (messageDigits_lt b) hEq))

theorem digits_incomparable {a b : Message} (h : a ≠ b) :
    ¬ List.Forall₂ (· ≤ ·) (digits a) (digits b) ∧
    ¬ List.Forall₂ (· ≤ ·) (digits b) (digits a) :=
  ⟨fun hab => h (digits_le_imp_eq hab), fun hba => h (digits_le_imp_eq hba).symm⟩

def digit (m : Message) (i : Fin 43) : ℕ :=
  (digits m)[i.val]'(by rw [digits_length]; exact i.isLt)

theorem digit_le (m : Message) (i : Fin 43) : digit m i ≤ 127 := by
  have h := digits_lt m (digit m i) (List.getElem_mem _)
  omega

theorem digit_of_lt (m : Message) (k : Fin 43) (hk : k.val < 41) :
    digit m k = digitOff k + m.toNat / 2 ^ fieldOff k % 2 ^ fieldWidth k := by
  simp only [digit, digits, List.getElem_append, messageDigits_length, hk, dite_true,
    getElem_messageDigits]

theorem digit_hi (m : Message) :
    digit m 41 = 64 + wotsChecksumValue 128 (messageDigits m) / 64 := by
  simp [digit, digits, messageDigits_length]

theorem digit_lo (m : Message) :
    digit m 42 = 64 + wotsChecksumValue 128 (messageDigits m) % 64 := by
  simp [digit, digits, messageDigits_length]

theorem messageDigits_eq_ofFn (m : Message) :
    messageDigits m = List.ofFn (fun k : Fin 41 => digit m (Fin.castLE (by norm_num) k)) := by
  apply List.ext_getElem (by simp [messageDigits_length])
  intro k h1 _
  rw [List.getElem_ofFn, digit_of_lt m _ (by simpa [messageDigits_length] using h1),
    getElem_messageDigits]
  rfl

/-- The checksum value as a sum over the message chains. -/
theorem wotsChecksumValue_messageDigits (m : Message) :
    wotsChecksumValue 128 (messageDigits m) =
      ∑ k : Fin 41, (127 - digit m (Fin.castLE (by norm_num) k)) := by
  rw [wotsChecksumValue, messageDigits_eq_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

end OptimalOTS.LeanIsaBaseline
