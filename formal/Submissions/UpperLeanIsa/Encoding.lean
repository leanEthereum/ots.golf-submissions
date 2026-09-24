import OptimalOTS.Model
import Submissions.UpperLeanIsa.Checksum

/-! Base-128 Winternitz encoding: 37 message digits and two checksum digits.
The checksum prevents changing a message by advancing every disclosed chain. -/

namespace OptimalOTS.LeanIsaBaseline

open Checksum

def messageDigits (m : Message) : List ℕ := digitsOfBaseW m.toNat 128 37

def digits (m : Message) : List ℕ := wotsFullDigits (messageDigits m) 128 37 2

theorem messageDigits_length (m : Message) : (messageDigits m).length = 37 :=
  digitsOfBaseW_length _ _ _

theorem messageDigits_lt (m : Message) : ∀ d ∈ messageDigits m, d < 128 :=
  digitsOfBaseW_lt _ _ _ (by decide)

theorem digits_length (m : Message) : (digits m).length = 39 :=
  wotsFullDigits_length _ _ _ _ (messageDigits_length m)

theorem messageDigits_injective : Function.Injective messageDigits := by
  intro a b h
  have bound (m : Message) : m.toNat < 128 ^ 37 := by
    have hm := m.isLt
    change m.toNat < 2 ^ 256 at hm
    exact lt_of_lt_of_le hm (by norm_num)
  have ha := fromBaseW_digitsOfBaseW_of_lt a.toNat 128 37 (bound a)
  have hb := fromBaseW_digitsOfBaseW_of_lt b.toNat 128 37 (bound b)
  apply BitVec.eq_of_toNat_eq
  exact ha.symm.trans ((congrArg (fromBaseW 128) h).trans hb)

theorem digits_lt (m : Message) : ∀ d ∈ digits m, d < 128 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact messageDigits_lt m d hd
  · exact digitsOfBaseW_lt _ _ _ (by decide) d hd

theorem digits_incomparable {a b : Message} (h : a ≠ b) :
    ¬ List.Forall₂ (· ≤ ·) (digits a) (digits b) ∧
    ¬ List.Forall₂ (· ≤ ·) (digits b) (digits a) :=
  wots_fullDigits_incomparable (messageDigits_length a) (messageDigits_length b)
    (messageDigits_lt a) (messageDigits_lt b) (by decide)
    (fun hab => h (messageDigits_injective hab))

def digit (m : Message) (i : Fin 39) : ℕ :=
  (digits m)[i.val]'(by rw [digits_length]; exact i.isLt)

theorem digit_le (m : Message) (i : Fin 39) : digit m i ≤ 127 := by
  have h := digits_lt m (digit m i) (List.getElem_mem _)
  omega

end OptimalOTS.LeanIsaBaseline
