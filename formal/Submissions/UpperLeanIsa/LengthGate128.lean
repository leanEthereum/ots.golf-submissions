import Submissions.UpperLeanIsa.LengthLogs128

/-! A length gate for the full 5504-bit signature. Unlike the 5503-bit gate,
ten invalid lengths land in memory. The caller must establish that none of
those cells contains ONE; the checked alias list is exhaustive for κ ≤ 32. -/

namespace OptimalOTS.HLG3.LengthGate128

open LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer

def scale : K := gpow (ordG - 1434881718044321323 + 48)

/-- These short signatures have no bits in the cell their length addresses. -/
def lowAliases : List (Nat × Nat) :=
  [(43,41), (86,42), (172,43), (344,44), (688,45), (1376,46)]

theorem low_alias_bounds : ∀ p ∈ lowAliases,
    p.1 < 5505 ∧ 4 ≤ p.2 ∧ p.2 < 47 ∧ p.1 ≤ 128 * (p.2 - 4) := by decide

theorem natV_ofK {n : Nat} (hn : n ≤ 5505) : natV n = ofK (BitVec.ofNat 64 n) := by
  apply E.ext
  intro i
  fin_cases i <;> simp [natV, LeanIsa.cellOfBits]
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega

theorem target_address : (BitVec.ofNat 64 5504 : K) * scale = gpow 48 := by
  change (5504 : K) * scale = gpow 48
  rw [← LengthGate.log5504, scale, gpow_mul_gpow, ← gpow_mod]
  congr 1

theorem wrong_length_read_ne_one {κ n : Nat} (hκ : κ ≤ 32) (hn : n ≤ 5505)
    (hne : n ≠ 5504) (L : MemImage κ)
    (halias : ∀ a, (n,a) ∈ aliases → L.read (gpow a) ≠ some (ofK 1)) :
    L.read ((BitVec.ofNat 64 n : K) * scale) ≠ some (ofK 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · change L.read ((0 : K) * scale) ≠ _
    rw [zero_mul, MemImage.read_zero]
    simp
  · obtain ⟨e, he, heM, hbad⟩ := bounded_log h0 hn
    have hadd : e + (ordG - 1434881718044321323 + 48) =
        e + ordG - 1434881718044321323 + 48 := by unfold ordG; omega
    rw [← he, scale, gpow_mul_gpow, hadd, ← gpow_mod]
    rcases hbad.resolve_left hne with hb | ha
    · rw [MemImage.read,
        gLog?_gpow_eq_none (le_trans (Nat.pow_le_pow_right (by norm_num) hκ) hb)
          (by rw [← ordG_eq]; exact Nat.mod_lt _ (by norm_num [ordG])),
        Option.map_none]
      simp
    · exact halias _ ha

end OptimalOTS.HLG3.LengthGate128
