import Submissions.UpperLeanIsa.LengthLogs

/-!
The loader supplies a length in 0..5505. Multiplication by `scale` addresses
cell 48 exactly for length 5503, and no cell at any allowed memory size for
any other length. A single DEREF with source `fp` therefore checks the length
and pins cell 48 to ONE.
-/

namespace OptimalOTS.HLG3.LengthGate

open LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer

def scale : K := gpow (ordG - 4674821839435376859 + 48)

theorem target_address : (BitVec.ofNat 64 5503 : K) * scale = gpow 48 := by
  change (5503 : K) * scale = gpow 48
  rw [← log5503, scale, gpow_mul_gpow, ← gpow_mod]
  congr 1

theorem wrong_length_read {κ n : Nat} (hκ : κ ≤ 32) (hn : n ≤ 5505)
    (hne : n ≠ 5503) (L : MemImage κ) :
    L.read ((BitVec.ofNat 64 n : K) * scale) = none := by
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · change L.read ((0 : K) * scale) = none
    rw [zero_mul, MemImage.read_zero]
  · obtain ⟨e, he, heM, hbad⟩ := bounded_log h0 hn
    have hb := hbad.resolve_left hne
    have hadd : e + (ordG - 4674821839435376859 + 48) =
        e + ordG - 4674821839435376859 + 48 := by unfold ordG; omega
    rw [← he, scale, gpow_mul_gpow, hadd, ← gpow_mod, MemImage.read,
      gLog?_gpow_eq_none (le_trans (Nat.pow_le_pow_right (by norm_num) hκ) hb)
        (by rw [← ordG_eq]; exact Nat.mod_lt _ (by norm_num [ordG])),
      Option.map_none]

theorem natV_ofK {n : Nat} (hn : n ≤ 5505) : natV n = ofK (BitVec.ofNat 64 n) := by
  apply E.ext
  intro i
  fin_cases i <;> simp [natV, LeanIsa.cellOfBits]
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega

end OptimalOTS.HLG3.LengthGate
