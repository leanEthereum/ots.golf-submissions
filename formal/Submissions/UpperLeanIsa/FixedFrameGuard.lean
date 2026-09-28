import Submissions.UpperLeanIsa.FixedFrameData

/-! Exact fixed-frame address separation, including the zero-target exception. -/

namespace OptimalOTS.FixedFrameChecks

open LeanerVM.Parameters LeanerVM.Semantics

theorem initial_certificate {s : ℕ} (hs : 0 < s) (hs' : s ≤ 26) :
    ∃ d, fixedCheck s d = true ∧ 2 ^ 32 ≤ d ∧
      d ≤ 18446744073709551615 - 2 ^ 16 := by
  have hm : s ∈ FixedFrameData.initialLogs.map Prod.fst := by
    rw [FixedFrameData.initialLogs_cover, List.mem_range']
    exact ⟨s - 1, by omega, by omega⟩
  obtain ⟨⟨t, d⟩, hd, he⟩ := List.mem_map.mp hm
  change t = s at he
  subst t
  have hc := List.all_eq_true.mp FixedFrameData.initialLogs_checked (s, d) hd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  exact ⟨d, hc.1.1, hc.1.2, hc.2⟩

theorem fixed_initial_address_ne {s c j : ℕ}
    (hs : s ≤ 26) (hc : c < 2 ^ 16) (hj : j < 2 ^ 32) :
    (gpow s + 1) * gpow c ≠ gpow j := by
  by_cases hs0 : s = 0
  · subst s
    rw [fixed_frame_zero, zero_mul]
    exact (pow_ne_zero _ g_ne_zero).symm
  · obtain ⟨d, hd, hlo, hhi⟩ := initial_certificate (by omega) hs
    rw [← fixedCheck_sound hd, OptimalOTS.HLFour.gpow_mul_gpow]
    intro he
    have hi := OptimalOTS.GenFast.gpow_injOn
      (show d + c < 2 ^ 64 - 1 by omega)
      (show j < 2 ^ 64 - 1 by omega) he
    omega

theorem fixed_body_address_ne {s entry d c j : ℕ}
    (hcheck : freeCheck s entry d = true) (hc : c < 2 ^ 16) (hj : j < 2 ^ 32)
    (hne : gpow entry + 1 ≠ 0) :
    (gpow s + 1) * (gpow c / (gpow entry + 1)) ≠ gpow j := by
  obtain ⟨heq, hlo, hhi⟩ := freeCheck_sound hcheck
  have haddr : (gpow s + 1) * (gpow c / (gpow entry + 1)) = gpow (d + c) := by
    rw [← heq, ← OptimalOTS.HLFour.gpow_mul_gpow]
    field_simp
  rw [haddr]
  intro he
  have hi := OptimalOTS.GenFast.gpow_injOn
    (show d + c < 2 ^ 64 - 1 by omega)
    (show j < 2 ^ 64 - 1 by omega) he
  omega

end OptimalOTS.FixedFrameChecks
