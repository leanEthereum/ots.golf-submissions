import Submissions.UpperLeanIsa.LengthFrameData

namespace OptimalOTS.LengthFrameChecks
open LeanerVM.Parameters OptimalOTS.ByteWindow OptimalOTS.HLFour
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def lengthInitialLogs : List Nat := [5964272755547696522, 12602611137583932103, 12916234136842968191, 15583995979017690692, 2742418359028718976, 14896535518370912139, 9814162397024267240, 16596076596669831777, 8585735640345490788, 12746647391527443349, 10238601820406108052, 7344803378031303196, 11757256920966263743, 15670742858149971853, 12398778086476669869, 5119204930372233738, 1955678632332730820, 1683171615607563846, 6498877933036128681, 1789096593446902040, 18195509037103324781, 11187089087534088195, 2643062508116976761, 10426618702247173759, 1746470684334986599, 358415034118422119, 306049139976886983]

theorem lengthInitial_checked : ((List.range 27).all fun s =>
    frameCheck bytePow s 0 5504 0 (lengthInitialLogs.getD s 0)) = true := rfl

theorem length_initial_address_ne {s c j : Nat}
    (hs : s ≤ 26) (hc : c < 2^16) (hj : j < 2^32) :
    (gpow s + lengthBias) * gpow c ≠ gpow j := by
  have h := List.all_eq_true.mp lengthInitial_checked s (List.mem_range.mpr (by omega))
  have hh := frameCheck_address_ne bytePow bytePow_correct h
    (by change (1 : K) + 0 ≠ 0; simp) hc hj
  simpa only [lengthBias, gpow, pow_zero, show (BitVec.ofNat 64 0 : K) = 0 from rfl,
    add_zero, div_one] using hh

def oneInitialLogs : List Nat := [0, 9686038906114705801, 925333738519859987, 8760705167594845878, 1850667477039719974, 8976526559427161943, 17521410335189691756, 14160487312297385890, 3701334954079439948, 9779170839485912523, 17953053118854323886, 628860363488390338, 16596076596669831897, 8251907150518977384, 9874230550885220165, 2939314230241565933, 7402669908158879896, 3746867709785537448, 1111597605262273431, 2902489875044988326, 17459362163999096157, 5597509194598222404, 1257720726976780676, 16180097153950408784, 14745409119630112179, 3473049422076689798, 16503814301037954768]

theorem oneInitial_checked : ((List.range' 1 26).all fun s =>
    frameCheck bytePow s 0 1 0 (oneInitialLogs.getD s 0)) = true := rfl

theorem one_initial_address_ne {s c j : Nat}
    (hs : s ≤ 26) (hc : c < 2^16) (hj : j < 2^32) :
    (gpow s + 1) * gpow c ≠ gpow j := by
  by_cases hs0 : s = 0
  · subst s
    rw [OptimalOTS.FixedFrameChecks.fixed_frame_zero,zero_mul]
    exact (pow_ne_zero _ g_ne_zero).symm
  · have h := List.all_eq_true.mp oneInitial_checked s
      (by rw [List.mem_range']; exact ⟨s-1,by omega,by omega⟩)
    have hh := frameCheck_address_ne bytePow bytePow_correct h
      (by change (1 : K) + 0 ≠ 0; simp) hc hj
    simpa only [gpow,pow_zero,show (BitVec.ofNat 64 0 : K) = 0 from rfl,
      show (BitVec.ofNat 64 1 : K) = 1 from rfl,add_zero,div_one] using hh

theorem block_address_ne {x i incoming c j : Nat}
    (hx : x < 1088) (hi : i < certLength x)
    (hb : incoming = 1 ∨ incoming = 5504)
    (hw : ¬(certEntry x+i = certEntry x ∧ incoming = certBias x))
    (hne : gpow (certEntry x) + (BitVec.ofNat 64 (certBias x) : K) ≠ 0)
    (hc : c < 2^16) (hj : j < 2^32) :
    (gpow (certEntry x+i) + (BitVec.ofNat 64 incoming : K)) *
      (gpow c / (gpow (certEntry x) + (BitVec.ofNat 64 (certBias x) : K))) ≠ gpow j := by
  obtain ⟨r, hr, hcheck⟩ := all_blocks hx
  obtain ⟨delta, hd⟩ := scan_sound _ _ r _ hcheck i (by omega) incoming hb hw
  exact frameCheck_address_ne bytePow bytePow_correct hd hne hc hj

theorem length_block_address_ne {x i incoming c j : Nat}
    (hx : x < 1024) (hi : i < certLength x)
    (hb : incoming = 1 ∨ incoming = 5504)
    (hw : ¬(certEntry x+i = certEntry x ∧ incoming = certBias x))
    (hne : gpow (certEntry x) + (BitVec.ofNat 64 (certBias x) : K) ≠ 0)
    (hc : c < 2^16) (hj : j < 2^32) :
    (gpow (certEntry x+i) + (BitVec.ofNat 64 incoming : K)) *
      (gpow c / (gpow (certEntry x) + (BitVec.ofNat 64 (certBias x) : K))) ≠ gpow j := by
  obtain ⟨r, hr, hcheck⟩ := length_blocks hx
  obtain ⟨delta, hd⟩ := scan_sound _ _ r _ hcheck i (by omega) incoming hb hw
  exact frameCheck_address_ne bytePow bytePow_correct hd hne hc hj

end OptimalOTS.LengthFrameChecks
