import Submissions.UpperLeanIsa.OneFrame11Data0
import Submissions.UpperLeanIsa.OneFrame11Data1
import Submissions.UpperLeanIsa.OneFrame11Data2
import Submissions.UpperLeanIsa.OneFrame11Data3
import Submissions.UpperLeanIsa.OneFrame11Data4
import Submissions.UpperLeanIsa.OneFrame11Data5
import Submissions.UpperLeanIsa.OneFrame11Data6
import Submissions.UpperLeanIsa.OneFrame11Data7

namespace OptimalOTS.OneFrame11
open LeanerVM.Parameters OptimalOTS.HLFour OptimalOTS.ByteWindow
open OptimalOTS.LengthFrameChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_blocks {x : Nat} (hx : x < 512) :
    ∃ r, r.length = SL 11 x ∧ scan (entryOf 11 x) 1 (entryOf 11 x) r = true := by
  have hq : x / 64 < 8 := by omega
  have hr : x % 64 < 64 := Nat.mod_lt _ (by decide)
  interval_cases h : x / 64
  · have hs : 0 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk0 0 chunk0_checked
      (x % 64) (by rw [chunk0_length]; exact hr)
  · have hs : 64 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk1 64 chunk1_checked
      (x % 64) (by rw [chunk1_length]; exact hr)
  · have hs : 128 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk2 128 chunk2_checked
      (x % 64) (by rw [chunk2_length]; exact hr)
  · have hs : 192 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk3 192 chunk3_checked
      (x % 64) (by rw [chunk3_length]; exact hr)
  · have hs : 256 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk4 256 chunk4_checked
      (x % 64) (by rw [chunk4_length]; exact hr)
  · have hs : 320 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk5 320 chunk5_checked
      (x % 64) (by rw [chunk5_length]; exact hr)
  · have hs : 384 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk6 384 chunk6_checked
      (x % 64) (by rw [chunk6_length]; exact hr)
  · have hs : 448 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk7 448 chunk7_checked
      (x % 64) (by rw [chunk7_length]; exact hr)

theorem block_address_ne {x i incoming c j : Nat}
    (hx : x < 512) (hi : i < SL 11 x)
    (hb : incoming = 1 ∨ incoming = 5504)
    (hw : ¬(entryOf 11 x+i = entryOf 11 x ∧ incoming = 1))
    (hne : gpow (entryOf 11 x) + 1 ≠ 0)
    (hc : c < 2^16) (hj : j < 2^32) :
    (gpow (entryOf 11 x+i) + (BitVec.ofNat 64 incoming : K)) *
      (gpow c / (gpow (entryOf 11 x) + 1)) ≠ gpow j := by
  obtain ⟨r, hr, hcheck⟩ := all_blocks hx
  obtain ⟨delta, hd⟩ := scan_sound _ _ r _ hcheck i (by omega) incoming hb hw
  exact frameCheck_address_ne bytePow bytePow_correct hd hne hc hj

theorem entry_bounds : ∀ x < 512, 0 < entryOf 11 x ∧ entryOf 11 x < 2^18 := by decide +kernel

theorem exits_checked {x : Nat} (hx : x < 512) :
    ∃ delta, frameCheck bytePow 0 (entryOf 11 x) 0 1 delta = true := by
  have hq : x / 64 < 8 := by omega
  have hr : x % 64 < 64 := Nat.mod_lt _ (by decide)
  interval_cases h : x / 64
  · have hs : 0 + x % 64 = x := by omega
    simpa only [hs] using exitCheck_sound exits0 0 exits0_checked
      (x % 64) (by rw [exits0_length]; exact hr)
  · have hs : 64 + x % 64 = x := by omega
    simpa only [hs] using exitCheck_sound exits1 64 exits1_checked
      (x % 64) (by rw [exits1_length]; exact hr)
  · have hs : 128 + x % 64 = x := by omega
    simpa only [hs] using exitCheck_sound exits2 128 exits2_checked
      (x % 64) (by rw [exits2_length]; exact hr)
  · have hs : 192 + x % 64 = x := by omega
    simpa only [hs] using exitCheck_sound exits3 192 exits3_checked
      (x % 64) (by rw [exits3_length]; exact hr)
  · have hs : 256 + x % 64 = x := by omega
    simpa only [hs] using exitCheck_sound exits4 256 exits4_checked
      (x % 64) (by rw [exits4_length]; exact hr)
  · have hs : 320 + x % 64 = x := by omega
    simpa only [hs] using exitCheck_sound exits5 320 exits5_checked
      (x % 64) (by rw [exits5_length]; exact hr)
  · have hs : 384 + x % 64 = x := by omega
    simpa only [hs] using exitCheck_sound exits6 384 exits6_checked
      (x % 64) (by rw [exits6_length]; exact hr)
  · have hs : 448 + x % 64 = x := by omega
    simpa only [hs] using exitCheck_sound exits7 448 exits7_checked
      (x % 64) (by rw [exits7_length]; exact hr)
theorem exit_address_ne {x c j : Nat} (hx : x < 512)
    (hc : c < 2^16) (hj : j < 2^32) :
    gpow c / (gpow (entryOf 11 x) + 1) ≠ gpow j := by
  obtain ⟨delta, hd⟩ := exits_checked hx
  obtain ⟨hpos, hlt⟩ := entry_bounds x hx
  have h := frameCheck_address_ne bytePow bytePow_correct hd
    (FixedFrameChecks.fixed_frame_ne_zero hpos hlt) hc hj
  simpa only [gpow, pow_zero,
    show (BitVec.ofNat 64 0 : K) = 0 from rfl,
    show (BitVec.ofNat 64 1 : K) = 1 from rfl, add_zero, one_mul] using h

end OptimalOTS.OneFrame11
