import Submissions.UpperLeanIsa.LengthFrameData0
import Submissions.UpperLeanIsa.LengthFrameData1
import Submissions.UpperLeanIsa.LengthFrameData2
import Submissions.UpperLeanIsa.LengthFrameData3
import Submissions.UpperLeanIsa.LengthFrameData4
import Submissions.UpperLeanIsa.LengthFrameData5
import Submissions.UpperLeanIsa.LengthFrameData6
import Submissions.UpperLeanIsa.LengthFrameData7
import Submissions.UpperLeanIsa.LengthFrameData8
import Submissions.UpperLeanIsa.LengthFrameData9
import Submissions.UpperLeanIsa.LengthFrameData10
import Submissions.UpperLeanIsa.LengthFrameData11
import Submissions.UpperLeanIsa.LengthFrameData12
import Submissions.UpperLeanIsa.LengthFrameData13
import Submissions.UpperLeanIsa.LengthFrameData14
import Submissions.UpperLeanIsa.LengthFrameData15
import Submissions.UpperLeanIsa.LengthFrameData16

namespace OptimalOTS.LengthFrameChecks
theorem all_blocks {x : Nat} (hx : x < 1088) :
    ∃ r, r.length = certLength x ∧
      scan (certEntry x) (certBias x) (certEntry x) r = true := by
  have hq : x / 64 < 17 := by omega
  have hr : x % 64 < 64 := Nat.mod_lt _ (by decide)
  have he := Nat.div_add_mod x 64
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
  · have hs : 512 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk8 512 chunk8_checked
      (x % 64) (by rw [chunk8_length]; exact hr)
  · have hs : 576 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk9 576 chunk9_checked
      (x % 64) (by rw [chunk9_length]; exact hr)
  · have hs : 640 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk10 640 chunk10_checked
      (x % 64) (by rw [chunk10_length]; exact hr)
  · have hs : 704 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk11 704 chunk11_checked
      (x % 64) (by rw [chunk11_length]; exact hr)
  · have hs : 768 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk12 768 chunk12_checked
      (x % 64) (by rw [chunk12_length]; exact hr)
  · have hs : 832 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk13 832 chunk13_checked
      (x % 64) (by rw [chunk13_length]; exact hr)
  · have hs : 896 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk14 896 chunk14_checked
      (x % 64) (by rw [chunk14_length]; exact hr)
  · have hs : 960 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk15 960 chunk15_checked
      (x % 64) (by rw [chunk15_length]; exact hr)
  · have hs : 1024 + x % 64 = x := by omega
    simpa only [hs] using blocksCheck_sound chunk16 1024 chunk16_checked
      (x % 64) (by rw [chunk16_length]; exact hr)
end OptimalOTS.LengthFrameChecks
