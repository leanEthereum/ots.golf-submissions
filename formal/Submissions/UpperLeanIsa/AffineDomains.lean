import Submissions.UpperLeanIsa.AffineGuard
import Submissions.UpperLeanIsa.SplitDomains

/-! Field-level separation of split-packet metadata. Label17 reuses the validated
signature-length word; it is not interpreted as the seventeenth power. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.AffineCodec
open LeanerVM.Parameters OptimalOTS.AffineFrames
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (L : Layout)

def word (i : ℕ) : Word := LeanIsa.cellBits (ofK (safeBase L ^ i))

theorem word_eq (i : ℕ) : word L i = (0 : BitVec 64) ++ (safeBase L ^ i : K) := by
  unfold word LeanIsa.cellBits
  rw [limb_ofK, limb_ofK]
  simp

theorem word_inj {i j : ℕ} (hi : i ≤ 300) (hj : j ≤ 300)
    (h : word L i = word L j) : i = j := by
  rw [word_eq, word_eq] at h
  have h' : safeBase L ^ i = safeBase L ^ j := by
    simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (64 + 64) => z.extractLsb' 0 64) h
  exact safeBase_powers_injective L hi hj h'


def lengthWord : Word := LeanIsa.cellBits (ofK lengthK)

theorem word_ne_length {i : ℕ} (hi : i ≤ 14) : word L i ≠ lengthWord := by
  intro h
  have hl : lengthWord = (0 : BitVec 64) ++ (lengthK : K) := by
    unfold lengthWord LeanIsa.cellBits
    rw [limb_ofK, limb_ofK]
    simp
  rw [word_eq, hl] at h
  have hk : safeBase L ^ i = lengthK := by
    simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (64 + 64) => z.extractLsb' 0 64) h
  by_cases hz : i = 0
  · subst i
    rw [pow_zero] at hk
    exact lengthK_ne_one hk.symm
  · exact safeBase_length_ne L (by omega) hi hk

def domainWord (i : ℕ) : Word := if i = 17 then lengthWord else word L i

theorem domainWord_inj {i j : ℕ} (hi : i ≤ 14 ∨ i = 17) (hj : j ≤ 14 ∨ j = 17)
    (h : domainWord L i = domainWord L j) : i = j := by
  by_cases hi17 : i = 17
  · by_cases hj17 : j = 17
    · omega
    · have hj14 : j ≤ 14 := hj.resolve_right hj17
      have he : lengthWord = word L j := by simpa [domainWord, hi17, hj17] using h
      exact (word_ne_length L hj14 he.symm).elim
  · by_cases hj17 : j = 17
    · have hi14 : i ≤ 14 := hi.resolve_right hi17
      have he : word L i = lengthWord := by simpa [domainWord, hi17, hj17] using h
      exact (word_ne_length L hi14 he).elim
    · apply word_inj L (by rcases hi with h | h <;> omega) (by rcases hj with h | h <;> omega)
      simpa [domainWord, hi17, hj17] using h

end
end OptimalOTS.LeanIsaBaseline.Layer.AffineCodec
