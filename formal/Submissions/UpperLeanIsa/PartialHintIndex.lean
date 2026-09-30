import Submissions.UpperLeanIsa.PartialHintData

/-! The three concrete masks form a bijection on all raw 128-bit words.
The final codec also needs the bit and label permutations; those are kept
separate so this theorem does not assume a prover-supplied hint is correct. -/

namespace OptimalOTS.PartialHints
open LeanIsaBaseline.Layer
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem selector8_xor (x y : Word) :
    selector8 (x ^^^ y) = selector8 x ^^^ selector8 y := by
  simp only [selector8, BitVec.extractLsb'_xor]
  exact BitVec.xor_append.symm

theorem selector9_xor (x y : Word) :
    selector9 (x ^^^ y) = selector9 x ^^^ selector9 y := by
  simp only [selector9, BitVec.extractLsb'_xor]

theorem stable_aa : TriangularHints.Stable (fun x => (hintField x).toNat) hintMask := by
  intro x v
  dsimp only
  rw [hintField_xor_mask]

theorem stable_ab : TriangularHints.Stable (fun x => (hintField x).toNat) mask8 := by
  intro x v
  dsimp only
  have h := (mask8_selectors v).1
  unfold hintField at h ⊢
  rw [BitVec.extractLsb'_xor, h]
  simp

theorem stable_ac : TriangularHints.Stable (fun x => (hintField x).toNat) mask9 := by
  intro x v
  dsimp only
  have h := (mask9_selectors v).1
  unfold hintField at h ⊢
  rw [BitVec.extractLsb'_xor, h]
  simp

theorem stable_bb : TriangularHints.Stable (fun x => (selector8 x).toNat) mask8 := by
  intro x v
  dsimp only
  rw [selector8_xor, (mask8_selectors v).2]
  simp

theorem stable_bc : TriangularHints.Stable (fun x => (selector8 x).toNat) mask9 := by
  intro x v
  dsimp only
  rw [selector8_xor, (mask9_selectors v).2.1]
  simp

theorem stable_cc : TriangularHints.Stable (fun x => (selector9 x).toNat) mask9 := by
  intro x v
  dsimp only
  rw [selector9_xor, (mask9_selectors v).2.2]
  simp

def hintEquiv : Word ≃ Word := TriangularHints.equiv
  (fun x => (hintField x).toNat) (fun x => (selector8 x).toNat) (fun x => (selector9 x).toNat)
  hintMask mask8 mask9 stable_aa stable_ab stable_ac stable_bb stable_bc stable_cc

theorem hintEquiv_apply (x : Word) :
    hintEquiv x = x ^^^ hintMask (hintField x).toNat ^^^
      mask8 (selector8 x).toNat ^^^ mask9 (selector9 x).toNat := rfl

theorem hint_roundtrip (x : Word) : hintEquiv.symm (hintEquiv x) = x :=
  hintEquiv.symm_apply_apply x

theorem hint_roundtrip_reverse (x : Word) : hintEquiv (hintEquiv.symm x) = x :=
  hintEquiv.apply_symm_apply x

end OptimalOTS.PartialHints
