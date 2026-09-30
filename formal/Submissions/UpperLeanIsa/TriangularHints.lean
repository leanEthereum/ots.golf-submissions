import Mathlib

/-! A three-hint index bijection. This algebraic helper is not a machine
certificate: the concrete masks, layout and landing invariants must establish
the selector-stability hypotheses before a machine can use it. -/

namespace OptimalOTS.TriangularHints

abbrev Word := BitVec 128

def shear (s : Word → Nat) (m : Nat → Word) (x : Word) : Word := x ^^^ m (s x)

def Stable (s : Word → Nat) (m : Nat → Word) : Prop :=
  ∀ x v, s (x ^^^ m v) = s x

theorem shear_involutive (s : Word → Nat) (m : Nat → Word)
    (hs : Stable s m) (x : Word) : shear s m (shear s m x) = x := by
  unfold Stable at hs
  simp only [shear, hs, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

def encode (a b c : Word → Nat) (ma mb mc : Nat → Word) (x : Word) : Word :=
  x ^^^ ma (a x) ^^^ mb (b x) ^^^ mc (c x)

def decode (a b c : Word → Nat) (ma mb mc : Nat → Word) (x : Word) : Word :=
  shear c mc (shear b mb (shear a ma x))

theorem encode_eq_shears (a b c : Word → Nat) (ma mb mc : Nat → Word)
    (hab : Stable a mb) (hac : Stable a mc) (hbc : Stable b mc) (x : Word) :
    encode a b c ma mb mc x = shear a ma (shear b mb (shear c mc x)) := by
  unfold Stable at hab hac hbc
  simp only [encode, shear, hab, hac, hbc]
  ac_rfl

theorem decode_encode (a b c : Word → Nat) (ma mb mc : Nat → Word)
    (haa : Stable a ma) (hab : Stable a mb) (hac : Stable a mc)
    (hbb : Stable b mb) (hbc : Stable b mc) (hcc : Stable c mc) (x : Word) :
    decode a b c ma mb mc (encode a b c ma mb mc x) = x := by
  rw [encode_eq_shears a b c ma mb mc hab hac hbc]
  unfold decode
  rw [shear_involutive a ma haa, shear_involutive b mb hbb, shear_involutive c mc hcc]

theorem encode_decode (a b c : Word → Nat) (ma mb mc : Nat → Word)
    (haa : Stable a ma) (hab : Stable a mb) (hac : Stable a mc)
    (hbb : Stable b mb) (hbc : Stable b mc) (hcc : Stable c mc) (x : Word) :
    encode a b c ma mb mc (decode a b c ma mb mc x) = x := by
  rw [encode_eq_shears a b c ma mb mc hab hac hbc]
  unfold decode
  rw [shear_involutive c mc hcc, shear_involutive b mb hbb, shear_involutive a ma haa]

def equiv (a b c : Word → Nat) (ma mb mc : Nat → Word)
    (haa : Stable a ma) (hab : Stable a mb) (hac : Stable a mc)
    (hbb : Stable b mb) (hbc : Stable b mc) (hcc : Stable c mc) : Word ≃ Word where
  toFun := encode a b c ma mb mc
  invFun := decode a b c ma mb mc
  left_inv := decode_encode a b c ma mb mc haa hab hac hbb hbc hcc
  right_inv := encode_decode a b c ma mb mc haa hab hac hbb hbc hcc

end OptimalOTS.TriangularHints
