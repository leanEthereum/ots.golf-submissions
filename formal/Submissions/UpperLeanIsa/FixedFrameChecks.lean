import Submissions.UpperLeanIsa.BF64Fast
import Submissions.UpperLeanIsa.AffineFrames
import Submissions.UpperLeanIsa.FourMachineProgram

/-! Research support: exact, kernel-evaluable logarithm certificates for the
fixed frame `1 + g^slot`. These do not yet replace the machine's frame guard. -/
namespace OptimalOTS.FixedFrameChecks
open LeanerVM.Parameters
open OptimalOTS.BF64Fast

def powN (a n : Nat) : Nat → Nat
  | 0 => 1
  | fuel + 1 =>
      let half := powN (fastMul a a) (n / 2) fuel
      if n % 2 = 0 then half else fastMul half a

theorem powN_correct (fuel : Nat) (a : K) (n : Nat) (hn : n < 2 ^ fuel) :
    powN a.toNat n fuel = (a ^ n).toNat := by
  induction fuel generalizing a n with
  | zero =>
    have : n = 0 := by simp only [pow_zero] at hn; omega
    subst n
    rfl
  | succ fuel ih =>
    have hhalf : n / 2 < 2 ^ fuel := by
      rw [pow_succ] at hn
      omega
    have hp : a ^ n = (a * a) ^ (n / 2) * a ^ (n % 2) := by
      rw [← pow_two, ← pow_mul, ← pow_add]
      congr 1
      omega
    simp only [powN, ← mul_toNat, ih (a * a) (n / 2) hhalf]
    rw [hp]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp only [h, if_true, pow_zero, mul_one]
    · simp only [h, Nat.one_ne_zero, if_false, pow_one, mul_toNat]

/-- A closed natural calculation suffices to certify a field power. -/
theorem gpow_eq_of_check {e : Nat} {v : K} (he : e < 2 ^ 64)
    (h : powN 2 e 64 = v.toNat) : gpow e = v := by
  apply BitVec.eq_of_toNat_eq
  have hg : g.toNat = 2 := rfl
  rw [← hg, powN_correct 64 g e he] at h
  exact h

/-- `fixedCheck` checks the exact field identity, not a floating approximation. -/
def fixedCheck (s e : Nat) : Bool :=
  Nat.blt s (2 ^ 18) && Nat.blt e (2 ^ 64) &&
    Nat.beq (powN 2 e 64) (Nat.xor (powN 2 s 18) 1)

theorem fixedCheck_sound {s e : Nat} (h : fixedCheck s e = true) :
    gpow e = gpow s + 1 := by
  simp only [fixedCheck, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨hs, he⟩, hp⟩ := h
  apply gpow_eq_of_check he
  rw [show (2 : Nat) = g.toNat from rfl, powN_correct 18 g s hs] at hp
  change powN 2 e 64 = ((gpow s) ^^^ (1 : BitVec 64)).toNat
  rw [BitVec.toNat_xor]
  exact hp

theorem frame_toNat {s : Nat} (hs : s < 2 ^ 18) :
    (gpow s + 1).toNat = Nat.xor (powN 2 s 18) 1 := by
  change ((gpow s) ^^^ (1 : BitVec 64)).toNat = _
  rw [BitVec.toNat_xor, show (2 : Nat) = g.toNat from rfl, powN_correct 18 g s hs]
  rfl

def freeCheck (s entry d : Nat) : Bool :=
  Nat.blt s (2 ^ 18) && Nat.blt entry (2 ^ 18) &&
    Nat.ble (2 ^ 32) d && Nat.ble d (18446744073709551615 - 2 ^ 16) &&
    Nat.beq (fastMul (powN 2 d 64) (Nat.xor (powN 2 entry 18) 1))
      (Nat.xor (powN 2 s 18) 1)

theorem freeCheck_sound {s entry d : Nat} (h : freeCheck s entry d = true) :
    gpow d * (gpow entry + 1) = gpow s + 1 ∧
      2 ^ 32 ≤ d ∧ d ≤ 18446744073709551615 - 2 ^ 16 := by
  simp only [freeCheck, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hs, he⟩, hd0⟩, hd1⟩, hp⟩ := h
  refine ⟨?_, hd0, hd1⟩
  apply BitVec.eq_of_toNat_eq
  rw [mul_toNat, frame_toNat he, frame_toNat hs]
  have hpow : powN 2 d 64 = (gpow d).toNat :=
    powN_correct 64 g d (by omega)
  rwa [hpow] at hp

/-- For any admissible image size, a certified wrong free-block landing fails
its first read. The statement covers every first operand below 2^16. -/
theorem wrong_free_read_none {κ s entry d c : Nat} (hκ : κ ≤ 32)
    (M : LeanerVM.Semantics.MemImage κ)
    (hcheck : freeCheck s entry d = true) (hc : c < 2 ^ 16)
    (hne : gpow entry + 1 ≠ 0) :
    M.read ((gpow s + 1) * (gpow c / (gpow entry + 1))) = none := by
  obtain ⟨heq, hd0, hd1⟩ := freeCheck_sound hcheck
  have hadd : d + c < OptimalOTS.HLFour.ordG := by
    unfold OptimalOTS.HLFour.ordG
    omega
  have haddr : (gpow s + 1) * (gpow c / (gpow entry + 1)) = gpow (d + c) := by
    rw [← heq, ← OptimalOTS.HLFour.gpow_mul_gpow]
    field_simp
  rw [haddr]
  exact OptimalOTS.HLFour.read_gpow_none hκ M (by rw [Nat.mod_eq_of_lt hadd]; omega)

theorem fixed_frame_zero : gpow 0 + (1 : K) = 0 := by decide +kernel

theorem fixed_frame_ne_zero {s : Nat} (hs0 : 0 < s) (hs : s < 2 ^ 18) :
    gpow s + (1 : K) ≠ 0 := by
  intro h
  have hn : -(1 : K) = 1 := by decide +kernel
  have he : gpow s = gpow 0 := by
    simpa only [gpow, pow_zero, hn] using eq_neg_of_add_eq_zero_left h
  have hi := OptimalOTS.HLG3.gpow_inj (by omega) (by norm_num) he
  omega

theorem fixed_halt_ne_one : gpow 262143 + (1 : K) ≠ 1 := by
  intro h
  have he : gpow 262143 = 0 := add_right_cancel (show gpow 262143 + 1 = 0 + 1 by simpa using h)
  exact (pow_ne_zero _ g_ne_zero) he

open Polynomial OptimalOTS.AffineFrames

/-- Cross-stage guards still give nonzero polynomials when one stage uses ONE. -/
theorem positive_fixed_collision_ne_zero {u s e c j : Nat} (hu : 0 < u) :
    collisionPoly u 0 s e c j ≠ 0 := by
  intro h
  have hh := congrArg (fun p : K[X] => p.coeff u) h
  have hz : gpow c = 0 := by
    simpa only [collisionPoly, framePoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_zero, if_pos rfl, if_neg (Nat.ne_of_gt hu),
      add_zero, mul_one, mul_zero, sub_zero, ite_true] using hh
  exact (pow_ne_zero _ g_ne_zero) hz

theorem fixed_positive_collision_ne_zero {v s e c j : Nat} (hv : 0 < v) :
    collisionPoly 0 v s e c j ≠ 0 := by
  intro h
  apply positive_fixed_collision_ne_zero (u := v) (s := e) (e := s) (c := j) (j := c) hv
  unfold collisionPoly at h ⊢
  exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

end OptimalOTS.FixedFrameChecks
