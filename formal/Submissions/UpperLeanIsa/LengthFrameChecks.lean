import Submissions.UpperLeanIsa.FixedFrameChecks
import Submissions.UpperLeanIsa.ByteWindow

/-! Exact arithmetic guard with two arbitrary 64-bit fixed biases.
The evaluator is parameterized so a certified byte-window implementation can
check the finite data without repeating 64 squarings per row. -/
namespace OptimalOTS.LengthFrameChecks

open LeanerVM.Parameters
open OptimalOTS.BF64Fast OptimalOTS.FixedFrameChecks

def frameCheck (eval : Nat → Nat) (s e incoming declared delta : Nat) : Bool :=
  Nat.blt s (2^18) && Nat.blt e (2^18) &&
  Nat.blt incoming (2^64) && Nat.blt declared (2^64) &&
  Nat.ble (2^32) delta && Nat.ble delta (18446744073709551615 - 2^16) &&
  Nat.beq (fastMul (eval delta) (Nat.xor (eval e) declared))
    (Nat.xor (eval s) incoming)

theorem frameCheck_sound (eval : Nat → Nat)
    (heval : ∀ n, n < 2^64 → eval n = (gpow n).toNat)
    {s e incoming declared delta : Nat}
    (h : frameCheck eval s e incoming declared delta = true) :
    gpow delta * (gpow e + (BitVec.ofNat 64 declared : K)) =
      gpow s + (BitVec.ofNat 64 incoming : K) ∧
    2^32 ≤ delta ∧ delta ≤ 18446744073709551615 - 2^16 := by
  simp only [frameCheck, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, he⟩, hi⟩, hd⟩, hlo⟩, hhi⟩, hp⟩ := h
  refine ⟨?_, hlo, hhi⟩
  apply BitVec.eq_of_toNat_eq
  rw [mul_toNat]
  change fastMul (gpow delta).toNat
      ((gpow e) ^^^ BitVec.ofNat 64 declared).toNat =
    ((gpow s) ^^^ BitVec.ofNat 64 incoming).toNat
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hi]
  rw [heval delta (by omega), heval e (by omega), heval s (by omega)] at hp
  exact hp

/-- Each checked relation excludes every possible admitted first operand,
not just the values used by an honest trace. -/
theorem frameCheck_address_ne (eval : Nat → Nat)
    (heval : ∀ n, n < 2^64 → eval n = (gpow n).toNat)
    {s e incoming declared delta c j : Nat}
    (h : frameCheck eval s e incoming declared delta = true)
    (hne : gpow e + (BitVec.ofNat 64 declared : K) ≠ 0)
    (hc : c < 2^16) (hj : j < 2^32) :
    (gpow s + (BitVec.ofNat 64 incoming : K)) *
      (gpow c / (gpow e + (BitVec.ofNat 64 declared : K))) ≠ gpow j := by
  obtain ⟨hlog, hlo, hhi⟩ := frameCheck_sound eval heval h
  have ha : (gpow s + (BitVec.ofNat 64 incoming : K)) *
      (gpow c / (gpow e + (BitVec.ofNat 64 declared : K))) = gpow (delta+c) := by
    rw [← hlog, ← OptimalOTS.HLFour.gpow_mul_gpow]
    field_simp
  rw [ha]
  intro heq
  have := OptimalOTS.GenFast.gpow_injOn
    (show delta+c < 2^64-1 by omega) (show j < 2^64-1 by omega) heq
  omega

def slowEval (n : Nat) : Nat := powN 2 n 64

theorem slowEval_correct (n : Nat) (hn : n < 2^64) :
    slowEval n = (gpow n).toNat := powN_correct 64 g n hn

def lengthBias : K := BitVec.ofNat 64 5504

theorem length_log : gpow 1434881718044321323 = lengthBias := by
  apply gpow_eq_of_check (by decide)
  decide +kernel

/-- Length cannot cancel the slot power anywhere in the complete code image. -/
theorem length_frame_ne_zero {s : Nat} (hs : s < 2^18) :
    gpow s + lengthBias ≠ 0 := by
  intro hz
  have hneg : -lengthBias = lengthBias := by decide +kernel
  have heq : gpow s = gpow 1434881718044321323 := by
    rw [length_log]
    simpa only [hneg] using eq_neg_of_add_eq_zero_left hz
  have := OptimalOTS.GenFast.gpow_injOn
    (show s < 2^64-1 by omega) (by decide) heq
  omega

theorem length_halt_ne_one : gpow 262143 + lengthBias ≠ 1 := by
  have hp : gpow 262143 = (BitVec.ofNat 64 156645908148787 : K) := by
    apply gpow_eq_of_check (by decide)
    decide +kernel
  rw [hp]
  decide +kernel


end OptimalOTS.LengthFrameChecks
