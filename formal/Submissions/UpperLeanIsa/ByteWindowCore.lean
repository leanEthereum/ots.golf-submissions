import Submissions.UpperLeanIsa.GenOrderFast

namespace OptimalOTS.ByteWindow
open LeanerVM.Parameters OptimalOTS.BF64Fast
set_option maxRecDepth 100000

def packedGet (p j : Nat) : Nat := Nat.land (Nat.shiftRight p (64*j)) 18446744073709551615

def rowCheck (b : Nat) : Nat → Nat → Nat → Bool
  | _, 0, _ => true
  | p, n+1, v => Nat.beq (Nat.land p 18446744073709551615) v &&
      rowCheck b (Nat.shiftRight p 64) n (fastMul v b)

theorem packedGet_step (p j : Nat) :
    packedGet p (j+1) = packedGet (Nat.shiftRight p 64) j := by
  unfold packedGet
  change (p >>> (64*(j+1))) &&& _ = ((p >>> 64) >>> (64*j)) &&& _
  rw [← Nat.shiftRight_add]
  congr 2
  omega

theorem rowCheck_sound (a : K) : ∀ n p (x : K),
    rowCheck a.toNat p n x.toNat = true →
    ∀ j < n, packedGet p j = (x*a^j).toNat := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro p x h j hj
    simp only [rowCheck, Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero =>
      change Nat.land p 18446744073709551615 = (x*a^0).toNat
      simpa only [pow_zero, mul_one] using h.1
    | succ j =>
      rw [packedGet_step]
      have ht : rowCheck a.toNat (Nat.shiftRight p 64) n (x*a).toNat = true := by
        simpa only [mul_toNat] using h.2
      rw [ih _ (x*a) ht j (by omega)]
      exact congrArg BitVec.toNat (by rw [mul_assoc, ← pow_succ'])

/-- An 11-bit window evaluator. The first lookup is already a field value,
so the base case avoids multiplying it by ONE. -/
def windowPow (tab : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | 1, n => tab 0 n
  | k+2, n => fastMul (windowPow tab (k+1) (n % 2048^(k+1))) (tab (k+1) (n / 2048^(k+1)))

theorem windowPow_correct (tab : Nat → Nat → Nat) (a : K) :
    ∀ k, (∀ i < k, ∀ j < 2048, tab i j = (a^(j*2048^i)).toNat) →
    ∀ n, n < 2048^k → windowPow tab k n = (a^n).toNat := by
  intro k
  induction k with
  | zero =>
    intro _ n hn
    have hn0 : n = 0 := by simpa using hn
    subst n
    rfl
  | succ k ih =>
    intro htab n hn
    cases k with
    | zero =>
      simpa only [windowPow, pow_zero, Nat.mul_one] using
        htab 0 (by omega) n (by simpa using hn)
    | succ k =>
      have hk : 0 < 2048^(k+1) := by positivity
      have hq : n / 2048^(k+1) < 2048 := by
        apply (Nat.div_lt_iff_lt_mul hk).mpr
        simpa only [pow_succ, Nat.mul_comm] using hn
      rw [windowPow, ih (fun i hi => htab i (by omega)) _ (Nat.mod_lt _ hk),
        htab (k+1) (by omega) _ hq, ← mul_toNat, ← pow_add]
      congr 2
      simpa only [Nat.mul_comm] using Nat.mod_add_div n (2048^(k+1))



end OptimalOTS.ByteWindow
