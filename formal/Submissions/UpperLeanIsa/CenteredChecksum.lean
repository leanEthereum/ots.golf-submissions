import Submissions.UpperLeanIsa.PackedSupport

/-! Centered-checksum algebra used by the 1095-cycle execution proof.

Center each of the thirteen charged costs at six. A negative offset is enforced
by reversing the operands of one multiplication, not by executing division.
The existing tables and group lengths can be retained: replace the old second
checksum multiplication with a NOP where necessary.
-/
namespace OptimalOTS.CenteredChecksum

section Algebra
variable {F : Type*} [Field F]

def Step (a : F) (c : Nat) (x y : F) : Prop :=
  if 6 ≤ c then y = x * a ^ (c - 6) else x = y * a ^ (6 - c)

theorem step_iff {a x y : F} (ha : a ≠ 0) (c : Nat) :
    Step a c x y ↔ y * a ^ 6 = x * a ^ c := by
  unfold Step
  split_ifs with hc
  · have hp : a ^ c = a ^ (c - 6) * a ^ 6 := by
      rw [← pow_add, Nat.sub_add_cancel hc]
    rw [hp, ← mul_assoc]
    exact (mul_left_injective₀ (pow_ne_zero 6 ha)).eq_iff.symm
  · have hp : a ^ 6 = a ^ (6 - c) * a ^ c := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : c ≤ 6)]
    rw [hp, ← mul_assoc]
    constructor
    · intro h
      rw [← h]
    · intro h
      exact (mul_right_cancel₀ (pow_ne_zero c ha) h).symm

theorem step_ratio {a x y : F} (ha : a ≠ 0) (c : Nat) :
    Step a c x y ↔ y = x * a ^ c / a ^ 6 := by
  rw [step_iff ha, eq_div_iff (pow_ne_zero 6 ha)]

/-- Only powers zero through ten are used, for every admitted charged cost. -/
theorem power_bound {c : Nat} (hc : c ≤ 16) :
    (if 6 ≤ c then c - 6 else 6 - c) ≤ 10 := by
  split_ifs <;> omega

/-- An invariant with natural exponents avoids signed-exponent bookkeeping. -/
theorem invariant {a : F} (ha : a ≠ 0) (c : Nat → Nat) (q : Nat → F)
    (hs : ∀ u, Step a (c u) (q u) (q (u + 1))) :
    ∀ n, q n * a ^ (6 * n) = q 0 * a ^ (∑ u ∈ Finset.range n, c u) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := (step_iff ha (c n)).mp (hs n)
    calc
      q (n + 1) * a ^ (6 * (n + 1)) =
          (q (n + 1) * a ^ 6) * a ^ (6 * n) := by
        rw [show 6 * (n + 1) = 6 + 6 * n by omega, pow_add, mul_assoc]
      _ = (q n * a ^ (6 * n)) * a ^ (c n) := by rw [hn]; ring
      _ = q 0 * a ^ (∑ u ∈ Finset.range (n + 1), c u) := by
        rw [ih, Finset.sum_range_succ, pow_add, mul_assoc]

/-- With eight binding deductions, the new free seed is simply `halt * a^(s+1)`. -/
theorem final_identity (a halt : F) (s charged : Nat) :
    (halt * a ^ (s + 1)) * a ^ charged = halt * a ^ (s + 1 + charged) := by
  rw [pow_add a (s + 1) charged, mul_assoc]

theorem layer_identity {s costs charged : Nat} (h : charged + 8 = costs) :
    s + 1 + charged = 6 * 13 ↔ s + costs = 85 := by omega

end Algebra

open LeanerVM.Parameters OptimalOTS.HLFour
noncomputable section

/-- One actual cell instruction for either sign of the centered exponent. -/
def instr (u c : Nat) : CInstr :=
  if 6 ≤ c then .mul (gpCell u) (cCell (c - 6)) (gpCell (u + 1))
  else .mul (gpCell (u + 1)) (cCell (6 - c)) (gpCell u)

theorem instr_cost (u c : Nat) : (instr u c).cost = 1 := by
  unfold instr; split_ifs <;> rfl

theorem instr_bounded {u c : Nat} (hu : u < 13) (hc : c ≤ 16) :
    (instr u c).Bounded := by
  have hcell : ∀ n ≤ 10, cCell n < 2 ^ 16 := by
    intro n hn
    unfold cCell
    split_ifs <;> omega
  unfold instr
  split_ifs with h
  · exact ⟨by unfold gpCell; omega, hcell _ (by omega), by unfold gpCell; omega⟩
  · exact ⟨by unfold gpCell; omega, hcell _ (by omega), by unfold gpCell; omega⟩

/-- Its existing machine relation is exactly the centered field equation. -/
theorem instr_relation (B : BlakeRel) (v : Nat → E) (a : E) (u c : Nat)
    (hc : c ≤ 16) (hconst : ∀ n ≤ 10, v (cCell n) = a ^ n) :
    (instr u c).RelB B v ↔ Step a c (v (gpCell u)) (v (gpCell (u + 1))) := by
  unfold instr Step
  split_ifs with h
  · change (v (gpCell (u + 1)) = v (gpCell u) * v (cCell (c - 6))) ↔ _
    rw [hconst _ (by omega)]
  · change (v (gpCell u) = v (gpCell (u + 1)) * v (cCell (6 - c))) ↔ _
    rw [hconst _ (by omega)]

/-- Conditional path arithmetic only; not a universal execution certificate. -/
theorem proposed_score : (106 - 1 : Nat) + 87 * 10 + 120 = 1095 := by decide

end
end OptimalOTS.CenteredChecksum
