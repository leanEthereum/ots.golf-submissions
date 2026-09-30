import Submissions.UpperLeanIsa.FreeLastGroups

namespace OptimalOTS.FreeLastVM
open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.FreeLastBase (base)
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def charges (xs : Nat → Nat) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, chargedCost fusionTab (unit j) (xs (unit j))

def productValue (mem : Nat → E) (z : Bool) (j : Nat) : E :=
  if j = 13 ∧ z = true then mem oneCell else mem (FreeLastBlocks.gp j)

theorem checksum_step {B : BlakeRel} {mem : Nat → E} {u v : Nat} {z : Bool}
    (hp : ∀ ci ∈ prefixCode 15, ci.RelB B mem) (hu : u < 13) (hv : v < VF u)
    (hc : (FreeLastBlocks.checksum u v z).RelB B mem) :
    CenteredChecksum.Step (ofK base) (chargedCost fusionTab u v)
      (mem (FreeLastBlocks.gp (FreeLastBlocks.position u)))
      (mem (if z then oneCell else FreeLastBlocks.gp (FreeLastBlocks.position u+1))) := by
  have hbound := LengthFrame.cost_shift_le fusionTab_hyp hu hv
  change chargedCost fusionTab u v ≤ 16 at hbound
  unfold FreeLastBlocks.checksum at hc
  unfold CenteredChecksum.Step
  by_cases hc6 : 6 ≤ chargedCost fusionTab u v
  · rw [if_pos hc6] at hc ⊢
    change mem _ = mem _ * mem (cCell _) at hc
    rw [pro_c hp (by omega),checksum_embed_pow] at hc
    exact hc
  · rw [if_neg hc6] at hc ⊢
    change mem _ = mem _ * mem (cCell _) at hc
    rw [pro_c hp (by omega),checksum_embed_pow] at hc
    exact hc

theorem product_step {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {z : Bool}
    (hp : ∀ ci ∈ prefixCode 15, ci.RelB B mem) (hv : ∀ u < 13, xs u < VF u)
    (hb : ∀ j < 13, ∀ ci ∈ groupBody (unit j) (xs (unit j)) (if j = 12 then z else false), ci.RelB B mem)
    {j : Nat} (hj : j < 13) :
    CenteredChecksum.Step (ofK base) (chargedCost fusionTab (unit j) (xs (unit j)))
      (productValue mem z j) (productValue mem z (j+1)) := by
  have hz : (if j = 12 then z else false) = true → unit j = 1 := by
    split_ifs <;> simp_all [unit]
  have hc := core_rel hz (hb j hj) (FreeLastBlocks.checksum (unit j) (xs (unit j)) (if j = 12 then z else false))
    (by simp only [FreeLastBlocks.core,List.mem_append,List.mem_singleton]; tauto)
  have h := checksum_step hp (unit_lt hj) (hv _ (unit_lt hj)) hc
  rw [unit_position hj] at h
  have h0 : productValue mem z j = mem (FreeLastBlocks.gp j) := by
    simp only [productValue,show j ≠ 13 by omega,false_and,if_false]
  rw [h0]
  have h1 : productValue mem z (j+1) =
      mem (if (if j = 12 then z else false) then oneCell else FreeLastBlocks.gp (j+1)) := by
    by_cases hj12 : j = 12
    · subst j; cases z <;> rfl
    · simp only [productValue,show j+1 ≠ 13 by omega,false_and,if_false,if_neg hj12,Bool.false_eq_true]
  rw [h1]
  exact h

theorem product_invariant {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {z : Bool}
    (hp : ∀ ci ∈ prefixCode 15, ci.RelB B mem) (hv : ∀ u < 13, xs u < VF u)
    (hb : ∀ j < 13, ∀ ci ∈ groupBody (unit j) (xs (unit j)) (if j = 12 then z else false), ci.RelB B mem) :
    ∀ n ≤ 13, productValue mem z n * ofK (base^(6*n)) = ofK (base^(1+charges xs n)) := by
  have ha := checksum_embed_ne_zero FreeLastBase.base_ne_zero
  intro n
  induction n with
  | zero =>
    intro hn
    have he : productValue mem z 0 = mem (cCell 1) := rfl
    rw [he,pro_c hp (by decide)]
    simp only [charges,Finset.sum_range_zero,Nat.mul_zero,pow_zero,Nat.add_zero,checksum_embed_one,mul_one]
  | succ n ih =>
    intro hn
    have hstep := (CenteredChecksum.step_iff ha _).mp (product_step hp hv hb (by omega : n < 13))
    simp only [← checksum_embed_pow] at hstep
    calc
      productValue mem z (n+1) * ofK (base^(6*(n+1))) =
          (productValue mem z (n+1) * ofK (base^6)) * ofK (base^(6*n)) := by
        rw [show 6*(n+1)=6+6*n by omega,pow_add,ofK_mul,mul_assoc]
      _ = (productValue mem z n * ofK (base^(6*n))) *
          ofK (base^chargedCost fusionTab (unit n) (xs (unit n))) := by rw [hstep]; ring
      _ = ofK (base^(1+charges xs (n+1))) := by
        rw [ih (by omega),← ofK_mul,← pow_add]
        simp only [charges,Finset.sum_range_succ,Nat.add_assoc]

theorem charges_bound {xs : Nat → Nat} (hv : ∀ u < 13, xs u < VF u) : charges xs 13 ≤ 208 := by
  calc
    _ ≤ ∑ _j ∈ Finset.range 13, 16 := by
      apply Finset.sum_le_sum
      intro j hj
      have hu := unit_lt (Finset.mem_range.mp hj)
      exact LengthFrame.cost_shift_le fusionTab_hyp hu (hv _ hu)
    _ = 208 := by decide

theorem centered_power (q : Nat) : base^((q : Int)-77) = base^(1+q)/base^78 := by
  have he : (q : Int)-77 = ((1+q : Nat) : Int)-(78 : Int) := by omega
  rw [he,zpow_sub₀ FreeLastBase.base_ne_zero,zpow_natCast]
  exact congrArg (fun x : K => base^(1+q)/x) (zpow_natCast base 78)

theorem final_product {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {z : Bool}
    (hp : ∀ ci ∈ prefixCode 15, ci.RelB B mem) (hv : ∀ u < 13, xs u < VF u)
    (hb : ∀ j < 13, ∀ ci ∈ groupBody (unit j) (xs (unit j)) (if j = 12 then z else false), ci.RelB B mem) :
    productValue mem z 13 = ofK (base^((charges xs 13 : Int)-77)) := by
  rw [centered_power,checksum_embed_div _ _ (pow_ne_zero _ FreeLastBase.base_ne_zero),
    eq_div_iff (checksum_embed_ne_zero (pow_ne_zero _ FreeLastBase.base_ne_zero))]
  exact product_invariant hp hv hb 13 le_rfl

theorem charges_cost {xs : Nat → Nat} (hv : ∀ u < 13, xs u < VF u) :
    charges xs 13 + 8 = FreeLastBlocks.sumCosts xs := by
  have hs : ∀ u ∈ FreeLastBlocks.order,
      chargedCost fusionTab u (xs u) + LengthFrame.deduction u = cost fusionTab u (xs u) := by
    intro u hu
    exact Nat.sub_add_cancel (LengthFrame.cost_lower fusionTab_hyp (FreeLastBlocks.order_lt hu) (hv u (FreeLastBlocks.order_lt hu)))
  have hd : (FreeLastBlocks.order.map LengthFrame.deduction).sum = 8 := by decide
  have he : charges xs 13 = (FreeLastBlocks.order.map (fun u => chargedCost fusionTab u (xs u))).sum := by
    rw [← unit_order,List.map_map,list_sum_range]
    rfl
  rw [he,← hd,← List.sum_map_add]
  unfold FreeLastBlocks.sumCosts
  congr 1
  exact List.map_congr_left hs

theorem zero_layer {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat}
    (hp : ∀ ci ∈ prefixCode 15, ci.RelB B mem) (hv : ∀ u < 13, xs u < VF u)
    (hb : ∀ j < 13, ∀ ci ∈ groupBody (unit j) (xs (unit j)) (if j = 12 then true else false), ci.RelB B mem) :
    FreeLastBlocks.sumCosts xs = 85 := by
  have h := product_invariant hp hv hb 13 le_rfl
  change mem oneCell * ofK (base^78) = ofK (base^(1+charges xs 13)) at h
  rw [pro_one hp,show oneV = (1 : E) from checksum_embed_one,one_mul] at h
  have he := FreeLastBase.powers_injective (by decide : 78 ≤ 300) (by have := charges_bound hv; omega) (ofK_injective h)
  have hc := charges_cost hv
  omega

end
end OptimalOTS.FreeLastVM
