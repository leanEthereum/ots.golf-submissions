import Submissions.UpperLeanIsa.FreeLastBlocks

/-! Counts from the candidate's actual cell instructions. The hypothesis that
a completing machine run has one of these paths still needs a separate proof. -/
namespace OptimalOTS.FreeLastBlocks
open LeanerVM.Parameters OptimalOTS.HLFour
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def chosen (z : Bool) (u v : Nat) : List CInstr := if u = 1 ∧ z = true then zero v else normal u v
def groupSteps (z : Bool) (xs : Nat → Nat) : Nat :=
  (order.map (fun u => (chosen z u (xs u)).length + 1)).sum
def groupCycles (z : Bool) (xs : Nat → Nat) : Nat :=
  (order.map (fun u => lcost (chosen z u (xs u)) + 1)).sum
def sumCosts (xs : Nat → Nat) : Nat := (order.map (fun u => cost fusionTab u (xs u))).sum

theorem order_lt {u : Nat} (h : u ∈ order) : u < 13 := by
  unfold order at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem chosen_length {u v : Nat} (hu : u < 13) (hv : v < VF u) (z : Bool) :
    (chosen z u v).length + 1 = budget u + cost fusionTab u v + hm u +
      (if u = 1 ∧ z = true then 1 else 0) := by
  unfold chosen
  split_ifs with h
  · rcases h with ⟨rfl, _⟩
    simpa only [show hm 1 = 0 from rfl, Nat.add_zero] using zero_length hv
  · simpa only [Nat.add_zero] using normal_length hu hv

theorem chosen_cost {u v : Nat} (hu : u < 13) (hv : v < VF u) (z : Bool) :
    lcost (chosen z u v) + 1 = budget u + 10*(cost fusionTab u v + hm u) +
      (if u = 1 ∧ z = true then 1 else 0) := by
  unfold chosen
  split_ifs with h
  · rcases h with ⟨rfl, _⟩
    simpa only [show hm 1 = 0 from rfl, Nat.add_zero] using zero_cost hv
  · simpa only [Nat.add_zero] using normal_cost hu hv

theorem extra_sum (z : Bool) :
    (order.map (fun u => if u = 1 ∧ z = true then 1 else 0)).sum = if z then 1 else 0 := by
  cases z <;> decide

theorem group_steps_eq (z : Bool) (xs : Nat → Nat) (hx : ∀ u < 13, xs u < VF u) :
    groupSteps z xs = 83 + sumCosts xs + (if z then 1 else 0) := by
  have he : order.map (fun u => (chosen z u (xs u)).length + 1) =
      order.map (fun u => budget u + cost fusionTab u (xs u) + hm u +
        (if u = 1 ∧ z = true then 1 else 0)) := by
    apply List.map_congr_left
    intro u hu
    exact chosen_length (order_lt hu) (hx u (order_lt hu)) z
  rw [groupSteps, he, List.sum_map_add, List.sum_map_add, List.sum_map_add,
    budget_sum, root_sum, extra_sum]
  unfold sumCosts
  omega

theorem group_cycles_eq (z : Bool) (xs : Nat → Nat) (hx : ∀ u < 13, xs u < VF u) :
    groupCycles z xs = 92 + 10*sumCosts xs + (if z then 1 else 0) := by
  have he : order.map (fun u => lcost (chosen z u (xs u)) + 1) =
      order.map (fun u => budget u + 10*(cost fusionTab u (xs u) + hm u) +
        (if u = 1 ∧ z = true then 1 else 0)) := by
    apply List.map_congr_left
    intro u hu
    exact chosen_cost (order_lt hu) (hx u (order_lt hu)) z
  rw [groupCycles, he, List.sum_map_add, List.sum_map_add, List.sum_map_mul_left,
    List.sum_map_add, budget_sum, root_sum, extra_sum]
  unfold sumCosts
  omega

theorem intended_steps (a : K) (z : Bool) (xs : Nat → Nat) (s : Nat)
    (hx : ∀ u < 13, xs u < VF u) (hlayer : s + sumCosts xs = 85)
    (hz : z = true → s = 0) :
    (prologue a).length + 1 + groupSteps z xs +
      (if z then 0 else (free s).length+1) = 186 := by
  rw [prologue_length, group_steps_eq z xs hx, free_length]
  cases z <;> simp_all <;> omega

theorem intended_cycles (a : K) (z : Bool) (xs : Nat → Nat) (s : Nat)
    (hx : ∀ u < 13, xs u < VF u) (hlayer : s + sumCosts xs = 85)
    (hz : z = true → s = 0) :
    lcost (prologue a) + 1 + groupCycles z xs +
      (if z then 0 else lcost (free s)+1) + LeanIsa.boundaryCycles = 1089 := by
  rw [prologue_cost, group_cycles_eq z xs hx, free_cost]
  change 26 + (92 + 10 * sumCosts xs + (if z then 1 else 0)) +
    (if z then 0 else 10*s+1) + 120 = 1089
  cases z <;> simp_all <;> omega

end
end OptimalOTS.FreeLastBlocks
