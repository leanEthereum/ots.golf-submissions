import Submissions.UpperLeanIsa.AffineUnits

/-! Relations extracted from the affine path: initialized powers, successive
hint sums, and the running checksum. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.HLG3 (natV)
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Prologue

variable {T : Tab} {B : BlakeRel} {v : ℕ → E}
  (hp : ∀ ci ∈ prefixCode T 17, ci.RelB B v)
include hp

theorem pro_one : v oneCell = oneV := by
  have h := hp _ (prefixCode_mem T (i:=13) (by decide : 13 < 17))
  exact h.1

theorem pro_length : v lenCell = natV 5504 := by
  have h := hp _ (prefixCode_mem T (i:=13) (by decide : 13 < 17))
  exact h.2

theorem pro_g : v gCell = ofK (base T ^ 14) :=
  hp _ (prefixCode_mem T (i:=14) (by decide : 14 < 17))

theorem pro_c {c : ℕ} (hc : c ≤ 14) : v (cCell c) = ofK (base T ^ c) := by
  by_cases hc14 : c = 14
  · subst c; exact pro_g hp
  have hc : c ≤ 13 := by omega
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · simpa only [cCell,ite_true,pow_zero,oneV,oneCell] using pro_one hp
  · have h := hp _ (prefixCode_mem T (i:=c-1) (by omega : c-1 < 17))
    simpa only [raw,if_pos (show c-1 < 13 by omega),Nat.sub_add_cancel hc0,CInstr.RelB] using h

theorem pro_bias {f : ℕ} (hf : f < 14) : v (biasCell f) = ofK (base T ^ (stageIndex f+1)) := by
  by_cases h0 : f = 0
  · subst f
    exact pro_g hp
  · simp only [biasCell,stageIndex,if_neg h0,Nat.sub_add_cancel (show 1 ≤ f by omega)]
    exact pro_c hp (by omega)

theorem pro_hint_zero : Hint T v 0 := by
  have h := hp _ (prefixCode_mem T (i:=16) (by decide : 16 < 17))
  change v (h1Cell 0) = v (hCell 0)+v gCell at h
  rw [pro_g hp] at h
  exact h

end Prologue

theorem nextHint_mem (T : Tab) (a : K) {f x : ℕ} (hf : f < 13) :
    CInstr.xor (hCell (f+1)) (biasCell (f+1)) (h1Cell (f+1)) ∈ bodyCode T a f x := by
  by_cases h0 : f = 0
  · subst f
    rw [free_bodyCode]
    change CInstr.xor (hCell 1) (cCell 1) (h1Cell 1) ∈ _
    simp
  · have hm := nextMul_mem T x hf (fun _ => rfl)
    change CInstr.mul (hCell (f+1)) gCell (h1Cell (f+1)) ∈ bodyF T f x at hm
    simp only [bodyF,if_neg h0,gOf] at hm
    rw [bodyCode,if_neg h0]
    refine List.mem_map.mpr ⟨_,hm,?_⟩
    simp only [rehint,ite_true,h1Cell]
    rw [show 180+(f+1)-180 = f+1 by omega]
    rw [if_pos ⟨trivial, by unfold hCell; omega⟩]

theorem next_hint {T : Tab} {B : BlakeRel} {v : ℕ → E}
    (hp : ∀ ci ∈ prefixCode T 17, ci.RelB B v) {f x : ℕ} (hf : f < 13)
    (hb : ∀ ci ∈ bodyCode T (base T) f x, ci.RelB B v) : Hint T v (f+1) := by
  have h := hb _ (nextHint_mem T (base T) hf)
  change v (h1Cell (f+1)) = v (hCell (f+1))+v (biasCell (f+1)) at h
  rw [pro_bias hp (by omega)] at h
  exact h

theorem seed_mem (T : Tab) (x : ℕ) :
    CInstr.setc (gpCell 0) (ofK (AffineFrames.initialProduct (layout T) 77 x)) ∈
      bodyCode T (base T) 0 x := by
  rw [free_bodyCode]
  exact List.mem_cons_self

theorem rehint_prodOp (T : Tab) (u x : ℕ) :
    rehint (prodOp T u x) = prodOp T u x := by
  simp only [prodOp, rehint]
  rw [if_neg (by unfold gpCell; omega)]

theorem rehint_prodOps {T : Tab} {u x : ℕ} {ci : CInstr}
    (hi : ci ∈ prodOps T u x) : rehint ci = ci := by
  unfold prodOps at hi
  split_ifs at hi <;> simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hi
  · rcases hi with rfl | rfl
    · exact rehint_prodOp T u x
    · simp only [rehint]; rw [if_neg (by unfold gpTmp; omega)]
  · subst ci; exact rehint_prodOp T u x

theorem prodOps_mem {T : Tab} {u x : ℕ} {ci : CInstr}
    (hi : ci ∈ prodOps T u x) :
    ci ∈ bodyCode T (base T) (u+1) x := by
  rw [bodyCode, if_neg (by omega), Nat.add_sub_cancel]
  refine List.mem_map.mpr ⟨ci, ?_, rehint_prodOps hi⟩
  unfold body
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hi))))

/-- Both checksum multipliers are extracted from the actual instruction list. -/
theorem prod_relation {T : Tab} (hT : T.Hyp) {B : BlakeRel} {v : ℕ → E}
    (hp : ∀ ci ∈ prefixCode T 17, ci.RelB B v) {u x : ℕ}
    (hu : u < 13) (hx : x < VF u)
    (hb : ∀ ci ∈ bodyCode T (base T) (u+1) x, ci.RelB B v) :
    v (gpCell (u+1)) = v (gpCell u) * ofK (base T ^ chargedCost T u x) := by
  have hc := LengthFrame.cost_shift_le hT hu hx
  change chargedCost T u x ≤ 16 at hc
  have hfirst := hb _ (prodOps_mem (show prodOp T u x ∈ prodOps T u x by
    unfold prodOps; simp))
  by_cases he : 14 < chargedCost T u x
  · have hsecond := hb _ (prodOps_mem (show
        CInstr.mul (gpTmp u) (cCell (chargedCost T u x - 14)) (gpCell (u+1)) ∈ prodOps T u x by
      unfold prodOps; rw [if_pos he]; simp))
    change v (gpCell (u+1)) = v (gpTmp u) * v (cCell (chargedCost T u x - 14)) at hsecond
    have hmin : min 14 (chargedCost T u x) = 14 := min_eq_left (by omega)
    simp only [prodOp, hmin, if_pos he, CInstr.RelB] at hfirst
    rw [hsecond, hfirst, pro_c hp (by omega : 14 ≤ 14),
      pro_c hp (by omega : chargedCost T u x - 14 ≤ 14),
      mul_assoc, ← ofK_mul, ← pow_add, Nat.add_sub_of_le (by omega : 14 ≤ chargedCost T u x)]
  · have hmin : min 14 (chargedCost T u x) = chargedCost T u x := min_eq_right (by omega)
    simp only [prodOp, hmin, if_neg he, CInstr.RelB] at hfirst
    rw [hfirst, pro_c hp (by omega)]

/-- The free seed multiplied by exactly the preceding charged group costs. -/
theorem prod_eq {T : Tab} (hT : T.Hyp) {B : BlakeRel} {v : ℕ → E} {xs : ℕ → ℕ}
    (hV : Valid xs) (hp : ∀ ci ∈ prefixCode T 17, ci.RelB B v)
    (hb : ∀ f < 14, ∀ ci ∈ bodyCode T (base T) f (xs f), ci.RelB B v) :
    ∀ u ≤ 13, v (gpCell u) = ofK (AffineFrames.initialProduct (layout T) 77 (xs 0) *
      base T ^ (∑ w ∈ Finset.range u, chargedCost T w (xs (w+1)))) := by
  intro u
  induction u with
  | zero =>
    intro hu
    have h := hb 0 (by decide) _ (seed_mem T (xs 0))
    simpa only [CInstr.RelB,Finset.sum_range_zero,pow_zero,mul_one] using h
  | succ u ih =>
    intro hu
    have hx : xs (u+1) < VF u := by
      have h := hV (u+1) (by omega)
      rwa [Wf_succ (by omega)] at h
    have hr := prod_relation hT hp (by omega) hx (hb (u+1) (by omega))
    rw [hr, ih (by omega), ← ofK_mul, Finset.sum_range_succ, pow_add, mul_assoc]

def ctlSlot (T : Tab) (xs : ℕ → ℕ) (f : ℕ) : ℕ :=
  if f = 0 then 17 else ent (f-1) (xs (f-1))+(bodyCode T (base T) (f-1) (xs (f-1))).length

def ctlFrame (T : Tab) (xs : ℕ → ℕ) (f : ℕ) : K :=
  if f = 0 then 1 else blockFrame T (f-1) (xs (f-1))

theorem ctlSlot_succ (T : Tab) (xs : ℕ → ℕ) (f : ℕ) :
    ctlSlot T xs (f+1) = ent f (xs f)+(bodyCode T (base T) f (xs f)).length := by
  simp only [ctlSlot,if_neg (show f+1 ≠ 0 by omega),Nat.add_sub_cancel]

theorem ctlFrame_succ (T : Tab) (xs : ℕ → ℕ) (f : ℕ) :
    ctlFrame T xs (f+1) = blockFrame T f (xs f) := by
  simp only [ctlFrame,if_neg (show f+1 ≠ 0 by omega),Nat.add_sub_cancel]

theorem ctl_geometry {T : Tab} (hT : T.Hyp) (xs : ℕ → ℕ) {f : ℕ} (hf : f ≤ 14)
    (hV : ∀ j < f, xs j < Wf j) :
    ctlSlot T xs f < sentinel ∧ ctlFrame T xs f ≠ 0 ∧
      ∀ s : AffineFrames.Slot, s.val = ctlSlot T xs f →
        instrAt T s = compile (ctlFrame T xs f) (if f < 14 then .dispatch f else .exit) := by
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · refine ⟨by change 17 < sentinel; decide,one_ne_zero,?_⟩
    intro s hs
    change s.val = 17 at hs
    rw [instrAt_initial T s (by omega),hs]
    rfl
  · obtain ⟨j,rfl⟩ : ∃ j, f = j+1 := ⟨f-1,by omega⟩
    have hj : j < 14 := by omega
    have hx := hV j (by omega)
    rw [ctlSlot_succ,ctlFrame_succ]
    refine ⟨bodyCode_slot_lt hT (base T) hj hx le_rfl,blockFrame_ne_zero T hj hx,?_⟩
    intro s hs
    rw [instrAt_body hT hj hx le_rfl s hs,raw_body_control,
      show ctlOf j (xs j) = (if j+1 < 14 then .dispatch (j+1) else .exit) from
        ctlOf_frU (xs 0) hj (fun h => by rw [h])]

end
end OptimalOTS.AffineVM
