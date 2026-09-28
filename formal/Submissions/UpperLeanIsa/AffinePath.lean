import Submissions.UpperLeanIsa.AffineFacts

/-! A completing execution traverses precisely the fourteen affine blocks.
The checksum forbids every exit target except the intended sentinel. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure PathFacts (T : Tab) (B : BlakeRel) (v : ℕ → E) (xs : ℕ → ℕ) : Prop where
  pro : ∀ ci ∈ prefixCode T 16, ci.RelB B v
  disp : ∀ f < 14, (CInstr.dispatch f).RelB B v
  blk : ∀ f < 14, ∀ ci ∈ bodyCode T (base T) f (xs f), ci.RelB B v
  exit : CInstr.exit.RelB B v
  gp13 : v (gpCell 13) = ofK (gpow sentinel)

/-- Recenter the final checksum into the generic guarded-product form. -/
theorem centered_final_product (T : Tab) (s c : ℕ) :
    seedProduct (base T) s * base T ^ c / base T ^ (6*13) =
      AffineFrames.initialProduct (layout T) 78 (s+1) * base T ^ c := by
  change (gpow sentinel * base T ^ (s+1)) * base T ^ c / base T ^ 78 =
    (gpow sentinel / base T ^ 78 * base T ^ (s+1)) * base T ^ c
  rw [mul_div_right_comm,mul_div_right_comm]

theorem run_exit {κ : ℕ} (T : Tab) (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (d : AffineFrames.Slot) (hd : d.val < sentinel)
    (q : K) (hq : q ≠ 0) (hci : instrAt T d = compile q .exit)
    (hOne : Lx M oneCell = oneV) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow d.val,q⟩)) :
    IsInK (Lx M (gpCell 13)) ∧
      ∃ n' c', n = n'+1 ∧ c = 1+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (program T) M n' ⟨(Lx M (gpCell 13)).limb 0,1⟩) := by
  cases n with
  | zero =>
    rw [runCost_zero_slot T M hd q] at h
    exact (Sm.some_not_pure_none h).elim
  | succ n =>
    rw [runCost_slot T M n d hd q,hci,exec_exit h16 hκ M _ q hq hOne,Sm.bind_iff] at h
    obtain ⟨r,hr,hc⟩ := h
    rw [Sm.pure_iff] at hr
    split_ifs at hr with hK
    · subst r
      rw [Option.elim_some,show LeanIsa.weight (compile q .exit).opcode = 1 from rfl] at hc
      obtain ⟨c',hc',hw⟩ := Sm.some_map_add hc
      exact ⟨hK,n,c',rfl,hc',hw⟩
    · subst r
      exact (Sm.some_not_pure_none hc).elim

/-- Exact path extraction from actual bytecode execution, uniformly in the
memory size and oracle semantics. -/
theorem run_full {κ : ℕ} {T : Tab} (hT : T.Hyp) (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow 0,1⟩)) :
    Valid (xsOf (Lx M)) ∧ PathFacts T B (Lx M) (xsOf (Lx M)) ∧
      Landing (Lx M) (xsOf (Lx M)) ∧ xsOf (Lx M) 0 + gsum T (xsOf (Lx M)) = 85 ∧
      n = pathSteps T (xsOf (Lx M)) ∧ c = pathCost T (xsOf (Lx M)) := by
  obtain ⟨hp,n0,c0,hn0,hc0,hw0⟩ := run_prologue T h16 hκ M Sm B hHash hd h
  have hOne := pro_one hp
  let xs := xsOf (Lx M)
  have key : ∀ j ≤ 14,
      (∀ f < j, xs f < Wf f ∧ Lx M (hCell f) = ofK (gpow (ent f (xs f))) ∧
        (CInstr.dispatch f).RelB B (Lx M) ∧
        ∀ ci ∈ bodyCode T (base T) f (xs f), ci.RelB B (Lx M)) ∧
      ∃ n' c', n0 = n'+∑ f ∈ Finset.range j, (1+(bodyCode T (base T) f (xs f)).length) ∧
        c0 = (∑ f ∈ Finset.range j, (1+lcost (bodyCode T (base T) f (xs f))))+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (program T) M n' ⟨gpow (ctlSlot T xs j),ctlFrame T xs j⟩) ∧
        (j < 14 → Hint T (Lx M) j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨(fun f hf => by omega),n0,c0,by simp,by simp,hw0,fun _ => pro_hint_zero hp⟩
    | succ j ih =>
      intro hj
      obtain ⟨hprev,n',c',hn,hc,hw,hhint⟩ := ih (by omega)
      have hj' : j < 14 := by omega
      obtain ⟨hslot,hframe,hcode⟩ := ctl_geometry hT xs (by omega : j ≤ 14)
        (fun f hf => (hprev f hf).1)
      let d : AffineFrames.Slot := ⟨ctlSlot T xs j,by unfold sentinel at hslot; omega⟩
      have hci : instrAt T d = compile (ctlFrame T xs j) (.dispatch j) := by
        rw [hcode d rfl,if_pos hj']
      obtain ⟨x,hx,hH,hD,n1,c1,hn1,hc1,hw1⟩ := run_dispatch T h16 hκ M Sm B d hslot
        (ctlFrame T xs j) hframe hj' hci hOne (hhint hj') hw
      have hxe : xs j = x := by
        change xOf j (slotOf ((Lx M (hCell j)).limb 0)) = x
        rw [hH,limb_ofK_zero,slotOf_gpow (by have := ent_lt hj' hx; unfold sentinel at this; omega),
          xOf_ent hj' hx]
      rw [← hxe] at hx hH hw1
      obtain ⟨hblk,n2,c2,hn2,hc2,hw2⟩ := run_body hT h16 hκ M Sm B hHash hd hj' hx hw1
      refine ⟨?_,n2,c2,?_,?_,?_,?_⟩
      · intro f hf
        by_cases hfj : f < j
        · exact hprev f hfj
        · have he : f = j := by omega
          subst f
          exact ⟨hx,hH,hD,hblk⟩
      · rw [hn,hn1,hn2,Finset.sum_range_succ]
        omega
      · rw [hc,hc1,hc2,Finset.sum_range_succ]
        omega
      · rwa [ctlSlot_succ,ctlFrame_succ]
      · intro hj1
        exact next_hint hp (by omega) hblk
  obtain ⟨hall,n1,c1,hn1,hc1,hw1,hhint⟩ := key 14 le_rfl
  have hV : Valid xs := fun f hf => (hall f hf).1
  have hblk := fun f hf => (hall f hf).2.2.2
  have hgp := prod_eq hT hV hp hblk 13 le_rfl
  obtain ⟨hslot,hframe,hcode⟩ := ctl_geometry hT xs (f:=14) le_rfl (fun f hf => hV f hf)
  let d : AffineFrames.Slot := ⟨ctlSlot T xs 14,by unfold sentinel at hslot; omega⟩
  have hci : instrAt T d = compile (ctlFrame T xs 14) .exit := by
    rw [hcode d rfl,if_neg (by decide : ¬14 < 14)]
  obtain ⟨hExit,n2,c2,hn2,hc2,hw2⟩ := run_exit T h16 hκ M Sm d hslot _ hframe hci hOne hw1
  obtain ⟨target,htarget⟩ := runCost_pc_valid T M Sm hw2
  change (Lx M (gpCell 13)).limb 0 = gpow target.val at htarget
  rw [hgp,limb_ofK_zero] at htarget
  have hsum : (∑ w ∈ Finset.range 13, chargedCost T w (xs (w+1))) ≤ 13*16 := by
    calc
      _ ≤ ∑ _w ∈ Finset.range 13, 16 := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' := Finset.mem_range.mp hw
        have hx := hV (w+1) (by omega)
        rw [Wf_succ hw'] at hx
        exact LengthFrame.cost_shift_le hT hw' hx
      _ = _ := by simp
  have hx0 : xs 0 < 64 := by have hh := hV 0 (by decide); rwa [Wf_zero] at hh
  have hbound : xs 0+1+(∑ w ∈ Finset.range 13, chargedCost T w (xs (w+1))) ≤ 300 := by omega
  have htarget' := htarget
  rw [centered_final_product] at htarget'
  obtain ⟨hcharged,hsent⟩ := (AffineFrames.checksum_landing_exact (layout T) target
    (by decide : 78 ≤ 300) hbound).mp htarget'
  have hgp_final : Lx M (gpCell 13) = ofK (gpow sentinel) := by
    rw [hgp,htarget,hsent]
    rfl
  rw [hgp_final,limb_ofK_zero] at hw2
  obtain ⟨hnzero,hczero⟩ := completion_at_sentinel T M Sm hw2
  have hLayer : xs 0+gsum T xs = 85 := by
    have hshift := charged_sum hT hV
    unfold gsum
    omega
  refine ⟨hV,⟨hp,(fun f hf => (hall f hf).2.2.1),hblk,hExit,hgp_final⟩,
    (fun f hf => (hall f hf).2.1),hLayer,?_,?_⟩
  · change n = pathSteps T xs
    unfold pathSteps
    omega
  · change c = pathCost T xs
    unfold pathCost
    omega

end
end OptimalOTS.AffineVM
