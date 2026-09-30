import Submissions.UpperLeanIsa.FreeLastBase
import Submissions.UpperLeanIsa.FreeLastCompile
import Submissions.UpperLeanIsa.AffineUnits

/-! Concrete decoder intervals, operand bounds and the first actual read. -/
namespace OptimalOTS.FreeLastDecode
open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.FreeLastBlocks OptimalOTS.FreeLastLayout
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem lookup_bounds {s : Nat} (hs : 27 ≤ s) (hs' : s < 262143) :
    27 ≤ (candidateTree.lookup s).entry ∧
    (candidateTree.lookup s).entry+(candidateTree.lookup s).length ≤ 262143 :=
  candidateTree.lookup_bounds candidateTree_checked hs hs'

theorem lookup_stable {s q : Nat} (hs : 27 ≤ s) (hs' : s < 262143)
    (hq : (candidateTree.lookup s).entry ≤ q)
    (hq' : q < (candidateTree.lookup s).entry+(candidateTree.lookup s).length) :
    candidateTree.lookup q = candidateTree.lookup s :=
  candidateTree.lookup_stable candidateTree_checked hs hs' hq hq'

theorem instruction_body (a : K) {s i : Nat} (hs : 27 ≤ s) (hs' : s < 262143)
    (hi : i < (FreeLastProgram.body (candidateTree.lookup s)).length) :
    FreeLastProgram.instruction a ((candidateTree.lookup s).entry+i) =
      FreeLastProgram.compile (FreeLastProgram.frame a (candidateTree.lookup s))
        ((FreeLastProgram.body (candidateTree.lookup s)).getD i .pad) := by
  obtain ⟨hg,_,_⟩ := candidate_lookup_good hs hs'
  have hb := lookup_bounds hs hs'
  have hf := FreeLastProgram.body_fits hg
  have hq : (candidateTree.lookup s).entry+i <
      (candidateTree.lookup s).entry+(candidateTree.lookup s).length := by omega
  have he := lookup_stable hs hs' (Nat.le_add_right _ i) hq
  simp only [FreeLastProgram.instruction, show ¬(candidateTree.lookup s).entry+i < 27 by omega,
    if_false, show (candidateTree.lookup s).entry+i < 262143 by omega, if_true,
    he, Nat.add_sub_cancel_left, if_pos hi]

theorem instruction_control (a : K) {s : Nat} (hs : 27 ≤ s) (hs' : s < 262143) :
    FreeLastProgram.instruction a ((candidateTree.lookup s).entry+
        (FreeLastProgram.body (candidateTree.lookup s)).length) =
      FreeLastProgram.control (FreeLastProgram.frame a (candidateTree.lookup s))
        (candidateTree.lookup s) := by
  obtain ⟨hg,_,_⟩ := candidate_lookup_good hs hs'
  have hb := lookup_bounds hs hs'
  have hf := FreeLastProgram.body_fits hg
  have hq : (candidateTree.lookup s).entry+(FreeLastProgram.body (candidateTree.lookup s)).length <
      (candidateTree.lookup s).entry+(candidateTree.lookup s).length := by omega
  have he := lookup_stable hs hs' (Nat.le_add_right _ _) hq
  simp only [FreeLastProgram.instruction,
    show ¬(candidateTree.lookup s).entry+(FreeLastProgram.body (candidateTree.lookup s)).length < 27 by omega,
    if_false, show (candidateTree.lookup s).entry+(FreeLastProgram.body (candidateTree.lookup s)).length < 262143 by omega,
    if_true, he, Nat.add_sub_cancel_left, Nat.lt_irrefl]

theorem tie_bounded {u v : Nat} (hu : u < 13) {ci : CInstr} (h : ci ∈ FreeLastBlocks.tie u v) :
    ci.Bounded := by
  unfold FreeLastBlocks.tie at h
  split_ifs at h <;> simp at h <;> (try rcases h with rfl | rfl) <;>
    simp only [CInstr.Bounded, accCell, tCell, copy, oneCell, idxCell, hCell] <;>
    (try split_ifs) <;> omega

theorem cCell_bounded {c : Nat} (hc : c ≤ 16) : cCell c < 65536 := by
  unfold cCell
  split_ifs <;> omega

theorem gp_bounded {p : Nat} (hp : p ≤ 13) : gp p < 65536 := by
  unfold gp
  split_ifs
  · exact cCell_bounded (by decide)
  · unfold gpCell; omega

theorem checksum_bounded {u v : Nat} (hu : u < 13) (hv : v < VF u) (z : Bool) :
    (checksum u v z).Bounded := by
  have hc := LengthFrame.cost_shift_le fusionTab_hyp hu hv
  change chargedCost fusionTab u v ≤ 16 at hc
  have hp : position u ≤ 12 := by unfold position; split_ifs <;> omega
  have hsrc := gp_bounded (by omega : position u ≤ 13)
  have hdst := gp_bounded (by omega : position u+1 ≤ 13)
  have hc1 := cCell_bounded (by omega : chargedCost fusionTab u v-6 ≤ 16)
  have hc2 := cCell_bounded (by omega : 6-chargedCost fusionTab u v ≤ 16)
  cases z <;> by_cases h : 6 ≤ chargedCost fusionTab u v <;>
    simp only [checksum,h,if_true,if_false,Bool.false_eq_true,CInstr.Bounded,oneCell] <;> omega

theorem core_bounded {u v : Nat} (hu : u < 13) (hv : v < VF u) (z : Bool)
    {ci : CInstr} (h : ci ∈ core u v z) : ci.Bounded := by
  simp only [core,List.mem_append,List.mem_singleton,List.mem_replicate] at h
  rcases h with (((h | h) | h) | h) | h
  · exact tie_bounded hu h
  · subst ci; exact checksum_bounded hu hv z
  · apply HLFour.body_bounded fusionTab_hyp (z:=false) hu hv ci
    simp only [HLFour.body,List.mem_append]; tauto
  · exact rootIns_bounded fusionTab hu ci h
  · rw [h.2]; simp only [NOP,CInstr.Bounded,oneCell]; omega

theorem normal_bounded {u v : Nat} (hu : u < 13) (hv : v < VF u)
    {ci : CInstr} (h : ci ∈ normal u v) : ci.Bounded := by
  simp only [normal,List.mem_append,List.mem_singleton] at h
  rcases h with h | h
  · exact core_bounded hu hv false h
  · subst ci
    have hn : nextGroup u < 13 := by unfold nextGroup; split_ifs <;> omega
    have hc := cCell_bounded (by omega : nextGroup u+1 ≤ 16)
    have hg := gp_bounded (by decide : 13 ≤ 13)
    unfold bias
    split_ifs <;> simp only [CInstr.Bounded,hCell,h1Cell,lenCell,oneCell] <;> omega

theorem zero_bounded {v : Nat} (hv : v < VF 1) {ci : CInstr} (h : ci ∈ zero v) :
    ci.Bounded := by
  simp only [zero,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h
  · exact core_bounded (by decide) hv true h
  · subst ci; simp only [copy,CInstr.Bounded,wCell,tfCell,oneCell]; omega
  · subst ci; simp only [NOP,CInstr.Bounded,oneCell]; omega

theorem free_bounded {s : Nat} (hs : s ≤ 63) {ci : CInstr} (h : ci ∈ free s) :
    ci.Bounded := by
  obtain ⟨t,ht,rfl⟩ := mem_chainOps.mp h
  exact chainOp_bounded topCell_read_bound (by decide) ht (by omega) (by unfold tfCell; omega)

theorem body_bounded {r : Row} (hg : Good r) {ci : CInstr}
    (h : ci ∈ FreeLastProgram.body r) : ci.Bounded := by
  have hb := hg.2
  cases he : r.body with
  | trap => simp [FreeLastProgram.body,he] at h
  | free s =>
    simp only [he] at hb
    simp only [FreeLastProgram.body,he] at h
    exact free_bounded hb.2.1 h
  | group u v z =>
    simp only [he] at hb
    simp only [FreeLastProgram.body,he] at h
    split_ifs at h with hz
    · have hu := hb.2.2.1 hz
      subst u
      exact zero_bounded hb.2.1 h
    · exact normal_bounded hb.1 hb.2.1 h

theorem compile_first (q : K) {ci : CInstr} (hs : ci.straight = true) :
    AffineFrames.firstOperand (FreeLastProgram.compile q ci) = gpow (FreeLastBase.cell0 ci)/q := by
  cases ci <;> first | rfl | cases hs

theorem firstCell_bounded {ci : CInstr} (hs : ci.straight = true) (hb : ci.Bounded) :
    FreeLastBase.cell0 ci < 2^16 := by
  cases ci <;> simp_all [CInstr.straight,CInstr.Bounded,FreeLastBase.cell0,lenCell]

theorem control_first (q : K) {r : Row} (h : r.body ≠ .trap) :
    AffineFrames.firstOperand (FreeLastProgram.control q r) = gpow oneCell/q := by
  unfold FreeLastProgram.control
  cases hb : r.body with
  | trap => exact (h hb).elim
  | free s => rfl
  | group u v z => dsimp only; split_ifs <;> rfl

/-- Traps have first operand zero; every executable body/control instruction
has exactly the relative operand used by the selected-base descriptor. -/
theorem instruction_first (a : K) {s : Nat} (hs : 27 ≤ s) (hs' : s < 262143)
    (hbody : (candidateTree.lookup s).body ≠ .trap) :
    AffineFrames.firstOperand (FreeLastProgram.instruction a s) = 0 ∨
      AffineFrames.firstOperand (FreeLastProgram.instruction a s) =
        gpow (FreeLastBase.bodyCell (candidateTree.lookup s) s)/
          FreeLastProgram.frame a (candidateTree.lookup s) := by
  have hg := (candidate_lookup_good hs hs').1
  simp only [FreeLastProgram.instruction,show ¬s < 27 by omega,if_false,hs',if_true]
  split_ifs with hi he
  · right
    rw [compile_first _ (FreeLastProgram.body_straight _ (by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi))]
    simp only [FreeLastBase.bodyCell,if_pos hi]
  · right
    rw [control_first _ hbody]
    simp only [FreeLastBase.bodyCell,if_neg hi]
  · left; rfl

theorem bodyCell_bounded {s : Nat} (hs : 27 ≤ s) (hs' : s < 262143) :
    FreeLastBase.bodyCell (candidateTree.lookup s) s < 2^16 := by
  have hg := (candidate_lookup_good hs hs').1
  unfold FreeLastBase.bodyCell
  dsimp only
  split_ifs with hi
  · have hm : (FreeLastProgram.body (candidateTree.lookup s)).getD
        (s-(candidateTree.lookup s).entry) .pad ∈ FreeLastProgram.body (candidateTree.lookup s) := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact firstCell_bounded (FreeLastProgram.body_straight _ hm) (body_bounded hg hm)
  · decide

end
end OptimalOTS.FreeLastDecode
