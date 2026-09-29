import Submissions.UpperLeanIsa.FreeLastFacts

namespace OptimalOTS.FreeLastVM
open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.FreeLastBase (base)
open OptimalOTS.FreeLastLayout
open OptimalOTS.AffineVM (HashSound)
noncomputable section
open scoped Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def groupRegs (mem : Nat → E) (u : Nat) : Regs K :=
  ⟨(mem (hCell (u+1))).limb 0,(mem (h1Cell (u+1))).limb 0⟩
def afterRegs (mem : Nat → E) (u : Nat) (z : Bool) : Regs K :=
  ⟨(mem (nextTarget u z)).limb 0,(mem (nextFrame u z)).limb 0⟩
theorem exists_groupRow (mem : Nat → E) (u : Nat) :
    ∃ r : Row, r = candidateTree.lookup (slotOf ((mem (hCell (u+1))).limb 0)) := ⟨_,rfl⟩
def groupRow (mem : Nat → E) (u : Nat) : Row := Classical.choose (exists_groupRow mem u)
theorem groupRow_eq (mem : Nat → E) (u : Nat) :
    groupRow mem u = candidateTree.lookup (slotOf ((mem (hCell (u+1))).limb 0)) :=
  Classical.choose_spec (exists_groupRow mem u)
def bodyRaw : Body → Nat
  | .group _ v _ => v
  | _ => 0
def bodyZero : Body → Bool
  | .group _ _ z => z
  | _ => false
def rawOf (mem : Nat → E) (u : Nat) : Nat := bodyRaw (groupRow mem u).body
def zeroOf (mem : Nat → E) (u : Nat) : Bool := bodyZero (groupRow mem u).body

def GroupLanding (mem : Nat → E) (u v : Nat) (z : Bool) : Prop :=
  ∃ e, 27 ≤ e ∧ e < sentinel ∧ mem (hCell (u+1)) = ofK (gpow e) ∧
    (candidateTree.lookup e).body = .group u v z ∧ (candidateTree.lookup e).entry = e

theorem after_normal {mem : Nat → E} {u : Nat} (hu : u ≠ 1) :
    afterRegs mem u false = groupRegs mem (FreeLastBlocks.nextGroup u) := by
  simp only [afterRegs,nextTarget,nextFrame,Bool.false_eq_true,if_false,if_neg hu,groupRegs]

theorem run_group {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) (hp : ∀ ci ∈ prefixCode 16, ci.RelB B (Lx M))
    {u n c : Nat} (hu : u < 13) (hh : Hint (Lx M) u)
    (hK : IsInK (Lx M (hCell (u+1))))
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n (groupRegs (Lx M) u))) :
    rawOf (Lx M) u < VF u ∧ (zeroOf (Lx M) u = true → u = 1) ∧
      (∀ ci ∈ groupBody u (rawOf (Lx M) u) (zeroOf (Lx M) u), ci.RelB B (Lx M)) ∧
      GroupLanding (Lx M) u (rawOf (Lx M) u) (zeroOf (Lx M) u) ∧
      IsInK (Lx M (nextTarget u (zeroOf (Lx M) u))) ∧
      ∃ n' c', n = n'+(groupBody u (rawOf (Lx M) u) (zeroOf (Lx M) u)).length+1 ∧
        c = lcost (groupBody u (rawOf (Lx M) u) (zeroOf (Lx M) u))+1+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n'
          (afterRegs (Lx M) u (zeroOf (Lx M) u))) := by
  obtain ⟨e,v,z,he27,hehi,het,hbody,hentry⟩ := stage_of_completion hκ M Sm ⟨u,hu⟩
    (fun s _ ht => hint_incoming hh ht) h
  have hq := (hint_incoming hh het).trans (stage_frame hu hbody hentry)
  have hrun : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n
      ⟨gpow e,FreeLastProgram.frame base (candidateTree.lookup e)⟩) := by
    change some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n
      ⟨(Lx M (hCell (u+1))).limb 0,(Lx M (h1Cell (u+1))).limb 0⟩) at h
    rwa [het,hq] at h
  obtain ⟨hg,_,_⟩ := candidate_lookup_good he27 hehi
  have hgood := hg.2
  simp only [hbody] at hgood
  have hnt : (candidateTree.lookup e).body ≠ .trap := by rw [hbody]; intro he; cases he
  obtain ⟨hbr,n1,c1,hn1,hc1,hr1⟩ := run_body h16 hκ M Sm B hHash hd he27 hehi hentry hnt hrun
  have hf := FreeLastProgram.body_fits hg
  have hb := FreeLastDecode.lookup_bounds he27 hehi
  have hcslot : e+(FreeLastProgram.body (candidateTree.lookup e)).length < sentinel := by
    unfold sentinel; omega
  have hqne := FreeLastBase.group_frame_nonzero he27 hehi hbody
  have ht : nextTarget u z < 2^16 := by
    have hn : FreeLastBlocks.nextGroup u < 13 := by unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
    unfold nextTarget
    split_ifs <;> simp only [FreeLastBlocks.exitCell,hCell] <;> omega
  have hframe : nextFrame u z < 2^16 := by
    have hn : FreeLastBlocks.nextGroup u < 13 := by unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
    unfold nextFrame
    split_ifs <;> simp only [oneCell,h1Cell] <;> omega
  have hci : FreeLastProgram.instruction base (e+(FreeLastProgram.body (candidateTree.lookup e)).length) =
      FreeLastProgram.jump (FreeLastProgram.frame base (candidateTree.lookup e)) (nextTarget u z) (nextFrame u z) := by
    have hh := FreeLastDecode.instruction_control base he27 hehi
    rw [hentry] at hh
    rw [hh]
    simp only [FreeLastProgram.control,hbody,nextTarget,nextFrame]
    split_ifs <;> rfl
  obtain ⟨hNext,_,n2,c2,hn2,hc2,hr2⟩ := run_jump h16 hκ M Sm hcslot ht hframe _ hqne hci (pro_one hp) hr1
  have heRow : groupRow (Lx M) u = candidateTree.lookup e := by
    have hslot : slotOf ((Lx M (hCell (u+1))).limb 0) = e :=
      (congrArg slotOf het).trans (slotOf_gpow (by unfold sentinel at hehi; omega))
    exact (groupRow_eq _ _).trans (congrArg (Tree.lookup candidateTree) hslot)
  have hbody' : (groupRow (Lx M) u).body = .group u v z :=
    @Eq.trans Body (groupRow (Lx M) u).body (candidateTree.lookup e).body (.group u v z)
      (congrArg Row.body heRow) hbody
  have hraw : rawOf (Lx M) u = v := congrArg bodyRaw hbody'
  have hz : zeroOf (Lx M) u = z := congrArg bodyZero hbody'
  have hbl : FreeLastProgram.body (candidateTree.lookup e) = groupBody u v z := by
    rw [FreeLastProgram.body,hbody]; rfl
  rw [hraw,hz]
  rw [hbl] at hbr hn1 hc1
  exact ⟨hgood.2.1,hgood.2.2.1,hbr,
    ⟨e,he27,hehi,(ofK_limb hK).trans (congrArg ofK het),hbody,hentry⟩,
    hNext,n2,c2,by omega,by omega,hr2⟩

end
end OptimalOTS.FreeLastVM
