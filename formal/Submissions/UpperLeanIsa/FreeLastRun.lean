import Submissions.UpperLeanIsa.FreeLastSemantics
import Submissions.UpperLeanIsa.FreeLastGuard
import Submissions.UpperLeanIsa.FreeLastNoRepeat

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

section Jump
variable {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (M : MemImage κ) (pc q : K) (hq : q ≠ 0)
include h16 hκ hq
open OptimalOTS.AffineVM (read_relative)
theorem exec_jump {t f : Nat} (ht : t < 2^16) (hf : f < 2^16) (hOne : Lx M oneCell = oneV) :
    LeanIsa.execute M ⟨pc,q⟩ (FreeLastProgram.jump q t f) =
      pure (if IsInK (Lx M t) ∧ IsInK (Lx M f)
        then some ⟨(Lx M t).limb 0,(Lx M f).limb 0⟩ else none) := by
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩
    (.jump (gpow oneCell/q) (gpow t/q) (gpow f/q))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,
    read_relative h16 hκ M q hq (show oneCell < 2 ^ 16 by decide),
    read_relative h16 hκ M q hq (show t < 2 ^ 16 from ht),
    read_relative h16 hκ M q hq (show f < 2 ^ 16 from hf),
    Option.bind_eq_bind,Option.bind_some,hOne]
  by_cases hh : IsInK (Lx M t) ∧ IsInK (Lx M f)
  · have hin : IsInK oneV ∧ IsInK (Lx M t) ∧ IsInK (Lx M f) :=
      ⟨isInK_ofK 1,hh⟩
    rw [show (guard (IsInK oneV ∧ IsInK (Lx M t) ∧ IsInK (Lx M f)) : Option Unit) =
      some () from if_pos hin,if_pos hh]
    simp only [Option.bind_some,oneV,if_neg ofK_one_ne_zero]
    rfl
  · rw [show (guard (IsInK oneV ∧ IsInK (Lx M t) ∧ IsInK (Lx M f)) : Option Unit) =
      none from if_neg (fun h => hh h.2),if_neg hh]
    rfl

end Jump


theorem run_first {κ : Nat} (hκ : κ ≤ 32) (M : MemImage κ) (Sm : Sem)
    {n c s : Nat} (hs : s < sentinel) (q : K)
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n ⟨gpow s,q⟩)) :
    ∃ j : FreeLastSelect.MaxCell,
      q * AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val := by
  cases n with
  | zero =>
    rw [runCost_zero_slot M hs q] at h
    exact (Sm.some_not_pure_none h).elim
  | succ n =>
    rw [runCost_slot M n ⟨s,by unfold sentinel at hs; omega⟩ hs q,Sm.bind_iff] at h
    obtain ⟨r,hr,hc⟩ := h
    cases r with
    | none => exact (Sm.some_not_pure_none hc).elim
    | some r =>
      exact FreeLastGuard.first_read hκ M Sm
        (r := ⟨gpow s,q⟩) (r' := r) (i := FreeLastProgram.instruction base s) hr

theorem run_halt {κ : Nat} (M : MemImage κ) (Sm : Sem) {n c : Nat} {q : K}
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n ⟨gpow sentinel,q⟩)) :
    n = 0 ∧ q = 1 ∧ c = 0 := by
  cases n with
  | zero =>
    rw [LeanIsa.runCost.eq_1,Sm.pure_iff] at h
    split_ifs at h with hh
    · exact ⟨rfl,hh.2,Option.some.inj h⟩
  | succ n =>
    rw [LeanIsa.runCost.eq_2,if_pos finalPc_eq.symm] at h
    exact (Sm.some_not_pure_none h).elim

/-- A completion from a stage frame begins at an actual entry of that group. -/
theorem stage_of_completion {κ : Nat} (hκ : κ ≤ 32) (M : MemImage κ) (Sm : Sem)
    (u : Fin 13) {n c : Nat} {target q : K}
    (hq : ∀ s < 2^18, target = gpow s → q = FreeLastGuard.incoming (FreeLastGuard.stageFlow u) s)
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n ⟨target,q⟩)) :
    ∃ s v z, 27 ≤ s ∧ s < sentinel ∧ target = gpow s ∧
      (candidateTree.lookup s).body = .group u.val v z ∧
      (candidateTree.lookup s).entry = s := by
  obtain ⟨s,hs⟩ := runCost_pc_valid M Sm h
  change target = gpow s.val at hs
  have hq' := hq s.val s.isLt hs
  rw [hs,hq'] at h
  have hlo : s.val < sentinel := by
    by_contra hn
    have he : s.val = sentinel := by have := s.isLt; unfold sentinel at *; omega
    rw [he] at h
    exact FreeLastGuard.stage_halt u (run_halt M Sm h).2.1
  obtain ⟨j,hj⟩ := run_first hκ M Sm hlo _ h
  obtain ⟨v,z,hb,he⟩ := FreeLastGuard.stage_read hlo u j hj
  have h27 : 27 ≤ s.val := by
    by_contra hn
    by_cases hi : s.val < 17
    · have hx := FreeLastGuard.initial_read hi j hj
      cases hx
    · rw [FreeLastGuard.initial_trap (by omega) (by omega)] at hj
      exact FreeLastGuard.no_zero_read hj
  exact ⟨s.val,v,z,h27,hlo,hs,hb,he.symm⟩

theorem core_ne_init (u v : Nat) (z : Bool) : CInstr.init ∉ FreeLastBlocks.core u v z := by
  intro hi
  simp only [FreeLastBlocks.core,List.mem_append,List.mem_singleton,List.mem_replicate] at hi
  rcases hi with (((hi | hi) | hi) | hi) | hi
  · unfold FreeLastBlocks.tie at hi
    split_ifs at hi <;> simp [copy] at hi
  · unfold FreeLastBlocks.checksum at hi
    cases z <;> by_cases hcost : 6 ≤ chargedCost fusionTab u v <;>
      simp only [hcost,if_true,if_false,Bool.false_eq_true] at hi <;> cases hi
  · exact AffineVM.init_not_body fusionTab u v false (by
      simp only [HLFour.body,List.mem_append]; tauto)
  · exact AffineVM.init_not_body fusionTab u v false (by
      simp only [HLFour.body,List.mem_append]; tauto)
  · cases hi.2

theorem body_ne_init (r : Row) : CInstr.init ∉ FreeLastProgram.body r := by
  intro h
  cases hb : r.body with
  | trap => simp [FreeLastProgram.body,hb] at h
  | free s =>
    simp only [FreeLastProgram.body,hb,FreeLastBlocks.free] at h
    exact AffineVM.init_not_chainOps _ _ _ _ h
  | group u v z =>
    simp only [FreeLastProgram.body,hb] at h
    cases z <;> simp only [Bool.false_eq_true,if_false,if_true] at h
    · simp only [FreeLastBlocks.normal,List.mem_append,List.mem_singleton] at h
      rcases h with h | h
      · exact core_ne_init u v false h
      · split_ifs at h <;> cases h
    · simp only [FreeLastBlocks.zero,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h | h | h
      · exact core_ne_init 1 v true h
      · cases h
      · cases h

/-- Executing a body exposes its cell equations and exact cost. -/
theorem run_body {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {s : Nat} (hs : 27 ≤ s) (hs' : s < sentinel)
    (he : (candidateTree.lookup s).entry = s)
    (hb : (candidateTree.lookup s).body ≠ .trap) {n c : Nat}
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n
      ⟨gpow s,FreeLastProgram.frame base (candidateTree.lookup s)⟩)) :
    (∀ ci ∈ FreeLastProgram.body (candidateTree.lookup s), ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+(FreeLastProgram.body (candidateTree.lookup s)).length ∧
        c = lcost (FreeLastProgram.body (candidateTree.lookup s))+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n'
          ⟨gpow (s+(FreeLastProgram.body (candidateTree.lookup s)).length),
            FreeLastProgram.frame base (candidateTree.lookup s)⟩) := by
  have hg := (candidate_lookup_good hs hs').1
  have hbound := FreeLastDecode.lookup_bounds hs hs'
  have hfit := FreeLastProgram.body_fits hg
  have hq : FreeLastProgram.frame base (candidateTree.lookup s) ≠ 0 := by
    cases hr : (candidateTree.lookup s).body with
    | trap => exact (hb hr).elim
    | group u v z => exact FreeLastBase.group_frame_nonzero hs hs' hr
    | free k => exact FreeLastBase.free_frame_nonzero hs hs' hr
  apply run_list M Sm B (FreeLastProgram.frame base (candidateTree.lookup s))
  · intro i hi t ht
    have hh := FreeLastDecode.instruction_body base hs hs' hi
    rw [he,List.getD_eq_getElem _ _ hi] at hh
    simpa only [ht] using hh
  · exact fun ci hi => FreeLastProgram.body_straight _ hi
  · intro ci hci pc r hr
    exact straight_of_sem h16 hκ M Sm B hHash hd pc _ hq ci
      (FreeLastDecode.body_bounded hg hci) (FreeLastProgram.body_straight _ hci)
      (fun hi => (body_ne_init _ (hi ▸ hci)).elim) r hr
  · unfold sentinel
    omega
  · exact h

/-- The control instruction consumes one ordinary cycle and exposes both
committed jump words. -/
theorem run_jump {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) {s t f : Nat} (hs : s < sentinel)
    (ht : t < 2^16) (hf : f < 2^16) (q : K) (hq : q ≠ 0)
    (hci : FreeLastProgram.instruction base s = FreeLastProgram.jump q t f)
    (hOne : Lx M oneCell = oneV) {n c : Nat}
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n ⟨gpow s,q⟩)) :
    IsInK (Lx M t) ∧ IsInK (Lx M f) ∧
      ∃ n' c', n = n'+1 ∧ c = 1+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n'
          ⟨(Lx M t).limb 0,(Lx M f).limb 0⟩) := by
  cases n with
  | zero =>
    rw [runCost_zero_slot M hs q] at h
    exact (Sm.some_not_pure_none h).elim
  | succ n =>
    rw [runCost_slot M n ⟨s,by unfold sentinel at hs; omega⟩ hs q,hci,
      exec_jump h16 hκ M _ q hq ht hf hOne,Sm.bind_iff] at h
    obtain ⟨r,hr,hc⟩ := h
    rw [Sm.pure_iff] at hr
    split_ifs at hr with hk
    · subst r
      rw [Option.elim_some,FreeLastProgram.jump_weight] at hc
      obtain ⟨c',hc',hw⟩ := Sm.some_map_add hc
      exact ⟨hk.1,hk.2,n,c',rfl,hc',hw⟩
    · subst r
      exact (Sm.some_not_pure_none hc).elim

end
end OptimalOTS.FreeLastVM
