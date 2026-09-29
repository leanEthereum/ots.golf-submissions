import Submissions.UpperLeanIsa.AffineBlocks

/-! Completing executions after an affine dispatch must start at the entry
of a valid block of the requested stage, for every admitted memory size. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def incomingFrame (T : Tab) (f : ℕ) (target : K) : K :=
  AffineFrames.stageBias (base T) (stageIndex f) + target

theorem finalPc_eq (T : Tab) : (program T).finalPc = gpow sentinel := by
  show gpow (2 ^ 18 - 1) = gpow 262143
  norm_num

theorem gpow_ne_finalPc (T : Tab) {s : ℕ} (hs : s < sentinel) :
    gpow s ≠ (program T).finalPc := by
  intro h
  have he := gpow_inj (show s < 2 ^ 64 - 1 by unfold sentinel at hs; omega)
    (show sentinel < 2 ^ 64 - 1 by unfold sentinel; norm_num) (h.trans (finalPc_eq T))
  omega

theorem runCost_slot {κ : ℕ} (T : Tab) (M : MemImage κ) (n : ℕ)
    (s : AffineFrames.Slot) (hs : s.val < sentinel) (fp : K) :
    LeanIsa.runCost (program T) M (n+1) ⟨gpow s.val,fp⟩ =
      (LeanIsa.execute M ⟨gpow s.val,fp⟩ (instrAt T s) >>= fun x =>
        x.elim (pure none) fun next =>
          Option.map (LeanIsa.weight (instrAt T s).opcode + ·) <$>
            LeanIsa.runCost (program T) M n next) :=
  runCost_succ_of (program T) M n ⟨gpow s.val,fp⟩ _ (gpow_ne_finalPc T hs)
    (OptimalOTS.GenFast.Program.fetch_gpow (program T) s)

/-- This failure is an equality of oracle computations, so it also holds in
the cache-free support semantics used for the universal cycle bound. -/
theorem runCost_nonentry {κ : ℕ} (hκ : κ ≤ 32) (M : MemImage κ) (T : Tab)
    {f : ℕ} (hf : f < 14) {target : K}
    (hno : ∀ e, IsEntry f e → target ≠ gpow e) (n : ℕ) :
    LeanIsa.runCost (program T) M n ⟨target,incomingFrame T f target⟩ = pure none := by
  cases n with
  | zero =>
    rw [LeanIsa.runCost.eq_1]
    apply congrArg pure
    apply if_neg
    intro h
    have ht : target = gpow sentinel := h.1.trans (finalPc_eq T)
    have hn := AffineFrames.frame_halt_ne_one (layout T) ⟨stageIndex f,stageIndex_lt hf⟩
    apply hn
    simpa only [incomingFrame,ht,AffineFrames.frame,AffineFrames.bias,base,
      show 2 ^ 18 - 1 = sentinel by decide] using h.2
  | succ n =>
    rw [LeanIsa.runCost.eq_2]
    split_ifs with hfinal
    · rfl
    · split
      · rfl
      · rename_i ins hins
        obtain ⟨s,hs,rfl⟩ := (OptimalOTS.GenFast.Program.fetch_eq_some_iff (program T)).mp hins
        have he : ¬IsEntry f s.val := fun h => hno s.val h hs
        have hfail := execute_nonentry hκ M T hf s he
        have hfail' : LeanIsa.execute M ⟨target,incomingFrame T f target⟩ ((program T).code s) =
            pure none := by
          change target = gpow s.val at hs
          rw [hs]
          exact hfail
        rw [hfail',pure_bind]

/-- Existence of any completing continuation forces a valid stage entry. -/
theorem entry_of_completion {κ : ℕ} (hκ : κ ≤ 32) (M : MemImage κ) (T : Tab)
    (Sm : Sem) {f n c : ℕ} (hf : f < 14) {target : K}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨target,incomingFrame T f target⟩)) :
    ∃ x < Wf f, target = gpow (ent f x) := by
  by_contra hn
  have hno : ∀ e, IsEntry f e → target ≠ gpow e := by
    intro e he heq
    obtain ⟨_,x,hx,rfl⟩ := he
    exact hn ⟨x,hx,heq⟩
  rw [runCost_nonentry hκ M T hf hno] at h
  exact Sm.some_not_pure_none h

theorem runCost_zero_slot {κ : ℕ} (T : Tab) (M : MemImage κ) {s : ℕ}
    (hs : s < sentinel) (q : K) :
    LeanIsa.runCost (program T) M 0 ⟨gpow s,q⟩ = pure none := by
  rw [LeanIsa.runCost.eq_1,if_neg (fun h => gpow_ne_finalPc T hs h.1)]

/-- Completion requires a program address even after an exit resets the frame. -/
theorem runCost_pc_valid {κ : ℕ} (T : Tab) (M : MemImage κ) (Sm : Sem)
    {n c : ℕ} {r : Regs K}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n r)) :
    ∃ s : AffineFrames.Slot, r.pc = gpow s.val := by
  by_contra hn
  have hfinal : r.pc ≠ (program T).finalPc := fun he =>
    hn ⟨⟨sentinel,by decide⟩,he.trans (finalPc_eq T)⟩
  cases n with
  | zero =>
    rw [LeanIsa.runCost.eq_1,if_neg (fun he => hfinal he.1)] at h
    exact Sm.some_not_pure_none h
  | succ n =>
    have hfetch : (program T).fetch r.pc = none :=
      (program T).fetch_eq_none_iff.mpr (fun s hs => hn ⟨s,hs⟩)
    rw [LeanIsa.runCost.eq_2,if_neg hfinal,hfetch] at h
    exact Sm.some_not_pure_none h

theorem completion_at_sentinel {κ : ℕ} (T : Tab) (M : MemImage κ) (Sm : Sem)
    {n c : ℕ} (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow sentinel,1⟩)) :
    n = 0 ∧ c = 0 := by
  cases n with
  | zero =>
    rw [LeanIsa.runCost.eq_1,if_pos ⟨(finalPc_eq T).symm,rfl⟩,Sm.pure_iff] at h
    exact ⟨rfl,Option.some.inj h⟩
  | succ n =>
    rw [LeanIsa.runCost.eq_2,if_pos (finalPc_eq T).symm] at h
    exact (Sm.some_not_pure_none h).elim

end
end OptimalOTS.AffineVM
