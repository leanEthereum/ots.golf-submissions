import Submissions.UpperLeanIsa.AffineRun

/-! Straight block execution preserves its affine frame and exposes exactly
the cell relations and instruction costs used by the path proof. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.HLG3 (HashTable fixed_hash)
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def HashSound (Sm : Sem) (B : BlakeRel) : Prop :=
  ∀ m cv0 cv1 o0 o1 md ans,
    ans ∈ Sm.S (hash (LeanIsa.blake2sQuery m cv0 cv1 md)) →
    LeanIsa.OracleCompressCells m cv0 cv1 o0 o1 md ans → B m cv0 cv1 o0 o1 md

theorem hashSound_sim (f : HashTable) : HashSound (simSem f) (oracleRel f) := by
  intro m cv0 cv1 o0 o1 md ans ha hr
  change ans ∈ support (simulateQ (unifFwdAnswerImpl f) _) at ha
  rw [fixed_hash,mem_support_pure_iff] at ha
  subst ans
  exact hr

theorem hashSound_supp : HashSound suppSem trueRel := by
  intro m cv0 cv1 o0 o1 md ans ha hr
  trivial

theorem straight_of_sem {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (M : MemImage κ)
    (T : Tab) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) (pc q : K) (hq : q ≠ 0) (ci : CInstr)
    (hb : ci.Bounded) (hs : ci.straight = true)
    (hinit : ci = .init → q = 1 ∧ InitConstants T (Lx M))
    (x : Option (Regs K)) (hx : x ∈ Sm.S (LeanIsa.execute M ⟨pc,q⟩ (compile q ci))) :
    x = none ∨ (x = some ⟨g*pc,q⟩ ∧ ci.RelB B (Lx M)) := by
  cases ci with
  | init =>
    obtain ⟨rfl,hp⟩ := hinit rfl
    rw [exec_init h16 hκ M pc T hd hp,Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx
  | xor a b c =>
    rw [exec_xor h16 hκ M pc q hq hb,Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx
  | mul a b c =>
    rw [exec_mul h16 hκ M pc q hq hb,Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx
  | setc a v =>
    rw [exec_setc h16 hκ M pc q hq hb,Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx
  | blake m0 m1 m2 m3 cv out md =>
    rw [exec_blake h16 hκ M pc q hq hb,Sm.bind_iff] at hx
    obtain ⟨ans,ha,hx⟩ := hx
    rw [Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hHash _ _ _ _ _ _ _ ha hr⟩
    · exact Or.inl hx
  | _ => simp [CInstr.straight] at hs

/-- A successful continuation through a consecutive list consumes exactly the
list length and cost and asserts every listed relation. -/
theorem run_list {κ : ℕ} (T : Tab) (M : MemImage κ) (Sm : Sem) (B : BlakeRel)
    (q : K) {l : List CInstr} {t : ℕ}
    (hl : ∀ i (hi : i < l.length) (s : AffineFrames.Slot), s.val = t+i →
      instrAt T s = compile q l[i])
    (hst : ∀ ci ∈ l, ci.straight = true)
    (hbridge : ∀ ci ∈ l, ∀ pc x,
      x ∈ Sm.S (LeanIsa.execute M ⟨pc,q⟩ (compile q ci)) →
        x = none ∨ (x = some ⟨g*pc,q⟩ ∧ ci.RelB B (Lx M)))
    (hta : t+l.length ≤ sentinel) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow t,q⟩)) :
    (∀ ci ∈ l, ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+l.length ∧ c = lcost l+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (program T) M n' ⟨gpow (t+l.length),q⟩) := by
  induction l generalizing t n c with
  | nil =>
    exact ⟨fun ci hi => (List.not_mem_nil hi).elim,n,c,by simp,by simp [lcost],by simpa using h⟩
  | cons ci l ih =>
    have ht : t < sentinel := by simp only [List.length_cons] at hta; omega
    let s : AffineFrames.Slot := ⟨t,by unfold sentinel at ht; omega⟩
    have h0 : instrAt T s = compile q ci := by
      exact hl 0 (by simp) s (by simp [s])
    have hsci := hst ci List.mem_cons_self
    cases n with
    | zero =>
      rw [runCost_zero_slot T M ht q] at h
      exact (Sm.some_not_pure_none h).elim
    | succ n =>
      rw [runCost_slot T M n s ht q,h0,Sm.bind_iff] at h
      obtain ⟨x,hx,hc⟩ := h
      rcases hbridge ci List.mem_cons_self _ x hx with rfl | ⟨rfl,hR⟩
      · exact (Sm.some_not_pure_none hc).elim
      · rw [Option.elim_some,compile_straight_weight q ci hsci,g_mul_gpow] at hc
        obtain ⟨c1,hc1,hw⟩ := Sm.some_map_add hc
        have hl' : ∀ i (hi : i < l.length) (s : AffineFrames.Slot),
            s.val = t+1+i → instrAt T s = compile q l[i] := by
          intro i hi s hs
          exact hl (i+1) (by simp; omega) s (by omega)
        obtain ⟨hRs,n2,c2,hn2,hc2,hw2⟩ := ih hl'
          (fun y hy => hst y (List.mem_cons_of_mem _ hy))
          (fun y hy => hbridge y (List.mem_cons_of_mem _ hy)) (by simp only [List.length_cons] at hta; omega) hw
        refine ⟨?_,n2,c2,?_,?_,?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hR
          · exact hRs y hy
        · rw [hn2,List.length_cons]; omega
        · rw [hc1,hc2,lcost_cons]; omega
        · rw [show t+(ci::l).length = t+1+l.length by simp only [List.length_cons]; omega]
          exact hw2

end
end OptimalOTS.AffineVM
