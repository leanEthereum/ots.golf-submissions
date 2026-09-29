import Submissions.UpperLeanIsa.FreeLastDecode

/-! Length, straight instruction and list semantics for the free-last program. -/
namespace OptimalOTS.FreeLastVM
open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.HLG3 (natV cellBits_natV)
open OptimalOTS.FreeLastBase (base)
open OptimalOTS.FreeLastProgram (compile)
open OptimalOTS.AffineVM (HashSound)
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Init
def InitConstants (v : ℕ → E) : Prop :=
  ∀ c, 1 ≤ c → c ≤ 4 → v (cCell c) = ofK (base ^ c)

variable {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (L : MemImage κ) (pc : K)
include h16 hκ

theorem exec_init (hd : LengthDomain (Lx L)) (hp : InitConstants (Lx L)) :
    LeanIsa.execute L ⟨pc, 1⟩ (compile 1 .init) =
      pure (if Lx L oneCell = oneV ∧ Lx L lenCell = natV 5504
        then some ⟨g * pc, 1⟩ else none) := by
  rw [show compile 1 .init = CInstr.init.toInstr by simp only [compile,CInstr.toInstr,div_one]]
  obtain ⟨n, hn, hv, hz⟩ := hd
  have hnat : natV n = ofK (BitVec.ofNat 64 n) := OptimalOTS.HLG3.LengthGate128.natV_ofK hn
  have hk : IsInK (natV n) := by rw [hnat]; exact isInK_ofK _
  have hl : (natV n).limb 0 = BitVec.ofNat 64 n := by rw [hnat]; exact limb_ofK_zero _
  have heq : natV n = natV 5504 ↔ n = 5504 := by
    constructor
    · intro h
      have h' := congrArg (fun x => (LeanIsa.cellBits x).toNat) h
      simp only [cellBits_natV, BitVec.toNat_ofNat] at h'
      rw [Nat.mod_eq_of_lt (by omega)] at h'
      norm_num at h'
      exact h'
    · rintro rfl; rfl
  show pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
    (.deref (gpow lenCell) OptimalOTS.HLG3.LengthGate128.scale (gpow lenCell) .fp)) = _
  simp only [LeanerVM.Semantics.execute, read_one h16 hκ L (by decide : lenCell < 2^16),
    Option.bind_eq_bind, Option.bind_some, hv]
  rw [show (guard (IsInK (natV n)) : Option Unit) = some () from if_pos hk]
  simp only [Option.bind_some, hl]
  by_cases he : n = 5504
  · subst n
    rw [OptimalOTS.HLG3.LengthGate128.target_address,
      show L.read (gpow 48) = some (Lx L oneCell) from by
        change L.read (gpow oneCell) = some (Lx L oneCell)
        simpa only [one_mul] using read_one h16 hκ L (by decide : oneCell < 2^16)]
    simp only [Option.bind_some, LeanerVM.Semantics.derefSource, heq, and_true]
    exact congrArg pure (guard_some _)
  · have hrne := OptimalOTS.HLG3.LengthGate128.wrong_length_read_ne_one hκ hn he L
      (fun a ha => by
        have hb : ∀ p ∈ OptimalOTS.HLG3.LengthGate128.aliases, p.2 < 2^16 := by decide
        have hc : a < 2^κ := lt_of_lt_of_le (hb _ ha)
          (Nat.pow_le_pow_right (by norm_num) h16)
        rw [show L.read (gpow a) = some (Lx L a) from read_gpow_some hκ L
          (by rw [Nat.mod_eq_of_lt (by have := hb _ ha; unfold ordG; omega)]) hc]
        intro h
        have h1 : Lx L a = oneV := Option.some.inj h
        have cases_alias : ∀ p ∈ OptimalOTS.HLG3.LengthGate128.aliases,
            p ∈ OptimalOTS.HLG3.LengthGate128.lowAliases ∨
              ∃ c : Fin 4, p.2 = cCell (c.val + 1) := by decide
        rcases cases_alias _ ha with ha0 | ⟨c, hc⟩
        · rw [hz a ha0] at h1
          exact ofK_one_ne_zero h1.symm
        · change a = cCell (c.val + 1) at hc
          rw [hc, hp (c.val + 1) (by omega) (by omega)] at h1
          have hfac := ofK_injective h1
          change base ^ (c.val + 1) = base ^ 0 at hfac
          have := FreeLastBase.powers_injective (by omega) (by omega) hfac
          omega)
    cases hr : L.read ((BitVec.ofNat 64 n : K) * OptimalOTS.HLG3.LengthGate128.scale) with
    | none => simp [hr, heq, he]
    | some z =>
      have hz1 : z ≠ ofK 1 := by intro hh; exact hrne (hr.trans (congrArg some hh))
      simp only [Option.bind_some, LeanerVM.Semantics.derefSource]
      simp [heq, he]
      exact hz1

end Init

theorem finalPc_eq : (FreeLastBase.program).finalPc = gpow sentinel := by
  show gpow (2 ^ 18 - 1) = gpow 262143
  norm_num

theorem gpow_ne_finalPc {s : ℕ} (hs : s < sentinel) :
    gpow s ≠ (FreeLastBase.program).finalPc := by
  intro h
  have he := gpow_inj (show s < 2 ^ 64 - 1 by unfold sentinel at hs; omega)
    (show sentinel < 2 ^ 64 - 1 by unfold sentinel; norm_num) (h.trans (finalPc_eq))
  omega

theorem runCost_slot {κ : ℕ} (M : MemImage κ) (n : ℕ)
    (s : AffineFrames.Slot) (hs : s.val < sentinel) (fp : K) :
    LeanIsa.runCost (FreeLastBase.program) M (n+1) ⟨gpow s.val,fp⟩ =
      (LeanIsa.execute M ⟨gpow s.val,fp⟩ (FreeLastProgram.instruction base s.val) >>= fun x =>
        x.elim (pure none) fun next =>
          Option.map (LeanIsa.weight (FreeLastProgram.instruction base s.val).opcode + ·) <$>
            LeanIsa.runCost (FreeLastBase.program) M n next) :=
  runCost_succ_of (FreeLastBase.program) M n ⟨gpow s.val,fp⟩ _ (gpow_ne_finalPc hs)
    (OptimalOTS.GenFast.Program.fetch_gpow (FreeLastBase.program) s)

theorem runCost_zero_slot {κ : ℕ} (M : MemImage κ) {s : ℕ}
    (hs : s < sentinel) (q : K) :
    LeanIsa.runCost (FreeLastBase.program) M 0 ⟨gpow s,q⟩ = pure none := by
  rw [LeanIsa.runCost.eq_1,if_neg (fun h => gpow_ne_finalPc hs h.1)]

/-- Completion requires a program address even after an exit resets the frame. -/
theorem runCost_pc_valid {κ : ℕ} (M : MemImage κ) (Sm : Sem)
    {n c : ℕ} {r : Regs K}
    (h : some c ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n r)) :
    ∃ s : AffineFrames.Slot, r.pc = gpow s.val := by
  by_contra hn
  have hfinal : r.pc ≠ (FreeLastBase.program).finalPc := fun he =>
    hn ⟨⟨sentinel,by decide⟩,he.trans (finalPc_eq)⟩
  cases n with
  | zero =>
    rw [LeanIsa.runCost.eq_1,if_neg (fun he => hfinal he.1)] at h
    exact Sm.some_not_pure_none h
  | succ n =>
    have hfetch : (FreeLastBase.program).fetch r.pc = none :=
      (FreeLastBase.program).fetch_eq_none_iff.mpr (fun s hs => hn ⟨s,hs⟩)
    rw [LeanIsa.runCost.eq_2,if_neg hfinal,hfetch] at h
    exact Sm.some_not_pure_none h

theorem completion_at_sentinel {κ : ℕ} (M : MemImage κ) (Sm : Sem)
    {n c : ℕ} (h : some c ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n ⟨gpow sentinel,1⟩)) :
    n = 0 ∧ c = 0 := by
  cases n with
  | zero =>
    rw [LeanIsa.runCost.eq_1,if_pos ⟨(finalPc_eq).symm,rfl⟩,Sm.pure_iff] at h
    exact ⟨rfl,Option.some.inj h⟩
  | succ n =>
    rw [LeanIsa.runCost.eq_2,if_pos (finalPc_eq).symm] at h
    exact (Sm.some_not_pure_none h).elim

theorem straight_of_sem {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (M : MemImage κ)
    (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) (pc q : K) (hq : q ≠ 0) (ci : CInstr)
    (hb : ci.Bounded) (hs : ci.straight = true)
    (hinit : ci = .init → q = 1 ∧ InitConstants (Lx M))
    (x : Option (Regs K)) (hx : x ∈ Sm.S (LeanIsa.execute M ⟨pc,q⟩ (compile q ci))) :
    x = none ∨ (x = some ⟨g*pc,q⟩ ∧ ci.RelB B (Lx M)) := by
  cases ci with
  | init =>
    obtain ⟨rfl,hp⟩ := hinit rfl
    rw [exec_init h16 hκ M pc hd hp,Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx
  | xor a b c =>
    rw [show compile q (.xor a b c) = AffineVM.compile q (.xor a b c) from rfl,AffineVM.exec_xor h16 hκ M pc q hq hb,Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx
  | mul a b c =>
    rw [show compile q (.mul a b c) = AffineVM.compile q (.mul a b c) from rfl,AffineVM.exec_mul h16 hκ M pc q hq hb,Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx
  | setc a v =>
    rw [show compile q (.setc a v) = AffineVM.compile q (.setc a v) from rfl,AffineVM.exec_setc h16 hκ M pc q hq hb,Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx
  | blake m0 m1 m2 m3 cv out md =>
    rw [show compile q (.blake m0 m1 m2 m3 cv out md) = AffineVM.compile q (.blake m0 m1 m2 m3 cv out md) from rfl,AffineVM.exec_blake h16 hκ M pc q hq hb,Sm.bind_iff] at hx
    obtain ⟨ans,ha,hx⟩ := hx
    rw [Sm.pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hHash _ _ _ _ _ _ _ ha hr⟩
    · exact Or.inl hx
  | _ => simp [CInstr.straight] at hs

/-- A successful continuation through a consecutive list consumes exactly the
list length and cost and asserts every listed relation. -/
theorem run_list {κ : ℕ} (M : MemImage κ) (Sm : Sem) (B : BlakeRel)
    (q : K) {l : List CInstr} {t : ℕ}
    (hl : ∀ i (hi : i < l.length) (s : AffineFrames.Slot), s.val = t+i →
      FreeLastProgram.instruction base s.val = compile q l[i])
    (hst : ∀ ci ∈ l, ci.straight = true)
    (hbridge : ∀ ci ∈ l, ∀ pc x,
      x ∈ Sm.S (LeanIsa.execute M ⟨pc,q⟩ (compile q ci)) →
        x = none ∨ (x = some ⟨g*pc,q⟩ ∧ ci.RelB B (Lx M)))
    (hta : t+l.length ≤ sentinel) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n ⟨gpow t,q⟩)) :
    (∀ ci ∈ l, ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+l.length ∧ c = lcost l+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n' ⟨gpow (t+l.length),q⟩) := by
  induction l generalizing t n c with
  | nil =>
    exact ⟨fun ci hi => (List.not_mem_nil hi).elim,n,c,by simp,by simp [lcost],by simpa using h⟩
  | cons ci l ih =>
    have ht : t < sentinel := by simp only [List.length_cons] at hta; omega
    let s : AffineFrames.Slot := ⟨t,by unfold sentinel at ht; omega⟩
    have h0 : FreeLastProgram.instruction base s.val = compile q ci := by
      exact hl 0 (by simp) s (by simp [s])
    have hsci := hst ci List.mem_cons_self
    cases n with
    | zero =>
      rw [runCost_zero_slot M ht q] at h
      exact (Sm.some_not_pure_none h).elim
    | succ n =>
      rw [runCost_slot M n s ht q,h0,Sm.bind_iff] at h
      obtain ⟨x,hx,hc⟩ := h
      rcases hbridge ci List.mem_cons_self _ x hx with rfl | ⟨rfl,hR⟩
      · exact (Sm.some_not_pure_none hc).elim
      · rw [Option.elim_some,FreeLastProgram.compile_weight q hsci,g_mul_gpow] at hc
        obtain ⟨c1,hc1,hw⟩ := Sm.some_map_add hc
        have hl' : ∀ i (hi : i < l.length) (s : AffineFrames.Slot),
            s.val = t+1+i → FreeLastProgram.instruction base s.val = compile q l[i] := by
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
end OptimalOTS.FreeLastVM
