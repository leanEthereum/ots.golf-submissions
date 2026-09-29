import Submissions.UpperLeanIsa.FreeLastDecode
import Submissions.UpperLeanIsa.FreeLastExitData

/-! Read guards for the concrete free-last bytecode, including all admitted
committed-memory sizes. -/
namespace OptimalOTS.FreeLastGuard
open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.FreeLastLayout OptimalOTS.FreeLastBlocks OptimalOTS.FreeLastBase
open OptimalOTS.FreeLastSelect (Flow TargetSlot)
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def incoming (f : Flow) (s : Nat) : K :=
  base ^ FreeLastSelect.exponent f + FreeLastSelect.constant f s

def exitFlow : Flow := .inr (.inr ())
def stageFlow (u : Fin 13) : Flow := .inl u
def freeFlow (n : Fin 209) : Flow := .inr (.inl n)

theorem incoming_exit (s : Nat) : incoming exitFlow s = 1 := by
  simp [incoming, exitFlow, FreeLastSelect.exponent, FreeLastSelect.constant]

theorem group_descriptor {s u v : Nat} {z : Bool} (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .group u v z) :
    layout.target (.inl ⟨s,by omega⟩) =
      ⟨if u < 12 then (u+1 : Nat) else 0,
        if u < 12 then gpow (candidateTree.lookup s).entry
        else gpow (candidateTree.lookup s).entry+AffineFrames.lengthK-1,
        bodyCell (candidateTree.lookup s) s⟩ := by
  simp only [FreeLastSelect.Layout.target,layout,groupTarget,show ¬s < 27 by omega,if_false,hb]
  split_ifs <;> rfl

theorem group_frame {s u v : Nat} {z : Bool} (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .group u v z) :
    base ^ (layout.target (.inl ⟨s,by omega⟩)).exponent +
      (layout.target (.inl ⟨s,by omega⟩)).constant =
        FreeLastProgram.frame base (candidateTree.lookup s) := by
  have hu := (candidate_lookup_good hs hs').1.2
  simp only [hb] at hu
  rw [group_descriptor hs hs' hb]
  by_cases hp : u < 12
  · simp only [if_pos hp,zpow_natCast,FreeLastProgram.frame,hb,show u ≠ 12 by omega,
      if_false,add_comm]
  · have he : u = 12 := by omega
    subst u
    simp only [show ¬(12 : Nat) < 12 by decide,if_false,zpow_zero,FreeLastProgram.frame,hb,if_true,AffineFrames.lengthK]
    exact (add_comm _ _).trans (sub_add_cancel _ _)

theorem free_descriptor {s n : Nat} (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .free n) :
    ∃ t : FreeLastSelect.FreeSlot, FreeLastSelect.address (.inr t) = s ∧
      layout.target (.inr t) =
        ⟨-(n : Int),gpow (candidateTree.lookup s).entry,bodyCell (candidateTree.lookup s) s⟩ := by
  obtain ⟨hg,he,_⟩ := candidate_lookup_good hs hs'
  have hh := hg.2
  simp only [hb] at hh
  have hlo : 260064 ≤ s := by omega
  refine ⟨⟨s-260064,by omega⟩,by dsimp [FreeLastSelect.address]; omega,?_⟩
  simp only [FreeLastSelect.Layout.target,layout,freeTarget,
    show 260064+(s-260064) = s by omega,hb,if_pos hh.2.1]

theorem free_frame {s n : Nat} (hb : (candidateTree.lookup s).body = .free n) :
    base ^ (-(n : Int)) + gpow (candidateTree.lookup s).entry =
      FreeLastProgram.frame base (candidateTree.lookup s) := by
  rw [zpow_neg,zpow_natCast,FreeLastProgram.frame,hb,add_comm]

/-- A successful primitive must have an addressable first operand. -/
theorem first_read {κ : Nat} (hκ : κ ≤ 32) (M : MemImage κ) (Sm : Sem)
    {r r' : Regs K} {i : Instr}
    (h : some r' ∈ Sm.S (LeanIsa.execute M r i)) :
    ∃ j : FreeLastSelect.MaxCell, r.fp * AffineFrames.firstOperand i = gpow j.val := by
  by_contra hn
  have hr : M.read (r.fp * AffineFrames.firstOperand i) = none := by
    apply (MemImage.read_eq_none_iff M).mpr
    intro j hj
    exact hn ⟨⟨j.val,lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by decide) hκ)⟩,hj⟩
  rw [AffineFrames.execute_none_of_first M r i hr] at h
  rw [Sm.pure_iff] at h
  exact Option.some_ne_none _ h

theorem no_zero_read {f : Flow} {s j : Nat} : incoming f s * 0 ≠ gpow j := by
  rw [mul_zero]
  exact (pow_ne_zero _ g_ne_zero).symm

/-- A nonconstant comparison fixes the exact exponent and block constant. -/
theorem group_read_exact {f : Flow} {s u v : Nat} {z : Bool}
    (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .group u v z)
    (hn : FreeLastSelect.exponent f ≠ 0 ∨ u < 12)
    (j : FreeLastSelect.MaxCell)
    (hr : incoming f s * AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val) :
    FreeLastSelect.exponent f = (if u < 12 then ((u+1 : Nat) : Int) else 0) ∧
      FreeLastSelect.constant f s =
        (if u < 12 then gpow (candidateTree.lookup s).entry
        else gpow (candidateTree.lookup s).entry+AffineFrames.lengthK-1) := by
  have hnt : (candidateTree.lookup s).body ≠ .trap := by rw [hb]; intro h; cases h
  rcases FreeLastDecode.instruction_first base hs hs' hnt with hz | hf
  · rw [hz] at hr
    exact (no_zero_read hr).elim
  · have hd := group_descriptor hs hs' hb
    have hframe := group_frame hs hs' hb
    have hn' : FreeLastSelect.exponent f ≠ 0 ∨
        (layout.target (.inl ⟨s,by omega⟩)).exponent ≠ 0 := by
      rcases hn with hn | hn
      · exact Or.inl hn
      · right; rw [hd]; simp only [if_pos hn]; omega
    have hread :
        (FreeLastSelect.base layout ^ FreeLastSelect.exponent f +
          FreeLastSelect.constant f (FreeLastSelect.address (.inl ⟨s,by omega⟩))) *
        (gpow (layout.target (.inl ⟨s,by omega⟩)).firstCell /
          (FreeLastSelect.base layout ^ (layout.target (.inl ⟨s,by omega⟩)).exponent +
            (layout.target (.inl ⟨s,by omega⟩)).constant)) = gpow j.val := by
      change incoming f s * (gpow (layout.target (.inl ⟨s,by omega⟩)).firstCell /
        (base ^ (layout.target (.inl ⟨s,by omega⟩)).exponent +
          (layout.target (.inl ⟨s,by omega⟩)).constant)) = gpow j.val
      rw [hframe,hd]
      rwa [hf] at hr
    have hdne : FreeLastSelect.base layout ^ (layout.target (.inl ⟨s,by omega⟩)).exponent +
        (layout.target (.inl ⟨s,by omega⟩)).constant ≠ 0 := by
      change base ^ _ + _ ≠ 0
      rw [hframe]
      exact group_frame_nonzero hs hs' hb
    have h := FreeLastSelect.read_exact layout f (.inl ⟨s,by omega⟩) j hn' hdne hread
    rw [hd] at h
    exact ⟨h.1,h.2.2⟩

theorem free_read_exact {f : Flow} {s n : Nat} (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .free n) (j : FreeLastSelect.MaxCell)
    (hr : incoming f s * AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val) :
    FreeLastSelect.exponent f = -(n : Int) ∧
      FreeLastSelect.constant f s = gpow (candidateTree.lookup s).entry := by
  obtain ⟨hg,_,_⟩ := candidate_lookup_good hs hs'
  have hgood := hg.2
  simp only [hb] at hgood
  have hnt : (candidateTree.lookup s).body ≠ .trap := by rw [hb]; intro h; cases h
  rcases FreeLastDecode.instruction_first base hs hs' hnt with hz | hf
  · rw [hz] at hr
    exact (no_zero_read hr).elim
  · obtain ⟨t,ht,hd⟩ := free_descriptor hs hs' hb
    have hn : FreeLastSelect.exponent f ≠ 0 ∨ (layout.target (.inr t)).exponent ≠ 0 := by
      right; rw [hd]; simp only; omega
    have hframe : base ^ (layout.target (.inr t)).exponent +
        (layout.target (.inr t)).constant = FreeLastProgram.frame base (candidateTree.lookup s) := by
      rw [hd]; exact free_frame hb
    have hdne : FreeLastSelect.base layout ^ (layout.target (.inr t)).exponent +
        (layout.target (.inr t)).constant ≠ 0 := by
      change base ^ _ + _ ≠ 0
      rw [hframe]
      exact free_frame_nonzero hs hs' hb
    have hread :
        (FreeLastSelect.base layout ^ FreeLastSelect.exponent f +
          FreeLastSelect.constant f (FreeLastSelect.address (.inr t))) *
        (gpow (layout.target (.inr t)).firstCell /
          (FreeLastSelect.base layout ^ (layout.target (.inr t)).exponent +
            (layout.target (.inr t)).constant)) = gpow j.val := by
      change (base ^ FreeLastSelect.exponent f + FreeLastSelect.constant f _) *
        (gpow (layout.target (.inr t)).firstCell /
          (base ^ (layout.target (.inr t)).exponent + (layout.target (.inr t)).constant)) = gpow j.val
      rw [ht,hframe,hd]
      rwa [hf] at hr
    have h := FreeLastSelect.read_exact layout f (.inr t) j hn hdne hread
    rw [hd,ht] at h
    exact ⟨h.1,h.2.2⟩

theorem trap_first {s : Nat} (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .trap) :
    AffineFrames.firstOperand (FreeLastProgram.instruction base s) = 0 := by
  simp only [FreeLastProgram.instruction,show ¬s < 27 by omega,if_false,hs',if_true,
    FreeLastProgram.body,hb,List.length_nil,Nat.not_lt_zero]
  split_ifs <;> simp only [FreeLastProgram.control,hb,AffineFrames.firstOperand]

theorem initial_first {s : Nat} (hs : s < 17) :
    AffineFrames.firstOperand (FreeLastProgram.instruction base s) =
      gpow (groupTarget ⟨s,by omega⟩).firstCell := by
  simp only [FreeLastProgram.instruction,show s < 27 by omega,if_true,groupTarget]
  interval_cases s <;>
    simp [FreeLastProgram.initial,FreeLastBlocks.prologue,FreeLastProgram.compile,FreeLastProgram.jump,
      AffineFrames.firstOperand,cell0]
  all_goals exact div_one _

theorem initial_cell_bound {s : Nat} (hs : s < 17) :
    (groupTarget ⟨s,by omega⟩).firstCell < 2^16 := by
  simp only [groupTarget,show s < 27 by omega,if_true]
  interval_cases s <;> decide

theorem initial_trap {s : Nat} (hs : 17 ≤ s) (hs' : s < 27) :
    AffineFrames.firstOperand (FreeLastProgram.instruction base s) = 0 := by
  interval_cases s <;> rfl


theorem initial_nonconstant {f : Flow} {s : Nat} (hs : s < 17)
    (hn : FreeLastSelect.exponent f ≠ 0) (j : FreeLastSelect.MaxCell)
    (hr : incoming f s * AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val) : False := by
  have hd : layout.target (.inl ⟨s,by omega⟩) =
      ⟨0,0,(groupTarget ⟨s,by omega⟩).firstCell⟩ := by
    simp only [FreeLastSelect.Layout.target,layout,groupTarget,show s < 27 by omega,if_true]
  have hne : FreeLastSelect.base layout ^ (layout.target (.inl ⟨s,by omega⟩)).exponent +
      (layout.target (.inl ⟨s,by omega⟩)).constant ≠ 0 := by
    rw [hd]; simp only [zpow_zero,add_zero,ne_eq,one_ne_zero,not_false_eq_true]
  have hh :
      (FreeLastSelect.base layout ^ FreeLastSelect.exponent f +
        FreeLastSelect.constant f (FreeLastSelect.address (.inl ⟨s,by omega⟩))) *
      (gpow (layout.target (.inl ⟨s,by omega⟩)).firstCell /
        (FreeLastSelect.base layout ^ (layout.target (.inl ⟨s,by omega⟩)).exponent +
          (layout.target (.inl ⟨s,by omega⟩)).constant)) = gpow j.val := by
    rw [hd]
    simp only [zpow_zero,add_zero,div_one]
    rwa [initial_first hs] at hr
  have h := FreeLastSelect.read_exact layout f (.inl ⟨s,by omega⟩) j (Or.inl hn) hne hh
  rw [hd] at h
  exact hn h.1

theorem initial_read {f : Flow} {s : Nat} (hs : s < 17) (j : FreeLastSelect.MaxCell)
    (hr : incoming f s * AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val) :
    f = exitFlow := by
  have hn : FreeLastSelect.exponent f = 0 := by
    by_contra hn; exact initial_nonconstant hs hn j hr
  rw [initial_first hs] at hr
  have hc := initial_cell_bound hs
  rcases f with u | n | t
  · by_cases hu : u.val < 12
    · simp only [FreeLastSelect.exponent,if_pos hu] at hn; omega
    · have he : incoming (.inl u) s = gpow s+LengthFrameChecks.lengthBias := by
        simp only [incoming,FreeLastSelect.exponent,FreeLastSelect.constant,if_neg hu,zpow_zero]
        change 1+(AffineFrames.lengthK+gpow s-1) = gpow s+AffineFrames.lengthK
        rw [add_comm (1 : K),sub_add_cancel,add_comm]
      rw [he] at hr
      exact (LengthFrameChecks.length_initial_address_ne (by omega) hc j.isLt hr).elim
  · have he : incoming (.inr (.inl n)) s = gpow s+1 := by
      change base ^ FreeLastSelect.exponent (.inr (.inl n)) + gpow s = _
      rw [hn,zpow_zero,add_comm]
    rw [he] at hr
    exact (LengthFrameChecks.one_initial_address_ne (by omega) hc j.isLt hr).elim
  · cases t; rfl

/-- The preserved group-12 intervals use the existing finite guard. -/
theorem length_read {s v b : Nat} {z : Bool} (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .group 12 v z)
    (hbias : b = 1 ∨ b = 5504) (j : FreeLastSelect.MaxCell)
    (hr : (gpow s+(BitVec.ofNat 64 b : K)) *
      AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val) :
    s = (candidateTree.lookup s).entry ∧ b = 5504 := by
  obtain ⟨hg,he,hl⟩ := candidate_lookup_good hs hs'
  have hgood := hg.2
  simp only [hb] at hgood
  have hv : v < 1024 := hgood.2.1
  obtain ⟨hre,hrl⟩ := hgood.2.2.2.2.1 (Or.inr trivial)
  have hnt : (candidateTree.lookup s).body ≠ .trap := by rw [hb]; intro h; cases h
  rcases FreeLastDecode.instruction_first base hs hs' hnt with hz | hf
  · rw [hz,mul_zero] at hr
    exact ((pow_ne_zero _ g_ne_zero) hr.symm).elim
  · by_contra hn
    have hce : LengthFrameChecks.certEntry v = (candidateTree.lookup s).entry := by
      rw [LengthFrameChecks.certEntry,if_pos hv]; exact hre.symm
    have hcl : LengthFrameChecks.certLength v = (candidateTree.lookup s).length := by
      rw [LengthFrameChecks.certLength,if_pos hv]; exact hrl.symm
    have hcb : LengthFrameChecks.certBias v = 5504 := if_pos hv
    have hi : s-(candidateTree.lookup s).entry < LengthFrameChecks.certLength v := by
      rw [hcl]; omega
    have hs0 : LengthFrameChecks.certEntry v+(s-(candidateTree.lookup s).entry) = s := by
      rw [hce]; omega
    have hwrong : ¬(LengthFrameChecks.certEntry v+(s-(candidateTree.lookup s).entry) =
        LengthFrameChecks.certEntry v ∧ b = LengthFrameChecks.certBias v) := by
      rwa [hs0,hce,hcb]
    have hne : gpow (LengthFrameChecks.certEntry v)+(BitVec.ofNat 64 (LengthFrameChecks.certBias v) : K) ≠ 0 := by
      rw [hce,hcb]
      exact LengthFrameChecks.length_frame_ne_zero (by omega)
    have hh := LengthFrameChecks.block_address_ne (by omega : v < 1088) hi hbias hwrong hne
      (FreeLastDecode.bodyCell_bounded hs hs') j.isLt
    rw [hs0,hce,hcb] at hh
    apply hh
    rw [hf] at hr
    simp only [FreeLastProgram.frame,hb,if_true] at hr
    exact hr

theorem group_entry_of_constant {s : Nat} (hs : s < 262143)
    (h : gpow s = gpow (candidateTree.lookup s).entry)
    (hb : 27 ≤ s) : s = (candidateTree.lookup s).entry := by
  have he := (candidate_lookup_good hb hs).2.1
  exact gpow_inj (by omega) (by omega) h

/-- A stage dispatch can execute only at an entry of that same group. -/
theorem stage_read {s : Nat} (hs : s < 262143) (u : Fin 13) (j : FreeLastSelect.MaxCell)
    (hr : incoming (stageFlow u) s * AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val) :
    ∃ v z, (candidateTree.lookup s).body = .group u.val v z ∧
      s = (candidateTree.lookup s).entry := by
  by_cases hi : s < 17
  · have h := initial_read hi j hr
    cases h
  by_cases hlo : s < 27
  · rw [initial_trap (by omega) hlo] at hr
    exact (no_zero_read hr).elim
  have h27 : 27 ≤ s := by omega
  obtain ⟨hg,he,hl⟩ := candidate_lookup_good h27 hs
  cases hb : (candidateTree.lookup s).body with
  | trap =>
    rw [trap_first h27 hs hb] at hr
    exact (no_zero_read hr).elim
  | free n =>
    have hh := free_read_exact h27 hs hb j hr
    have hn := hg.2
    simp only [hb] at hn
    simp only [stageFlow,FreeLastSelect.exponent] at hh
    split_ifs at hh <;> omega
  | group w v z =>
    have hw := hg.2
    simp only [hb] at hw
    by_cases hu : u.val < 12
    · have hn : FreeLastSelect.exponent (stageFlow u) ≠ 0 := by
        simp only [stageFlow,FreeLastSelect.exponent,if_pos hu]; omega
      obtain ⟨hx,hc⟩ := group_read_exact h27 hs hb (Or.inl hn) j hr
      simp only [stageFlow,FreeLastSelect.exponent,if_pos hu,FreeLastSelect.constant] at hx hc
      by_cases hw12 : w < 12
      · rw [if_pos hw12] at hx hc
        have hew : u.val = w := by omega
        rw [← hew] at hb
        exact ⟨v,z,by rw [hew],group_entry_of_constant hs hc h27⟩
      · rw [if_neg hw12] at hx; omega
    · have hu12 : u.val = 12 := by have := u.isLt; omega
      by_cases hw12 : w < 12
      · have hx := (group_read_exact h27 hs hb (Or.inr hw12) j hr).1
        simp only [stageFlow,FreeLastSelect.exponent,if_neg hu,if_pos hw12] at hx
        omega
      · have hew : w = 12 := by omega
        subst w
        have hin : incoming (stageFlow u) s = gpow s+(BitVec.ofNat 64 5504 : K) := by
          simp only [incoming,stageFlow,FreeLastSelect.exponent,FreeLastSelect.constant,if_neg hu,zpow_zero]
          exact (add_comm _ _).trans ((sub_add_cancel _ _).trans (add_comm _ _))
        rw [hin] at hr
        have he := (length_read h27 hs hb (Or.inr rfl) j hr).1
        rw [hu12]
        exact ⟨v,z,rfl,he⟩


/-- A free dispatch has either its negative-exponent free entry or an entry
of an earlier positive group. The path proof excludes the latter by no-return. -/
theorem free_read {s : Nat} (hs : s < 262143) (n : Fin 209) (j : FreeLastSelect.MaxCell)
    (hr : incoming (freeFlow n) s * AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val) :
    (∃ u v z, u < 12 ∧ (n.val : Int)-77 = (u+1 : Nat) ∧
      (candidateTree.lookup s).body = .group u v z ∧ s = (candidateTree.lookup s).entry) ∨
    (∃ k : Nat, (n.val : Int)-77 = -(k : Int) ∧
      (candidateTree.lookup s).body = .free k ∧ s = (candidateTree.lookup s).entry) := by
  by_cases hi : s < 17
  · have h := initial_read hi j hr
    cases h
  by_cases hlo : s < 27
  · rw [initial_trap (by omega) hlo] at hr
    exact (no_zero_read hr).elim
  have h27 : 27 ≤ s := by omega
  obtain ⟨hg,he,hl⟩ := candidate_lookup_good h27 hs
  cases hb : (candidateTree.lookup s).body with
  | trap =>
    rw [trap_first h27 hs hb] at hr
    exact (no_zero_read hr).elim
  | free k =>
    obtain ⟨hx,hc⟩ := free_read_exact h27 hs hb j hr
    exact Or.inr ⟨k,hx,rfl,group_entry_of_constant hs hc h27⟩
  | group u v z =>
    have hu := hg.2
    simp only [hb] at hu
    by_cases hpos : u < 12
    · obtain ⟨hx,hc⟩ := group_read_exact h27 hs hb (Or.inr hpos) j hr
      simp only [if_pos hpos] at hx hc
      exact Or.inl ⟨u,v,z,hpos,hx,rfl,group_entry_of_constant hs hc h27⟩
    · have hu12 : u = 12 := by omega
      subst u
      by_cases hn : FreeLastSelect.exponent (freeFlow n) = 0
      · have hin : incoming (freeFlow n) s = gpow s+(BitVec.ofNat 64 1 : K) := by
          change base ^ FreeLastSelect.exponent (freeFlow n) + gpow s = _
          rw [hn,zpow_zero,add_comm]; rfl
        rw [hin] at hr
        have hh := (length_read h27 hs hb (Or.inl rfl) j hr).2
        omega
      · have hx := (group_read_exact h27 hs hb (Or.inl hn) j hr).1
        simp only [show ¬(12 : Nat) < 12 by decide,if_false] at hx
        exact (hn hx).elim

/-- Resetting fp to ONE can execute only in the initial prologue. -/
theorem exit_read {s : Nat} (hs : s < 262143) (j : FreeLastSelect.MaxCell)
    (hr : incoming exitFlow s * AffineFrames.firstOperand (FreeLastProgram.instruction base s) = gpow j.val) :
    s < 17 := by
  by_contra hi
  by_cases hlo : s < 27
  · rw [initial_trap (by omega) hlo] at hr
    exact no_zero_read hr
  have h27 : 27 ≤ s := by omega
  obtain ⟨hg,he,hl⟩ := candidate_lookup_good h27 hs
  cases hb : (candidateTree.lookup s).body with
  | trap =>
    rw [trap_first h27 hs hb] at hr
    exact no_zero_read hr
  | free k =>
    have hx := (free_read_exact h27 hs hb j hr).1
    have hk := hg.2
    simp only [hb] at hk
    change (0 : Int) = -(k : Int) at hx
    omega
  | group u v z =>
    have hu := hg.2
    simp only [hb] at hu
    by_cases hpos : u < 12
    · have hx := (group_read_exact h27 hs hb (Or.inr hpos) j hr).1
      simp only [exitFlow,FreeLastSelect.exponent,if_pos hpos] at hx
      omega
    · have hu12 : u = 12 := by omega
      subst u
      have hv : v < 1024 := hu.2.1
      have he0 := (hu.2.2.2.2.1 (by simp)).1
      have hnt : (candidateTree.lookup s).body ≠ .trap := by rw [hb]; intro h; cases h
      rcases FreeLastDecode.instruction_first base h27 hs hnt with hz | hf
      · rw [hz] at hr
        exact no_zero_read hr
      · rw [incoming_exit,hf,one_mul] at hr
        simp only [FreeLastProgram.frame,hb,if_true] at hr
        rw [he0] at hr
        exact FreeLastExitData.exit_address_ne hv (by omega)
          (FreeLastDecode.bodyCell_bounded h27 hs) j.isLt hr

theorem incoming_halt_nonconstant (f : Flow) (hn : FreeLastSelect.exponent f ≠ 0) :
    incoming f 262143 ≠ 1 := by
  have hp : FreeLastSelect.haltPoly f ≠ 0 :=
    FreeLastSelect.framePoly_ne_zero
      ⟨FreeLastSelect.exponent f,FreeLastSelect.constant f 262143-1,0⟩ hn
  have ha := FreeLastPolys.of_guard_eval hp
    (FreeLastSelect.avoids layout (.inr (.inr (.inl f))))
  change (FreeLastSelect.haltPoly f).eval (FreeLastSelect.base layout) ≠ 0 at ha
  rw [FreeLastSelect.haltPoly,FreeLastPolys.collision_eval (FreeLastSelect.base_ne_zero layout)] at ha
  simp only [one_mul,zero_mul,sub_zero] at ha
  intro he
  apply ha
  change (base ^ FreeLastSelect.exponent f + (FreeLastSelect.constant f 262143-1)) * _ = 0
  rw [← add_sub_assoc,show base ^ FreeLastSelect.exponent f+FreeLastSelect.constant f 262143 = 1 from he,
    sub_self,zero_mul]

theorem stage_halt (u : Fin 13) : incoming (stageFlow u) 262143 ≠ 1 := by
  by_cases hu : u.val < 12
  · apply incoming_halt_nonconstant
    simp only [stageFlow,FreeLastSelect.exponent,if_pos hu]; omega
  · have he : incoming (stageFlow u) 262143 = gpow 262143+LengthFrameChecks.lengthBias := by
      simp only [incoming,stageFlow,FreeLastSelect.exponent,FreeLastSelect.constant,if_neg hu,zpow_zero]
      exact (add_comm _ _).trans ((sub_add_cancel _ _).trans (add_comm _ _))
    rw [he]
    exact LengthFrameChecks.length_halt_ne_one

theorem free_halt (n : Fin 209) : incoming (freeFlow n) 262143 ≠ 1 := by
  by_cases hn : FreeLastSelect.exponent (freeFlow n) = 0
  · change base ^ FreeLastSelect.exponent (freeFlow n) + gpow 262143 ≠ 1
    rw [hn,zpow_zero,add_comm]
    exact FixedFrameChecks.fixed_halt_ne_one
  · exact incoming_halt_nonconstant _ hn

end
end OptimalOTS.FreeLastGuard
