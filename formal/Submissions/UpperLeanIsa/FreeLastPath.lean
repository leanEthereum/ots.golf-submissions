import Submissions.UpperLeanIsa.FreeLastChecksum

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

theorem unit_inverse {u : Nat} (hu : u < 13) : unit (FreeLastBlocks.position u) = u := by
  interval_cases u <;> rfl

theorem position_lt {u : Nat} (hu : u < 13) : FreeLastBlocks.position u < 13 := by
  unfold FreeLastBlocks.position; split_ifs <;> omega

theorem position_lt12 {u : Nat} (hu : u < 13) (hn : u ≠ 1) : FreeLastBlocks.position u < 12 := by
  unfold FreeLastBlocks.position; split_ifs <;> omega

def earlier {κ : Nat} (M : MemImage κ) (Sm : Sem) (k n : Nat) : Prop :=
  ∀ j < k, ∃ nj cj, n < nj ∧
    some cj ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M nj (groupRegs (Lx M) (unit j)))

def prefixSteps (mem : Nat → E) (k : Nat) : Nat :=
  ∑ j ∈ Finset.range k, ((FreeLastBlocks.normal (unit j) (rawOf mem (unit j))).length+1)

def prefixCycles (mem : Nat → E) (k : Nat) : Nat :=
  ∑ j ∈ Finset.range k, (lcost (FreeLastBlocks.normal (unit j) (rawOf mem (unit j)))+1)

/-- The twelve preceding groups must run in the specified order. The retained
continuations are used to exclude re-entry from the final free dispatch. -/
theorem run_groups {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) (hp : ∀ ci ∈ prefixCode 16, ci.RelB B (Lx M))
    (hK : IsInK (Lx M (hCell 1)))
    {n c : Nat} (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n (groupRegs (Lx M) 0))) :
    ∀ k ≤ 12,
      (∀ j < k, rawOf (Lx M) (unit j) < VF (unit j) ∧ zeroOf (Lx M) (unit j) = false ∧
        GroupLanding (Lx M) (unit j) (rawOf (Lx M) (unit j)) false ∧
        ∀ ci ∈ FreeLastBlocks.normal (unit j) (rawOf (Lx M) (unit j)), ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+prefixSteps (Lx M) k ∧ c = prefixCycles (Lx M) k+c' ∧
        earlier M Sm k n' ∧ Hint (Lx M) (unit k) ∧ IsInK (Lx M (hCell (unit k+1))) ∧
        some c' ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n' (groupRegs (Lx M) (unit k))) := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact ⟨fun j hj => by omega,n,c,by simp [prefixSteps],by simp [prefixCycles],
      (fun j hj => by omega),pro_hint hp,hK,h⟩
  | succ k ih =>
    intro hk
    obtain ⟨hprev,n1,c1,hn1,hc1,hseen,hhint,hK1,hr1⟩ := ih (by omega)
    have hk12 : k < 12 := by omega
    have hu := unit_lt (by omega : k < 13)
    have hnu := unit_ne_one hk12
    obtain ⟨hv,hz,hb,hland,hK2,n2,c2,hn2,hc2,hr2⟩ := run_group h16 hκ M Sm B hHash hd hp hu hhint hK1 hr1
    have hzf : zeroOf (Lx M) (unit k) = false := by
      cases he : zeroOf (Lx M) (unit k) with
      | false => rfl
      | true => exact (hnu (hz he)).elim
    simp only [hzf,groupBody,Bool.false_eq_true,if_false] at hb hn2 hc2 hr2 hland hK2
    rw [after_normal hnu,unit_next hk12] at hr2
    refine ⟨?_,n2,c2,?_,?_,?_,?_,?_,hr2⟩
    · intro j hj
      by_cases hjk : j < k
      · exact hprev j hjk
      · have he : j = k := by omega
        subst j
        exact ⟨hv,hzf,hland,hb⟩
    · rw [hn1,hn2]
      simp only [prefixSteps,Finset.sum_range_succ]
      omega
    · rw [hc1,hc2]
      simp only [prefixCycles,Finset.sum_range_succ]
      omega
    · intro j hj
      by_cases hjk : j < k
      · obtain ⟨nj,cj,hj,hrj⟩ := hseen j hjk
        exact ⟨nj,cj,by omega,hrj⟩
      · have he : j = k := by omega
        subst j
        exact ⟨n1,c1,by omega,hr1⟩
    · rw [← unit_next hk12]
      exact next_hint hp hu hnu hb
    · simpa only [nextTarget,Bool.false_eq_true,if_false,if_neg hnu,unit_next hk12] using hK2

/-- Every completed initial execution supplies the prologue equations and a
completed group-0 continuation, after exactly seventeen instructions. -/
theorem run_start {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {n c : Nat}
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n ⟨gpow 0,1⟩)) :
    (∀ ci ∈ prefixCode 16, ci.RelB B (Lx M)) ∧ IsInK (Lx M (hCell 1)) ∧
      ∃ n' c', n = n'+17 ∧ c = 26+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n' (groupRegs (Lx M) 0)) := by
  obtain ⟨hp,n0,c0,hn0,hc0,hr0⟩ := run_prologue h16 hκ M Sm B hHash hd h
  have hci : FreeLastProgram.instruction base 16 = FreeLastProgram.jump 1 (hCell 1) (h1Cell 1) := rfl
  obtain ⟨hK,_,n1,c1,hn1,hc1,hr1⟩ := run_jump h16 hκ M Sm (by decide : 16 < sentinel)
    (by decide : hCell 1 < 2^16) (by decide : h1Cell 1 < 2^16) 1 one_ne_zero hci (pro_one hp) hr0
  exact ⟨hp,hK,n1,c1,by omega,by omega,hr1⟩

/-- A later exit cannot re-enter the initial prologue: that would give two
completing continuations of different lengths from the same register state. -/
theorem exit_done {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {N C n c : Nat} {target : K}
    (hstart : some C ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M N ⟨gpow 0,1⟩))
    (hn : n+17 ≤ N)
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n ⟨target,1⟩)) :
    target = gpow sentinel ∧ n = 0 ∧ c = 0 := by
  obtain ⟨s,hs⟩ := runCost_pc_valid M Sm h
  change target = gpow s.val at hs
  rw [hs] at h
  by_cases hsent : s.val = sentinel
  · rw [hsent] at h hs
    obtain ⟨hn,_,hc⟩ := run_halt M Sm h
    exact ⟨hs,hn,hc⟩
  · have hlt : s.val < sentinel := by have := s.isLt; unfold sentinel at *; omega
    obtain ⟨j,hj⟩ := run_first hκ M Sm hlt 1 h
    have hin : 1 = FreeLastGuard.incoming FreeLastGuard.exitFlow s.val := (FreeLastGuard.incoming_exit _).symm
    rw [hin] at hj
    have hpro := FreeLastGuard.exit_read hlt j hj
    have hp := initConstants_of_completion h16 hκ M Sm hstart
    obtain ⟨_,np,cp,hNp,_,hrp⟩ := run_prefix M Sm B (k:=s.val) (by omega)
      (fun i hi pc x hx => straight_of_sem h16 hκ M Sm B hHash hd pc 1 one_ne_zero _
        (raw_initial_facts _ (by omega)).1 (raw_initial_straight _ (by omega))
        (fun _ => ⟨rfl,hp⟩) x hx) hstart
    have he := FreeLastNoRepeat.completing_length_unique FreeLastBase.program M Sm Sm hrp h
    omega


/-- One complete group body and its control, starting at any certified entry. -/
theorem run_group_at {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) (hp : ∀ ci ∈ prefixCode 16, ci.RelB B (Lx M))
    {s u v n c : Nat} {z : Bool} (hs : 27 ≤ s) (hs' : s < sentinel)
    (hb : (candidateTree.lookup s).body = .group u v z) (he : (candidateTree.lookup s).entry = s)
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n
      ⟨gpow s,FreeLastProgram.frame base (candidateTree.lookup s)⟩)) :
    (∀ ci ∈ groupBody u v z, ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+(groupBody u v z).length+1 ∧ c = lcost (groupBody u v z)+1+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n' (afterRegs (Lx M) u z)) := by
  have hu : u < 13 := by
    have hh := (candidate_lookup_good hs hs').1.2
    simp only [hb] at hh
    exact hh.1
  obtain ⟨hg,_,_⟩ := candidate_lookup_good hs hs'
  have hgood := hg.2
  simp only [hb] at hgood
  have hnt : (candidateTree.lookup s).body ≠ .trap := by rw [hb]; intro he; cases he
  obtain ⟨hbr,n1,c1,hn1,hc1,hr1⟩ := run_body h16 hκ M Sm B hHash hd hs hs' he hnt h
  have hf := FreeLastProgram.body_fits hg
  have hbounds := FreeLastDecode.lookup_bounds hs hs'
  have hcslot : s+(FreeLastProgram.body (candidateTree.lookup s)).length < sentinel := by
    unfold sentinel; omega
  have hqne := FreeLastBase.group_frame_nonzero hs hs' hb
  have ht : nextTarget u z < 2^16 := by
    have hn : FreeLastBlocks.nextGroup u < 13 := by unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
    unfold nextTarget
    split_ifs <;> simp only [FreeLastBlocks.exitCell,hCell] <;> omega
  have hframe : nextFrame u z < 2^16 := by
    have hn : FreeLastBlocks.nextGroup u < 13 := by unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
    unfold nextFrame
    split_ifs <;> simp only [oneCell,h1Cell] <;> omega
  have hci : FreeLastProgram.instruction base (s+(FreeLastProgram.body (candidateTree.lookup s)).length) =
      FreeLastProgram.jump (FreeLastProgram.frame base (candidateTree.lookup s)) (nextTarget u z) (nextFrame u z) := by
    have hh := FreeLastDecode.instruction_control base hs hs'
    rw [he] at hh
    rw [hh]
    simp only [FreeLastProgram.control,hb,nextTarget,nextFrame]
    split_ifs <;> rfl
  obtain ⟨_,_,n2,c2,hn2,hc2,hr2⟩ := run_jump h16 hκ M Sm hcslot ht hframe _ hqne hci (pro_one hp) hr1

  have hbl : FreeLastProgram.body (candidateTree.lookup s) = groupBody u v z := by
    rw [FreeLastProgram.body,hb]; rfl
  rw [hbl] at hbr hn1 hc1
  exact ⟨hbr,n2,c2,by omega,by omega,hr2⟩


theorem last_hint {B : BlakeRel} {mem : Nat → E} {v : Nat}
    (h : ∀ ci ∈ FreeLastBlocks.normal 1 v, ci.RelB B mem) :
    mem (h1Cell 0) = mem (hCell 0)+mem (FreeLastBlocks.gp 13) := by
  exact h (.xor (hCell 0) (FreeLastBlocks.gp 13) (h1Cell 0))
    (by simp only [FreeLastBlocks.normal,if_true,List.mem_append,List.mem_singleton,or_true])

theorem free_incoming {B : BlakeRel} {mem : Nat → E} {v : Nat} (q : Fin 209)
    (hb : ∀ ci ∈ FreeLastBlocks.normal 1 v, ci.RelB B mem)
    (hp : mem (FreeLastBlocks.gp 13) = ofK (base^((q.val : Int)-77)))
    {s : Nat} (ht : (afterRegs mem 1 false).pc = gpow s) :
    (afterRegs mem 1 false).fp = FreeLastGuard.incoming (FreeLastGuard.freeFlow q) s := by
  change (mem (hCell 0)).limb 0 = gpow s at ht
  change (mem (h1Cell 0)).limb 0 = _
  rw [last_hint hb,hp,limb_add,limb_ofK_zero,ht]
  exact add_comm _ _

theorem core_checksum_mem (u v : Nat) (z : Bool) :
    FreeLastBlocks.checksum u v z ∈ FreeLastBlocks.core u v z := by
  simp only [FreeLastBlocks.core,List.mem_append,List.mem_singleton]
  tauto

theorem core_tie_mem {u v : Nat} {z : Bool} {ci : CInstr} (hi : ci ∈ FreeLastBlocks.tie u v) :
    ci ∈ FreeLastBlocks.core u v z := by
  simp only [FreeLastBlocks.core,List.mem_append]
  tauto

/-- Returning from the free dispatch to a group cannot complete. Normal
returns repeat a saved continuation; the Z twin contradicts the pinned checksum. -/
theorem group_return_impossible {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) (hp : ∀ ci ∈ prefixCode 16, ci.RelB B (Lx M))
    {s u v x n c : Nat} {z : Bool} (q : Fin 209)
    (hs : 27 ≤ s) (hs' : s < sentinel) (hu : u < 12)
    (hb : (candidateTree.lookup s).body = .group u v z) (he : (candidateTree.lookup s).entry = s)
    (hexp : (q.val : Int)-77 = ((u+1 : Nat) : Int))
    (hx : x < VF 1) (hN : ∀ ci ∈ FreeLastBlocks.normal 1 x, ci.RelB B (Lx M))
    (hprod : Lx M (FreeLastBlocks.gp 13) = ofK (base^((q.val : Int)-77)))
    (hseen : earlier M Sm 12 n)
    (hfree : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n (afterRegs (Lx M) 1 false)))
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n
      ⟨gpow s,FreeLastProgram.frame base (candidateTree.lookup s)⟩)) : False := by
  have hg := (candidate_lookup_good hs hs').1.2
  simp only [hb] at hg
  have hv := hg.2.1
  obtain ⟨hbr,n1,c1,hn1,_,hr1⟩ := run_group_at h16 hκ M Sm B hHash hd hp hs hs' hb he h
  cases z with
  | false =>
    by_cases hu1 : u = 1
    · subst u
      have hh := FreeLastNoRepeat.completing_length_unique FreeLastBase.program M Sm Sm hfree hr1
      omega
    · rw [after_normal hu1] at hr1
      have hnext : FreeLastBlocks.nextGroup u < 13 := by
        unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
      have hn1' : FreeLastBlocks.nextGroup u ≠ 1 := by
        unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
      obtain ⟨nj,cj,hj,hrj⟩ := hseen (FreeLastBlocks.position (FreeLastBlocks.nextGroup u))
        (position_lt12 hnext hn1')
      rw [unit_inverse hnext] at hrj
      have hh := FreeLastNoRepeat.completing_length_unique FreeLastBase.program M Sm Sm hrj hr1
      omega
  | true =>
    have hu1 := hg.2.2.1 rfl
    subst u
    have hcoreN := core_rel (z:=false) (u:=1) (v:=x) (by intro h; cases h) hN
    have hcoreZ := core_rel (z:=true) (u:=1) (v:=v) (by intro _; rfl) hbr
    have hone : Lx M oneCell = (1 : E) := (pro_one hp).trans checksum_embed_one
    have hsame : x = v := FreeLastBlocks.tie1_unique B (Lx M) hx hv hone
      (fun ci hi => hcoreN ci (core_tie_mem hi)) (fun ci hi => hcoreZ ci (core_tie_mem hi))
    subst v
    have hn := checksum_step hp (by decide : 1 < 13) hx (hcoreN _ (core_checksum_mem 1 x false))
    have hz := checksum_step hp (by decide : 1 < 13) hx (hcoreZ _ (core_checksum_mem 1 x true))
    have hh := FreeLastBlocks.checksum_unique (checksum_embed_ne_zero FreeLastBase.base_ne_zero)
      (chargedCost fusionTab 1 x) hn hz
    change Lx M (FreeLastBlocks.gp 13) = Lx M oneCell at hh
    have he2 : base^((q.val : Int)-77) = base^2 := by
      rw [hexp]
      exact zpow_natCast base 2
    rw [hprod,he2,pro_one hp] at hh
    have hf : base^2 = base^0 := ofK_injective hh
    have hi := FreeLastBase.powers_injective (by decide : 2 ≤ 300) (by decide : 0 ≤ 300) hf
    omega


/-- A positive-free completion takes one free chain and then the sentinel. -/
theorem free_done {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) (hp : ∀ ci ∈ prefixCode 16, ci.RelB B (Lx M))
    {N C n c x : Nat} (q : Fin 209)
    (hstart : some C ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M N ⟨gpow 0,1⟩))
    (hn : n+17 ≤ N) (hx : x < VF 1)
    (hN : ∀ ci ∈ FreeLastBlocks.normal 1 x, ci.RelB B (Lx M))
    (hprod : Lx M (FreeLastBlocks.gp 13) = ofK (base^((q.val : Int)-77)))
    (hseen : earlier M Sm 12 n)
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n (afterRegs (Lx M) 1 false))) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 63 ∧ (q.val : Int)-77 = -(k : Int) ∧
      (∀ ci ∈ FreeLastBlocks.free k, ci.RelB B (Lx M)) ∧
      n = k+1 ∧ c = lcost (FreeLastBlocks.free k)+1 := by
  obtain ⟨e,ht⟩ := runCost_pc_valid M Sm h
  have hq := free_incoming q hN hprod ht
  have hr : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n
      ⟨gpow e.val,FreeLastGuard.incoming (FreeLastGuard.freeFlow q) e.val⟩) := by
    have he : afterRegs (Lx M) 1 false =
        ⟨gpow e.val,FreeLastGuard.incoming (FreeLastGuard.freeFlow q) e.val⟩ := by
      exact congrArg₂ Regs.mk ht hq
    rwa [he] at h
  have hehi : e.val < sentinel := by
    by_contra hi
    have he : e.val = sentinel := by have := e.isLt; unfold sentinel at *; omega
    rw [he] at hr
    exact FreeLastGuard.free_halt q (run_halt M Sm hr).2.1
  obtain ⟨j,hj⟩ := run_first hκ M Sm hehi _ hr
  have he27 : 27 ≤ e.val := by
    by_contra he
    by_cases hi : e.val < 17
    · have hf := FreeLastGuard.initial_read hi j hj
      cases hf
    · rw [FreeLastGuard.initial_trap (by omega) (by omega)] at hj
      exact FreeLastGuard.no_zero_read hj
  rcases FreeLastGuard.free_read hehi q j hj with hg | hf
  · obtain ⟨u,v,z,hu,hexp,hb,he⟩ := hg
    have hframe : FreeLastGuard.incoming (FreeLastGuard.freeFlow q) e.val =
        FreeLastProgram.frame base (candidateTree.lookup e.val) := by
      change base^((q.val : Int)-77)+gpow e.val = _
      rw [hexp,zpow_natCast]
      simp only [FreeLastProgram.frame,hb,← he,show u ≠ 12 by omega,if_false,add_comm]
    rw [hframe] at hr
    exact (group_return_impossible h16 hκ M Sm B hHash hd hp q he27 hehi hu hb he.symm
      hexp hx hN hprod hseen h hr).elim
  · obtain ⟨k,hexp,hb,he⟩ := hf
    have hgood := (candidate_lookup_good he27 hehi).1
    have hk := hgood.2
    simp only [hb] at hk
    have hframe : FreeLastGuard.incoming (FreeLastGuard.freeFlow q) e.val =
        FreeLastProgram.frame base (candidateTree.lookup e.val) := by
      have hh := FreeLastGuard.free_frame hb
      rw [← he] at hh
      change base^((q.val : Int)-77)+gpow e.val = _
      rwa [hexp]
    rw [hframe] at hr
    have hnt : (candidateTree.lookup e.val).body ≠ .trap := by rw [hb]; intro h; cases h
    obtain ⟨hbr,n1,c1,hn1,hc1,hr1⟩ := run_body h16 hκ M Sm B hHash hd he27 hehi he.symm hnt hr
    have hfit := FreeLastProgram.body_fits hgood
    have hbounds := FreeLastDecode.lookup_bounds he27 hehi
    have hcslot : e.val+(FreeLastProgram.body (candidateTree.lookup e.val)).length < sentinel := by
      unfold sentinel; omega
    have hqne := FreeLastBase.free_frame_nonzero he27 hehi hb
    have hci : FreeLastProgram.instruction base (e.val+(FreeLastProgram.body (candidateTree.lookup e.val)).length) =
        FreeLastProgram.jump (FreeLastProgram.frame base (candidateTree.lookup e.val)) FreeLastBlocks.exitCell oneCell := by
      have hh := FreeLastDecode.instruction_control base he27 hehi
      rw [← he] at hh
      rw [hh]
      simp only [FreeLastProgram.control,hb]
    obtain ⟨_,_,n2,c2,hn2,hc2,hr2⟩ := run_jump h16 hκ M Sm hcslot (by decide) (by decide)
      _ hqne hci (pro_one hp) hr1
    rw [pro_one hp,show oneV.limb 0 = (1 : K) from limb_ofK_zero 1] at hr2
    obtain ⟨_,hnzero,hczero⟩ := exit_done h16 hκ M Sm B hHash hd hstart (by omega) hr2
    have hbl : FreeLastProgram.body (candidateTree.lookup e.val) = FreeLastBlocks.free k := by
      simp only [FreeLastProgram.body,hb]
    rw [hbl] at hbr hn1 hc1
    have hlen : (FreeLastBlocks.free k).length = k := chainOps_length ..
    exact ⟨k,hk.1,hk.2.1,hexp,hbr,by omega,by omega⟩


theorem body_chosen {j : Nat} (hj : j < 13) (z : Bool) (x : Nat) :
    groupBody (unit j) x (if j = 12 then z else false) = FreeLastBlocks.chosen z (unit j) x := by
  cases z <;> interval_cases j <;> rfl

theorem steps_split (mem : Nat → E) (z : Bool) :
    FreeLastBlocks.groupSteps z (rawOf mem) =
      prefixSteps mem 12+(groupBody 1 (rawOf mem 1) z).length+1 := by
  rw [FreeLastBlocks.groupSteps,← unit_order,List.map_map,list_sum_range]
  rw [show (13 : Nat) = 12+1 from rfl,Finset.sum_range_succ]
  simp only [Function.comp_def]
  have hp : (∑ j ∈ Finset.range 12, ((FreeLastBlocks.chosen z (unit j) (rawOf mem (unit j))).length+1)) =
      prefixSteps mem 12 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [FreeLastBlocks.chosen,unit_ne_one (Finset.mem_range.mp hj),false_and,if_false]
  rw [hp]
  have he : FreeLastBlocks.chosen z (unit 12) (rawOf mem (unit 12)) = groupBody 1 (rawOf mem 1) z := by
    cases z <;> rfl
  rw [he]
  omega

theorem cycles_split (mem : Nat → E) (z : Bool) :
    FreeLastBlocks.groupCycles z (rawOf mem) =
      prefixCycles mem 12+lcost (groupBody 1 (rawOf mem 1) z)+1 := by
  rw [FreeLastBlocks.groupCycles,← unit_order,List.map_map,list_sum_range]
  rw [show (13 : Nat) = 12+1 from rfl,Finset.sum_range_succ]
  simp only [Function.comp_def]
  have hp : (∑ j ∈ Finset.range 12, (lcost (FreeLastBlocks.chosen z (unit j) (rawOf mem (unit j)))+1)) =
      prefixCycles mem 12 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [FreeLastBlocks.chosen,unit_ne_one (Finset.mem_range.mp hj),false_and,if_false]
  rw [hp]
  have he : FreeLastBlocks.chosen z (unit 12) (rawOf mem (unit 12)) = groupBody 1 (rawOf mem 1) z := by
    cases z <;> rfl
  rw [he]
  omega

structure PathFacts (B : BlakeRel) (mem : Nat → E) (xs : Nat → Nat) (s : Nat) (z : Bool) : Prop where
  pro : ∀ ci ∈ prefixCode 16, ci.RelB B mem
  valid : ∀ u < 13, xs u < VF u
  blk : ∀ u < 13, ∀ ci ∈ FreeLastBlocks.chosen z u (xs u), ci.RelB B mem
  landing : ∀ u < 13, GroupLanding mem u (xs u) (if u = 1 then z else false)
  free_bound : s ≤ 63
  free : ∀ ci ∈ FreeLastBlocks.free s, ci.RelB B mem
  zero : z = true → s = 0
  positive : z = false → 1 ≤ s

/-- Universal extraction of the 1089 path from the actual bytecode. -/
theorem run_full {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {N C : Nat}
    (hstart : some C ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M N ⟨gpow 0,1⟩)) :
    ∃ s z, PathFacts B (Lx M) (rawOf (Lx M)) s z ∧
      s+FreeLastBlocks.sumCosts (rawOf (Lx M)) = 85 ∧
      N = 186 ∧ C+LeanIsa.boundaryCycles = 1089 := by
  obtain ⟨hp,hK0,n0,c0,hn0,hc0,hr0⟩ := run_start h16 hκ M Sm B hHash hd hstart
  obtain ⟨hprev,n1,c1,hn1,hc1,hseen,hhint,hK1,hr1⟩ := run_groups h16 hκ M Sm B hHash hd hp hK0 hr0 12 le_rfl
  change Hint (Lx M) 1 at hhint
  change some c1 ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n1 (groupRegs (Lx M) 1)) at hr1
  obtain ⟨hx,hz,hbr,hlast,hK2,n2,c2,hn2,hc2,hr2⟩ := run_group h16 hκ M Sm B hHash hd hp (by decide : 1 < 13) hhint hK1 hr1
  generalize hzz : zeroOf (Lx M) 1 = z at hbr hn2 hc2 hr2 hlast
  have hunits : ∀ j < 13, rawOf (Lx M) (unit j) < VF (unit j) ∧
      ∀ ci ∈ groupBody (unit j) (rawOf (Lx M) (unit j)) (if j = 12 then z else false), ci.RelB B (Lx M) := by
    intro j hj
    by_cases hj12 : j = 12
    · subst j
      exact ⟨hx,hbr⟩
    · obtain ⟨hv,hz,_,hb⟩ := hprev j (by omega)
      exact ⟨hv,by simpa only [if_neg hj12,groupBody,Bool.false_eq_true,if_false] using hb⟩
  have hv : ∀ u < 13, rawOf (Lx M) u < VF u := by
    intro u hu
    simpa only [unit_inverse hu] using (hunits (FreeLastBlocks.position u) (position_lt hu)).1
  have hblocks : ∀ u < 13, ∀ ci ∈ FreeLastBlocks.chosen z u (rawOf (Lx M) u), ci.RelB B (Lx M) := by
    intro u hu
    have hb := (hunits (FreeLastBlocks.position u) (position_lt hu)).2
    rw [body_chosen (position_lt hu),unit_inverse hu] at hb
    exact hb
  have hlanding : ∀ u < 13, GroupLanding (Lx M) u (rawOf (Lx M) u) (if u = 1 then z else false) := by
    intro u hu
    by_cases h1 : u = 1
    · subst u
      exact hlast
    · have hh := (hprev (FreeLastBlocks.position u) (position_lt12 hu h1)).2.2.1
      simpa only [unit_inverse hu,if_neg h1] using hh
  have hbunit := fun j hj => (hunits j hj).2
  have hnall : N = 17+FreeLastBlocks.groupSteps z (rawOf (Lx M))+n2 := by
    rw [steps_split]
    omega
  have hcall : C = 26+FreeLastBlocks.groupCycles z (rawOf (Lx M))+c2 := by
    rw [cycles_split]
    omega
  have hseen' : earlier M Sm 12 n2 := by
    intro j hj
    obtain ⟨nj,cj,hj,hrj⟩ := hseen j hj
    exact ⟨nj,cj,by omega,hrj⟩
  have hsmall : n2+17 ≤ N := by omega
  cases z with
  | true =>
    change some c2 ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n2
      ⟨(Lx M FreeLastBlocks.exitCell).limb 0,(Lx M oneCell).limb 0⟩) at hr2
    rw [pro_one hp,show oneV.limb 0 = (1 : K) from limb_ofK_zero 1] at hr2
    obtain ⟨_,hnz,hcz⟩ := exit_done h16 hκ M Sm B hHash hd hstart hsmall hr2
    have hl := zero_layer hp hv hbunit
    refine ⟨0,true,⟨hp,hv,hblocks,hlanding,by decide,?_,fun _ => rfl,by intro h; cases h⟩,by omega,?_,?_⟩
    · intro ci hi
      simp [FreeLastBlocks.free,chainOps] at hi
    · have hh := FreeLastBlocks.intended_steps base true (rawOf (Lx M)) 0 hv (by omega) (fun _ => rfl)
      rw [FreeLastBlocks.prologue_length] at hh
      simp only [if_true,Nat.add_zero] at hh
      omega
    · have hh := FreeLastBlocks.intended_cycles base true (rawOf (Lx M)) 0 hv (by omega) (fun _ => rfl)
      rw [FreeLastBlocks.prologue_cost] at hh
      simp only [if_true,Nat.add_zero] at hh
      omega
  | false =>
    have hprod := final_product hp hv hbunit
    change Lx M (FreeLastBlocks.gp 13) = ofK (base^((charges (rawOf (Lx M)) 13 : Int)-77)) at hprod
    let q : Fin 209 := ⟨charges (rawOf (Lx M)) 13,by have := charges_bound hv; omega⟩
    obtain ⟨k,hk,hk63,hexp,hfree,hnf,hcf⟩ := free_done h16 hκ M Sm B hHash hd hp q hstart hsmall hx hbr hprod hseen' hr2
    have hl : k+FreeLastBlocks.sumCosts (rawOf (Lx M)) = 85 := by
      have hc := charges_cost hv
      change (charges (rawOf (Lx M)) 13 : Int)-77 = -(k : Int) at hexp
      omega
    refine ⟨k,false,⟨hp,hv,hblocks,hlanding,hk63,hfree,(by intro h; cases h),fun _ => hk⟩,hl,?_,?_⟩
    · have hh := FreeLastBlocks.intended_steps base false (rawOf (Lx M)) k hv hl (by intro h; cases h)
      rw [FreeLastBlocks.prologue_length,FreeLastBlocks.free_length] at hh
      simp only [Bool.false_eq_true,if_false] at hh
      omega
    · have hh := FreeLastBlocks.intended_cycles base false (rawOf (Lx M)) k hv hl (by intro h; cases h)
      rw [FreeLastBlocks.prologue_cost] at hh
      simp only [Bool.false_eq_true,if_false] at hh
      omega


theorem run_exact {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {n c : Nat}
    (h : some c ∈ Sm.S (LeanIsa.runCost FreeLastBase.program M n ⟨gpow 0,1⟩)) :
    n = 186 ∧ c = 969 := by
  obtain ⟨_,_,_,_,hn,hc⟩ := run_full h16 hκ M Sm B hHash hd h
  change c+120=1089 at hc
  exact ⟨hn,by omega⟩

/-- The contract's universal cycle clause, for every admitted committed image. -/
theorem cycles (S : LeanIsa.Submission) (hS : S.program = FreeLastBase.program) :
    S.CyclesAtMost 1089 := by
  intro pk m bits κ h16 hκ M n cost h
  unfold LeanIsa.Submission.exec at h
  rw [hS,initial_eq] at h
  have hc := (run_exact h16 hκ (LeanIsa.loadInput pk m bits M) suppSem trueRel
    AffineVM.hashSound_supp (lengthDomain_load h16 pk m bits M) h).2
  change 120 + cost ≤ 1089
  rw [hc]

theorem PathFacts.core_rel {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {s : Nat} {z : Bool}
    (hp : PathFacts B mem xs s z) {u : Nat} (hu : u < 13) :
    ∀ ci ∈ FreeLastBlocks.core u (xs u) (if u = 1 then z else false), ci.RelB B mem := by
  intro ci hi
  apply hp.blk u hu ci
  cases z <;> by_cases h1 : u = 1
  all_goals simp only [FreeLastBlocks.chosen,h1,Bool.false_eq_true,and_false,and_self,if_false,if_true,
    FreeLastBlocks.normal,FreeLastBlocks.zero] at hi ⊢
  all_goals first | exact List.mem_append_left _ hi | subst u; exact List.mem_append_left _ hi

theorem PathFacts.tie_rel {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {s : Nat} {z : Bool}
    (hp : PathFacts B mem xs s z) {u : Nat} (hu : u < 13)
    {ci : CInstr} (hci : ci ∈ FreeLastBlocks.tie u (xs u)) : ci.RelB B mem := by
  apply hp.core_rel hu ci
  unfold FreeLastBlocks.core
  simp only [List.mem_append,List.mem_singleton]
  exact Or.inl (Or.inl (Or.inl (Or.inl hci)))

end
end OptimalOTS.FreeLastVM
