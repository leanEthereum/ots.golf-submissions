import Submissions.UpperLeanIsa.FreeLastRun

namespace OptimalOTS.FreeLastVM
open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.FreeLastBase (base)
open OptimalOTS.FreeLastProgram (compile)
open OptimalOTS.AffineVM (HashSound)
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def initialRaw (a : K) (s : Nat) : CInstr := (FreeLastBlocks.prologue a).getD s .pad

theorem initialRaw_first {a : K} {s : Nat} (hs : s < 11) :
    initialRaw a s = .setc (cCell (s+1)) (ofK (a^(s+1))) := by
  unfold initialRaw FreeLastBlocks.prologue
  rw [List.getD_append _ _ _ _ (by simpa using hs)]
  simp [List.getD_eq_getElem?_getD,hs]

theorem raw_initial_facts (a : K) {s : ℕ} (hs : s < 15) :
    (initialRaw a s).Bounded ∧ initialRaw a s ≠ .pad ∧
      ∀ j, initialRaw a s ≠ .entry j := by
  interval_cases s <;>
    norm_num [initialRaw,FreeLastBlocks.prologue,CInstr.Bounded,cCell,lenCell,oneCell,gCell,msgLo,msgHi,nonceCell,
      pkCell,idxCell,hCell,h1Cell,copy,stCell,FreeLastBlocks.bias] <;>
    exact ⟨(by intro h; cases h),(by intro j h; cases h)⟩

theorem raw_initial_straight (a : K) {s : ℕ} (hs : s < 15) :
    (initialRaw a s).straight = true := by
  interval_cases s <;> norm_num [initialRaw,FreeLastBlocks.prologue,CInstr.straight,copy]

theorem instrAt_initial (s : AffineFrames.Slot) (hs : s.val < 15) :
    FreeLastProgram.instruction base s.val = FreeLastProgram.compile 1 (initialRaw base s.val) := by
  simp only [FreeLastProgram.instruction,show s.val < 27 by omega,if_true,FreeLastProgram.initial]
  have hl : (FreeLastBlocks.prologue base).length = 15 := rfl
  rw [hl,if_pos hs]
  rfl

def prefixCode (n : ℕ) : List CInstr :=
  (List.range n).map (fun i => initialRaw base i)

theorem prefixCode_length (n : ℕ) : (prefixCode n).length = n := by
  simp only [prefixCode,List.length_map,List.length_range]

theorem prefixCode_get {n i : ℕ} (hi : i < (prefixCode n).length) :
    (prefixCode n)[i] = initialRaw base i := by
  simp only [prefixCode,List.getElem_map,List.getElem_range]

theorem prefixCode_mem {n i : ℕ} (hi : i < n) :
    initialRaw base i ∈ prefixCode n :=
  List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩

theorem run_prefix {κ : ℕ} (M : MemImage κ) (Sm : Sem) (B : BlakeRel)
    {k : ℕ} (hk : k ≤ 15)
    (hbridge : ∀ i < k, ∀ pc x,
      x ∈ Sm.S (LeanIsa.execute M ⟨pc,1⟩ (compile 1 (initialRaw base i))) →
        x = none ∨ (x = some ⟨g*pc,1⟩ ∧ (initialRaw base i).RelB B (Lx M)))
    {n c : ℕ} (h : some c ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n ⟨gpow 0,1⟩)) :
    (∀ ci ∈ prefixCode k, ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+k ∧ c = lcost (prefixCode k)+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n' ⟨gpow k,1⟩) := by
  have hh := run_list M Sm B 1 (l:=prefixCode k) (t:=0)
    (fun i hi s hs => by
      rw [prefixCode_get hi]
      rw [prefixCode_length] at hi
      have he : s.val = i := by omega
      rw [instrAt_initial s (by omega),he])
    (fun ci hci => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
      exact raw_initial_straight _ (by have := List.mem_range.mp hi; omega))
    (fun ci hci pc x hx => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
      exact hbridge i (List.mem_range.mp hi) pc x hx)
    (by rw [prefixCode_length]; unfold sentinel; omega) h
  simpa only [prefixCode_length,Nat.zero_add] using hh

theorem initConstants_of_completion {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n ⟨gpow 0,1⟩)) :
    InitConstants (Lx M) := by
  have hh := run_prefix M Sm trueRel (k:=11) (by decide) (fun i hi pc x hx => by
    have hb : (CInstr.setc (cCell (i+1)) (ofK (base^(i+1)))).Bounded := by
      simp only [CInstr.Bounded,cCell]
      split_ifs <;> omega
    rw [initialRaw_first hi,show FreeLastProgram.compile 1 (.setc (cCell (i+1)) (ofK (base^(i+1)))) = AffineVM.compile 1 (.setc (cCell (i+1)) (ofK (base^(i+1)))) from rfl,AffineVM.exec_setc h16 hκ M pc 1 one_ne_zero hb,Sm.pure_iff] at hx
    rw [initialRaw_first hi]
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx) h
  intro k hk hk4
  have hr := hh.1 _ (prefixCode_mem (i:=k-1) (by omega : k-1 < 11))
  simpa only [initialRaw_first (show k-1 < 11 by omega),Nat.sub_add_cancel hk,CInstr.RelB] using hr

theorem prologue_cost : lcost (prefixCode 15) = 24 := by
  norm_num [prefixCode,lcost,List.range_succ,initialRaw,FreeLastBlocks.prologue,CInstr.cost,copy]

theorem run_prologue {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n ⟨gpow 0,1⟩)) :
    (∀ ci ∈ prefixCode 15, ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+15 ∧ c = 24+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (FreeLastBase.program) M n' ⟨gpow 15,1⟩) := by
  have hp := initConstants_of_completion h16 hκ M Sm h
  have hh := run_prefix M Sm B (k:=15) le_rfl (fun i hi pc x hx =>
    straight_of_sem h16 hκ M Sm B hHash hd pc 1 one_ne_zero _
      (raw_initial_facts _ (by omega)).1 (raw_initial_straight _ hi)
      (fun _ => ⟨rfl,hp⟩) x hx) h
  rwa [prologue_cost] at hh

end
end OptimalOTS.FreeLastVM
