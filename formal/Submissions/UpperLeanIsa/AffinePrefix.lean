import Submissions.UpperLeanIsa.AffineStraight

/-! The setup pins the powers before the length assertion. A completing run
then traverses the complete seventeen-instruction prologue in frame one. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem raw_initial_facts (T : Tab) (a : K) {s : ℕ} (hs : s < 18) :
    (raw T a (.initial s)).Bounded ∧ raw T a (.initial s) ≠ .pad ∧
      ∀ j, raw T a (.initial s) ≠ .entry j := by
  interval_cases s <;>
    norm_num [raw,CInstr.Bounded,cCell,lenCell,oneCell,gCell,msgLo,msgHi,nonceCell,
      pkCell,idxCell,hCell,h1Cell] <;>
    exact ⟨(by intro h; cases h),(by intro j h; cases h)⟩

theorem raw_initial_straight (T : Tab) (a : K) {s : ℕ} (hs : s < 17) :
    (raw T a (.initial s)).straight = true := by
  interval_cases s <;> norm_num [raw,CInstr.straight]

theorem instrAt_initial (T : Tab) (s : AffineFrames.Slot) (hs : s.val < 18) :
    instrAt T s = compile 1 (raw T (base T) (.initial s.val)) := by
  have hp : place s.val = .initial s.val := by unfold place; rw [if_pos (by omega)]
  obtain ⟨hb,hn,he⟩ := raw_initial_facts T 1 hs
  have hc := CInstr.cell0_lt hb hn he
  have hnp : ¬isPad (raw T 1 (.initial s.val)) = true :=
    fun h => hn ((isPad_eq_true _).mp h)
  unfold instrAt layout
  rw [hp,if_neg hnp,dif_pos hc]

def prefixCode (T : Tab) (n : ℕ) : List CInstr :=
  (List.range n).map (fun i => raw T (base T) (.initial i))

theorem prefixCode_length (T : Tab) (n : ℕ) : (prefixCode T n).length = n := by
  simp only [prefixCode,List.length_map,List.length_range]

theorem prefixCode_get (T : Tab) {n i : ℕ} (hi : i < (prefixCode T n).length) :
    (prefixCode T n)[i] = raw T (base T) (.initial i) := by
  simp only [prefixCode,List.getElem_map,List.getElem_range]

theorem prefixCode_mem (T : Tab) {n i : ℕ} (hi : i < n) :
    raw T (base T) (.initial i) ∈ prefixCode T n :=
  List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩

theorem run_prefix {κ : ℕ} (T : Tab) (M : MemImage κ) (Sm : Sem) (B : BlakeRel)
    {k : ℕ} (hk : k ≤ 17)
    (hbridge : ∀ i < k, ∀ pc x,
      x ∈ Sm.S (LeanIsa.execute M ⟨pc,1⟩ (compile 1 (raw T (base T) (.initial i)))) →
        x = none ∨ (x = some ⟨g*pc,1⟩ ∧ (raw T (base T) (.initial i)).RelB B (Lx M)))
    {n c : ℕ} (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow 0,1⟩)) :
    (∀ ci ∈ prefixCode T k, ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+k ∧ c = lcost (prefixCode T k)+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (program T) M n' ⟨gpow k,1⟩) := by
  have hh := run_list T M Sm B 1 (l:=prefixCode T k) (t:=0)
    (fun i hi s hs => by
      rw [prefixCode_get T hi]
      rw [prefixCode_length] at hi
      have he : s.val = i := by omega
      rw [instrAt_initial T s (by omega),he])
    (fun ci hci => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
      exact raw_initial_straight T _ (by have := List.mem_range.mp hi; omega))
    (fun ci hci pc x hx => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
      exact hbridge i (List.mem_range.mp hi) pc x hx)
    (by rw [prefixCode_length]; unfold sentinel; omega) h
  simpa only [prefixCode_length,Nat.zero_add] using hh

theorem initConstants_of_completion {κ : ℕ} (T : Tab) (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow 0,1⟩)) :
    InitConstants T (Lx M) := by
  have hh := run_prefix T M Sm trueRel (k:=13) (by decide) (fun i hi pc x hx => by
    have hb : (CInstr.setc (cCell (i+1)) (ofK (base T^(i+1)))).Bounded := by
      simp only [CInstr.Bounded,cCell]
      split_ifs <;> omega
    rw [raw,if_pos hi,exec_setc h16 hκ M pc 1 one_ne_zero hb,Sm.pure_iff] at hx
    rw [raw,if_pos hi]
    split_ifs at hx with hr
    · exact Or.inr ⟨hx,hr⟩
    · exact Or.inl hx) h
  intro k hk hk4
  have hr := hh.1 _ (prefixCode_mem T (i:=k-1) (by omega : k-1 < 13))
  simpa only [raw,if_pos (show k-1 < 13 by omega),Nat.sub_add_cancel hk,CInstr.RelB] using hr

theorem prologue_cost (T : Tab) : lcost (prefixCode T 17) = 26 := by
  norm_num [prefixCode,lcost,List.range_succ,raw,CInstr.cost]

theorem run_prologue {κ : ℕ} (T : Tab) (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow 0,1⟩)) :
    (∀ ci ∈ prefixCode T 17, ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+17 ∧ c = 26+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (program T) M n' ⟨gpow 17,1⟩) := by
  have hp := initConstants_of_completion T h16 hκ M Sm h
  have hh := run_prefix T M Sm B (k:=17) le_rfl (fun i hi pc x hx =>
    straight_of_sem h16 hκ M T Sm B hHash hd pc 1 one_ne_zero _
      (raw_initial_facts T _ (by omega)).1 (raw_initial_straight T _ hi)
      (fun _ => ⟨rfl,hp⟩) x hx) h
  rwa [prologue_cost] at hh

end
end OptimalOTS.AffineVM
