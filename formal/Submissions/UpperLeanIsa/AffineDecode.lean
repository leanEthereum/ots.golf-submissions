import Submissions.UpperLeanIsa.AffineProgram

/-! The polynomial guard applies to the compiled bytecode, not just abstract
descriptors. All memory sizes admitted by the contract are covered. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem layout_first (T : Tab) (s : AffineFrames.Slot) :
    match layout T s with
    | .trap => True
    | .initial c => c.val = (raw T 1 (place s)).cell0 ∧ raw T 1 (place s) ≠ .pad
    | .body d => d.firstCell.val = (raw T 1 (place s)).cell0 ∧ raw T 1 (place s) ≠ .pad := by
  unfold layout
  dsimp only
  by_cases hpad : isPad (raw T 1 (place s)) = true
  · rw [if_pos hpad]
    trivial
  · rw [if_neg hpad]
    have hn : raw T 1 (place s) ≠ .pad := fun h => hpad ((isPad_eq_true _).mpr h)
    by_cases hc : (raw T 1 (place s)).cell0 < 2 ^ 16
    · rw [dif_pos hc]
      generalize hp : place s.val = p at *
      cases p with
      | initial n => exact ⟨rfl,hn⟩
      | body f x i =>
        dsimp only
        by_cases hf : f < 14
        · rw [dif_pos hf]
          by_cases he : ent f x < 2 ^ 18
          · rw [dif_pos he]; exact ⟨rfl,hn⟩
          · rw [dif_neg he]; trivial
        · rw [dif_neg hf]; trivial
      | trap => trivial
    · rw [dif_neg hc]; trivial

theorem body_descriptor (T : Tab) (s : AffineFrames.Slot) (d : AffineFrames.BodyDescriptor)
    (h : layout T s = .body d) :
    ∃ f x i, place s.val = .body f x i ∧ f < 14 ∧
      d.stage.val = stageIndex f ∧ d.entry.val = ent f x := by
  unfold layout at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · cases hp : place s.val with
      | initial n => simp only [hp] at h; contradiction
      | trap => simp only [hp] at h; contradiction
      | body f x i =>
        simp only [hp] at h
        split at h
        · rename_i hf
          split at h
          · cases h
            exact ⟨f,x,i,rfl,hf,rfl,rfl⟩
          · contradiction
        · contradiction
    · contradiction

/-- The fixed stage occupies only the enumerated free-chain region. -/
theorem layout_fixed (T : Tab) : AffineFrames.FixedHyp (layout T) := by
  constructor
  · intro s c h
    have hp : ∃ n, place s.val = .initial n := by
      unfold layout at h
      dsimp only at h
      split at h
      · contradiction
      · split at h
        · cases he : place s.val with
          | initial n => exact ⟨n,rfl⟩
          | trap => simp only [he] at h; contradiction
          | body f x i =>
            simp only [he] at h
            split at h
            · split at h <;> contradiction
            · contradiction
        · contradiction
    obtain ⟨n,hp⟩ := hp
    unfold place at hp
    split_ifs at hp <;> first | omega | contradiction
  · intro s d h hd
    obtain ⟨f,x,i,hp,hf,hs,he⟩ := body_descriptor T s d h
    have hf0 : f = 0 := by
      rw [hs] at hd
      unfold stageIndex at hd
      split_ifs at hd <;> omega
    subst f
    unfold place at hp
    split_ifs at hp with h27 hg hb hfree
    · cases hp
    · cases hp
      simpa only [ent,ite_true,entF,baseF] using
        And.intro (show 255615 ≤ s.val by unfold baseF at hb; omega)
          (And.intro (show s.val < 259967 by unfold baseF at hfree; omega) he)
  · intro s d h hd
    obtain ⟨f,x,i,hp,hf,hs,he⟩ := body_descriptor T s d h
    have hf13 : f = 13 := by
      rw [hs] at hd
      unfold stageIndex at hd
      split_ifs at hd <;> omega
    subst f
    unfold place at hp
    split_ifs at hp with h27 hg hb hfree <;> try contradiction
    · have hh := dec_spec (by omega : 27 ≤ s.val) hg
      injection hp with hf' hx' hi'
      have hu : (dec s.val).1 = 12 := by omega
      rw [hu] at hh
      refine ⟨(dec s.val).2.1,(dec s.val).2.2,hh.2.1,hh.2.2.1,hh.2.2.2,?_⟩
      simpa only [ent,show (13:Nat) ≠ 0 by decide,ite_false,show 13-1=12 from rfl,← hx'] using he
    · injection hp with hf'
      omega

/-- The compiler's declared first cells agree with the constants it actually chose. -/
theorem body_first (T : Tab) (s : AffineFrames.Slot) (d : AffineFrames.BodyDescriptor)
    (h : layout T s = .body d) :
    AffineFrames.firstOperand (instrAt T s) = AffineFrames.operand (layout T) d d.firstCell.val := by
  have hi := layout_first T s
  rw [h] at hi
  have hn : raw T (base T) (place s) ≠ .pad := fun hp =>
    hi.2 ((raw_pad T (base T) 1 _).mp hp)
  rw [instrAt,h,compile_first _ hn,raw_cell0 T (base T) 1,← hi.1]
  rfl

theorem initial_first (T : Tab) (s : AffineFrames.Slot) (c : AffineFrames.Cell)
    (h : layout T s = .initial c) :
    AffineFrames.firstOperand (instrAt T s) = gpow c.val := by
  have hi := layout_first T s
  rw [h] at hi
  have hn : raw T (base T) (place s) ≠ .pad := fun hp =>
    hi.2 ((raw_pad T (base T) 1 _).mp hp)
  rw [instrAt,h,compile_first _ hn,raw_cell0 T (base T) 1,← hi.1,div_one]

/-- A jump cannot enter an interior instruction, another stage, or the prologue. -/
theorem wrong_landing {κ : ℕ} (hκ : κ ≤ 32) (M : MemImage κ)
    (T : Tab) (u : AffineFrames.Stage) (s : AffineFrames.Slot)
    (hwrong : ∀ d, layout T s = .body d → ¬(u = d.stage ∧ s = d.entry)) :
    LeanIsa.execute M ⟨gpow s.val,AffineFrames.frame (layout T) u s⟩ (instrAt T s) = pure none := by
  cases hs : layout T s with
  | trap =>
    rw [instrAt,hs]
    exact exec_pad M _
  | initial c =>
    exact AffineFrames.execute_wrong_initial hκ M (layout T) (layout_fixed T) u s c (instrAt T s) hs
      (initial_first T s c hs)
  | body d =>
    exact AffineFrames.execute_wrong_body hκ M (layout T) (layout_fixed T) u s d (instrAt T s) hs
      (hwrong d hs) (body_first T s d hs)

end
end OptimalOTS.AffineVM
