import Submissions.UpperLeanIsa.AffineDecode
import Submissions.UpperLeanIsa.AffineExit
import Submissions.UpperLeanIsa.PackedSupport

/-! Exact execution of the compiled cell instructions in any nonzero frame. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
noncomputable section

section Normal

variable {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (M : MemImage κ) (pc q : K) (hq : q ≠ 0)
include h16 hκ hq

theorem read_relative {c : ℕ} (hc : c < 2 ^ 16) :
    M.read (q * (gpow c / q)) = some (Lx M c) := by
  rw [mul_div_cancel₀ _ hq]
  simpa only [one_mul] using read_one h16 hκ M hc

theorem read_relative_g {c : ℕ} (hc : c+1 < 2 ^ 16) :
    M.read (q * (g * (gpow c / q))) = some (Lx M (c+1)) := by
  rw [← mul_div_assoc,g_mul_gpow]
  exact read_relative h16 hκ M q hq hc

theorem exec_xor {a b c : ℕ} (hb : (CInstr.xor a b c).Bounded) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.xor a b c)) =
      pure (if Lx M c = Lx M a + Lx M b then some ⟨g*pc,q⟩ else none) := by
  obtain ⟨ha,hb,hc⟩ := hb
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩
    (.xor (gpow a / q) (gpow b / q) (gpow c / q))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,read_relative h16 hκ M q hq ha,
    read_relative h16 hκ M q hq hb,read_relative h16 hκ M q hq hc,
    Option.bind_eq_bind,Option.bind_some]
  exact guard_some _

theorem exec_mul {a b c : ℕ} (hb : (CInstr.mul a b c).Bounded) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.mul a b c)) =
      pure (if Lx M c = Lx M a * Lx M b then some ⟨g*pc,q⟩ else none) := by
  obtain ⟨ha,hb,hc⟩ := hb
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩
    (.mulNative (gpow a / q) (gpow b / q) (gpow c / q))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,read_relative h16 hκ M q hq ha,
    read_relative h16 hκ M q hq hb,read_relative h16 hκ M q hq hc,
    Option.bind_eq_bind,Option.bind_some]
  exact guard_some _

theorem exec_setc {a : ℕ} {v : E} (hb : (CInstr.setc a v).Bounded) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.setc a v)) =
      pure (if Lx M a = v then some ⟨g*pc,q⟩ else none) := by
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩ (.setConstant (gpow a / q) v)) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,read_relative h16 hκ M q hq hb,
    Option.bind_eq_bind,Option.bind_some]
  exact guard_some _

/-- Rebasing preserves the complete oracle query, including both words of each pair. -/
theorem exec_blake {m0 m1 m2 m3 cv out md : ℕ}
    (hb : (CInstr.blake m0 m1 m2 m3 cv out md).Bounded) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.blake m0 m1 m2 m3 cv out md)) =
      (hash (LeanIsa.blake2sQuery ![Lx M m0,Lx M m1,Lx M m2,Lx M m3]
        (Lx M cv) (Lx M (cv+1)) (Lx M md))) >>= fun ans =>
        pure (if LeanIsa.OracleCompressCells ![Lx M m0,Lx M m1,Lx M m2,Lx M m3]
          (Lx M cv) (Lx M (cv+1)) (Lx M out) (Lx M (out+1)) (Lx M md) ans
          then some ⟨g*pc,q⟩ else none) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6⟩ := hb
  simp only [compile,LeanIsa.execute,Matrix.cons_val,Fin.isValue,
    read_relative h16 hκ M q hq c0,read_relative h16 hκ M q hq c1,
    read_relative h16 hκ M q hq c2,read_relative h16 hκ M q hq c3,
    read_relative h16 hκ M q hq (show cv < 2 ^ 16 by omega),read_relative_g h16 hκ M q hq c4,
    read_relative h16 hκ M q hq (show out < 2 ^ 16 by omega),read_relative_g h16 hκ M q hq c5,
    read_relative h16 hκ M q hq c6,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
  rfl

theorem exec_dispatch {f : ℕ} (hf : f < 14) (hOne : Lx M oneCell = oneV) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.dispatch f)) =
      pure (if IsInK (Lx M (hCell f)) ∧ IsInK (Lx M (h1Cell f))
        then some ⟨(Lx M (hCell f)).limb 0,(Lx M (h1Cell f)).limb 0⟩ else none) := by
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩
    (.jump (gpow oneCell/q) (gpow (hCell f)/q) (gpow (h1Cell f)/q))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,
    read_relative h16 hκ M q hq (show oneCell < 2 ^ 16 by decide),
    read_relative h16 hκ M q hq (show hCell f < 2 ^ 16 by unfold hCell; omega),
    read_relative h16 hκ M q hq (show h1Cell f < 2 ^ 16 by unfold h1Cell; omega),
    Option.bind_eq_bind,Option.bind_some,hOne]
  by_cases hh : IsInK (Lx M (hCell f)) ∧ IsInK (Lx M (h1Cell f))
  · have hin : IsInK oneV ∧ IsInK (Lx M (hCell f)) ∧ IsInK (Lx M (h1Cell f)) :=
      ⟨isInK_ofK 1,hh⟩
    rw [show (guard (IsInK oneV ∧ IsInK (Lx M (hCell f)) ∧ IsInK (Lx M (h1Cell f))) : Option Unit) =
      some () from if_pos hin,if_pos hh]
    simp only [Option.bind_some,oneV,if_neg ofK_one_ne_zero]
    rfl
  · rw [show (guard (IsInK oneV ∧ IsInK (Lx M (hCell f)) ∧ IsInK (Lx M (h1Cell f))) : Option Unit) =
      none from if_neg (fun h => hh h.2),if_neg hh]
    rfl

theorem exec_exit (hOne : Lx M oneCell = oneV) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q .exit) =
      pure (if IsInK (Lx M (gpCell 13)) then some ⟨(Lx M (gpCell 13)).limb 0,1⟩ else none) := by
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩
    (.jump (gpow oneCell/q) (gpow (gpCell 13)/q) (gpow oneCell/q))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,
    read_relative h16 hκ M q hq (show oneCell < 2 ^ 16 by decide),
    read_relative h16 hκ M q hq (show gpCell 13 < 2 ^ 16 by decide),
    Option.bind_eq_bind,Option.bind_some,hOne]
  by_cases hh : IsInK (Lx M (gpCell 13))
  · have hin : IsInK oneV ∧ IsInK (Lx M (gpCell 13)) ∧ IsInK oneV :=
      ⟨isInK_ofK 1,hh,isInK_ofK 1⟩
    rw [show (guard (IsInK oneV ∧ IsInK (Lx M (gpCell 13)) ∧ IsInK oneV) : Option Unit) =
      some () from if_pos hin,if_pos hh]
    simp only [Option.bind_some,oneV,if_neg ofK_one_ne_zero,limb_ofK_zero]
    rfl
  · rw [show (guard (IsInK oneV ∧ IsInK (Lx M (gpCell 13)) ∧ IsInK oneV) : Option Unit) =
      none from if_neg (fun h => hh h.2.1),if_neg hh]
    rfl

end Normal

/-- The preceding XOR forces the new fp to contain the actual destination. -/
theorem hint_frame (T : Tab) (v : ℕ → E) {f : ℕ} (hf : f < 14) (s : AffineFrames.Slot)
    (hHint : v (h1Cell f) = v (hCell f) + ofK (AffineFrames.stageBias (base T) (stageIndex f)))
    (hTarget : (v (hCell f)).limb 0 = gpow s.val) :
    (v (h1Cell f)).limb 0 =
      AffineFrames.frame (layout T) ⟨stageIndex f,stageIndex_lt hf⟩ s := by
  rw [hHint,limb_add,hTarget,limb_ofK_zero]
  exact add_comm _ _

end
end OptimalOTS.AffineVM
