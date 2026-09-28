import Submissions.UpperLeanIsa.AffineSemantics

/-! The original one-instruction length check still works with affine constants.
Its four nonzero aliases contain distinct positive powers, so none can equal ONE. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.HLG3 (natV cellBits_natV)
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def InitConstants (T : Tab) (v : ℕ → E) : Prop :=
  ∀ c, 1 ≤ c → c ≤ 4 → v (cCell c) = ofK (base T ^ c)

variable {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (L : MemImage κ) (pc : K)
include h16 hκ

theorem exec_init (T : Tab) (hd : LengthDomain (Lx L)) (hp : InitConstants T (Lx L)) :
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
          change base T ^ (c.val + 1) = base T ^ 0 at hfac
          have := AffineFrames.safeBase_powers_injective (layout T) (by omega) (by omega) hfac
          omega)
    cases hr : L.read ((BitVec.ofNat 64 n : K) * OptimalOTS.HLG3.LengthGate128.scale) with
    | none => simp [hr, heq, he]
    | some z =>
      have hz1 : z ≠ ofK 1 := by intro hh; exact hrne (hr.trans (congrArg some hh))
      simp only [Option.bind_some, LeanerVM.Semantics.derefSource]
      simp [heq, he]
      exact hz1

end
end OptimalOTS.AffineVM
