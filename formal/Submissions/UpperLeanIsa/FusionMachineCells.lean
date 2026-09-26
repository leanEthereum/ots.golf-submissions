import Submissions.UpperLeanIsa.FusionMachineProver

/-! Physical cell inverses and canonical values of the honest fused image. -/
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OptimalOTS.HLFusion
open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV ans)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section

macro "hsimp" : tactic => `(tactic| simp (disch := omega) only [if_pos,if_neg,↓reduceIte])

def junkCell (k dst : ℕ) : ℕ := if topOff k=0 then dst+1 else dst-1

def cvTop (_k : ℕ) : Prop := True
instance (k : ℕ) : Decidable (cvTop k) := by unfold cvTop; infer_instance

theorem cvTop_of_exported {k : ℕ} (_he : exported k) : cvTop k := trivial

theorem xc_band {k t : ℕ} (hk : k < 42) (ht : 2 * t + 1 < 2 * LEN k) :
    bandIdx xcBase 42 (xcCell k t) = k ∧ bandIdx xcBase 42 (xcCell k t + 1) = k := by
  have hs := xcBase_succ k
  unfold xcCell
  exact ⟨bandIdx_eq xcBase_mono hk (by omega) (by omega),
    bandIdx_eq xcBase_mono hk (by omega) (by omega)⟩

/-! ## The honest cells -/

section Cells

variable (T : Tab) (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256)
  (RA : ℕ → BitVec 256)

theorem hc_one : hcell T bits y0 A RA oneCell = oneV := by unfold hcell oneCell; hsimp
theorem hc_g : hcell T bits y0 A RA gCell = gV := by unfold hcell gCell; hsimp

theorem hc_c {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ 22) : hcell T bits y0 A RA (cCell c) = cV c := by
  by_cases h16 : c = 16
  · subst c; rw [cV_sixteen]; exact hc_g ..
  · have hc : cCell c = 50 + c := by unfold cCell; rw [if_neg (by omega), if_neg h16]
    rw [hc]; unfold hcell; hsimp; congr 1; omega

theorem hc_frame {r : ℕ} (hr : r < 15) : hcell T bits y0 A RA (fCell r) = frameV r := by
  rw [fCell, frameV_eq_cV]; exact hc_c T bits y0 A RA (by omega) (by omega)

theorem hc_idx : hcell T bits y0 A RA idxCell = loC y0 := by unfold hcell idxCell; hsimp
theorem hc_idx1 : hcell T bits y0 A RA (idxCell + 1) = hiC y0 := by unfold hcell idxCell; hsimp

theorem hc_t {u : ℕ} (hu : u < 13) :
    hcell T bits y0 A RA (tCell u) = fpat u (hxs T (idxOf y0) (u + 1)) := by
  unfold hcell tCell; hsimp; congr 2 <;> omega

theorem hc_acc {u : ℕ} (hu : u < 12) :
    hcell T bits y0 A RA (accCell u) =
      natV (ofDigitsW gb (fun w => hxs T (idxOf y0) (w + 1)) (u + 1)) := by
  rw [show accCell u = 120 + u from if_neg (by omega)]; unfold hcell; hsimp; congr 2; omega

theorem hc_h {r : ℕ} (hr : r < 14) :
    hcell T bits y0 A RA (hCell r) = ofK (gpow (ent r (hxs T (idxOf y0) r))) := by
  unfold hcell hCell; hsimp; rw [show 160 + r - 160 = r by omega]

theorem hc_h1 {r : ℕ} (hr : r < 14) :
    hcell T bits y0 A RA (h1Cell r) = ofK (gpow (ent r (hxs T (idxOf y0) r) + 1)) := by
  unfold hcell h1Cell; hsimp; rw [show 180 + r - 180 = r by omega]

theorem hc_gp {u : ℕ} (hu : u ≤ 13) :
    hcell T bits y0 A RA (gpCell u) = gpV T (idxOf y0) u := by
  unfold gpCell hcell; hsimp; congr 1; omega

theorem hc_tf : hcell T bits y0 A RA tfCell = cellOfBits (topOf T bits y0 A 0) := by
  simp [hcell,tfCell,pairK,topPair,topOff]

theorem hc_tf1 : hcell T bits y0 A RA (tfCell+1) = hiOf T y0 A 0 := by
  simp [hcell,tfCell,pairK,topPair,topOff]

theorem hc_top {k : ℕ} (hk : k<42) (_he : cvTop k) :
    hcell T bits y0 A RA (topCell k) = cellOfBits (topOf T bits y0 A k) ∧
      hcell T bits y0 A RA (junkCell k (topCell k)) = hiOf T y0 A k := by
  interval_cases k <;> simp [topCell,junkCell,topOff,hcell,topPair,pairK]

theorem hc_xh {k : ℕ} (hk : k<42) (_hk0 : k≠0) (_he : ¬ exported k) :
    hcell T bits y0 A RA (xhCell k) = cellOfBits (topOf T bits y0 A k) ∧
      hcell T bits y0 A RA (junkCell k (xhCell k)) = hiOf T y0 A k := hc_top T bits y0 A RA hk trivial

theorem hc_st {r : ℕ} (hr : r<3) :
    hcell T bits y0 A RA (stCell r) = loC (RA r) ∧
      hcell T bits y0 A RA (stCell r+1) = hiC (RA r) := by
  interval_cases r <;> simp [hcell,stCell]

theorem hc_xc {k t : ℕ} (hk : k < 42) (ht : t < LEN k) :
    hcell T bits y0 A RA (xcCell k t) = loC (A k t) ∧
      hcell T bits y0 A RA (xcCell k t + 1) = hiC (A k t) := by
  obtain ⟨b1, b2⟩ := xc_band hk (show 2 * t + 1 < 2 * LEN k by omega)
  have h0 := xcBase_mono (Nat.zero_le k)
  have h42 := xcBase_mono (show k + 1 ≤ 42 by omega)
  rw [xcBase_zero] at h0
  rw [xcBase_42, xcBase_succ] at h42
  have hx : xcCell k t = xcBase k + 2 * t := rfl
  constructor
  · unfold hcell; rw [b1, hx]; hsimp; congr 2; omega
  · unfold hcell; rw [b2, hx]; hsimp; congr 2; omega

end Cells

/-! ## Canonical cells and generic relations -/

theorem canon_cellOfBits (b : BitVec 128) : IsCanonical128 (cellOfBits b) := by
  show (cellOfBits b).limb 2 = 0
  simp [cellOfBits]

theorem canon_natV (n : ℕ) : IsCanonical128 (natV n) := canon_cellOfBits _
theorem canon_loC (a : BitVec 256) : IsCanonical128 (loC a) := canon_cellOfBits _
theorem canon_hiC (a : BitVec 256) : IsCanonical128 (hiC a) := canon_cellOfBits _
theorem canon_ofK (a : K) : IsCanonical128 (ofK a) := by
  show (ofK a).limb 2 = 0; rw [limb_ofK]; rfl
theorem canon_zero : IsCanonical128 (0 : E) := by
  show (0 : E).limb 2 = 0; exact limb_zero 2

theorem cellBits_loC (a : BitVec 256) : cellBits (loC a) = a.extractLsb' 0 128 := cellBits_cellOfBits _
theorem cellBits_hiC (a : BitVec 256) : cellBits (hiC a) = a.extractLsb' 128 128 :=
  cellBits_cellOfBits _

theorem canon_hiOf (T : Tab) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (k : ℕ) :
    IsCanonical128 (hiOf T y0 A k) := by
  unfold hiOf; split_ifs
  · exact canon_zero
  · exact canon_cellOfBits _

/-- A `BLAKE2S` whose nine cells are canonical and whose output pair is the answer holds. -/
theorem canon_topPair (T : Tab) (bits : List Bool) (y0 : BitVec 256)
    (A : ℕ → ℕ → BitVec 256) (k b : ℕ) : IsCanonical128 (topPair T bits y0 A k b) := by
  unfold topPair; split_ifs
  · exact canon_cellOfBits _
  · exact canon_hiOf _ _ _ _

theorem canon_gpV (T : Tab) (I : Word) (u : ℕ) : IsCanonical128 (gpV T I u) := canon_ofK _
theorem canon_cV (c : ℕ) : IsCanonical128 (cV c) := canon_ofK _
theorem canon_fpat (u v : ℕ) : IsCanonical128 (fpat u v) := canon_natV _
theorem canon_oneV : IsCanonical128 oneV := canon_ofK _
theorem canon_gV : IsCanonical128 gV := canon_ofK _

set_option maxRecDepth 4000 in
theorem canon_hcell (T : Tab) (bits : List Bool) (y0 : BitVec 256)
    (A : ℕ → ℕ → BitVec 256) (RA : ℕ → BitVec 256) (c : ℕ) :
    IsCanonical128 (hcell T bits y0 A RA c) := by
  simp only [hcell, apply_ite IsCanonical128, canon_zero, canon_cellOfBits, canon_ofK, canon_natV,
    canon_loC, canon_hiC, canon_hiOf, canon_topPair, canon_gpV, canon_cV, canon_fpat,
    canon_oneV, canon_gV, ite_self]

theorem blake_rel {f : HashTable} {v : ℕ → E} {m0 m1 m2 m3 cv out md : ℕ} {a : BitVec 256}
    (h0 : IsCanonical128 (v m0)) (h1 : IsCanonical128 (v m1)) (h2 : IsCanonical128 (v m2))
    (h3 : IsCanonical128 (v m3)) (hc0 : IsCanonical128 (v cv)) (hc1 : IsCanonical128 (v (cv + 1)))
    (hmd : IsCanonical128 (v md))
    (hq : ans f (blake2sQuery ![v m0, v m1, v m2, v m3] (v cv) (v (cv + 1)) (v md)) = a)
    (hlo : v out = loC a) (hhi : v (out + 1) = hiC a) :
    (CInstr.blake m0 m1 m2 m3 cv out md).Rel f v := by
  show oracleRel f _ _ _ _ _ _
  unfold oracleRel
  refine ⟨fun i => ?_, hc0, hc1, ?_, ?_, hmd, ?_, ?_⟩
  · fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rw [hlo]; exact canon_loC a
  · rw [hhi]; exact canon_hiC a
  · rw [hlo, cellBits_loC]; exact congrArg (fun b : BitVec 256 => b.extractLsb' 0 128) hq.symm
  · rw [hhi, cellBits_hiC]; exact congrArg (fun b : BitVec 256 => b.extractLsb' 128 128) hq.symm

end
end OptimalOTS.HLFusion
