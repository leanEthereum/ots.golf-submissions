import Submissions.UpperLeanIsa.FreeLastProver

/-! Physical cell inverses and canonical values of the honest fused image. -/
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OptimalOTS.FreeLastVM
open OracleComp LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
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
theorem hc_g : hcell T bits y0 A RA gCell = gV T := by unfold hcell gCell; hsimp

theorem hc_c {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ 13) : hcell T bits y0 A RA (cCell c) = cV T c := by
  by_cases h4 : c ≤ 4
  · interval_cases c <;> simp [cCell,hcell]
  · have hc : cCell c = 50+c := by simp [cCell,show c ≠ 14 by omega,show c ≠ 0 by omega,
      show c ≠ 1 by omega,show c ≠ 2 by omega,show c ≠ 3 by omega,show c ≠ 4 by omega]
    rw [hc]; unfold hcell; hsimp; congr 1; omega

theorem hc_idx : hcell T bits y0 A RA idxCell = loC y0 := by unfold hcell idxCell; hsimp
theorem hc_idx1 : hcell T bits y0 A RA (idxCell + 1) = hiC y0 := by unfold hcell idxCell; hsimp

theorem hc_t {u : ℕ} (hu : u < 13) :
    hcell T bits y0 A RA (tCell u) = FreeLastBlocks.pattern u (hxs T (idxOf y0) (u + 1)) := by
  interval_cases u <;> simp [hcell, tCell]

theorem hc_acc {u : ℕ} (hu : u < 12) :
    hcell T bits y0 A RA (accCell u) =
      cellOfBits (FreeLastTie.accBits (fun w => hxs T (idxOf y0) (w + 1)) u) := by
  rw [show accCell u = 120 + u from if_neg (by omega)]; unfold hcell; hsimp; congr 2; omega

theorem hc_h {r : ℕ} (hr : r < 14) :
    hcell T bits y0 A RA (hCell r) = ofK (gpow (entryK T (idxOf y0) r)) := by
  unfold hcell hCell; hsimp; rw [show 160 + r - 160 = r by omega]

theorem hc_h1 {r : ℕ} (hr : r < 14) :
    hcell T bits y0 A RA (h1Cell r) = ofK (frameK T (idxOf y0) r) := by
  unfold hcell h1Cell; hsimp; rw [show 180 + r - 180 = r by omega]

theorem hc_gp {u : ℕ} (hu : u ≤ 13) :
    hcell T bits y0 A RA (gpCell u) = gpV T (idxOf y0) u := by
  unfold gpCell hcell; hsimp; congr 1; omega

theorem hc_tf : hcell T bits y0 A RA tfCell = cellOfBits (topOf T bits y0 A 0) := by
  simp [hcell,tfCell,pairK,topPair,topOff,topCell]

theorem hc_tf1 : hcell T bits y0 A RA (tfCell+1) = hiOf T y0 A 0 := by
  simp [hcell,tfCell,pairK,topPair,topOff,topCell]

theorem hc_top {k : ℕ} (hk : k<42) (_he : cvTop k) :
    hcell T bits y0 A RA (topCell k) = cellOfBits (topOf T bits y0 A k) ∧
      hcell T bits y0 A RA (junkCell k (topCell k)) = hiOf T y0 A k := by
  interval_cases k <;> simp [topCell,junkCell,topOff,hcell,topPair,pairK]

theorem hc_xh {k : ℕ} (hk : k<42) (_hk0 : k≠0) (_he : ¬ exported k) :
    hcell T bits y0 A RA (xhCell k) = cellOfBits (topOf T bits y0 A k) ∧
      hcell T bits y0 A RA (junkCell k (xhCell k)) = hiOf T y0 A k := hc_top T bits y0 A RA hk trivial

theorem hc_st {r : ℕ} (hr : r<1) :
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
theorem canon_cV (T : Tab) (c : ℕ) : IsCanonical128 (cV T c) := canon_ofK _
theorem canon_pattern (u v : ℕ) : IsCanonical128 (FreeLastBlocks.pattern u v) := canon_cellOfBits _
theorem canon_oneV : IsCanonical128 oneV := canon_ofK _
theorem canon_gV (T : Tab) : IsCanonical128 (gV T) := canon_ofK _

set_option maxRecDepth 4000 in
theorem canon_hcell (T : Tab) (bits : List Bool) (y0 : BitVec 256)
    (A : ℕ → ℕ → BitVec 256) (RA : ℕ → BitVec 256) (c : ℕ) :
    IsCanonical128 (hcell T bits y0 A RA c) := by
  simp only [hcell, apply_ite IsCanonical128, canon_zero, canon_cellOfBits, canon_ofK, canon_natV,
    canon_loC, canon_hiC, canon_hiOf, canon_topPair, canon_gpV, canon_cV, canon_pattern,
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
end OptimalOTS.FreeLastVM


/-! The loaded honest image: indices, dependencies and fixed-oracle answers. -/
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OptimalOTS.FreeLastVM
open OracleComp LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV ans inputWord_sig inputWord_pk inputWord_nonce inputWord_one inputWord_two inputWord_len_of)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section

open FourFusion in
theorem reconstruction_spec (P : FourFusion.Params) (f : HashTable) (I : Index) (bits : List Bool)
    (l : List (Fin 42)) (hl : l.Pairwise (fun k k' => evaluationRank k.val < evaluationRank k'.val)) (t : Tops) :
    let t' := P.reconFromValue f I bits l t
    ∀ k ∈ l, P.chainValue f t' k (P.codec.len k-1-P.codec.digit I k) (P.codec.digit I k)
      (decodeWord bits k) = t' k.val := by
  induction l generalizing t with
  | nil => simp
  | cons k l ih =>
    obtain ⟨hbefore,hl⟩ := List.pairwise_cons.mp hl
    let t' := P.reconFromValue f I bits (k::l) t
    have hdep : ∀ u : Fin 8, owner k = some u → ∀ d ∈ children u, t d = t' d := by
      intro u hu d hd
      apply (P.reconFromValue_preserves f I bits (k::l) t d ?_).symm
      intro hmem
      have hr := dependency_precedes u u.isLt k.val ((owner_mem k u).mp hu) d hd
      change evaluationRank d < evaluationRank k.val at hr
      obtain ⟨k',hk',he⟩ := List.mem_map.mp hmem
      rcases List.mem_cons.mp hk' with he' | hk'
      · have heq : d=k.val := he.symm.trans (congrArg Fin.val he')
        rw [heq] at hr; omega
      · have hh := hbefore k' hk'; rw [he] at hh; omega
    have hknot : k.val ∉ l.map Fin.val := by
      rintro hmem
      obtain ⟨k',hk',he⟩ := List.mem_map.mp hmem
      have hh := hbefore k' hk'; rw [he] at hh; omega
    have htop : t' k.val = P.chainValue f t k (P.codec.len k-1-P.codec.digit I k)
        (P.codec.digit I k) (decodeWord bits k) := by
      change P.reconFromValue f I bits l (Function.update t k.val _) k.val = _
      rw [P.reconFromValue_preserves _ _ _ _ _ _ hknot,Function.update_self]
    intro tt k' hk'
    rcases List.mem_cons.mp hk' with he | hk'
    · subst k'
      exact (P.chainValue_context f t t' k _ _ _ hdep).symm.trans htop.symm
    · exact ih hl _ k' hk'

section Honest
variable (P : FourFusion.Params) (T : Tab) (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

/-- The loaded honest image, as cell values. -/
def hv (c : ℕ) : E := Lx (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) c

/-- The honest index. -/
abbrev IF : Word := idxOf (y0F P f pk m bits)

/-- The honest index vector. -/
abbrev XF : ℕ → ℕ := hxs T (IF P f pk m bits)

theorem hv_lt {c : ℕ} (h : c < 47) : hv P T f pk m bits c = inputWord pk m bits c :=
  Lx_loadInput_pin (le_refl 16) pk m bits _ h

theorem hv_ge {c : ℕ} (h1 : 47 ≤ c) (h2 : c < 2 ^ 16) :
    hv P T f pk m bits c =
      hcell T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) c := by
  unfold hv
  rw [Lx_loadInput pk m bits _ h2, if_neg (by omega)]
  unfold Lx; rw [dif_pos h2]; rfl

theorem hv_canonical (c : ℕ) : IsCanonical128 (hv P T f pk m bits c) := by
  by_cases h47 : c < 47
  · rw [hv_lt P T f pk m bits h47]
    unfold inputWord
    exact canon_cellOfBits _
  · by_cases hc : c < 2 ^ 16
    · rw [hv_ge P T f pk m bits (by omega) hc]
      exact canon_hcell _ _ _ _ _ _
    · unfold hv Lx; rw [dif_neg hc]; exact canon_zero

theorem hxs_zero (I : Word) : hxs T I 0 = freeDigit (gcost T I) := if_pos rfl

theorem hxs_succ (I : Word) (u : ℕ) : hxs T I (u + 1) = field u I := by
  unfold hxs; rw [if_neg (by omega), Nat.add_sub_cancel]

theorem hxs_zero_lt (I : Word) : hxs T I 0 < 64 := by
  rw [hxs_zero]; unfold freeDigit; split_ifs <;> omega

/-- The honest index vector of an index without dummy fields is in range. -/
theorem hxs_valid (I : Word) (hl : ∀ u < 13, field u I < VF u) : Valid (hxs T I) := by
  intro r hr
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · rw [Wf_zero]; exact hxs_zero_lt T I
  · obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
    rw [hxs_succ, Wf_succ (by omega)]; exact hl u (by omega)

/-- The honest digits are the scheme's. -/
theorem hd_eq (hC : Compat P T) (y0 : BitVec 256) (hl : ∀ u < 13, field u (idxOf y0) < VF u)
    (k : Fin numChains) : hd T y0 k.val = P.codec.digit (effective (idxOf y0)) k := by
  unfold hd dg
  by_cases hk0 : k.val = 0
  · rw [if_pos hk0, hxs_zero, ← hC.digit_free _ hl]
    congr 1; exact Fin.ext hk0.symm
  · rw [if_neg hk0]
    obtain ⟨hu, hi, hc⟩ := chainOf_unitOf k.val k.isLt (by omega)
    have hk : k = ⟨chainOf (unitOf k.val) (coordOf k.val), chainOf_lt _ hu _ hi⟩ :=
      Fin.ext hc.symm
    rw [hxs_succ, hk, hC.digit_grp _ _ _ hu hi]
    simp only [hc]

theorem hd_lt (hT : T.Hyp) (y0 : BitVec 256) {k : ℕ} (hk : k < 42) : hd T y0 k < LEN k :=
  dg_lt_raw hT (hxs_zero_lt T _) (fun u _ => by rw [hxs_succ]; exact digitW_lt _ _ _) hk

theorem AF_eq {k : ℕ} (hk : k < 42) (t : ℕ) :
    AF P T f pk m bits k t = chainAnsF P f (ctxF P f pk m bits) ⟨k, hk⟩ (LEN k - 1 - hd T (y0F P f pk m bits) k)
      (hd T (y0F P f pk m bits) k) (sigW bits k) t := by
  unfold AF chainTab; rw [dif_pos hk]

/-- The honest chain values. -/
theorem AF_spec {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < hd T (y0F P f pk m bits) k) :
    AF P T f pk m bits k t = ans f (P.chainInput (ctxF P f pk m bits) ⟨k, hk⟩
      (LEN k - 1 - hd T (y0F P f pk m bits) k + t)
      (P.chainValue f (ctxF P f pk m bits) ⟨k, hk⟩ (LEN k - 1 - hd T (y0F P f pk m bits) k) t (sigW bits k))) := by
  rw [AF_eq P T f pk m bits hk, chainAnsF_spec P f _ _ _ _ _ _ ht]

/-- The honest top of chain `k` is the verifier's chain value. -/
theorem topOf_eq (hT : T.Hyp) (hC : Compat P T) {k : ℕ} (hk : k < 42) :
    topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k =
      P.chainValue f (ctxF P f pk m bits) ⟨k, hk⟩ (LEN k - 1 - hd T (y0F P f pk m bits) k)
        (hd T (y0F P f pk m bits) k) (sigW bits k) := by
  unfold topOf
  by_cases h0 : hd T (y0F P f pk m bits) k = 0
  · rw [if_pos h0, h0]; rfl
  · rw [if_neg h0]
    obtain ⟨u, hu⟩ : ∃ u, hd T (y0F P f pk m bits) k = u + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero h0).symm⟩
    have hs := AF_spec P T f pk m bits hk (t := u) (by omega)
    rw [hu, Nat.add_sub_cancel, hs, hu, chainValue_succ]
    simp only [Params.slice]
    have hd := hd_lt T hT (y0F P f pk m bits) hk
    rw [hu] at hd
    rw [stepOff_eq hC hk hd (by omega), if_pos (by omega)]

/-! ### Cell values of the loaded honest image -/

section Values

variable {P T f pk m bits}

theorem hv_c {c : ℕ} (h1 : 47 ≤ c) (h2 : c < 2 ^ 16) {x : E}
    (h : hcell T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) c = x) :
    hv P T f pk m bits c = x := (hv_ge P T f pk m bits h1 h2).trans h

theorem hv_one : hv P T f pk m bits oneCell = oneV := hv_c (by decide) (by decide) (hc_one ..)
theorem hv_g : hv P T f pk m bits gCell = gV T := hv_c (by decide) (by decide) (hc_g ..)
theorem hv_cc {c : ℕ} (hc : c ≤ 13) : hv P T f pk m bits (cCell c) = cV T c := by
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · simpa only [cV,pow_zero,oneV,cCell,ite_true,oneCell] using (hv_one (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits))
  · exact hv_c (by unfold cCell; split_ifs <;> omega)
      (by unfold cCell; split_ifs <;> omega) (hc_c _ _ _ _ _ h0 hc)

theorem hv_cost_c {c : ℕ} (hc : c ≤ 14) : hv P T f pk m bits (cCell c) = cV T c := by
  by_cases h14 : c = 14
  · subst c
    exact hv_g
  · exact hv_cc (by omega)
theorem hv_idx : hv P T f pk m bits idxCell = loC (y0F P f pk m bits) :=
  hv_c (by decide) (by decide) (hc_idx ..)
theorem hv_idx1 : hv P T f pk m bits (idxCell + 1) = hiC (y0F P f pk m bits) :=
  hv_c (by decide) (by decide) (hc_idx1 ..)
theorem hv_t {u : ℕ} (hu : u < 13) :
    hv P T f pk m bits (tCell u) = FreeLastBlocks.pattern u (XF P T f pk m bits (u + 1)) :=
  hv_c (by unfold tCell; split_ifs <;> omega) (by unfold tCell; split_ifs <;> omega) (hc_t _ _ _ _ _ hu)
theorem hv_accl {u : ℕ} (hu : u < 12) :
    hv P T f pk m bits (accCell u) =
      cellOfBits (FreeLastTie.accBits (fun w => XF P T f pk m bits (w + 1)) u) :=
  hv_c (by unfold accCell; split_ifs <;> omega)
    (by unfold accCell; split_ifs <;> omega) (hc_acc _ _ _ _ _ hu)
abbrev XFr (r : ℕ) : ℕ := XF P T f pk m bits r

theorem hv_h {r : ℕ} (hr : r<14) :
    hv P T f pk m bits (hCell r) = ofK (gpow (entryK T (IF P f pk m bits) r)) :=
  hv_c (by unfold hCell; omega) (by unfold hCell; omega) (hc_h _ _ _ _ _ hr)

theorem hv_h1 {r : ℕ} (hr : r<14) :
    hv P T f pk m bits (h1Cell r) = ofK (frameK T (IF P f pk m bits) r) :=
  hv_c (by unfold h1Cell; omega) (by unfold h1Cell; omega) (hc_h1 _ _ _ _ _ hr)

theorem hv_gpl {u : ℕ} (hu : u ≤ 13) :
    hv P T f pk m bits (gpCell u) = gpV T (IF P f pk m bits) u :=
  hv_c (by unfold gpCell; omega)
    (by unfold gpCell; omega) (hc_gp _ _ _ _ _ hu)

theorem hv_tf : hv P T f pk m bits tfCell =
    cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) 0) :=
  hv_c (by decide) (by decide) (hc_tf ..)
theorem hv_tf1 : hv P T f pk m bits (tfCell + 1) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) 0 :=
  hv_c (by decide) (by decide) (hc_tf1 ..)
theorem hv_top {k : ℕ} (hk : k < 42) (he : cvTop k) :
    hv P T f pk m bits (topCell k) =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k (topCell k)) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k := by
  have h1 := topCell_lt hk
  have h2 : 256 ≤ topCell k := by
    have hh : ∀ k<42, 256 ≤ topCell k := by decide
    exact hh k hk
  have h3 : 255 ≤ junkCell k (topCell k) ∧ junkCell k (topCell k) < 347 := by
    unfold junkCell; split_ifs <;> omega
  obtain ⟨e1, e2⟩ := hc_top T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) hk he
  exact ⟨hv_c (by omega) (by omega) e1, hv_c (by omega) (by omega) e2⟩
theorem hv_xh {k : ℕ} (hk : k<42) (_hk0 : k≠0) (_he : ¬ exported k) :
    hv P T f pk m bits (xhCell k) = cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k (xhCell k)) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k := hv_top hk trivial

theorem hv_st {r : ℕ} (hr : r<1) :
    hv P T f pk m bits (stCell r) = loC (RAF P T f pk m bits r) ∧
      hv P T f pk m bits (stCell r+1) = hiC (RAF P T f pk m bits r) := by
  have hh : ∀ r<1, 256 ≤ stCell r ∧ stCell r+1<346 := by decide
  have hb := hh r hr
  obtain ⟨e1,e2⟩ := hc_st T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) hr
  exact ⟨hv_c (by omega) (by omega) e1,hv_c (by omega) (by omega) e2⟩

theorem hv_xc {k t : ℕ} (hk : k < 42) (ht : t < LEN k) :
    hv P T f pk m bits (xcCell k t) = loC (AF P T f pk m bits k t) ∧
      hv P T f pk m bits (xcCell k t + 1) = hiC (AF P T f pk m bits k t) := by
  have hb := xcBase_bound k hk
  have h0 := xcBase_mono (Nat.zero_le k); rw [xcBase_zero] at h0
  obtain ⟨e1, e2⟩ := hc_xc T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) hk ht
  exact ⟨hv_c (by unfold xcCell; omega) (by unfold xcCell; omega) e1,
    hv_c (by unfold xcCell; omega) (by unfold xcCell; omega) e2⟩

/-- The revealed words (for an admitted length). -/
theorem hv_w (hlen : bits.length = 5504) {k : ℕ} (hk : k < 42) :
    hv P T f pk m bits (wCell k) = cellOfBits (sigW bits k) := by
  rw [hv_lt P T f pk m bits (by unfold wCell; omega), show wCell k = 4 + k from rfl,
    inputWord_sig pk m bits hlen k]
  rfl

theorem hv_rtop (hlen : bits.length=5504) {k : ℕ} (hk : k<42) :
    hv P T f pk m bits (rtopCell k (hd T (y0F P f pk m bits) k)) =
      cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) := by
  unfold rtopCell
  split_ifs with hh
  · rw [hv_w hlen hk]
    unfold topOf; rw [if_pos hh.1]
  · exact (hv_top hk trivial).1

end Values

section Accepted

variable {P T f pk m bits}
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length = 5504)
  (hacc : P.codec.Accepted (effective (IF P f pk m bits)))
  (hroot : rootValue f P (topsOf f P (effective (IF P f pk m bits)) bits) = pk)

include hC hacc in
/-- The accepted honest index has no dummy field. -/
theorem hlive : ∀ u < 13, field u (IF P f pk m bits) < VF u := hC.live _ hacc

include hC hacc in
theorem hsum : XF P T f pk m bits 0 + gsum T (XF P T f pk m bits) = 85 := by
  have h : ∑ k : Fin numChains, P.codec.digit (effective (IF P f pk m bits)) k = P.codec.layer := hacc
  rw [hC.layer, Finset.sum_congr rfl (fun k _ => (hd_eq P T hC _ (hlive hC hacc) k).symm),
    Fin.sum_univ_eq_sum_range (fun k => hd T (y0F P f pk m bits) k) 42] at h
  unfold hd at h
  rw [dg_sum] at h
  exact h

include hacc in
theorem topsOfV_eq (hT : T.Hyp) (hC : Compat P T) :
    topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits) =
      topsOf f P (effective (IF P f pk m bits)) bits := by
  funext k
  by_cases hk : k<42
  · rw [topsOfV,if_pos hk,topOf_eq P T f pk m bits hT hC hk]
    rw [hd_eq P T hC _ (hlive hC hacc) ⟨k,hk⟩,← hC.len ⟨k,hk⟩]
    exact reconstruction_spec P f _ bits FourFusion.chainOrder FourFusion.Params.chainOrder_ranked
      (fun _ => 0) ⟨k,hk⟩ (FourFusion.chainOrder_permutation.mem_iff.mpr (List.mem_finRange ⟨k,hk⟩))
  · rw [topsOfV,if_neg hk]
    symm
    exact P.reconFromValue_preserves f _ bits FourFusion.chainOrder (fun _ => 0) k (by
      rintro hmem
      obtain ⟨j,_,he⟩ := List.mem_map.mp hmem
      have hj := j.isLt
      rw [he] at hj
      exact hk hj)

include hC hlen in
/-- The index query of the honest image. -/
theorem honest_idx_query :
    blake2sQuery ![hv P T f pk m bits msgLo, hv P T f pk m bits msgHi,
      hv P T f pk m bits nonceCell, hv P T f pk m bits pkCell] (hv P T f pk m bits (cCell 1))
      (hv P T f pk m bits (cCell 1 + 1)) (hv P T f pk m bits (cCell 11)) =
      P.codec.idxInput m (decodeNonce bits) pk := by
  have hpk : cellBits (hv P T f pk m bits pkCell) = pk := by
    rw [show pkCell = 0 from rfl, hv_lt P T f pk m bits (by omega), inputWord_pk]
    exact cellBits_cellOfBits pk
  rw [blake2sQuery_eq, show cCell 1 + 1 = cCell 2 from rfl,
    hv_cc (c:=1) (by decide), hv_cc (c:=2) (by decide), hv_cc (c:=11) (by decide),
    show nonceCell = 46 from rfl, show msgHi = 2 from rfl, show msgLo = 1 from rfl,
    hv_lt P T f pk m bits (show 46 < 47 by omega), hv_lt P T f pk m bits (show 2 < 47 by omega),
    hv_lt P T f pk m bits (show 1 < 47 by omega), inputWord_nonce pk m bits hlen, inputWord_two,
    inputWord_one, cellBits_cellOfBits (nonceWord (decodeNonce bits)),
    cellBits_cellOfBits (m.extractLsb' 128 128), cellBits_cellOfBits (m.extractLsb' 0 128),
    msg_split, hpk]
  unfold Params.idxInput
  rw [hC.cv, hC.idxMd]

end Accepted
end Honest
end
end OptimalOTS.FreeLastVM


/-! Honest chain assertions, including the fused dependency packet at each binding endpoint
using four or five children and separated domain words. -/
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OptimalOTS.FreeLastVM
open OracleComp LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV ans inputWord_len_of)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
variable {P : FourFusion.Params} {T : Tab} {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length=5504)
  (hacc : P.codec.Accepted (effective (IF P f pk m bits)))

include hT hC hacc in
theorem honest_topBits {k : ℕ} (hk : k<42) :
    cellBits (hv P T f pk m bits (topCell k)) = ctxF P f pk m bits k := by
  rw [(hv_top hk trivial).1,cellBits_cellOfBits]
  have hh := congrFun (topsOfV_eq hacc hT hC) k
  rw [topsOfV,if_pos hk] at hh
  exact hh


include hC hlen hacc in
theorem honest_fusedMd (k : Fin 42) (_hk : binds k.val) :
    cellBits (hv P T f pk m bits (fusedMdCell k.val)) = P.fusedMd k := by
  rw [hC.fusedMd]
  have he : ∀ k : Fin 42, fusedMdCell k.val =
      if (FourFusion.mdIndex k).val = 17 then lenCell else cCell (FourFusion.mdIndex k).val := by decide
  rw [he]
  unfold FreeLastCodec.domainWord
  by_cases h17 : (FourFusion.mdIndex k).val = 17
  · rw [if_pos h17, if_pos h17]
    have hl : hv P T f pk m bits lenCell = natV 5504 := by
      rw [hv_lt P T f pk m bits (by decide)]
      exact inputWord_len_of pk m bits hlen
    rw [hl]
    rfl
  · have hi : (FourFusion.mdIndex k).val ≤ 13 := by
      have hb : ∀ k : Fin 42, (FourFusion.mdIndex k).val ≤ 13 ∨
          (FourFusion.mdIndex k).val = 17 := by decide
      exact (hb k).resolve_right h17
    rw [if_neg h17, if_neg h17, hv_cc hi, factor_bits T _]

include hC hlen in
theorem honest_fusedTag (k : Fin 42) :
    cellBits (hv P T f pk m bits (fusedTagCell k.val)) = P.fusedTag k := by
  rw [hC.fusedTag]
  have hsmall : ∀ k : Fin 42,
      fusedTagCell k.val = (if (FourFusion.tagIndex k).val = 12 then lenCell else
        cCell (FourFusion.tagIndex k).val) ∧ (FourFusion.tagIndex k).val ≤ 12 := by decide
  obtain ⟨he,hi⟩ := hsmall k
  rw [he]
  unfold FreeLastCodec.tagWord
  by_cases h12 : (FourFusion.tagIndex k).val = 12
  · rw [if_pos h12,if_pos h12,hv_lt P T f pk m bits (by decide),
      show lenCell = 3 from rfl,inputWord_len_of pk m bits hlen]
    rfl
  · rw [if_neg h12,if_neg h12,hv_cc (by omega),factor_bits T _]

def HonestReadContext (readTop : ℕ → ℕ) (k : Fin 42) : Prop :=
  ∀ u : Fin 8, FourFusion.owner k = some u →
    ∀ i < (FourFusion.children u).length,
      cellBits (hv P T f pk m bits (readTop ((FourFusion.children u).getD i 0))) =
        ctxF P f pk m bits ((FourFusion.children u).getD i 0)

include hT hC hlen hacc in
theorem honest_groupRead_context (k : Fin 42) :
    HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits)
      (groupRead T (unitOf k.val) (XF P T f pk m bits (unitOf k.val+1))) k := by
  intro u ho i hi
  have hk : binds k.val := (binds_owner k).mpr (by rw [ho]; simp)
  have hdep := (fusion_cells k hk u ho).2.2 i hi
  rw [groupRead_rtop T (XF P T f pk m bits) hdep.2.2 hdep.2.1]
  change cellBits (hv P T f pk m bits (rtopCell _ (hd T (y0F P f pk m bits) _))) = _
  rw [hv_rtop hlen hdep.2.2,cellBits_cellOfBits]
  have hh := congrFun (topsOfV_eq hacc hT hC) ((FourFusion.children u).getD i 0)
  simpa only [topsOfV,if_pos hdep.2.2,ctxF,IF] using hh

include hT hC hlen hacc in
theorem honest_fusion_query (readTop : ℕ → ℕ) (k : Fin 42) (hk : binds k.val)
    (u : Fin 8) (hu : FourFusion.owner k = some u)
    (hread : HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) readTop k)
    (x : E) :
    blake2sQuery ![x,hv P T f pk m bits (readTop (depTop k.val 2)),
      hv P T f pk m bits (readTop (depTop k.val 3)),
      hv P T f pk m bits (if fiveChildren k.val then readTop (depTop k.val 4) else fusedTagCell k.val)]
      (hv P T f pk m bits (depCv k.val)) (hv P T f pk m bits (depCv k.val+1))
      (hv P T f pk m bits (fusedMdCell k.val)) =
      FourFusion.packet (FourFusion.fusionWords (ctxF P f pk m bits) u (cellBits x)
        (P.fusedTag k) (P.fusedMd k)) := by
  obtain ⟨hc0,hc1,hd⟩ := fusion_cells k hk u hu
  have hl : 4 ≤ (FourFusion.children u).length := by
    have hh : ∀ u : Fin 8, 4 ≤ (FourFusion.children u).length := by decide
    exact hh u
  rw [blake2sQuery_eq,hc1,hc0,honest_fusedMd hC hlen hacc k hk]
  unfold FourFusion.packet Fusion.packet FourFusion.fusionWords
  simp only [Matrix.cons_val,Fin.isValue]
  rw [(hd 2 (by omega)).1,(hd 3 (by omega)).1,hread u hu 2 (by omega),hread u hu 3 (by omega),
    honest_topBits hT hC hacc (hd 0 (by omega)).2.2,
    honest_topBits hT hC hacc (hd 1 (by omega)).2.2]
  by_cases hf : FourFusion.five u = true
  · have hf' := (fiveChildren_owner k u hu).mpr hf
    have hl5 : 4 < (FourFusion.children u).length := by
      rw [Fusion.SplitRoot.packet_lengths u u.isLt, if_pos hf]
      decide
    rw [if_pos hf', if_pos hf, (hd 4 hl5).1, hread u hu 4 hl5]
  · have hf' : ¬ fiveChildren k.val := fun hh => hf ((fiveChildren_owner k u hu).mp hh)
    rw [if_neg hf', if_neg hf, honest_fusedTag hC hlen k]

include hT hC hlen hacc in
/-- The honest chain step `t` of chain `k` (the last writes `dst`). -/
theorem honest_chainOp (readTop : ℕ → ℕ) {k : ℕ} (hk : k < 42)
    (hread : HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) readTop ⟨k,hk⟩)
    {t dst : ℕ}
    (ht : t < hd T (y0F P f pk m bits) k)
    (hdstpos : 1 ≤ dst)
    (hdst : hv P T f pk m bits dst =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k dst) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k) :
    (chainOp readTop k (hd T (y0F P f pk m bits) k) t dst).Rel f (hv P T f pk m bits) := by
  set d := hd T (y0F P f pk m bits) k with hddef
  have hdl := hd_lt T hT (y0F P f pk m bits) hk
  rw [← hddef] at hdl
  have hsrc : IsCanonical128 (hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1))) ∧
      cellBits (hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1))) =
        P.chainValue f (ctxF P f pk m bits) ⟨k, hk⟩ (LEN k - 1 - d) t (sigW bits k) := by
    by_cases h0 : t = 0
    · rw [if_pos h0, hv_w hlen hk, cellBits_cellOfBits, h0]
      exact ⟨canon_cellOfBits _, rfl⟩
    · rw [if_neg h0, (hv_xc hk (show t - 1 < LEN k by omega)).1, cellBits_loC]
      refine ⟨canon_loC _, ?_⟩
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      rw [Nat.add_sub_cancel, AF_spec P T f pk m bits hk (by omega), chainValue_succ]
      simp only [Params.slice]
      rw [stepOff_eq hC hk hdl (by omega), if_neg (by omega)]
  have hout : hv P T f pk m bits (if t + 1 = d then dst - topOff k else xcCell k t) =
        loC (AF P T f pk m bits k t) ∧
      hv P T f pk m bits ((if t + 1 = d then dst - topOff k else xcCell k t) + 1) =
        hiC (AF P T f pk m bits k t) := by
    by_cases hl : t + 1 = d
    · rw [if_pos hl]
      have hsel := hdst.1
      have hjunk := hdst.2
      unfold topOf at hsel
      unfold hiOf at hjunk
      rw [← hddef, if_neg (by omega), show d - 1 = t by omega] at hsel hjunk
      have hoff := topOff_le k
      by_cases hz : topOff k = 0
      · simpa [junkCell, hz, loC, hiC] using And.intro hsel hjunk
      · have ho : topOff k = 1 := by omega
        have he : dst - 1 + 1 = dst := by omega
        simpa [junkCell, ho, loC, hiC, he]
          using And.intro hjunk hsel
    · rw [if_neg hl]; exact hv_xc hk (by omega)
  have hp : tpos k d t / 81 ≤ 13 := by
    have := OFFT_bound k hk; unfold tpos; omega
  have hq : blake2sQuery ![hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1)),
      hv P T f pk m bits (cCell (tpos k d t % 9)), hv P T f pk m bits (cCell (tpos k d t / 9 % 9)),
      hv P T f pk m bits (cCell (tpos k d t / 81))] (hv P T f pk m bits (cCell 1))
      (hv P T f pk m bits (cCell 1 + 1)) (hv P T f pk m bits oneCell) =
      P.codec.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t)
        (P.chainValue f (ctxF P f pk m bits) ⟨k, hk⟩ (LEN k - 1 - d) t (sigW bits k)) := by
    have hj : LEN k - 1 - d + t + 1 < LEN k := by omega
    obtain ⟨h0, h1, h2⟩ := hC.tag ⟨k, hk⟩ _ hj
    rw [blake2sQuery_eq, hv_cc (c := tpos k d t % 9) (by omega),
      hv_cc (c := tpos k d t / 9 % 9) (by omega), hv_cc hp, show cCell 1 + 1 = cCell 2 from rfl,
      hv_cc (c:=1) (by decide), hv_cc (c:=2) (by decide), hv_one, hsrc.2]
    unfold Params.chainInput
    rw [h0, h1, h2, hC.chainMd, hC.cv]
    rfl
  unfold chainOp
  dsimp only
  by_cases hb : t+1=d ∧ binds k
  · rw [if_pos hb]
    obtain ⟨u,hu⟩ : ∃ u, FourFusion.owner ⟨k,hk⟩ = some u :=
      Option.ne_none_iff_exists'.mp ((binds_owner ⟨k,hk⟩).mp hb.2)
    have ha : P.active ⟨k,hk⟩ (LEN k-1-d+t) = some u := by
      unfold FourFusion.Params.active
      rw [hC.len]
      change (if LEN k-1-d+t+2=LEN k then FourFusion.owner ⟨k,hk⟩ else none) = some u
      rw [if_pos (by omega),hu]
    refine blake_rel (a:=AF P T f pk m bits k t)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) ?_ hout.1 hout.2
    rw [honest_fusion_query hT hC hlen hacc readTop ⟨k,hk⟩ hb.2 u hu hread,hsrc.2,
      AF_spec P T f pk m bits hk ht,chainInput_fused ha]
  · rw [if_neg hb]
    have ha : P.active ⟨k,hk⟩ (LEN k-1-d+t) = none := by
      unfold FourFusion.Params.active
      rw [hC.len]
      change (if LEN k-1-d+t+2=LEN k then FourFusion.owner ⟨k,hk⟩ else none) = none
      split_ifs with hh
      · by_contra ho
        exact hb ⟨by omega, (binds_owner ⟨k,hk⟩).mpr ho⟩
      · rfl
    refine blake_rel (a:=AF P T f pk m bits k t)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) ?_ hout.1 hout.2
    rw [hq,AF_spec P T f pk m bits hk ht,FourFusion.Params.chainInput,ha]

include hT hC hlen hacc in
/-- The honest chain steps of chain `k` into `dst`. -/
theorem honest_chainOps (readTop : ℕ → ℕ) {k dst : ℕ} (hk : k < 42)
    (hread : HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) readTop ⟨k,hk⟩)
    (hdstpos : 1 ≤ dst)
    (hdst : hv P T f pk m bits dst =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k dst) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k) :
    ∀ y ∈ chainOps readTop k (hd T (y0F P f pk m bits) k) dst, y.Rel f (hv P T f pk m bits) := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp hy
  exact honest_chainOp hT hC hlen hacc readTop hk hread ht hdstpos hdst

include hlen in
/-- An honest copy of a top from the revealed word (digit `0`). -/
theorem honest_copyW {k c : ℕ} (hk : k < 42) (h0 : hd T (y0F P f pk m bits) k = 0)
    (hc : hv P T f pk m bits c =
      cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k)) :
    (copy (wCell k) c).Rel f (hv P T f pk m bits) := by
  show hv P T f pk m bits c = hv P T f pk m bits (wCell k) * hv P T f pk m bits oneCell
  rw [hv_one, mul_oneV, hc, hv_w hlen hk]
  unfold topOf; rw [if_pos h0]


end
end OptimalOTS.FreeLastVM
