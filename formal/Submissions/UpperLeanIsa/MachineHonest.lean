import Submissions.UpperLeanIsa.MachineProver

/-!
# The honest image satisfies every relation on its path

Under a table `f` for which the verifier accepts, the honest image `imageF P T f pk m bits`, loaded
with the statement, satisfies the fixed-table relation of every op on the path of the honest index
vector `hxs T I` (`honest_path`), with the return hints the walk needs; so the machine
completes in `207` instructions (`honest_run`). Together with `fixed_sound` this is `Faithful`.
-/

namespace OptimalOTS.HLG3

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

set_option linter.unusedSimpArgs false

/-- Decode an `hcell` if-chain whose conditions `omega` decides. -/
macro "hsimp" : tactic => `(tactic| simp (disch := omega) only [if_pos, if_neg, ↓reduceIte])

/-! ## Cell inverses -/

/-- The unused half is before a high-half top, and after a low-half top. -/
def junkCell (k dst : ℕ) : ℕ := if topOff k = 0 then dst + 1 else dst - 1

/-- Chains whose output pair sits at a fixed cv-pair cell: the exported chains and the home
chains 1, 2, 7, 8 of the former cv pairs. -/
def cvTop (k : ℕ) : Prop :=
  k ∈ [1, 2, 7, 8, 12, 13, 17, 18, 22, 23, 27, 28, 32, 33, 37, 38]

instance (k : ℕ) : Decidable (cvTop k) := by unfold cvTop; infer_instance

theorem cvTop_of_exported {k : ℕ} (he : exported k) : cvTop k := by
  unfold exported at he; unfold cvTop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢; omega

theorem xh_topCell : ∀ k < 42, cvTop k → ¬ exported k → xhCell k = topCell k := by decide

theorem xh_inv : ∀ k < 42, k ≠ 0 → ¬ cvTop k →
    xhK ((xhCell k - 187) / 2) = k ∧ (xhCell k - 187) % 2 = topOff k ∧
      187 ≤ xhCell k ∧ xhCell k < 237 := by decide

theorem xh_junk : ∀ k < 42, k ≠ 0 → ¬ cvTop k →
    xhK ((junkCell k (xhCell k) - 187) / 2) = k ∧ (junkCell k (xhCell k) - 187) % 2 ≠ topOff k ∧
      187 ≤ junkCell k (xhCell k) ∧ junkCell k (xhCell k) < 237 := by decide

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

theorem hc_c {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ 17) : hcell T bits y0 A RA (cCell c) = cV c := by
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
  rw [show accCell u = 96 + u from if_neg (by omega)]; unfold hcell; hsimp; congr 2; omega

theorem hc_h {r : ℕ} (hr : r < 14) :
    hcell T bits y0 A RA (hCell r) = ofK (gpow (ent r (hxs T (idxOf y0) r))) := by
  unfold hcell hCell; hsimp; rw [show 108 + r - 108 = r by omega]

theorem hc_h1 {r : ℕ} (hr : r < 14) :
    hcell T bits y0 A RA (h1Cell r) = ofK (gpow (ent r (hxs T (idxOf y0) r) + 1)) := by
  unfold hcell h1Cell; hsimp; rw [show 122 + r - 122 = r by omega]

theorem hc_h14 : hcell T bits y0 A RA (hCell 14) = ofK (gpow (ent 14 (hxs T (idxOf y0) 1))) := by
  unfold hcell hCell; hsimp

theorem hc_h1_14 :
    hcell T bits y0 A RA (h1Cell 14) = ofK (gpow (ent 14 (hxs T (idxOf y0) 1) + 1)) := by
  unfold hcell h1Cell; hsimp

set_option maxRecDepth 4000 in
theorem hc_gp {u : ℕ} (hu : u ≤ 13) :
    hcell T bits y0 A RA (gpCell u) = gpV T (idxOf y0) u := by
  by_cases h13 : u = 13
  · subst u; unfold hcell gpCell; hsimp
  · rw [show gpCell u = 136 + u by unfold gpCell; rw [if_neg h13]]
    unfold hcell; hsimp; congr 1; omega

theorem hc_tf : hcell T bits y0 A RA tfCell = cellOfBits (topOf T bits y0 A 0) := by
  unfold hcell tfCell; hsimp
theorem hc_tf1 : hcell T bits y0 A RA (tfCell + 1) = hiOf T y0 A 0 := by
  unfold hcell tfCell; hsimp

/-- The exported top pair of chain `k`. -/
theorem hc_top {k : ℕ} (hk : k < 42) (he : cvTop k) :
    hcell T bits y0 A RA (topCell k) = cellOfBits (topOf T bits y0 A k) ∧
      hcell T bits y0 A RA (junkCell k (topCell k)) = hiOf T y0 A k := by
  interval_cases k <;> simp [cvTop] at he
  all_goals simp [topCell, junkCell, topOff, hcell, topPair, xhK]

/-- The in-block home pair of chain `k`. -/
theorem hc_xh {k : ℕ} (hk : k < 42) (hk0 : k ≠ 0) (he : ¬ exported k) :
    hcell T bits y0 A RA (xhCell k) = cellOfBits (topOf T bits y0 A k) ∧
      hcell T bits y0 A RA (junkCell k (xhCell k)) = hiOf T y0 A k := by
  by_cases hc : cvTop k
  · rw [xh_topCell k hk hc he]; exact hc_top T bits y0 A RA hk hc
  obtain ⟨e1, e2, e5, e6⟩ := xh_inv k hk hk0 hc
  obtain ⟨e3, e4, e7, e8⟩ := xh_junk k hk hk0 hc
  constructor
  · unfold hcell; hsimp; rw [e1, e2]; simp [topPair]
  · unfold hcell; hsimp; rw [e3]; simp [topPair, e4]

theorem hc_st {r : ℕ} (hr : r < 9) :
    hcell T bits y0 A RA (stCell r) = loC (RA r) ∧
      hcell T bits y0 A RA (stCell r + 1) = hiC (RA r) := by
  constructor
  · unfold hcell stCell; hsimp; congr 2; omega
  · unfold hcell stCell; hsimp; congr 2; omega

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

/-! ## The honest values after loading -/

section Honest

variable (P : Params) (T : Tab) (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

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
    (k : Fin numChains) : hd T y0 k.val = P.digit (effective (idxOf y0)) k := by
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
    AF P T f pk m bits k t = chainAnsF P f ⟨k, hk⟩ (LEN k - 1 - hd T (y0F P f pk m bits) k)
      (hd T (y0F P f pk m bits) k) (sigW bits k) t := by
  unfold AF chainTab; rw [dif_pos hk]

/-- The honest chain values. -/
theorem AF_spec {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < hd T (y0F P f pk m bits) k) :
    AF P T f pk m bits k t = ans f (P.chainInput ⟨k, hk⟩
      (LEN k - 1 - hd T (y0F P f pk m bits) k + t)
      (chainValue f P ⟨k, hk⟩ (LEN k - 1 - hd T (y0F P f pk m bits) k) t (sigW bits k))) := by
  rw [AF_eq P T f pk m bits hk, chainAnsF_spec P f _ _ _ _ _ ht]

/-- The honest top of chain `k` is the verifier's chain value. -/
theorem topOf_eq (hT : T.Hyp) (hC : Compat P T) {k : ℕ} (hk : k < 42) :
    topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k =
      chainValue f P ⟨k, hk⟩ (LEN k - 1 - hd T (y0F P f pk m bits) k)
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
    rfl

/-! ### Cell values of the loaded honest image -/

section Values

variable {P T f pk m bits}

theorem hv_c {c : ℕ} (h1 : 47 ≤ c) (h2 : c < 2 ^ 16) {x : E}
    (h : hcell T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) c = x) :
    hv P T f pk m bits c = x := (hv_ge P T f pk m bits h1 h2).trans h

theorem hv_one : hv P T f pk m bits oneCell = oneV := hv_c (by decide) (by decide) (hc_one ..)
theorem hv_g : hv P T f pk m bits gCell = gV := hv_c (by decide) (by decide) (hc_g ..)
theorem hv_cc {c : ℕ} (hc : c ≤ 17) : hv P T f pk m bits (cCell c) = cV c := by
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · rw [cV_zero]; exact hv_one
  · exact hv_c (by unfold cCell; split_ifs <;> omega)
      (by unfold cCell; split_ifs <;> omega) (hc_c _ _ _ _ _ h0 hc)
theorem hv_frame {r : ℕ} (hr : r < 15) : hv P T f pk m bits (fCell r) = frameV r := by
  apply hv_c (by unfold fCell cCell; split_ifs <;> omega)
    (by unfold fCell cCell; split_ifs <;> omega)
  exact hc_frame _ _ _ _ _ hr

theorem hv_idx : hv P T f pk m bits idxCell = loC (y0F P f pk m bits) :=
  hv_c (by decide) (by decide) (hc_idx ..)
theorem hv_idx1 : hv P T f pk m bits (idxCell + 1) = hiC (y0F P f pk m bits) :=
  hv_c (by decide) (by decide) (hc_idx1 ..)
theorem hv_t {u : ℕ} (hu : u < 13) :
    hv P T f pk m bits (tCell u) = fpat u (XF P T f pk m bits (u + 1)) :=
  hv_c (by unfold tCell; omega) (by unfold tCell; omega) (hc_t _ _ _ _ _ hu)
theorem hv_accl {u : ℕ} (hu : u < 12) :
    hv P T f pk m bits (accCell u) =
      natV (ofDigitsW gb (fun w => XF P T f pk m bits (w + 1)) (u + 1)) :=
  hv_c (by unfold accCell; split_ifs <;> omega)
    (by unfold accCell; split_ifs <;> omega) (hc_acc _ _ _ _ _ hu)
/-- The honest index of frame `r`: frame 14 is the first group's `s = 0` variant. -/
abbrev XFr (r : ℕ) : ℕ := if r = 14 then XF P T f pk m bits 1 else XF P T f pk m bits r

theorem hv_h {r : ℕ} (hr : r < 15) :
    hv P T f pk m bits (hCell r) = ofK (gpow (ent r (XFr (P := P) (T := T) (f := f) (pk := pk)
      (m := m) (bits := bits) r))) := by
  by_cases h14 : r = 14
  · subst r; exact hv_c (by decide) (by decide) (hc_h14 ..)
  · simp only [XFr, if_neg h14]
    exact hv_c (by unfold hCell; split_ifs <;> omega) (by unfold hCell; split_ifs <;> omega)
      (hc_h _ _ _ _ _ (by omega))
theorem hv_h1 {r : ℕ} (hr : r < 15) :
    hv P T f pk m bits (h1Cell r) = ofK (gpow (ent r (XFr (P := P) (T := T) (f := f) (pk := pk)
      (m := m) (bits := bits) r) + 1)) := by
  by_cases h14 : r = 14
  · subst r; exact hv_c (by decide) (by decide) (hc_h1_14 ..)
  · simp only [XFr, if_neg h14]
    exact hv_c (by unfold h1Cell; split_ifs <;> omega) (by unfold h1Cell; split_ifs <;> omega)
      (hc_h1 _ _ _ _ _ (by omega))
theorem hv_gpl {u : ℕ} (hu : u ≤ 13) :
    hv P T f pk m bits (gpCell u) = gpV T (IF P f pk m bits) u :=
  hv_c (by unfold gpCell; split_ifs <;> omega)
    (by unfold gpCell; split_ifs <;> omega) (hc_gp _ _ _ _ _ hu)

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
  have h2 : 150 ≤ topCell k := by unfold topCell; split_ifs <;> omega
  have h3 : 149 ≤ junkCell k (topCell k) ∧ junkCell k (topCell k) < 241 := by
    unfold junkCell; split_ifs <;> omega
  obtain ⟨e1, e2⟩ := hc_top T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) hk he
  exact ⟨hv_c (by omega) (by omega) e1, hv_c (by omega) (by omega) e2⟩
theorem hv_xh {k : ℕ} (hk : k < 42) (hk0 : k ≠ 0) (he : ¬ exported k) :
    hv P T f pk m bits (xhCell k) =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k (xhCell k)) =
        hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k := by
  by_cases hc : cvTop k
  · rw [xh_topCell k hk hc he]; exact hv_top hk hc
  obtain ⟨-, -, i5, i6⟩ := xh_inv k hk hk0 hc
  obtain ⟨-, -, i7, i8⟩ := xh_junk k hk hk0 hc
  obtain ⟨e1, e2⟩ := hc_xh T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits)
    hk hk0 he
  exact ⟨hv_c (by omega) (by omega) e1, hv_c (by omega) (by omega) e2⟩
theorem hv_st {r : ℕ} (hr : r < 9) :
    hv P T f pk m bits (stCell r) = loC (RAF P T f pk m bits r) ∧
      hv P T f pk m bits (stCell r + 1) = hiC (RAF P T f pk m bits r) := by
  obtain ⟨e1, e2⟩ := hc_st T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) hr
  exact ⟨hv_c (by unfold stCell; omega) (by unfold stCell; omega) e1,
    hv_c (by unfold stCell; omega) (by unfold stCell; omega) e2⟩
theorem hv_xc {k t : ℕ} (hk : k < 42) (ht : t < LEN k) :
    hv P T f pk m bits (xcCell k t) = loC (AF P T f pk m bits k t) ∧
      hv P T f pk m bits (xcCell k t + 1) = hiC (AF P T f pk m bits k t) := by
  have hb := xcBase_bound k hk
  have h0 := xcBase_mono (Nat.zero_le k); rw [xcBase_zero] at h0
  obtain ⟨e1, e2⟩ := hc_xc T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits) hk ht
  exact ⟨hv_c (by unfold xcCell; omega) (by unfold xcCell; omega) e1,
    hv_c (by unfold xcCell; omega) (by unfold xcCell; omega) e2⟩

/-- The revealed words (for an admitted length). -/
theorem hv_w (hlen : bits.length = 5503) {k : ℕ} (hk : k < 42) :
    hv P T f pk m bits (wCell k) = cellOfBits (sigW bits k) := by
  rw [hv_lt P T f pk m bits (by unfold wCell; omega), show wCell k = 4 + k from rfl,
    inputWord_sig pk m bits hlen k]
  rfl

/-- The cell the root and the copies read chain `k`'s top from. -/
theorem hv_rtop (hlen : bits.length = 5503) {k : ℕ} (hk : k < 42) :
    hv P T f pk m bits (rtopCell k (hd T (y0F P f pk m bits) k)) =
      cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) := by
  unfold rtopCell
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos rfl]
    by_cases hd0 : hd T (y0F P f pk m bits) 0 = 0
    · rw [if_pos hd0, hv_w hlen hk]; unfold topOf; rw [if_pos hd0]
    · rw [if_neg hd0]; exact hv_tf
  rw [if_neg h0]
  by_cases he : exported k
  · rw [if_pos he]; exact (hv_top hk (cvTop_of_exported he)).1
  rw [if_neg he]
  by_cases hd0 : hd T (y0F P f pk m bits) k = 0
  · rw [if_pos hd0, hv_w hlen hk]; unfold topOf; rw [if_pos hd0]
  · rw [if_neg hd0]; exact (hv_xh hk h0 he).1

end Values

section Accepted

variable {P T f pk m bits}
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length = 5503)
  (hacc : P.Accepted (effective (IF P f pk m bits)))
  (hroot : rootValue f P (topsOf f P (effective (IF P f pk m bits)) bits) = pk)

include hC hacc in
/-- The accepted honest index has no dummy field. -/
theorem hlive : ∀ u < 13, field u (IF P f pk m bits) < VF u := hC.live _ hacc

include hC hacc in
theorem hsum : XF P T f pk m bits 0 + gsum T (XF P T f pk m bits) = 88 := by
  have h : ∑ k : Fin numChains, P.digit (effective (IF P f pk m bits)) k = P.layer := hacc
  rw [hC.layer, Finset.sum_congr rfl (fun k _ => (hd_eq P T hC _ (hlive hC hacc) k).symm),
    Fin.sum_univ_eq_sum_range (fun k => hd T (y0F P f pk m bits) k) 42] at h
  unfold hd at h
  rw [dg_sum] at h
  exact h

include hacc in
theorem topsOfV_eq (hT : T.Hyp) (hC : Compat P T) : topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits) =
    topsOf f P (effective (IF P f pk m bits)) bits := by
  funext k
  unfold topsOfV topsOf
  rw [topOf_eq P T f pk m bits hT hC k.isLt, hC.len k, hd_eq P T hC _ (hlive hC hacc)]
  rfl

theorem XFr_frU {r : ℕ} (hr : r < 14) :
    XFr (P := P) (T := T) (f := f) (pk := pk) (m := m) (bits := bits)
      (frU (XF P T f pk m bits 0) r) = XF P T f pk m bits r := by
  unfold frU frG0
  by_cases h1 : r = 1
  · subst h1
    by_cases hs : XF P T f pk m bits 0 = 0
    · simp only [if_pos rfl, if_pos hs, XFr, if_true]
    · simp only [if_pos rfl, if_neg hs, XFr]; rfl
  · simp only [if_neg h1, XFr, if_neg (show r ≠ 14 by omega)]

include hC hacc in
/-- The honest dispatch of unit `r`. -/
theorem honest_dispatch {r : ℕ} (hr : r < 14) :
    (CInstr.dispatch (frU (XF P T f pk m bits 0) r)).Rel f (hv P T f pk m bits) := by
  have hF := frU_lt (XF P T f pk m bits 0) hr
  refine ⟨?_, ?_, ent (frU (XF P T f pk m bits 0) r) (XF P T f pk m bits r),
    ⟨hF, XF P T f pk m bits r, by rw [Wf_frU _ hr]; exact hxs_valid T _ (hlive hC hacc) r hr,
      rfl⟩, ?_⟩
  · rw [hv_h hF]; exact isInK_ofK _
  · rw [hv_h1 hF]; exact isInK_ofK _
  · rw [hv_h hF, XFr_frU hr, limb_ofK_zero]

/-- The honest `MUL(H_r, g, H'_r)`. -/
theorem honest_hmul {r : ℕ} (hr : r < 15) :
    (CInstr.mul (hCell r) gCell (h1Cell r)).Rel f (hv P T f pk m bits) := by
  show hv P T f pk m bits (h1Cell r) = hv P T f pk m bits (hCell r) * hv P T f pk m bits gCell
  rw [hv_h1 hr, hv_h hr, hv_g, gV, ← ofK_mul, mul_comm, g_mul_gpow]

include hC hlen in
/-- The index query of the honest image. -/
theorem honest_idx_query :
    blake2sQuery ![hv P T f pk m bits msgLo, hv P T f pk m bits msgHi,
      hv P T f pk m bits nonceCell, hv P T f pk m bits pkCell] (hv P T f pk m bits oneCell)
      (hv P T f pk m bits (oneCell + 1)) (hv P T f pk m bits gCell) =
      P.idxInput m (decodeNonce bits) pk := by
  have hpk : cellBits (hv P T f pk m bits pkCell) = pk := by
    rw [show pkCell = 0 from rfl, hv_lt P T f pk m bits (by omega), inputWord_pk]
    exact cellBits_cellOfBits pk
  rw [blake2sQuery_eq, show oneCell + 1 = gCell from rfl, hv_one, hv_g,
    show nonceCell = 46 from rfl, show msgHi = 2 from rfl, show msgLo = 1 from rfl,
    hv_lt P T f pk m bits (show 46 < 47 by omega), hv_lt P T f pk m bits (show 2 < 47 by omega),
    hv_lt P T f pk m bits (show 1 < 47 by omega), inputWord_nonce pk m bits hlen, inputWord_two,
    inputWord_one, cellBits_cellOfBits (nonceWord (decodeNonce bits)),
    cellBits_cellOfBits (m.extractLsb' 128 128), cellBits_cellOfBits (m.extractLsb' 0 128),
    msg_split, hpk]
  unfold Params.idxInput
  rw [hC.cv, hC.idxMd]
  rfl

/-- The honest landing product before group `u`. -/
theorem honest_gp {u : ℕ} (hu : u ≤ 13) :
    hv P T f pk m bits (gpCell u) = gpV T (IF P f pk m bits) u := hv_gpl hu

include hC hacc in
/-- On an accepted index the last landing product is `g ^ sentinel`: the exit target. -/
theorem honest_gp13 : hv P T f pk m bits (gpCell 13) = ofK (gpow sentinel) := by
  rw [honest_gp (by omega)]
  unfold gpV
  apply congrArg ofK
  have hs := hsum hC hacc
  change hxs T (IF P f pk m bits) 0 + ∑ w ∈ Finset.range 13,
    cost T w (hxs T (IF P f pk m bits) (w + 1)) = 88 at hs
  exact (LeanIsaFieldRescale.checksum_exact (by omega : 88 ≤ 300) (by omega)).mpr hs

include hC hlen hacc in
/-- **The honest prologue.** -/
theorem honest_pro : ∀ y ∈ proList, y.Rel f (hv P T f pk m bits) := by
  intro y hy
  unfold proList at hy
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hy
  rcases hy with ((h | h) | ⟨c, hc, rfl⟩) | h | h
  · subst h; refine ⟨hv_one, ?_⟩
    show hv P T f pk m bits 3 = natV 5503
    rw [hv_lt P T f pk m bits (by omega)]; exact inputWord_len_of pk m bits hlen
  · subst h; exact hv_g
  · exact hv_cc (by omega)
  · subst h
    refine blake_rel (a := y0F P f pk m bits) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hv_idx hv_idx1
    · rw [show msgLo = 1 from rfl, hv_lt P T f pk m bits (by omega), inputWord_one]
      exact canon_cellOfBits _
    · rw [show msgHi = 2 from rfl, hv_lt P T f pk m bits (by omega), inputWord_two]
      exact canon_cellOfBits _
    · rw [show nonceCell = 46 from rfl, hv_lt P T f pk m bits (by omega),
        inputWord_nonce pk m bits hlen]
      exact canon_cellOfBits _
    · rw [show pkCell = 0 from rfl, hv_lt P T f pk m bits (by omega), inputWord_pk]
      exact canon_cellOfBits _
    · rw [hv_one]; exact canon_ofK 1
    · rw [show oneCell + 1 = gCell from rfl, hv_g]; exact canon_ofK _
    · rw [hv_g]; exact canon_ofK _
    · rw [honest_idx_query hC hlen]; rfl
  · subst h; exact honest_hmul (by omega)

include hT hC hlen in
/-- The honest chain step `t` of chain `k` (the last writes `dst`). -/
theorem honest_chainOp {k : ℕ} (hk : k < 42) {t dst : ℕ}
    (ht : t < hd T (y0F P f pk m bits) k)
    (hdstpos : 1 ≤ dst)
    (hdst : hv P T f pk m bits dst =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k dst) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k) :
    (chainOp k (hd T (y0F P f pk m bits) k) t dst).Rel f (hv P T f pk m bits) := by
  set d := hd T (y0F P f pk m bits) k with hddef
  have hdl := hd_lt T hT (y0F P f pk m bits) hk
  rw [← hddef] at hdl
  have hsrc : IsCanonical128 (hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1))) ∧
      cellBits (hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1))) =
        chainValue f P ⟨k, hk⟩ (LEN k - 1 - d) t (sigW bits k) := by
    by_cases h0 : t = 0
    · rw [if_pos h0, hv_w hlen hk, cellBits_cellOfBits, h0]
      exact ⟨canon_cellOfBits _, rfl⟩
    · rw [if_neg h0, (hv_xc hk (show t - 1 < LEN k by omega)).1, cellBits_loC]
      refine ⟨canon_loC _, ?_⟩
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      rw [Nat.add_sub_cancel, AF_spec P T f pk m bits hk (by omega), chainValue_succ]
      simp only [Params.slice]
      rw [stepOff_eq hC hk hdl (by omega), if_neg (by omega)]
      rfl
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
  have hp : tpos k d t / 81 ≤ 17 := by
    have := OFFT_bound k hk; unfold tpos; omega
  have hq : blake2sQuery ![hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1)),
      hv P T f pk m bits (cCell (tpos k d t % 9)), hv P T f pk m bits (cCell (tpos k d t / 9 % 9)),
      hv P T f pk m bits (cCell (tpos k d t / 81))] (hv P T f pk m bits oneCell)
      (hv P T f pk m bits (oneCell + 1)) (hv P T f pk m bits oneCell) =
      P.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t)
        (chainValue f P ⟨k, hk⟩ (LEN k - 1 - d) t (sigW bits k)) := by
    have hj : LEN k - 1 - d + t + 1 < LEN k := by omega
    obtain ⟨h0, h1, h2⟩ := hC.tag ⟨k, hk⟩ _ hj
    rw [blake2sQuery_eq, hv_cc (c := tpos k d t % 9) (by omega),
      hv_cc (c := tpos k d t / 9 % 9) (by omega), hv_cc hp, show oneCell + 1 = gCell from rfl,
      hv_g, hv_one, hsrc.2]
    unfold Params.chainInput
    rw [h0, h1, h2, hC.chainMd, hC.cv]
    rfl
  unfold chainOp
  refine blake_rel (a := AF P T f pk m bits k t) hsrc.1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hout.1 hout.2
  · rw [hv_cc (by omega)]; exact canon_ofK _
  · rw [hv_cc (by omega)]; exact canon_ofK _
  · rw [hv_cc hp]; exact canon_ofK _
  · rw [hv_one]; exact canon_ofK 1
  · rw [show oneCell + 1 = gCell from rfl, hv_g]; exact canon_ofK _
  · rw [hv_one]; exact canon_ofK 1
  · rw [hq, AF_spec P T f pk m bits hk ht]

include hT hC hlen in
/-- The honest chain steps of chain `k` into `dst`. -/
theorem honest_chainOps {k dst : ℕ} (hk : k < 42)
    (hdstpos : 1 ≤ dst)
    (hdst : hv P T f pk m bits dst =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k dst) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k) :
    ∀ y ∈ chainOps k (hd T (y0F P f pk m bits) k) dst, y.Rel f (hv P T f pk m bits) := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp hy
  exact honest_chainOp hT hC hlen hk ht hdstpos hdst

include hlen in
/-- An honest copy of a top from the revealed word (digit `0`). -/
theorem honest_copyW {k c : ℕ} (hk : k < 42) (h0 : hd T (y0F P f pk m bits) k = 0)
    (hc : hv P T f pk m bits c =
      cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k)) :
    (copy (wCell k) c).Rel f (hv P T f pk m bits) := by
  show hv P T f pk m bits c = hv P T f pk m bits (wCell k) * hv P T f pk m bits oneCell
  rw [hv_one, mul_oneV, hc, hv_w hlen hk]
  unfold topOf; rw [if_pos h0]

/-- The honest accumulator after group `u`. -/
theorem honest_acc {u : ℕ} (hu : u < 13) :
    hv P T f pk m bits (accCell u) =
      natV (ofDigitsW gb (fun w => XF P T f pk m bits (w + 1)) (u + 1)) := by
  by_cases h12 : u < 12
  · exact hv_accl h12
  · obtain rfl : u = 12 := by omega
    rw [show accCell 12 = idxCell from rfl, hv_idx]
    have hfun : (fun w => XF P T f pk m bits (w + 1)) = digitW gb (IF P f pk m bits).toNat := by
      funext w; show hxs T _ (w + 1) = _; rw [hxs_succ]; rfl
    rw [hfun, show 12 + 1 = 13 from rfl,
      ofDigitsW_digitW gb _ 13 (by rw [show posW gb 13 = 128 from POS_13]; exact BitVec.isLt _)]
    show cellOfBits _ = cellOfBits _
    rw [BitVec.ofNat_toNat]
    rfl

end Accepted

end Honest

end

end OptimalOTS.HLG3
