import Submissions.UpperLeanIsa.FusionMachineCells

/-! The loaded honest image: indices, dependencies and fixed-oracle answers. -/
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OptimalOTS.HLFusion
open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV ans inputWord_sig inputWord_pk inputWord_nonce inputWord_one inputWord_two inputWord_len_of)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section

open Fusion in
theorem reconstruction_spec (P : Fusion.Params) (f : HashTable) (I : Index) (bits : List Bool)
    (l : List (Fin 42)) (hl : l.Pairwise (fun k k' => evaluationRank k.val < evaluationRank k'.val)) (t : Tops) :
    let t' := P.reconFromValue f I bits l t
    ∀ k ∈ l, P.chainValue f t' k (P.codec.len k-1-P.codec.digit I k) (P.codec.digit I k)
      (decodeWord bits k) = t' k.val := by
  induction l generalizing t with
  | nil => simp
  | cons k l ih =>
    obtain ⟨hbefore,hl⟩ := List.pairwise_cons.mp hl
    let t' := P.reconFromValue f I bits (k::l) t
    have hdep : ∀ u : Fin 6, owner k = some u → ∀ d ∈ children u, t d = t' d := by
      intro u hu d hd
      apply (P.reconFromValue_preserves f I bits (k::l) t d ?_).symm
      intro hmem
      have hr := dependency_precedes u u.isLt k.val ((owner_mem k u).mp hu) d hd
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
variable (P : Fusion.Params) (T : Tab) (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

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
theorem hv_g : hv P T f pk m bits gCell = gV := hv_c (by decide) (by decide) (hc_g ..)
theorem hv_cc {c : ℕ} (hc : c ≤ 22) : hv P T f pk m bits (cCell c) = cV c := by
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
abbrev XFr (r : ℕ) : ℕ := XF P T f pk m bits r

theorem hv_h {r : ℕ} (hr : r<14) :
    hv P T f pk m bits (hCell r) = ofK (gpow (ent r (XFr (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) r))) :=
  hv_c (by unfold hCell; omega) (by unfold hCell; omega) (hc_h _ _ _ _ _ hr)

theorem hv_h1 {r : ℕ} (hr : r<14) :
    hv P T f pk m bits (h1Cell r) = ofK (gpow (ent r (XFr (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) r)+1)) :=
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

theorem hv_st {r : ℕ} (hr : r<3) :
    hv P T f pk m bits (stCell r) = loC (RAF P T f pk m bits r) ∧
      hv P T f pk m bits (stCell r+1) = hiC (RAF P T f pk m bits r) := by
  have hh : ∀ r<3, 256 ≤ stCell r ∧ stCell r+1<346 := by decide
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
theorem hv_w (hlen : bits.length = 5503) {k : ℕ} (hk : k < 42) :
    hv P T f pk m bits (wCell k) = cellOfBits (sigW bits k) := by
  rw [hv_lt P T f pk m bits (by unfold wCell; omega), show wCell k = 4 + k from rfl,
    inputWord_sig pk m bits hlen k]
  rfl

theorem hv_rtop (hlen : bits.length=5503) {k : ℕ} (hk : k<42) :
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
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length = 5503)
  (hacc : P.codec.Accepted (effective (IF P f pk m bits)))
  (hroot : rootValue f P (topsOf f P (effective (IF P f pk m bits)) bits) = pk)

include hC hacc in
/-- The accepted honest index has no dummy field. -/
theorem hlive : ∀ u < 13, field u (IF P f pk m bits) < VF u := hC.live _ hacc

include hC hacc in
theorem hsum : XF P T f pk m bits 0 + gsum T (XF P T f pk m bits) = 86 := by
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
    exact reconstruction_spec P f _ bits Fusion.chainOrder Fusion.Params.chainOrder_ranked
      (fun _ => 0) ⟨k,hk⟩ (Fusion.chainOrder_permutation.mem_iff.mpr (List.mem_finRange ⟨k,hk⟩))
  · rw [topsOfV,if_neg hk]
    symm
    exact P.reconFromValue_preserves f _ bits Fusion.chainOrder (fun _ => 0) k (by
      rintro hmem
      obtain ⟨j,_,he⟩ := List.mem_map.mp hmem
      have hj := j.isLt
      rw [he] at hj
      exact hk hj)

theorem XFr_frU {r : ℕ} (_hr : r<14) :
    XFr (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) (frU (XF P T f pk m bits 0) r) =
      XF P T f pk m bits r := rfl

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
theorem honest_hmul {r : ℕ} (hr : r < 14) :
    (CInstr.mul (hCell r) gCell (h1Cell r)).Rel f (hv P T f pk m bits) := by
  show hv P T f pk m bits (h1Cell r) = hv P T f pk m bits (hCell r) * hv P T f pk m bits gCell
  rw [hv_h1 hr, hv_h hr, hv_g, gV, ← ofK_mul, mul_comm, g_mul_gpow]

include hC hlen in
/-- The index query of the honest image. -/
theorem honest_idx_query :
    blake2sQuery ![hv P T f pk m bits msgLo, hv P T f pk m bits msgHi,
      hv P T f pk m bits nonceCell, hv P T f pk m bits pkCell] (hv P T f pk m bits oneCell)
      (hv P T f pk m bits (oneCell + 1)) (hv P T f pk m bits gCell) =
      P.codec.idxInput m (decodeNonce bits) pk := by
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
    cost T w (hxs T (IF P f pk m bits) (w + 1)) = 86 at hs
  exact (LeanIsaFieldRescale.checksum_exact (by omega : 86 ≤ 300) (by omega)).mpr hs

include hC hlen hacc in
/-- **The honest prologue.** -/
theorem honest_pro : ∀ y ∈ proList, y.Rel f (hv P T f pk m bits) := by
  intro y hy
  unfold proList at hy
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hy
  rcases hy with (((h | h) | ⟨c,hc,rfl⟩) | ⟨c,hc,rfl⟩) | h | h
  · subst h; refine ⟨hv_one, ?_⟩
    show hv P T f pk m bits 3 = natV 5503
    rw [hv_lt P T f pk m bits (by omega)]; exact inputWord_len_of pk m bits hlen
  · subst h; exact hv_g
  · exact hv_cc (by omega)
  · apply hv_cc
    omega
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

end Accepted
end Honest
end
end OptimalOTS.HLFusion
