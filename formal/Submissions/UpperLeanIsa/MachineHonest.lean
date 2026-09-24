import Submissions.UpperLeanIsa.MachineProver

/-!
# The honest image satisfies every relation on its path

Under a table `f` for which the verifier accepts, the honest image `imageF f pk m bits`, loaded
with the statement, satisfies the fixed-table relation of every slot on the path of the index
digits (`honest_path`), with the return hints and `K0` the walk needs; so the machine completes
in `425` instructions (`honest_run`). Together with `fixed_sound` this is `Faithful`.
-/

namespace OptimalOTS.HLFlat

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

/-! ## The honest cells -/

/-- `omega` after unfolding the cell layout. -/
macro "cellω" : tactic => `(tactic| ((try simp only [zCell, oneCell, tidxCell, gCell, k0Cell,
  symCell, fCell, idxCell, tCell, hCell, h1Cell, topCell, cvCell, xCell, stCell] at *) <;> omega))

section Cells

variable (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (RA : ℕ → BitVec 256)

theorem hc_z :
    hcell bits y0 A RA (zCell) = 0 := by
  unfold hcell
  rw [if_pos (by cellω)]

theorem hc_one :
    hcell bits y0 A RA (oneCell) = oneV := by
  unfold hcell
  rw [if_neg (by cellω), if_pos (by cellω)]

theorem hc_tidx :
    hcell bits y0 A RA (tidxCell) = natV 10 := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_g :
    hcell bits y0 A RA (gCell) = gV := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_k0 :
    hcell bits y0 A RA (k0Cell) = k0V := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_sym {i : ℕ} (hi : i < 7) :
    hcell bits y0 A RA (symCell i) = natV (i + 3) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  congr 1; unfold symCell; omega

theorem hc_frame {k : ℕ} (hk : k < 42) :
    hcell bits y0 A RA (fCell k) = frameV k := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  congr 1; unfold fCell; omega

theorem hc_idx :
    hcell bits y0 A RA (idxCell) = loC y0 := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_idx1 :
    hcell bits y0 A RA (idxCell + 1) = hiC y0 := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_t {k : ℕ} (hk : k < 42) :
    hcell bits y0 A RA (tCell k) = fpat k (dg (idxOf y0) k) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [show tCell k - 103 = k by unfold tCell; omega]

theorem hc_acc {k : ℕ} (hk : k < 41) :
    hcell bits y0 A RA (145 + k) = natV (ofDigitsW Flat.wid (dg (idxOf y0)) (k + 1)) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [show 145 + k - 144 = k + 1 by omega]

theorem hc_h {k : ℕ} (hk : k < 42) :
    hcell bits y0 A RA (hCell k) = ofK (gpow (entryOf k (dg (idxOf y0) k))) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [show hCell k - 186 = k by unfold hCell; omega]

theorem hc_h1 {k : ℕ} (hk : k < 42) :
    hcell bits y0 A RA (h1Cell k) = ofK (gpow (entryOf k (dg (idxOf y0) k) + 1)) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [show h1Cell k - 228 = k by unfold h1Cell; omega]

theorem hc_prod {k : ℕ} (hk : k < 41) :
    hcell bits y0 A RA (270 + k) = ofK (gpow (∑ j ∈ Finset.range (k + 1), entryOf j (dg (idxOf y0) j))) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [show 270 + k - 269 = k + 1 by omega]

theorem hc_top {k : ℕ} (hk : k < 42) :
    hcell bits y0 A RA (topCell k) = cellOfBits (topOf bits y0 A k) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_pos (by unfold topCell; omega), show (topCell k - 320) / 2 = k by unfold topCell; omega]

theorem hc_top1 {k : ℕ} (hk : k < 42) :
    hcell bits y0 A RA (topCell k + 1) = hiOf y0 A k := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_neg (by unfold topCell; omega), show (topCell k + 1 - 320) / 2 = k by unfold topCell; omega]

theorem hc_cv0 :
    hcell bits y0 A RA (cvCell) = cellOfBits (topOf bits y0 A 0) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_cv1 :
    hcell bits y0 A RA (cvCell + 1) = cellOfBits (topOf bits y0 A 1) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_cv2 :
    hcell bits y0 A RA (cvCell + 2) = hiOf y0 A 1 := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_x {k t : ℕ} (hk : k < 42) (ht : t < 16) :
    hcell bits y0 A RA (xCell k t) = loC (A k t) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_pos (by unfold xCell; omega), show (xCell k t - 1024) / 32 = k by unfold xCell; omega,
    show (xCell k t - 1024) % 32 / 2 = t by unfold xCell; omega]

theorem hc_x1 {k t : ℕ} (hk : k < 42) (ht : t < 16) :
    hcell bits y0 A RA (xCell k t + 1) = hiC (A k t) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_neg (by unfold xCell; omega), show (xCell k t + 1 - 1024) / 32 = k by unfold xCell; omega,
    show (xCell k t + 1 - 1024) % 32 / 2 = t by unfold xCell; omega]

theorem hc_st {r : ℕ} (hr : r < 10) :
    hcell bits y0 A RA (stCell r) = loC (RA r) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_pos (by unfold stCell; omega), show (stCell r - 2400) / 2 = r by unfold stCell; omega]

theorem hc_st1 {r : ℕ} (hr : r < 10) :
    hcell bits y0 A RA (stCell r + 1) = hiC (RA r) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_neg (by unfold stCell; omega), show (stCell r + 1 - 2400) / 2 = r by unfold stCell; omega]

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

/-- A `BLAKE2S` whose nine cells are canonical and whose output pair is the answer holds. -/
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

/-! ## Block ops by position -/

theorem blockOp0_one {s : ℕ} : blockOp 0 s 1 = .setc (accCell 0) (fpat 0 s) := by
  unfold blockOp; rw [if_pos rfl, if_pos rfl]

theorem blockOp0_copy {s : ℕ} :
    blockOp 0 s (s + 2) = .xor (if s = 0 then wCell 0 else topCell 0) zCell cvCell := by
  unfold blockOp; rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem blockOpK_one {k s : ℕ} (hk : k ≠ 0) :
    blockOp k s 1 = if s = 0 then .xor (wCell k) zCell (rootTop k) else .setc (tCell k) (fpat k s) := by
  unfold blockOp; rw [if_neg hk, if_pos rfl]

theorem blockOpK_two {k s : ℕ} (hk : k ≠ 0) :
    blockOp k s 2 = .xor (accCell (k - 1)) (if s = 0 then zCell else tCell k) (accCell k) := by
  unfold blockOp; rw [if_neg hk, if_neg (by omega), if_pos rfl]

/-- The chain-step query of a chain op, from the constants' values. -/
theorem chain_query {v : ℕ → E} (hz : v zCell = 0) (hone : v oneCell = oneV)
    (hsym : ∀ i < 7, v (symCell i) = natV (i + 3)) {k : ℕ} (hk : k < 42) {j : ℕ} (hj : j < W k)
    (x : E) :
    blake2sQuery ![x, v (symCell (tagPos k j % 7)), v (symCell (tagPos k j / 7 % 7)),
        v (symCell (tagPos k j / 49))] (v zCell) (v (zCell + 1)) (v oneCell) =
      FP.chainInput ⟨k, hk⟩ j (cellBits x) := by
  have hp : tagPos k j < 343 := by
    have := @W_le k; unfold tagPos Flat.off; split_ifs <;> omega
  rw [blake2sQuery_eq, hsym _ (Nat.mod_lt _ (by norm_num)), hsym _ (Nat.mod_lt _ (by norm_num)),
    hsym _ (by omega), cellBits_natV, cellBits_natV, cellBits_natV,
    show zCell + 1 = oneCell from rfl, hone, hz, cellBits_zero_E, cellBits_oneV, cv_const]
  rfl

/-! ## The honest values after loading -/

section Honest

variable (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

/-- The loaded honest image, as cell values. -/
def hv (c : ℕ) : E := Lx (LeanIsa.loadInput pk m bits (imageF f pk m bits)) c

theorem hv_lt {c : ℕ} (h : c < 47) : hv f pk m bits c = inputWord pk m bits c :=
  Lx_loadInput_pin (le_refl 16) pk m bits _ h

theorem hv_ge {c : ℕ} (h1 : 47 ≤ c) (h2 : c < 2 ^ 16) :
    hv f pk m bits c = hcell bits (y0F f pk m bits) (AF f pk m bits) (RAF f pk m bits) c := by
  unfold hv
  rw [Lx_loadInput pk m bits _ h2, if_neg (by omega)]
  unfold Lx; rw [dif_pos h2]; rfl

theorem W_eq_pow {k : ℕ} (hk : k < 42) : W k = 2 ^ Flat.wid k := by
  unfold W Flat.wid; split_ifs <;> rfl

theorem dF_lt {k : ℕ} (hk : k < 42) : dg (idxOf (y0F f pk m bits)) k < W k := by
  rw [W_eq_pow hk]; exact digitW_lt _ _ _

theorem dF_valid : Valid (dg (idxOf (y0F f pk m bits))) := fun _ hk => dF_lt f pk m bits hk

theorem AF_eq {k : ℕ} (hk : k < 42) (t : ℕ) :
    AF f pk m bits k t = chainAnsF f ⟨k, hk⟩ (W k - 1 - dg (idxOf (y0F f pk m bits)) k) (dg (idxOf (y0F f pk m bits)) k)
      (sigW bits k) t := by
  unfold AF chainTab; rw [dif_pos hk]

/-- The honest chain values. -/
theorem AF_spec {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < dg (idxOf (y0F f pk m bits)) k) :
    AF f pk m bits k t = ans f (FP.chainInput ⟨k, hk⟩ (W k - 1 - dg (idxOf (y0F f pk m bits)) k + t)
      (chainValue f FP ⟨k, hk⟩ (W k - 1 - dg (idxOf (y0F f pk m bits)) k) t (sigW bits k))) := by
  rw [AF_eq f pk m bits hk, chainAnsF_spec f _ _ _ _ _ ht]

/-- The honest top of chain `k` is the verifier's. -/
theorem topOf_eq {k : ℕ} (hk : k < 42) :
    topOf bits (y0F f pk m bits) (AF f pk m bits) k =
      chainValue f FP ⟨k, hk⟩ (W k - 1 - dg (idxOf (y0F f pk m bits)) k) (dg (idxOf (y0F f pk m bits)) k) (sigW bits k) := by
  unfold topOf
  by_cases h0 : dg (idxOf (y0F f pk m bits)) k = 0
  · rw [if_pos h0, h0]; rfl
  · rw [if_neg h0]
    obtain ⟨u, hu⟩ : ∃ u, dg (idxOf (y0F f pk m bits)) k = u + 1 := ⟨dg (idxOf (y0F f pk m bits)) k - 1, by omega⟩
    have hs := AF_spec f pk m bits hk (t := u) (by omega)
    rw [hu] at hs
    rw [hu, Nat.add_sub_cancel, hs, chainValue_succ]

/-! ### Cell values of the loaded honest image -/

section Values

variable {f pk m bits}

theorem hv_c {c : ℕ} (h1 : 47 ≤ c) (h2 : c < 2 ^ 16) {x : E}
    (h : hcell bits (y0F f pk m bits) (AF f pk m bits) (RAF f pk m bits) c = x) :
    hv f pk m bits c = x := (hv_ge f pk m bits h1 h2).trans h

theorem hv_z : hv f pk m bits zCell = 0 := hv_c (by decide) (by decide) (hc_z ..)
theorem hv_one : hv f pk m bits oneCell = oneV := hv_c (by decide) (by decide) (hc_one ..)
theorem hv_tidx : hv f pk m bits tidxCell = natV 10 := hv_c (by decide) (by decide) (hc_tidx ..)
theorem hv_g : hv f pk m bits gCell = gV := hv_c (by decide) (by decide) (hc_g ..)
theorem hv_k0 : hv f pk m bits k0Cell = k0V := hv_c (by decide) (by decide) (hc_k0 ..)
theorem hv_sym {i : ℕ} (hi : i < 7) : hv f pk m bits (symCell i) = natV (i + 3) :=
  hv_c (by unfold symCell; omega) (by unfold symCell; omega) (hc_sym _ _ _ _ hi)
theorem hv_frame {k : ℕ} (hk : k < 42) : hv f pk m bits (fCell k) = frameV k :=
  hv_c (by unfold fCell; omega) (by unfold fCell; omega) (hc_frame _ _ _ _ hk)
theorem hv_idx : hv f pk m bits idxCell = loC (y0F f pk m bits) :=
  hv_c (by decide) (by decide) (hc_idx ..)
theorem hv_idx1 : hv f pk m bits (idxCell + 1) = hiC (y0F f pk m bits) :=
  hv_c (by decide) (by decide) (hc_idx1 ..)
theorem hv_t {k : ℕ} (hk : k < 42) :
    hv f pk m bits (tCell k) = fpat k (dg (idxOf (y0F f pk m bits)) k) :=
  hv_c (by unfold tCell; omega) (by unfold tCell; omega) (hc_t _ _ _ _ hk)
theorem hv_acc {k : ℕ} (hk : k < 41) :
    hv f pk m bits (accCell k) = natV (ofDigitsW Flat.wid (dg (idxOf (y0F f pk m bits))) (k + 1)) := by
  rw [show accCell k = 145 + k by unfold accCell; rw [if_neg (by omega)]]
  exact hv_c (by omega) (by omega) (hc_acc _ _ _ _ hk)
theorem hv_h {k : ℕ} (hk : k < 42) :
    hv f pk m bits (hCell k) = ofK (gpow (entryOf k (dg (idxOf (y0F f pk m bits)) k))) :=
  hv_c (by unfold hCell; omega) (by unfold hCell; omega) (hc_h _ _ _ _ hk)
theorem hv_h1 {k : ℕ} (hk : k < 42) :
    hv f pk m bits (h1Cell k) = ofK (gpow (entryOf k (dg (idxOf (y0F f pk m bits)) k) + 1)) :=
  hv_c (by unfold h1Cell; omega) (by unfold h1Cell; omega) (hc_h1 _ _ _ _ hk)
theorem hv_prod {k : ℕ} (h1 : 1 ≤ k) (hk : k < 41) :
    hv f pk m bits (prodOut k) =
      ofK (gpow (∑ j ∈ Finset.range (k + 1), entryOf j (dg (idxOf (y0F f pk m bits)) j))) := by
  rw [show prodOut k = 270 + k by unfold prodOut; rw [if_neg (by omega)]]
  exact hv_c (by omega) (by omega) (hc_prod _ _ _ _ hk)
theorem hv_top {k : ℕ} (hk : k < 42) :
    hv f pk m bits (topCell k) = cellOfBits (topOf bits (y0F f pk m bits) (AF f pk m bits) k) :=
  hv_c (by unfold topCell; omega) (by unfold topCell; omega) (hc_top _ _ _ _ hk)
theorem hv_top1 {k : ℕ} (hk : k < 42) :
    hv f pk m bits (topCell k + 1) = hiOf (y0F f pk m bits) (AF f pk m bits) k :=
  hv_c (by unfold topCell; omega) (by unfold topCell; omega) (hc_top1 _ _ _ _ hk)
theorem hv_cv0 : hv f pk m bits cvCell =
    cellOfBits (topOf bits (y0F f pk m bits) (AF f pk m bits) 0) :=
  hv_c (by decide) (by decide) (hc_cv0 ..)
theorem hv_cv1 : hv f pk m bits (cvCell + 1) =
    cellOfBits (topOf bits (y0F f pk m bits) (AF f pk m bits) 1) :=
  hv_c (by decide) (by decide) (hc_cv1 ..)
theorem hv_cv2 : hv f pk m bits (cvCell + 1 + 1) = hiOf (y0F f pk m bits) (AF f pk m bits) 1 :=
  hv_c (by decide) (by decide) (hc_cv2 ..)
theorem hv_x {k t : ℕ} (hk : k < 42) (ht : t < 16) :
    hv f pk m bits (xCell k t) = loC (AF f pk m bits k t) :=
  hv_c (by unfold xCell; omega) (by unfold xCell; omega) (hc_x _ _ _ _ hk ht)
theorem hv_x1 {k t : ℕ} (hk : k < 42) (ht : t < 16) :
    hv f pk m bits (xCell k t + 1) = hiC (AF f pk m bits k t) :=
  hv_c (by unfold xCell; omega) (by unfold xCell; omega) (hc_x1 _ _ _ _ hk ht)
theorem hv_st {r : ℕ} (hr : r < 10) : hv f pk m bits (stCell r) = loC (RAF f pk m bits r) :=
  hv_c (by unfold stCell; omega) (by unfold stCell; omega) (hc_st _ _ _ _ hr)
theorem hv_st1 {r : ℕ} (hr : r < 10) : hv f pk m bits (stCell r + 1) = hiC (RAF f pk m bits r) :=
  hv_c (by unfold stCell; omega) (by unfold stCell; omega) (hc_st1 _ _ _ _ hr)

/-- The root reads the honest tops. -/
theorem hv_rootTop {k : ℕ} (hk : k < 42) :
    hv f pk m bits (rootTop k) = cellOfBits (topOf bits (y0F f pk m bits) (AF f pk m bits) k) := by
  unfold rootTop
  by_cases h0 : k = 0
  · subst h0; rw [if_pos rfl]; exact hv_cv0
  · rw [if_neg h0]
    by_cases h1 : k = 1
    · subst h1; rw [if_pos rfl]; exact hv_cv1
    · rw [if_neg h1]; exact hv_top hk

/-- The revealed words (for an admitted length). -/
theorem hv_w (hlen : bits.length = 5504) {k : ℕ} (hk : k < 42) :
    hv f pk m bits (wCell k) = cellOfBits (sigW bits k) := by
  rw [hv_lt f pk m bits (by unfold wCell; omega), show wCell k = 4 + k from rfl,
    inputWord_sig pk m bits hlen k]
  rfl

end Values

section Accepted

variable {f pk m bits}
variable (hlen : bits.length = 5504) (hacc : FP.Accepted (idxOf (y0F f pk m bits)))
  (hroot : rootValue f FP (topsOf f FP (idxOf (y0F f pk m bits)) bits) = pk)

include hacc in
theorem dF_sum : ∑ k ∈ Finset.range 42, dg (idxOf (y0F f pk m bits)) k = 106 := by
  have h : ∑ k : Fin numChains, FP.digit (idxOf (y0F f pk m bits)) k = 106 := hacc
  rw [← Fin.sum_univ_eq_sum_range (fun k => dg (idxOf (y0F f pk m bits)) k) 42]
  exact h

theorem ofDigits_idx : ofDigitsW Flat.wid (dg (idxOf (y0F f pk m bits))) 42 = (idxOf (y0F f pk m bits)).toNat := by
  apply ofDigitsW_digitW
  rw [Flat.pos_42]; exact BitVec.isLt _

theorem topsOfV_eq : topsOfV bits (y0F f pk m bits) (AF f pk m bits) =
    topsOf f FP (idxOf (y0F f pk m bits)) bits := by
  funext k
  unfold topsOfV topsOf
  rw [topOf_eq f pk m bits k.isLt, show FP.len k = W k.val from (W_eq_len k).symm]
  rfl

/-- The fixed-table relation on the loaded honest image. -/
abbrev HR (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) (t : ℕ) : Prop :=
  (cinstrAt t).Rel f (hv f pk m bits)

theorem hv_sym' : ∀ i < 7, hv f pk m bits (symCell i) = natV (i + 3) := fun _ hi => hv_sym hi

include hlen in
/-- The index query of the honest image. -/
theorem honest_idx_query :
    blake2sQuery ![hv f pk m bits msgLo, hv f pk m bits msgHi, hv f pk m bits nonceCell,
      hv f pk m bits pkCell] (hv f pk m bits zCell) (hv f pk m bits (zCell + 1))
      (hv f pk m bits tidxCell) = FP.idxInput m (decodeNonce bits) pk := by
  have hpk : cellBits (hv f pk m bits pkCell) = pk := by
    rw [show pkCell = 0 from rfl, hv_lt f pk m bits (by omega), inputWord_pk]
    exact cellBits_cellOfBits pk
  rw [blake2sQuery_eq, show zCell + 1 = oneCell from rfl, hv_one, hv_z, hv_tidx, cellBits_natV,
    cellBits_zero_E, cellBits_oneV, cv_const,
    show nonceCell = 46 from rfl, show msgHi = 2 from rfl, show msgLo = 1 from rfl,
    hv_lt f pk m bits (show 46 < 47 by omega), hv_lt f pk m bits (show 2 < 47 by omega),
    hv_lt f pk m bits (show 1 < 47 by omega), inputWord_nonce pk m bits hlen, inputWord_two,
    inputWord_one, cellBits_cellOfBits (decodeNonce bits),
    cellBits_cellOfBits (m.extractLsb' 128 128), cellBits_cellOfBits (m.extractLsb' 0 128),
    msg_split, hpk]
  rfl

/-- The honest dispatch of chain `k`. -/
theorem honest_dispatch {k : ℕ} (hk : k < 42) : (CInstr.dispatch k).Rel f (hv f pk m bits) := by
  refine ⟨?_, ?_, entryOf k (dg (idxOf (y0F f pk m bits)) k),
    isEntry_of hk (dF_lt f pk m bits hk), ?_⟩
  · rw [hv_h hk]; exact isInK_ofK _
  · rw [hv_h1 hk]; exact isInK_ofK _
  · rw [hv_h hk, limb_ofK_zero]

/-- The honest `MUL(H_k, g, H'_k)`. -/
theorem honest_hmul {k : ℕ} (hk : k < 42) :
    (CInstr.mul (hCell k) gCell (h1Cell k)).Rel f (hv f pk m bits) := by
  show hv f pk m bits (h1Cell k) = hv f pk m bits (hCell k) * hv f pk m bits gCell
  rw [hv_h1 hk, hv_h hk, hv_g, gV, ← ofK_mul, mul_comm, g_mul_gpow]

include hlen in
theorem honest_pro : ∀ t < 58, HR f pk m bits t := by
  intro t ht
  by_cases h6 : t < 6
  · unfold HR
    interval_cases t
    · rw [cinstrAt_set0]; exact hv_z
    · rw [cinstrAt_set1]; exact hv_one
    · rw [cinstrAt_set2]
      show hv f pk m bits 3 = natV 5504
      rw [hv_lt f pk m bits (by omega)]; exact inputWord_len_of pk m bits hlen
    · rw [cinstrAt_set3]; exact hv_tidx
    · rw [cinstrAt_set4]; exact hv_g
    · rw [cinstrAt_set5]; exact hv_k0
  by_cases h13 : t < 13
  · obtain ⟨i, rfl⟩ : ∃ i, t = 6 + i := ⟨t - 6, by omega⟩
    unfold HR; rw [cinstrAt_sym (by omega)]; exact hv_sym (by omega)
  by_cases h55 : t < 55
  · obtain ⟨k, rfl⟩ : ∃ k, t = 13 + k := ⟨t - 13, by omega⟩
    unfold HR; rw [cinstrAt_frame (by omega)]; exact hv_frame (by omega)
  unfold HR
  rcases (show t = 55 ∨ t = 56 ∨ t = 57 by omega) with rfl | rfl | rfl
  · rw [cinstrAt_55]
    refine blake_rel (a := y0F f pk m bits) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hv_idx hv_idx1
    · rw [show msgLo = 1 from rfl, hv_lt f pk m bits (by omega), inputWord_one]
      exact canon_cellOfBits _
    · rw [show msgHi = 2 from rfl, hv_lt f pk m bits (by omega), inputWord_two]
      exact canon_cellOfBits _
    · rw [show nonceCell = 46 from rfl, hv_lt f pk m bits (by omega),
        inputWord_nonce pk m bits hlen]
      exact canon_cellOfBits _
    · rw [show pkCell = 0 from rfl, hv_lt f pk m bits (by omega), inputWord_pk]
      exact canon_cellOfBits _
    · rw [hv_z]; exact canon_zero
    · rw [show zCell + 1 = oneCell from rfl, hv_one]; exact canon_ofK 1
    · rw [hv_tidx]; exact canon_natV _
    · rw [honest_idx_query hlen]; rfl
  · rw [cinstrAt_56]; exact honest_hmul (by omega)
  · rw [cinstrAt_57]; exact honest_dispatch (by omega)

include hlen in
/-- The honest source of chain step `t`. -/
theorem honest_src {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < dg (idxOf (y0F f pk m bits)) k) :
    cellBits (hv f pk m bits (if t = 0 then wCell k else xCell k (t - 1))) =
      chainValue f FP ⟨k, hk⟩ (W k - 1 - dg (idxOf (y0F f pk m bits)) k) t (sigW bits k) := by
  by_cases h0 : t = 0
  · rw [if_pos h0, hv_w hlen hk, cellBits_cellOfBits, h0]; rfl
  · rw [if_neg h0]
    have hd := dF_lt f pk m bits hk
    have := @W_le k
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    rw [Nat.add_sub_cancel, hv_x hk (by omega), cellBits_loC, AF_spec f pk m bits hk (by omega),
      chainValue_succ]

/-- The honest destination pair of chain step `t`. -/
theorem honest_dst {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < dg (idxOf (y0F f pk m bits)) k) :
    hv f pk m bits (if t + 1 = dg (idxOf (y0F f pk m bits)) k then chainOut k else xCell k t) =
        loC (AF f pk m bits k t) ∧
      hv f pk m bits ((if t + 1 = dg (idxOf (y0F f pk m bits)) k then chainOut k else xCell k t) + 1) =
        hiC (AF f pk m bits k t) := by
  have hd := dF_lt f pk m bits hk
  have := @W_le k
  by_cases hl : t + 1 = dg (idxOf (y0F f pk m bits)) k
  · rw [if_pos hl]
    have htop : topOf bits (y0F f pk m bits) (AF f pk m bits) k =
        (AF f pk m bits k t).extractLsb' 0 128 := by
      unfold topOf; rw [if_neg (by omega), show dg (idxOf (y0F f pk m bits)) k - 1 = t by omega]
    have hhi : hiOf (y0F f pk m bits) (AF f pk m bits) k = hiC (AF f pk m bits k t) := by
      unfold hiOf; rw [if_neg (by omega), show dg (idxOf (y0F f pk m bits)) k - 1 = t by omega]; rfl
    unfold chainOut
    by_cases h1 : k = 1
    · subst h1
      rw [if_pos rfl]
      exact ⟨by rw [hv_cv1, htop]; rfl, by rw [hv_cv2, hhi]⟩
    · rw [if_neg h1]
      exact ⟨by rw [hv_top hk, htop]; rfl, by rw [hv_top1 hk, hhi]⟩
  · rw [if_neg hl]
    exact ⟨hv_x hk (by omega), hv_x1 hk (by omega)⟩

include hlen in
/-- The honest chain step `t` of chain `k`. -/
theorem honest_chainOp {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < dg (idxOf (y0F f pk m bits)) k) :
    (chainOp k (dg (idxOf (y0F f pk m bits)) k) t).Rel f (hv f pk m bits) := by
  have hd := dF_lt f pk m bits hk
  have hdst := honest_dst hk ht
  unfold chainOp
  refine blake_rel (a := AF f pk m bits k t) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hdst.1 hdst.2
  · by_cases h0 : t = 0
    · rw [if_pos h0, hv_w hlen hk]; exact canon_cellOfBits _
    · rw [if_neg h0, hv_x hk (by have := @W_le k; omega)]; exact canon_loC _
  · rw [hv_sym (Nat.mod_lt _ (by norm_num))]; exact canon_natV _
  · rw [hv_sym (Nat.mod_lt _ (by norm_num))]; exact canon_natV _
  · have hp : tagPos k (W k - 1 - dg (idxOf (y0F f pk m bits)) k + t) < 343 := by
      have := @W_le k; unfold tagPos Flat.off; split_ifs <;> omega
    rw [hv_sym (by omega)]; exact canon_natV _
  · rw [hv_z]; exact canon_zero
  · rw [show zCell + 1 = oneCell from rfl, hv_one]; exact canon_ofK 1
  · rw [hv_one]; exact canon_ofK 1
  · rw [chain_query hv_z hv_one hv_sym' hk (by omega), honest_src hlen hk ht,
      AF_spec f pk m bits hk ht]

include hacc in
/-- The landing product before and after chain `k`. -/
theorem honest_prod {k : ℕ} (h1 : 1 ≤ k) (hk : k < 42) :
    hv f pk m bits (prodPrev k) =
        ofK (gpow (∑ j ∈ Finset.range k, entryOf j (dg (idxOf (y0F f pk m bits)) j))) ∧
      hv f pk m bits (prodOut k) =
        ofK (gpow (∑ j ∈ Finset.range (k + 1), entryOf j (dg (idxOf (y0F f pk m bits)) j))) := by
  refine ⟨?_, ?_⟩
  · by_cases hk1 : k = 1
    · subst hk1
      rw [show prodPrev 1 = hCell 0 from rfl, hv_h (by omega), Finset.sum_range_one]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [prodPrev_succ (by omega) (by omega), hv_prod (by omega) (by omega)]
  · by_cases hk41 : k < 41
    · exact hv_prod h1 hk41
    · obtain rfl : k = 41 := by omega
      rw [show prodOut 41 = k0Cell from rfl, hv_k0, k0V]
      have hsplit : ∑ j ∈ Finset.range 42, entryOf j (dg (idxOf (y0F f pk m bits)) j) =
          ∑ j ∈ Finset.range 42, BASE j + 21 * ∑ j ∈ Finset.range 42, dg (idxOf (y0F f pk m bits)) j := by
        unfold entryOf; rw [Finset.sum_add_distrib, Finset.mul_sum]
      have heq : rootSlot = ∑ j ∈ Finset.range 42, entryOf j (dg (idxOf (y0F f pk m bits)) j) := by
        rw [hsplit, base_sum, dF_sum hacc]; rfl
      rw [heq]

/-- The honest accumulator after chain `k`. -/
theorem honest_acc {k : ℕ} (hk : k < 42) :
    hv f pk m bits (accCell k) =
      natV (ofDigitsW Flat.wid (dg (idxOf (y0F f pk m bits))) (k + 1)) := by
  by_cases hk41 : k < 41
  · exact hv_acc hk41
  · obtain rfl : k = 41 := by omega
    rw [show accCell 41 = idxCell from rfl, hv_idx, show 41 + 1 = 42 from rfl, ofDigits_idx]
    unfold loC natV idxOf
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]

include hlen hacc in
/-- **The honest blocks.** Every op of every block on the honest path holds. -/
theorem honest_blk : ∀ k < 42, ∀ i, 0 < i →
    i ≤ 1 + pre k + dg (idxOf (y0F f pk m bits)) k + post k →
      HR f pk m bits (entryOf k (dg (idxOf (y0F f pk m bits)) k) + i) := by
  intro k hk i hi0 hi
  have hd := dF_lt f pk m bits hk
  obtain ⟨s, hs⟩ : ∃ s, dg (idxOf (y0F f pk m bits)) k = s := ⟨_, rfl⟩
  have hchain : ∀ t < s, (chainOp k s t).Rel f (hv f pk m bits) := fun t ht => by
    subst hs; exact honest_chainOp hlen hk ht
  rw [hs] at hi hd ⊢
  unfold HR
  rw [cinstrAt_blk hk hd hi0 hi]
  by_cases hk0 : k = 0
  · subst hk0
    rw [pre_zero, post_zero] at hi
    by_cases h1 : i = 1
    · subst h1
      rw [blockOp0_one]
      show hv f pk m bits (accCell 0) = fpat 0 s
      rw [honest_acc (by omega), ofDigitsW_succ, ofDigitsW_zero, Nat.zero_add, hs]
      rfl
    by_cases h2 : i < s + 2
    · have := blockOp_chain (k := 0) (s := s) (t := i - 2) (by omega)
      rw [pre_zero, show 1 + 1 + (i - 2) = i by omega] at this
      rw [this]; exact hchain _ (by omega)
    by_cases h3 : i = s + 2
    · subst h3
      rw [blockOp0_copy]
      show hv f pk m bits cvCell = hv f pk m bits _ + hv f pk m bits zCell
      rw [hv_z, add_zero, hv_cv0]
      unfold topOf
      rw [hs]
      by_cases hs0 : s = 0
      · rw [if_pos hs0, if_pos hs0, hv_w hlen (by omega)]
      · rw [if_neg hs0, if_neg hs0, hv_top (by omega)]
        unfold topOf; rw [hs, if_neg hs0]
    by_cases h4 : i = s + 3
    · subst h4
      have := blockOp_nextMul (k := 0) (s := s) (by omega)
      rw [pre_zero, post_zero, show 1 + 1 + s + 2 - 1 = s + 3 by omega] at this
      rw [this]; exact honest_hmul (by omega)
    · obtain rfl : i = s + 4 := by omega
      have := blockOp_ctl (k := 0) (s := s) (by omega)
      rw [pre_zero, post_zero, show 1 + 1 + s + 2 = s + 4 by omega, if_pos (by omega)] at this
      rw [this]; exact honest_dispatch (by omega)
  · rw [pre_pos hk0] at hi
    by_cases h1 : i = 1
    · subst h1
      rw [blockOpK_one hk0]
      by_cases hs0 : s = 0
      · rw [if_pos hs0]
        show hv f pk m bits (rootTop k) = hv f pk m bits (wCell k) + hv f pk m bits zCell
        rw [hv_z, add_zero, hv_rootTop hk, hv_w hlen hk]
        unfold topOf; rw [hs, if_pos hs0]
      · rw [if_neg hs0]
        show hv f pk m bits (tCell k) = fpat k s
        rw [hv_t hk, hs]
    by_cases h2 : i = 2
    · subst h2
      rw [blockOpK_two hk0]
      show hv f pk m bits (accCell k) = hv f pk m bits (accCell (k - 1)) + hv f pk m bits _
      have hop : hv f pk m bits (if s = 0 then zCell else tCell k) = fpat k s := by
        by_cases hs0 : s = 0
        · rw [if_pos hs0, hv_z, hs0, fpat_zero]
        · rw [if_neg hs0, hv_t hk, hs]
      have hlt := ofDigitsW_lt Flat.wid (dg (idxOf (y0F f pk m bits)))
        (fun j => digitW_lt Flat.wid _ j) k
      have hlt2 := ofDigitsW_lt Flat.wid (dg (idxOf (y0F f pk m bits)))
        (fun j => digitW_lt Flat.wid _ j) (k + 1)
      have h42 := posW_le_42 (k := k + 1) (by omega)
      have hpow : 2 ^ posW Flat.wid (k + 1) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) h42
      rw [hop, honest_acc hk, honest_acc (by omega), show k - 1 + 1 = k by omega]
      unfold fpat
      rw [ofDigitsW_succ Flat.wid _ k, hs] at hlt2 ⊢
      rw [natV_add_disjoint hlt (by omega)]
    by_cases h3 : i = 3
    · subst h3
      rw [blockOp_three hk0]
      show hv f pk m bits (prodOut k) = hv f pk m bits (prodPrev k) * hv f pk m bits (hCell k)
      obtain ⟨hp, ho⟩ := honest_prod hacc (k := k) (by omega) hk
      rw [ho, hp, hv_h hk, ← ofK_mul, gpow_mul_gpow, Finset.sum_range_succ]
    by_cases h4 : i < s + 4
    · have := blockOp_chain (k := k) (s := s) (t := i - 4) (by omega)
      rw [pre_pos hk0, show 1 + 3 + (i - 4) = i by omega] at this
      rw [this]; exact hchain _ (by omega)
    by_cases h41 : k < 41
    · rw [post_mid hk0 h41] at hi
      by_cases h5 : i = s + 4
      · subst h5
        have := blockOp_nextMul (k := k) (s := s) h41
        rw [pre_pos hk0, post_mid hk0 h41, show 1 + 3 + s + 1 - 1 = s + 4 by omega] at this
        rw [this]; exact honest_hmul (by omega)
      · obtain rfl : i = s + 5 := by omega
        have := blockOp_ctl (k := k) (s := s) hk
        rw [pre_pos hk0, post_mid hk0 h41, show 1 + 3 + s + 1 = s + 5 by omega, if_pos h41] at this
        rw [this]; exact honest_dispatch (by omega)
    · obtain rfl : k = 41 := by omega
      rw [post_41] at hi
      obtain rfl : i = s + 4 := by omega
      have := blockOp_ctl_exit (s := s)
      rw [pre_pos hk0, post_41, show 1 + 3 + s + 0 = s + 4 by omega] at this
      rw [this]
      show IsInK (hv f pk m bits k0Cell)
      rw [hv_k0]; exact isInK_ofK _

/-- The honest root tops. -/
abbrev tpsF (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) : Fin numChains → Word :=
  topsOfV bits (y0F f pk m bits) (AF f pk m bits)

theorem rootState_last (f : HashTable) (P : Params) (tp : Fin numChains → Word) :
    ∀ n r st, rootState f P tp r (n + 1) st = ans f (P.rootInput tp (r + n) (rootState f P tp r n st)) := by
  intro n
  induction n with
  | zero => intro r st; rfl
  | succ n ih =>
    intro r st
    show rootState f P tp (r + 1) (n + 1) _ = _
    rw [ih, show r + 1 + n = r + (n + 1) by ring]
    rfl

theorem RAF_eq {i : ℕ} (hi : i < 10) :
    RAF f pk m bits i = rootState f FP (tpsF f pk m bits) 0 (i + 1)
      (Params.rootInit (tpsF f pk m bits)) := by
  unfold RAF; exact rootAnsF_spec f _ 10 0 _ i hi

theorem topAt_tps {j : ℕ} (hj : j < 42) :
    Params.topAt (tpsF f pk m bits) j = topOf bits (y0F f pk m bits) (AF f pk m bits) j := by
  unfold Params.topAt; rw [dif_pos hj]; rfl

theorem cb_rootTop {j : ℕ} (hj : j < 42) :
    cellBits (hv f pk m bits (rootTop j)) = Params.topAt (tpsF f pk m bits) j := by
  rw [hv_rootTop hj, cellBits_cellOfBits, topAt_tps hj]

/-- The honest cv pair of root call `i`. -/
theorem honest_rootCv {i : ℕ} (hi : i < 10) :
    cellBits (hv f pk m bits (rootCv i + 1)) ++ cellBits (hv f pk m bits (rootCv i)) =
      rootState f FP (tpsF f pk m bits) 0 i (Params.rootInit (tpsF f pk m bits)) := by
  unfold rootCv
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl, hv_cv1, hv_cv0, cellBits_cellOfBits, cellBits_cellOfBits]
    unfold Params.rootInit
    rw [topAt_tps (by omega), topAt_tps (by omega)]
    rfl
  · rw [if_neg h0, hv_st1 (by omega), hv_st (by omega), cellBits_hiC, cellBits_loC, hi_append_lo]
    obtain ⟨u, rfl⟩ : ∃ u, i = u + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel, RAF_eq (by omega)]

include hlen in
theorem honest_rho {i : ℕ} (hi : i < 10) :
    IsCanonical128 (hv f pk m bits (rhoCell i)) ∧ cellBits (hv f pk m bits (rhoCell i)) = FP.rootMd i := by
  by_cases h0 : i = 0
  · subst h0; rw [show rhoCell 0 = zCell from rfl, hv_z]
    exact ⟨canon_zero, by rw [cellBits_zero_E]; rfl⟩
  by_cases h1 : i = 1
  · subst h1; rw [show rhoCell 1 = gCell from rfl, hv_g]
    exact ⟨canon_ofK _, by rw [cellBits_gV]; rfl⟩
  by_cases h9 : i < 9
  · rw [rhoCell_eq (by omega) h9, rootMd_eq (by omega) h9, hv_sym (by omega)]
    exact ⟨canon_natV _, by rw [cellBits_natV, show i - 2 + 3 = i + 1 by omega]⟩
  · obtain rfl : i = 9 := by omega
    rw [show rhoCell 9 = lenCell from rfl, show lenCell = 3 from rfl, hv_lt f pk m bits (by omega),
      inputWord_len_of pk m bits hlen]
    exact ⟨canon_natV _, by rw [cellBits_natV]; rfl⟩

include hlen hroot in
/-- **The honest root.** -/
theorem honest_root : ∀ t < 11, HR f pk m bits (rootSlot + t) := by
  intro t ht
  unfold HR
  rw [cinstrAt_root ht]
  unfold rootOp
  by_cases h10 : t < 10
  · rw [if_pos h10]
    obtain ⟨hcan, hmd⟩ := honest_rho hlen h10
    refine blake_rel (a := RAF f pk m bits t) ?_ ?_ ?_ ?_ ?_ ?_ hcan ?_ (hv_st h10) (hv_st1 h10)
    · rw [hv_rootTop (by omega)]; exact canon_cellOfBits _
    · rw [hv_rootTop (by omega)]; exact canon_cellOfBits _
    · rw [hv_rootTop (by omega)]; exact canon_cellOfBits _
    · rw [hv_rootTop (by omega)]; exact canon_cellOfBits _
    · unfold rootCv; split_ifs
      · rw [hv_cv0]; exact canon_cellOfBits _
      · rw [hv_st (by omega)]; exact canon_loC _
    · unfold rootCv; split_ifs
      · rw [hv_cv1]; exact canon_cellOfBits _
      · rw [hv_st1 (by omega)]; exact canon_hiC _
    · rw [blake2sQuery_eq, honest_rootCv h10, hmd, cb_rootTop (by omega), cb_rootTop (by omega),
        cb_rootTop (by omega), cb_rootTop (by omega), RAF_eq h10, rootState_last, Nat.zero_add]
      rfl
  · obtain rfl : t = 10 := by omega
    rw [if_neg (by omega)]
    show hv f pk m bits pkCell = hv f pk m bits (stCell 9) + hv f pk m bits zCell
    rw [hv_z, add_zero, hv_st (by omega), show pkCell = 0 from rfl, hv_lt f pk m bits (by omega),
      inputWord_pk]
    have hlo : (RAF f pk m bits 9).extractLsb' 0 128 = pk := by
      rw [RAF_eq (by omega)]
      show rootValue f FP (topsOfV bits (y0F f pk m bits) (AF f pk m bits)) = pk
      rw [topsOfV_eq]
      exact hroot
    unfold loC
    exact (congrArg cellOfBits hlo).symm

include hlen hacc hroot in
/-- **The honest path.** Every slot on the path of the index digits holds on the loaded honest
image. -/
theorem honest_path : PathFacts (HR f pk m bits) (dg (idxOf (y0F f pk m bits))) :=
  ⟨honest_pro hlen, honest_blk hlen hacc, honest_root hlen hroot⟩

include hlen hacc hroot in
/-- **Honest run.** When the verifier accepts under the table, the honest image completes in
`425` instructions. -/
theorem honest_run :
    simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost program (LeanIsa.loadInput pk m bits (imageF f pk m bits)) 425
          Regs.initial) = pure (some 1478) := by
  obtain ⟨n, c, hw⟩ := walk_mk (dF_valid f pk m bits) (honest_path hlen hacc hroot)
    (fun k hk => hv_h1 hk) hv_k0
  have hpin : Pinned (hv f pk m bits) := ⟨hv_one, fun k hk => hv_frame hk⟩
  obtain ⟨hV, hP, hL, rfl, rfl⟩ := walk_full (fun t h => CInstr.relNH_of_relB h) hw
  have hsum := layer_of_facts (fun t h => CInstr.relNH_of_relB h) hV hP hL
  have := sim_of_walk (le_refl 16) (by decide) f hpin hw
  rw [initial_eq]
  rw [totalSteps_eq hsum, totalCost_eq hsum] at this
  exact this

end Accepted

end Honest

end

end OptimalOTS.HLFlat
