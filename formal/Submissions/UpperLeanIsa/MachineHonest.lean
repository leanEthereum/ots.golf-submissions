import Submissions.UpperLeanIsa.MachineProver

/-!
# The honest image satisfies every relation on its path

Under a table `f` for which the verifier accepts, the honest image `imageF f pk m bits`, loaded
with the statement, satisfies the fixed-table relation of every slot on the path of the index
digits (`honest_path`), with the return hints and `K0` the walk needs; so the machine completes
in `253` instructions (`honest_run`). Together with `fixed_sound` this is `Faithful`.
-/

namespace OptimalOTS.HLFlat

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

/-! ## The honest cells -/

/-- `omega` after unfolding the cell layout. -/
macro "cellω" : tactic => `(tactic| ((try simp only [zCell, oneCell, gCell, k0Cell,
  fCell, idxCell, tCell, hCell, h1Cell, cCell, xCell, stCell] at *) <;>
  omega))

section Cells

variable (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (RA : ℕ → BitVec 256)

theorem hc_z : hcell bits y0 A RA zCell = 0 := by
  unfold hcell
  rw [if_pos (by cellω)]

theorem hc_one : hcell bits y0 A RA oneCell = oneV := by
  unfold hcell
  rw [if_neg (by cellω), if_pos (by cellω)]

theorem hc_g : hcell bits y0 A RA gCell = gV := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_k0 : hcell bits y0 A RA k0Cell = k0V := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_pos (by cellω)]

theorem hc_frame {g : ℕ} (hg : g < 14) : hcell bits y0 A RA (fCell g) = frameV g := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  congr 1; unfold fCell; omega

theorem hc_idx : hcell bits y0 A RA idxCell = loC y0 := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]

theorem hc_idx1 : hcell bits y0 A RA (idxCell + 1) = hiC y0 := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_pos (by cellω)]

theorem hc_t {g : ℕ} (hg : g < 14) :
    hcell bits y0 A RA (tCell g) = natV (gwordS (dg y0) g) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_pos (by cellω)]
  rw [show tCell g - 103 = g by unfold tCell; omega]

theorem hc_acc {g : ℕ} (hg : g < 13) :
    hcell bits y0 A RA (145 + g) = ∑ j ∈ Finset.range (g + 1), natV (gwordS (dg y0) j) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [show 145 + g - 144 = g + 1 by omega]

theorem hc_h {g : ℕ} (hg : g < 14) :
    hcell bits y0 A RA (hCell g) = ofK (gpow (entryOf g (dg y0))) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_pos (by cellω)]
  rw [show hCell g - 186 = g by unfold hCell; omega]

theorem hc_h1 {g : ℕ} (hg : g < 14) :
    hcell bits y0 A RA (h1Cell g) = ofK (gpow (entryOf g (dg y0) + 1)) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [show h1Cell g - 228 = g by unfold h1Cell; omega]

theorem hc_c {g : ℕ} (hg : g < 14) :
    hcell bits y0 A RA (cCell g) = ofK (gpow (sig (dg y0) g)) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [show cCell g - 270 = g by unfold cCell; omega]

theorem hc_lay {g : ℕ} (hg : g < 13) :
    hcell bits y0 A RA (290 + g) =
      ofK (gpow (rootSlot - 103 + ∑ j ∈ Finset.range (g + 1), sig (dg y0) j)) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_pos (by cellω)]
  rw [show 290 + g - 289 = g + 1 by omega]

theorem hc_gp {v : ℕ} (h2 : 2 ≤ v) (h7 : v ≤ 7) :
    hcell bits y0 A RA (440 + v) = ofK (gpow v) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_pos (by cellω)]
  rw [show 440 + v - 440 = v by omega]

theorem hc_out {k b : ℕ} (hk : k < 42) (hb : b < 2) :
    hcell bits y0 A RA (chainOut k + b) = pairV bits y0 A k b := by
  obtain ⟨h1, h2, h3, h4⟩ := out_decode k hk b hb
  generalize chainOut k + b = c at *
  subst h1 h2
  unfold hcell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem hc_x {k t : ℕ} (hk : k < 42) (ht : t < 16) :
    hcell bits y0 A RA (xCell k t) = loC (A k t) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_pos (by cellω), show (xCell k t - 1024) / 32 = k by unfold xCell; omega,
    show (xCell k t - 1024) % 32 / 2 = t by unfold xCell; omega]

theorem hc_x1 {k t : ℕ} (hk : k < 42) (ht : t < 16) :
    hcell bits y0 A RA (xCell k t + 1) = hiC (A k t) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_neg (by cellω), show (xCell k t + 1 - 1024) / 32 = k by unfold xCell; omega,
    show (xCell k t + 1 - 1024) % 32 / 2 = t by unfold xCell; omega]

theorem hc_st {r : ℕ} (hr : r < 9) : hcell bits y0 A RA (stCell r) = loC (RA r) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_pos (by cellω), show (stCell r - 2400) / 2 = r by unfold stCell; omega]

theorem hc_st1 {r : ℕ} (hr : r < 9) : hcell bits y0 A RA (stCell r + 1) = hiC (RA r) := by
  unfold hcell
  rw [if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω),
    if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_neg (by cellω), if_pos (by cellω)]
  rw [if_neg (by cellω), show (stCell r + 1 - 2400) / 2 = r by unfold stCell; omega]

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
theorem canon_symV (i : ℕ) : IsCanonical128 (symV i) := by
  unfold symV; split_ifs
  · exact canon_zero
  · exact canon_ofK _

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


/-- The chain-step query of a chain op, from the constants' values. -/
theorem chain_query {v : ℕ → E} (hz : v zCell = 0) (hone : v oneCell = oneV)
    (hsym : ∀ i < 7, v (symCell i) = symV i) {k : ℕ} (hk : k < 42) {j : ℕ} (hj : j < W k)
    (x : E) :
    blake2sQuery ![x, v (symCell (tagPos k j % 7)), v (symCell (tagPos k j / 7 % 7)),
        v (symCell (tagPos k j / 49))] (v zCell) (v (zCell + 1)) (v oneCell) =
      FP.chainInput ⟨k, hk⟩ j (cellBits x) := by
  have hp : tagPos k j < 343 := by
    have := @W_le k; unfold tagPos Flat.off; split_ifs <;> omega
  rw [blake2sQuery_eq, hsym _ (Nat.mod_lt _ (by norm_num)), hsym _ (Nat.mod_lt _ (by norm_num)),
    hsym _ (by omega), cellBits_symV (Nat.mod_lt _ (by norm_num)),
    cellBits_symV (Nat.mod_lt _ (by norm_num)), cellBits_symV (by omega),
    show zCell + 1 = oneCell from rfl, hone, hz, cellBits_zero_E, cellBits_oneV, cv_const]
  rfl

/-! ## Blocks by region -/

/-- Every op of a block holds once its pre ops, nops, steps and tail hold. -/
theorem blockOp_of {P : CInstr → Prop} {g d a b c i : ℕ} (hg : g < 14) (ha : a < 8) (hb : b < 8)
    (hc : c < Wc g) (hi0 : 0 < i) (hi : i ≤ NH g + (a + b + c) + (if g < 13 then 1 else 0))
    (hpre : ∀ q < preLen g a b c, P (preOp g d a b c q)) (hnop : P nop)
    (hstep : ∀ t < a + b + c, P (stepOp g a b c t))
    (htail : P (if g < 13 then .mul (hCell (g + 1)) gCell (h1Cell (g + 1)) else .exit))
    (hdisp : g < 13 → P (.dispatch (g + 1))) : P (blockOp g d a b c i) := by
  have hfit := pre_fit hg ha hb hc
  by_cases h1 : i < 1 + preLen g a b c
  · obtain ⟨q, rfl⟩ : ∃ q, i = 1 + q := ⟨i - 1, by omega⟩
    rw [blockOp_pre (by omega)]; exact hpre q (by omega)
  by_cases h2 : i < NH g
  · rw [blockOp_nop (by omega) h2]; exact hnop
  by_cases h3 : i < NH g + (a + b + c)
  · obtain ⟨t, rfl⟩ : ∃ t, i = NH g + t := ⟨i - NH g, by omega⟩
    rw [blockOp_step hfit (by omega)]; exact hstep t (by omega)
  by_cases h5 : i = NH g + (a + b + c)
  · rw [h5, blockOp_tail hfit]; exact htail
  · have hg13 : g < 13 := by split_ifs at hi <;> omega
    rw [if_pos hg13] at hi
    rw [show i = NH g + (a + b + c) + 1 by omega, blockOp_disp hfit hg13]
    exact hdisp hg13

/-- The place of a zero digit. -/
theorem zeroIdx_spec {a b c q : ℕ} (hq : q < zeroCount a b c) :
    zeroIdx a b q < 3 ∧ (zeroIdx a b q = 0 → a = 0) ∧ (zeroIdx a b q = 1 → b = 0) ∧
      (zeroIdx a b q = 2 → c = 0) := by
  unfold zeroIdx; unfold zeroCount at hq
  by_cases h0 : a = 0 <;> by_cases h1 : b = 0 <;> by_cases h2 : c = 0 <;>
    simp only [h0, h1, h2, if_true, if_false] at hq ⊢ <;>
    rcases (show q = 0 ∨ q = 1 ∨ q = 2 by omega) with rfl | rfl | rfl <;> simp_all

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

theorem dF_lt {k : ℕ} (hk : k < 42) : dg (y0F f pk m bits) k < W k := by
  rw [W_eq_pow hk, dg_lt hk]; exact digitW_lt _ _ _

theorem dF_valid : Valid (dg (y0F f pk m bits)) :=
  ⟨fun _ hk => dF_lt f pk m bits hk, by unfold dg; rw [if_pos rfl]; omega⟩

theorem AF_eq {k : ℕ} (hk : k < 42) (t : ℕ) :
    AF f pk m bits k t = chainAnsF f ⟨k, hk⟩ (W k - 1 - dg (y0F f pk m bits) k) (dg (y0F f pk m bits) k)
      (sigW bits k) t := by
  unfold AF chainTab; rw [dif_pos hk]

/-- The honest chain values. -/
theorem AF_spec {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < dg (y0F f pk m bits) k) :
    AF f pk m bits k t = ans f (FP.chainInput ⟨k, hk⟩ (W k - 1 - dg (y0F f pk m bits) k + t)
      (chainValue f FP ⟨k, hk⟩ (W k - 1 - dg (y0F f pk m bits) k) t (sigW bits k))) := by
  rw [AF_eq f pk m bits hk, chainAnsF_spec f _ _ _ _ _ ht]

/-- The slice of the step producing the top: the top's half. -/
theorem slice_last {k : ℕ} (hk : k < 42) {j : ℕ} (hj : j + 2 = W k) (y : BitVec 256) :
    FP.slice ⟨k, hk⟩ j y = y.extractLsb' (128 * topBit k) 128 := by
  unfold Params.slice topBit
  rw [stepOff_eq hk]
  by_cases h : hiChain k = true
  · rw [if_pos ⟨h, hj⟩, if_pos h]; rfl
  · rw [if_neg (fun h' => h h'.1), if_neg h]; rfl

/-- The slice of every other step: the low half. -/
theorem slice_mid {k : ℕ} (hk : k < 42) {j : ℕ} (hj : j + 2 ≠ W k) (y : BitVec 256) :
    FP.slice ⟨k, hk⟩ j y = y.extractLsb' 0 128 := by
  unfold Params.slice
  rw [stepOff_eq hk, if_neg (fun h' => hj h'.2)]
  rfl

/-- The honest top of chain `k` is the verifier's. -/
theorem topOf_eq {k : ℕ} (hk : k < 42) :
    topOf bits (y0F f pk m bits) (AF f pk m bits) k =
      chainValue f FP ⟨k, hk⟩ (W k - 1 - dg (y0F f pk m bits) k) (dg (y0F f pk m bits) k) (sigW bits k) := by
  unfold topOf
  by_cases h0 : dg (y0F f pk m bits) k = 0
  · rw [if_pos h0, h0]; rfl
  · rw [if_neg h0]
    have hd := dF_lt f pk m bits hk
    obtain ⟨u, hu⟩ : ∃ u, dg (y0F f pk m bits) k = u + 1 := ⟨dg (y0F f pk m bits) k - 1, by omega⟩
    have hs := AF_spec f pk m bits hk (t := u) (by omega)
    rw [hu] at hs hd
    rw [hu, Nat.add_sub_cancel, hs, chainValue_succ, slice_last hk (by omega)]

/-! ### Cell values of the loaded honest image -/

section Values

variable {f pk m bits}

theorem hv_c {c : ℕ} (h1 : 47 ≤ c) (h2 : c < 2 ^ 16) {x : E}
    (h : hcell bits (y0F f pk m bits) (AF f pk m bits) (RAF f pk m bits) c = x) :
    hv f pk m bits c = x := (hv_ge f pk m bits h1 h2).trans h

theorem hv_z : hv f pk m bits zCell = 0 := hv_c (by decide) (by decide) (hc_z ..)
theorem hv_one : hv f pk m bits oneCell = oneV := hv_c (by decide) (by decide) (hc_one ..)
theorem hv_g : hv f pk m bits gCell = gV := hv_c (by decide) (by decide) (hc_g ..)
theorem hv_k0 : hv f pk m bits k0Cell = k0V := hv_c (by decide) (by decide) (hc_k0 ..)
theorem hv_frame {g : ℕ} (hg : g < 14) : hv f pk m bits (fCell g) = frameV g :=
  hv_c (by unfold fCell; omega) (by unfold fCell; omega) (hc_frame _ _ _ _ hg)
theorem hv_idx : hv f pk m bits idxCell = loC (y0F f pk m bits) :=
  hv_c (by decide) (by decide) (hc_idx ..)
theorem hv_idx1 : hv f pk m bits (idxCell + 1) = hiC (y0F f pk m bits) :=
  hv_c (by decide) (by decide) (hc_idx1 ..)
theorem hv_t {g : ℕ} (hg : g < 14) :
    hv f pk m bits (tCell g) = natV (gwordS (dg (y0F f pk m bits)) g) :=
  hv_c (by unfold tCell; omega) (by unfold tCell; omega) (hc_t _ _ _ _ hg)
theorem hv_h {g : ℕ} (hg : g < 14) :
    hv f pk m bits (hCell g) = ofK (gpow (entryOf g (dg (y0F f pk m bits)))) :=
  hv_c (by unfold hCell; omega) (by unfold hCell; omega) (hc_h _ _ _ _ hg)
theorem hv_h1 {g : ℕ} (hg : g < 14) :
    hv f pk m bits (h1Cell g) = ofK (gpow (entryOf g (dg (y0F f pk m bits)) + 1)) :=
  hv_c (by unfold h1Cell; omega) (by unfold h1Cell; omega) (hc_h1 _ _ _ _ hg)
theorem hv_c' {g : ℕ} (hg : g < 14) :
    hv f pk m bits (cCell g) = ofK (gpow (sig (dg (y0F f pk m bits)) g)) :=
  hv_c (by unfold cCell; omega) (by unfold cCell; omega) (hc_c _ _ _ _ hg)

/-- The prologue constants `g ^ v`. -/
theorem hv_gp {v : ℕ} (h1 : 1 ≤ v) (h7 : v ≤ 7) : hv f pk m bits (gpCell v) = ofK (gpow v) := by
  unfold gpCell
  split_ifs with hv1
  · subst hv1
    rw [hv_g, gV, show gpow 1 = g from (g_mul_gpow 0).symm.trans (by rw [gpow_zero', mul_one])]
  · exact hv_c (by omega) (by omega) (hc_gp _ _ _ _ (by omega) h7)

/-- The symbol cells. -/
theorem hv_sym {i : ℕ} (hi : i < 7) : hv f pk m bits (symCell i) = symV i := by
  unfold symCell symV
  split_ifs with h0 h1
  · exact hv_z
  · subst h1; rw [hv_one, oneV, show 1 - 1 = 0 from rfl, gpow_zero']
  · exact hv_gp (by omega) (by omega)

theorem hv_out {k b : ℕ} (hk : k < 42) (hb : b < 2) :
    hv f pk m bits (chainOut k + b) = pairV bits (y0F f pk m bits) (AF f pk m bits) k b := by
  have := out_decode k hk b hb
  exact hv_c (by omega) (by omega) (hc_out _ _ _ _ hk hb)
theorem hv_x {k t : ℕ} (hk : k < 42) (ht : t < 16) :
    hv f pk m bits (xCell k t) = loC (AF f pk m bits k t) :=
  hv_c (by unfold xCell; omega) (by unfold xCell; omega) (hc_x _ _ _ _ hk ht)
theorem hv_x1 {k t : ℕ} (hk : k < 42) (ht : t < 16) :
    hv f pk m bits (xCell k t + 1) = hiC (AF f pk m bits k t) :=
  hv_c (by unfold xCell; omega) (by unfold xCell; omega) (hc_x1 _ _ _ _ hk ht)
theorem hv_st {r : ℕ} (hr : r < 9) : hv f pk m bits (stCell r) = loC (RAF f pk m bits r) :=
  hv_c (by unfold stCell; omega) (by unfold stCell; omega) (hc_st _ _ _ _ hr)
theorem hv_st1 {r : ℕ} (hr : r < 9) : hv f pk m bits (stCell r + 1) = hiC (RAF f pk m bits r) :=
  hv_c (by unfold stCell; omega) (by unfold stCell; omega) (hc_st1 _ _ _ _ hr)

theorem rootTop_eq_out (k : ℕ) : rootTop k = chainOut k + topBit k := by
  unfold topBit
  by_cases h : hiChain k = true
  · rw [if_pos h, rootTop_of_hi h]
  · rw [if_neg h, rootTop_of_lo h, Nat.add_zero]

/-- The root reads the honest tops. -/
theorem hv_rootTop {k : ℕ} (hk : k < 42) :
    hv f pk m bits (rootTop k) = cellOfBits (topOf bits (y0F f pk m bits) (AF f pk m bits) k) := by
  rw [rootTop_eq_out, hv_out hk (by unfold topBit; split_ifs <;> omega)]
  unfold pairV topOf
  by_cases h0 : dg (y0F f pk m bits) k = 0
  · rw [if_pos h0, if_pos h0, if_pos rfl]
  · rw [if_neg h0, if_neg h0]
    unfold topBit
    by_cases h : hiChain k = true
    · rw [if_pos h, if_neg (by omega)]; rfl
    · rw [if_neg h, if_pos rfl]; rfl

/-- The revealed words (for an admitted length). -/
theorem hv_w (hlen : bits.length = 5504) {k : ℕ} (hk : k < 42) :
    hv f pk m bits (wCell k) = cellOfBits (sigW bits k) := by
  rw [hv_lt f pk m bits (by unfold wCell; omega), show wCell k = 4 + k from rfl,
    inputWord_sig pk m bits hlen k]
  rfl

end Values

section Accepted

variable {f pk m bits}
variable (hlen : bits.length = 5504) (hacc : FP.Accepted (idxAns (y0F f pk m bits)))
  (hroot : rootValue f FP (topsOf f FP (idxAns (y0F f pk m bits)) bits) = pk)

include hacc in
theorem dF_sum : ∑ k ∈ Finset.range 42, dg (y0F f pk m bits) k = 103 := by
  have h : ∑ k : Fin numChains, FP.digit (idxAns (y0F f pk m bits)) k = 103 := hacc
  rw [Finset.sum_congr rfl fun k hk => dg_lt (Finset.mem_range.mp hk),
    ← Fin.sum_univ_eq_sum_range (fun k => digitW Flat.wid (idxAns (y0F f pk m bits)).toNat k) 42]
  exact h

theorem ofDigits_idx : ofDigitsW Flat.wid (digitW Flat.wid (idxAns (y0F f pk m bits)).toNat) 42 =
    (idxAns (y0F f pk m bits)).toNat := by
  apply ofDigitsW_digitW
  rw [Flat.pos_42]; exact BitVec.isLt _

theorem topsOfV_eq : topsOfV bits (y0F f pk m bits) (AF f pk m bits) =
    topsOf f FP (idxAns (y0F f pk m bits)) bits := by
  funext k
  unfold topsOfV topsOf
  rw [topOf_eq f pk m bits k.isLt, show FP.len k = W k.val from (W_eq_len k).symm, dg_lt k.isLt]
  rfl

/-- The fixed-table relation on the loaded honest image. -/
abbrev HR (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) (t : ℕ) : Prop :=
  (cinstrAt t).Rel f (hv f pk m bits)

theorem hv_sym' : ∀ i < 7, hv f pk m bits (symCell i) = symV i := fun _ hi => hv_sym hi

include hlen in
/-- The index query of the honest image. -/
theorem honest_idx_query :
    blake2sQuery ![hv f pk m bits msgLo, hv f pk m bits msgHi, hv f pk m bits nonceCell,
      hv f pk m bits pkCell] (hv f pk m bits zCell) (hv f pk m bits (zCell + 1))
      (hv f pk m bits lenCell) = FP.idxInput m (decodeNonce bits) pk := by
  have hpk : cellBits (hv f pk m bits pkCell) = pk := by
    rw [show pkCell = 0 from rfl, hv_lt f pk m bits (by omega), inputWord_pk]
    exact cellBits_cellOfBits pk
  rw [blake2sQuery_eq, show zCell + 1 = oneCell from rfl, hv_one, hv_z, show lenCell = 3 from rfl,
    hv_lt f pk m bits (show 3 < 47 by omega), inputWord_len_of pk m bits hlen, cellBits_natV,
    cellBits_zero_E, cellBits_oneV, cv_const,
    show nonceCell = 46 from rfl, show msgHi = 2 from rfl, show msgLo = 1 from rfl,
    hv_lt f pk m bits (show 46 < 47 by omega), hv_lt f pk m bits (show 2 < 47 by omega),
    hv_lt f pk m bits (show 1 < 47 by omega), inputWord_nonce pk m bits hlen, inputWord_two,
    inputWord_one, cellBits_cellOfBits (decodeNonce bits),
    cellBits_cellOfBits (m.extractLsb' 128 128), cellBits_cellOfBits (m.extractLsb' 0 128),
    msg_split, hpk]
  rfl

/-- The honest dispatch of group `g`. -/
theorem honest_dispatch {g : ℕ} (hg : g < 14) : (CInstr.dispatch g).Rel f (hv f pk m bits) := by
  refine ⟨?_, ?_, entryOf g (dg (y0F f pk m bits)),
    entryOf_isEntry (gvalid_of_valid (dF_valid f pk m bits) hg) hg, ?_⟩
  · rw [hv_h hg]; exact isInK_ofK _
  · rw [hv_h1 hg]; exact isInK_ofK _
  · rw [hv_h hg, limb_ofK_zero]

/-- The honest `MUL(H_g, g, H'_g)`. -/
theorem honest_hmul {g : ℕ} (hg : g < 14) :
    (CInstr.mul (hCell g) gCell (h1Cell g)).Rel f (hv f pk m bits) := by
  show hv f pk m bits (h1Cell g) = hv f pk m bits (hCell g) * hv f pk m bits gCell
  rw [hv_h1 hg, hv_h hg, hv_g, gV, ← ofK_mul, mul_comm, g_mul_gpow]

/-- The honest accumulator after group `g`; after group 13 it is the index cell. -/
theorem honest_acc {g : ℕ} (hg : g < 14) :
    hv f pk m bits (accCell g) =
      ∑ j ∈ Finset.range (g + 1), natV (gwordS (dg (y0F f pk m bits)) j) := by
  by_cases h13 : g < 13
  · rw [show accCell g = 145 + g by unfold accCell; rw [if_neg (by omega)]]
    exact hv_c (by omega) (by omega) (hc_acc _ _ _ _ h13)
  · obtain rfl : g = 13 := by omega
    simp only [show (13 : ℕ) + 1 = 14 from rfl]
    have hw : ∀ j ∈ Finset.range 14, gwordS (dg (y0F f pk m bits)) j =
        gword j (if j = 0 then (y0F f pk m bits).toNat % 2 else 0)
          (digitW Flat.wid (idxAns (y0F f pk m bits)).toNat (gch j 0))
          (digitW Flat.wid (idxAns (y0F f pk m bits)).toNat (gch j 1))
          (digitW Flat.wid (idxAns (y0F f pk m bits)).toNat (gch j 2)) := fun j hj => by
      have hj' := Finset.mem_range.mp hj
      unfold gwordS jdig
      rw [dg_lt (gch_lt hj' (by omega)), dg_lt (gch_lt hj' (by omega)),
        dg_lt (gch_lt hj' (by omega))]
      unfold dg; simp only [if_true]
    rw [show accCell 13 = idxCell from rfl, hv_idx, Finset.sum_congr rfl fun j hj => by rw [hw j hj],
      tie_sum _ (fun k => digitW_lt Flat.wid _ k) (Nat.mod_lt _ (by norm_num)), ofDigits_idx,
      toNat_idxAns]
    set y := (y0F f pk m bits).toNat with hy
    have hlt : y / 2 % 2 ^ 127 < 2 ^ 127 := Nat.mod_lt _ (by norm_num)
    rw [show 2 * (y / 2 % 2 ^ 127) = y / 2 % 2 ^ 127 * 2 ^ 1 by ring,
      natV_add_disjoint (N := y % 2) (a := y / 2 % 2 ^ 127) (n := 1) (by rw [pow_one]; omega)
        (by rw [pow_one]; omega)]
    unfold loC natV
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, ← hy, pow_one]
    omega

/-- The honest tie of group `g ≥ 1` adds its word to the previous accumulator. -/
theorem honest_tie {g : ℕ} (hg : g < 14) (hg0 : g ≠ 0) :
    hv f pk m bits (accCell g) =
      hv f pk m bits (accCell (g - 1)) + natV (gwordS (dg (y0F f pk m bits)) g) := by
  obtain ⟨j, rfl⟩ : ∃ j, g = j + 1 := ⟨g - 1, by omega⟩
  rw [honest_acc hg, Nat.add_sub_cancel, honest_acc (by omega), Finset.sum_range_succ _ (j + 1)]

include hacc in
/-- The honest layer product after group `g`; after group 13 it is `K0`. -/
theorem honest_lay {g : ℕ} (hg : g < 14) :
    hv f pk m bits (layCell g) = ofK (gpow (rootSlot - 103 +
      ∑ j ∈ Finset.range (g + 1), sig (dg (y0F f pk m bits)) j)) := by
  by_cases h13 : g < 13
  · rw [show layCell g = 290 + g by unfold layCell; rw [if_neg (by omega)]]
    exact hv_c (by omega) (by omega) (hc_lay _ _ _ _ h13)
  · obtain rfl : g = 13 := by omega
    rw [show layCell 13 = k0Cell from rfl, hv_k0, k0V, sum_sig, dF_sum hacc,
      show rootSlot - 103 + 103 = rootSlot by unfold rootSlot; omega]

include hacc in
theorem honest_lay_step {g : ℕ} (h1 : 1 ≤ g) (hg : g < 14) :
    hv f pk m bits (layCell g) =
      hv f pk m bits (layCell (g - 1)) * ofK (gpow (sig (dg (y0F f pk m bits)) g)) := by
  rw [honest_lay hacc hg, honest_lay hacc (by omega), ← ofK_mul, gpow_mul_gpow]
  obtain ⟨j, rfl⟩ : ∃ j, g = j + 1 := ⟨g - 1, by omega⟩
  rw [Nat.add_sub_cancel, Finset.sum_range_succ _ (j + 1), Nat.add_assoc]

include hlen in
theorem honest_pro : ∀ t < 28, HR f pk m bits t := by
  intro t ht
  by_cases h5 : t < 5
  · unfold HR
    interval_cases t
    · rw [cinstrAt_set0]; exact hv_z
    · rw [cinstrAt_set1]; exact hv_one
    · rw [cinstrAt_set2]
      show hv f pk m bits 3 = natV 5504
      rw [hv_lt f pk m bits (by omega)]; exact inputWord_len_of pk m bits hlen
    · rw [cinstrAt_set3]; exact hv_g
    · rw [cinstrAt_set4]; exact hv_k0
  by_cases h19 : t < 19
  · obtain ⟨g, rfl⟩ : ∃ g, t = 5 + g := ⟨t - 5, by omega⟩
    unfold HR; rw [cinstrAt_frame (by omega)]; exact hv_frame (by omega)
  by_cases h25 : t < 25
  · obtain ⟨v, rfl⟩ : ∃ v, t = 17 + v := ⟨t - 17, by omega⟩
    unfold HR; rw [cinstrAt_gp (by omega) (by omega)]; exact hv_gp (by omega) (by omega)
  unfold HR
  rcases (show t = 25 ∨ t = 26 ∨ t = 27 by omega) with rfl | rfl | rfl
  · rw [cinstrAt_idx]
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
    · rw [show lenCell = 3 from rfl, hv_lt f pk m bits (by omega), inputWord_len_of pk m bits hlen]
      exact canon_natV _
    · rw [honest_idx_query hlen]; rfl
  · rw [cinstrAt_hmul0]; exact honest_hmul (by omega)
  · rw [cinstrAt_disp0]; exact honest_dispatch (by omega)

include hlen in
/-- The honest source of chain step `t`. -/
theorem honest_src {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < dg (y0F f pk m bits) k) :
    cellBits (hv f pk m bits (if t = 0 then wCell k else xCell k (t - 1))) =
      chainValue f FP ⟨k, hk⟩ (W k - 1 - dg (y0F f pk m bits) k) t (sigW bits k) := by
  by_cases h0 : t = 0
  · rw [if_pos h0, hv_w hlen hk, cellBits_cellOfBits, h0]; rfl
  · rw [if_neg h0]
    have hd := dF_lt f pk m bits hk
    have := @W_le k
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    rw [Nat.add_sub_cancel, hv_x hk (by omega), cellBits_loC, AF_spec f pk m bits hk (by omega),
      chainValue_succ, slice_mid hk (by omega)]

/-- The honest destination pair of chain step `t`. -/
theorem honest_dst {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < dg (y0F f pk m bits) k) :
    hv f pk m bits (if t + 1 = dg (y0F f pk m bits) k then chainOut k else xCell k t) =
        loC (AF f pk m bits k t) ∧
      hv f pk m bits ((if t + 1 = dg (y0F f pk m bits) k then chainOut k else xCell k t) + 1) =
        hiC (AF f pk m bits k t) := by
  have hd := dF_lt f pk m bits hk
  have := @W_le k
  by_cases hl : t + 1 = dg (y0F f pk m bits) k
  · rw [if_pos hl]
    have hp : ∀ b, pairV bits (y0F f pk m bits) (AF f pk m bits) k b =
        if b = 0 then loC (AF f pk m bits k t) else hiC (AF f pk m bits k t) := fun b => by
      unfold pairV; rw [if_neg (by omega), show dg (y0F f pk m bits) k - 1 = t by omega]
    refine ⟨?_, ?_⟩
    · have h := hv_out (f := f) (pk := pk) (m := m) (bits := bits) hk (show 0 < 2 by omega)
      rw [Nat.add_zero] at h
      rw [h, hp 0, if_pos rfl]
    · rw [hv_out hk (show 1 < 2 by omega), hp 1, if_neg (by omega)]
  · rw [if_neg hl]
    exact ⟨hv_x hk (by omega), hv_x1 hk (by omega)⟩

include hlen in
/-- The honest chain step `t` of chain `k`. -/
theorem honest_chainOp {k : ℕ} (hk : k < 42) {t : ℕ} (ht : t < dg (y0F f pk m bits) k) :
    (chainOp k (dg (y0F f pk m bits) k) t).Rel f (hv f pk m bits) := by
  have hd := dF_lt f pk m bits hk
  have hdst := honest_dst hk ht
  unfold chainOp
  refine blake_rel (a := AF f pk m bits k t) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hdst.1 hdst.2
  · by_cases h0 : t = 0
    · rw [if_pos h0, hv_w hlen hk]; exact canon_cellOfBits _
    · rw [if_neg h0, hv_x hk (by have := @W_le k; omega)]; exact canon_loC _
  · rw [hv_sym (Nat.mod_lt _ (by norm_num))]; exact canon_symV _
  · rw [hv_sym (Nat.mod_lt _ (by norm_num))]; exact canon_symV _
  · have hp : tagPos k (W k - 1 - dg (y0F f pk m bits) k + t) < 343 := by
      have := @W_le k; unfold tagPos Flat.off; split_ifs <;> omega
    rw [hv_sym (by omega)]; exact canon_symV _
  · rw [hv_z]; exact canon_zero
  · rw [show zCell + 1 = oneCell from rfl, hv_one]; exact canon_ofK 1
  · rw [hv_one]; exact canon_ofK 1
  · rw [chain_query hv_z hv_one hv_sym' hk (by omega), honest_src hlen hk ht,
      AF_spec f pk m bits hk ht]

section Block

variable {g d a b c : ℕ} (hg : g < 14) (hd : jdig (dg (y0F f pk m bits)) g = d)
  (ha : dg (y0F f pk m bits) (gch g 0) = a)
  (hb : dg (y0F f pk m bits) (gch g 1) = b)
  (hc : dg (y0F f pk m bits) (gch g 2) = c)
include hg ha hb hc

omit hg in
include hd in
theorem honest_gw : gwordS (dg (y0F f pk m bits)) g = gword g d a b c := by
  unfold gwordS; rw [hd, ha, hb, hc]

omit hg in
theorem honest_sig : sig (dg (y0F f pk m bits)) g = a + b + c := by
  unfold sig; rw [ha, hb, hc]

omit hg in
/-- The digit of the chain at place `j` of the group. -/
theorem honest_dig {j : ℕ} (hj : j < 3) :
    dg (y0F f pk m bits) (gch g j) = if j = 0 then a else if j = 1 then b else c := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · rw [ha]; rfl
  · rw [hb]; rfl
  · rw [hc]; rfl

include hlen hacc hd in
/-- The honest pre ops: tie, zero copies, layer factor. -/
theorem honest_pre : ∀ q < preLen g a b c, (preOp g d a b c q).Rel f (hv f pk m bits) := by
  intro q hq
  unfold preOp
  split_ifs with h1 h2
  · unfold tieOp
    split_ifs with hg0 hs0 hq0
    · subst hg0
      show hv f pk m bits (accCell 0) = natV (gword 0 d a b c)
      rw [honest_acc (by omega), Finset.sum_range_one, honest_gw hd ha hb hc]
    · show hv f pk m bits (accCell g) = hv f pk m bits (accCell (g - 1)) + hv f pk m bits zCell
      have hd0 : d = 0 := by rw [← hd]; unfold jdig; rw [if_neg hg0]
      rw [honest_tie hg hg0, hv_z, honest_gw hd ha hb hc, hd0, show a = 0 by omega,
        show b = 0 by omega, show c = 0 by omega]
      unfold gword
      simp only [Nat.zero_mul, Nat.add_zero, natV_zero]
    · show hv f pk m bits (tCell g) = natV (gword g d a b c)
      rw [hv_t hg, honest_gw hd ha hb hc]
    · show hv f pk m bits (accCell g) =
        hv f pk m bits (accCell (g - 1)) + hv f pk m bits (tCell g)
      rw [honest_tie hg hg0, hv_t hg]
  · unfold zcOp
    obtain ⟨hj3, h0, h1', h2'⟩ := zeroIdx_spec (a := a) (b := b) (c := c)
      (q := q - tieLen g (a + b + c)) (by omega)
    generalize zeroIdx a b (q - tieLen g (a + b + c)) = j at hj3 h0 h1' h2'
    have hk := gch_lt hg hj3
    have hdk : dg (y0F f pk m bits) (gch g j) = 0 := by
      rw [honest_dig ha hb hc hj3]; split_ifs <;> omega
    show hv f pk m bits (rootTop (gch g j)) =
      hv f pk m bits (wCell (gch g j)) + hv f pk m bits zCell
    rw [hv_z, add_zero, hv_rootTop hk, hv_w hlen hk]
    unfold topOf; rw [if_pos hdk]
  · unfold layOp
    split_ifs with hg0 hs0 hs7 hq0
    · subst hg0
      show hv f pk m bits (layCell 0) = ofK (gpow (rootSlot - 103 + (a + b + c)))
      rw [honest_lay hacc (by omega), Finset.sum_range_one, honest_sig ha hb hc]
    · show hv f pk m bits (layCell g) = hv f pk m bits (layCell (g - 1)) * hv f pk m bits oneCell
      rw [honest_lay_step hacc (by omega) hg, hv_one, honest_sig ha hb hc, hs0, gpow_zero']; rfl
    · show hv f pk m bits (layCell g) =
        hv f pk m bits (layCell (g - 1)) * hv f pk m bits (gpCell (a + b + c))
      rw [honest_lay_step hacc (by omega) hg, hv_gp (by omega) hs7, honest_sig ha hb hc]
    · show hv f pk m bits (cCell g) = ofK (gpow (a + b + c))
      rw [hv_c' hg, honest_sig ha hb hc]
    · show hv f pk m bits (layCell g) =
        hv f pk m bits (layCell (g - 1)) * hv f pk m bits (cCell g)
      rw [honest_lay_step hacc (by omega) hg, hv_c' hg]

include hlen in
/-- The honest chain steps of the group. -/
theorem honest_step : ∀ t < a + b + c, (stepOp g a b c t).Rel f (hv f pk m bits) := by
  intro t ht
  have hstep : ∀ j < 3, ∀ u < dg (y0F f pk m bits) (gch g j),
      (chainOp (gch g j) (dg (y0F f pk m bits) (gch g j)) u).Rel f (hv f pk m bits) :=
    fun j hj u hu => honest_chainOp hlen (gch_lt hg hj) hu
  unfold stepOp
  split_ifs with h1 h2
  · have := hstep 0 (by omega) t (by rw [ha]; omega); rwa [ha] at this
  · have := hstep 1 (by omega) (t - a) (by rw [hb]; omega); rwa [hb] at this
  · have := hstep 2 (by omega) (t - a - b) (by rw [hc]; omega); rwa [hc] at this

end Block

include hlen hacc in
/-- **The honest blocks.** Every op of every block on the honest path holds. -/
theorem honest_blk : ∀ g < 14, ∀ i, 0 < i →
    i ≤ ctlOff g (sig (dg (y0F f pk m bits)) g) →
      HR f pk m bits (entryOf g (dg (y0F f pk m bits)) + i) := by
  intro g hg i hi0 hi
  have hV := dF_valid f pk m bits
  unfold HR
  rw [cinstrAt_blk (gvalid_of_valid hV hg) hg hi0 hi]
  obtain ⟨d, hd⟩ : ∃ d, jdig (dg (y0F f pk m bits)) g = d := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, dg (y0F f pk m bits) (gch g 0) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, dg (y0F f pk m bits) (gch g 1) = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, dg (y0F f pk m bits) (gch g 2) = c := ⟨_, rfl⟩
  have hva := hV.1 _ (gch_lt hg (show 0 < 3 by omega))
  have hvb := hV.1 _ (gch_lt hg (show 1 < 3 by omega))
  have hvc := hV.1 _ (gch_lt hg (show 2 < 3 by omega))
  rw [W_gch hg (by omega), if_pos (by omega), ha] at hva
  rw [W_gch hg (by omega), if_pos (by omega), hb] at hvb
  rw [W_gch hg (by omega), if_neg (by omega), hc] at hvc
  rw [hd, ha, hb, hc]
  rw [honest_sig ha hb hc] at hi
  unfold ctlOff at hi
  apply blockOp_of hg hva hvb hvc hi0 hi (honest_pre hlen hacc hg hd ha hb hc)
  · show hv f pk m bits zCell = hv f pk m bits zCell + hv f pk m bits zCell
    rw [hv_z, add_zero]
  · exact honest_step hlen hg ha hb hc
  · split_ifs with h13
    · exact honest_hmul (by omega)
    · show IsInK (hv f pk m bits k0Cell)
      rw [hv_k0]; exact isInK_ofK _
  · intro h13
    exact honest_dispatch (by omega)

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

theorem RAF_eq {i : ℕ} (hi : i < 9) :
    RAF f pk m bits i = rootState f FP (tpsF f pk m bits) 0 (i + 1)
      (Params.rootInit (tpsF f pk m bits)) := by
  unfold RAF; exact rootAnsF_spec f _ 9 0 _ i hi

theorem topAt_tps {j : ℕ} (hj : j < 42) :
    Params.topAt (tpsF f pk m bits) j = topOf bits (y0F f pk m bits) (AF f pk m bits) j := by
  unfold Params.topAt; rw [dif_pos hj]; rfl

theorem cb_rootTop {j : ℕ} (hj : j < 42) :
    cellBits (hv f pk m bits (rootTop j)) = Params.topAt (tpsF f pk m bits) j := by
  rw [hv_rootTop hj, cellBits_cellOfBits, topAt_tps hj]

/-- The honest cv pair of root call `i`, and its cells are canonical. -/
theorem honest_rootCv {i : ℕ} (hi : i < 9) :
    IsCanonical128 (hv f pk m bits (rootCv i)) ∧ IsCanonical128 (hv f pk m bits (rootCv i + 1)) ∧
    cellBits (hv f pk m bits (rootCv i + 1)) ++ cellBits (hv f pk m bits (rootCv i)) =
      Params.rootCv (tpsF f pk m bits) i
        (rootState f FP (tpsF f pk m bits) 0 i (Params.rootInit (tpsF f pk m bits))) := by
  by_cases h0 : i = 0
  · subst h0
    rw [show rootCv 0 = rootTop 0 from rfl, show rootTop 0 + 1 = rootTop 1 from rfl,
      hv_rootTop (by omega), hv_rootTop (by omega), cellBits_cellOfBits, cellBits_cellOfBits,
      ← topAt_tps (by omega), ← topAt_tps (by omega)]
    exact ⟨canon_cellOfBits _, canon_cellOfBits _, rfl⟩
  by_cases h8 : i < 8
  · obtain ⟨hc0, hc1⟩ := rootTop_cv (r := i) (by omega) h8
    rw [show rootCv i = cvCell i by unfold rootCv; rw [if_pos h8], ← hc1, ← hc0,
      hv_rootTop (by omega), hv_rootTop (by omega), cellBits_cellOfBits, cellBits_cellOfBits,
      ← topAt_tps (by omega), ← topAt_tps (by omega)]
    refine ⟨canon_cellOfBits _, canon_cellOfBits _, ?_⟩
    unfold Params.rootCv; rw [if_neg (by omega)]
  · obtain rfl : i = 8 := by omega
    rw [show rootCv 8 = stCell 7 from rfl, hv_st1 (by omega), hv_st (by omega), cellBits_hiC,
      cellBits_loC, hi_append_lo, RAF_eq (by omega)]
    refine ⟨canon_loC _, canon_hiC _, ?_⟩
    unfold Params.rootCv; rw [if_pos (Or.inr le_rfl)]

theorem honest_rho {i : ℕ} (hi : i < 9) :
    IsCanonical128 (hv f pk m bits (rhoCell i)) ∧ cellBits (hv f pk m bits (rhoCell i)) = FP.rootMd i := by
  by_cases h0 : i = 0
  · subst h0; rw [show rhoCell 0 = zCell from rfl, hv_z]
    exact ⟨canon_zero, by rw [cellBits_zero_E]; rfl⟩
  by_cases h8 : i < 8
  · rw [rhoCell_eq (by omega) h8, rootMd_eq (by omega) h8, hv_gp (by omega) (by omega)]
    exact ⟨canon_ofK _, cellBits_gpow h8⟩
  · obtain rfl : i = 8 := by omega
    rw [show rhoCell 8 = k0Cell from rfl, hv_k0]
    exact ⟨canon_ofK _, by rw [cellBits_k0V]; rfl⟩

theorem canon_rootTop {j : ℕ} (hj : j < 42) : IsCanonical128 (hv f pk m bits (rootTop j)) := by
  rw [hv_rootTop hj]; exact canon_cellOfBits _

include hroot in
/-- **The honest root.** -/
theorem honest_root : ∀ t < 10, HR f pk m bits (rootSlot + t) := by
  intro t ht
  unfold HR
  rw [cinstrAt_root ht]
  by_cases h9 : t < 9
  · obtain ⟨hcan, hmd⟩ := honest_rho h9
    obtain ⟨hc0, hc1, hcv⟩ := honest_rootCv (f := f) (pk := pk) (m := m) (bits := bits) h9
    have hq : ∀ {a b c d : ℕ}, cellBits (hv f pk m bits d) ++ cellBits (hv f pk m bits c) ++
        cellBits (hv f pk m bits b) ++ cellBits (hv f pk m bits a) =
          Params.rootBlock (tpsF f pk m bits) t
            (rootState f FP (tpsF f pk m bits) 0 t (Params.rootInit (tpsF f pk m bits))) →
        ans f (blake2sQuery ![hv f pk m bits a, hv f pk m bits b, hv f pk m bits c,
          hv f pk m bits d] (hv f pk m bits (rootCv t)) (hv f pk m bits (rootCv t + 1))
          (hv f pk m bits (rhoCell t))) = RAF f pk m bits t := fun hblk => by
      rw [blake2sQuery_eq, hcv, hmd, hblk, RAF_eq h9, rootState_last, Nat.zero_add]
      rfl
    unfold rootOp
    by_cases h0 : t = 0
    · subst h0
      rw [if_pos rfl]
      refine blake_rel (a := RAF f pk m bits 0) (canon_rootTop (by omega))
        (canon_rootTop (by omega)) (canon_rootTop (by omega)) (canon_rootTop (by omega)) hc0 hc1
        hcan (hq ?_) (hv_st h9) (hv_st1 h9)
      rw [cb_rootTop (by omega), cb_rootTop (by omega), cb_rootTop (by omega),
        cb_rootTop (by omega)]
      unfold Params.rootBlock; rw [if_pos rfl]
    by_cases h8 : t < 8
    · rw [if_neg h0, if_pos h8]
      refine blake_rel (a := RAF f pk m bits t) (by rw [hv_st (by omega)]; exact canon_loC _)
        (canon_rootTop (by omega)) (canon_rootTop (by omega)) (canon_rootTop (by omega)) hc0 hc1
        hcan (hq ?_) (hv_st h9) (hv_st1 h9)
      rw [cb_rootTop (by omega), cb_rootTop (by omega), cb_rootTop (by omega), hv_st (by omega),
        cellBits_loC, RAF_eq (by omega), show t - 1 + 1 = t by omega]
      unfold Params.rootBlock; rw [if_neg h0, if_pos h8]
    · obtain rfl : t = 8 := by omega
      rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      refine blake_rel (a := RAF f pk m bits 8) (canon_rootTop (by omega))
        (by rw [hv_z]; exact canon_zero) (by rw [hv_z]; exact canon_zero)
        (by rw [hv_z]; exact canon_zero) hc0 hc1 hcan (hq ?_) (hv_st h9) (hv_st1 h9)
      rw [hv_z, cellBits_zero_E, cb_rootTop (by omega)]
      unfold Params.rootBlock; rw [if_neg (by omega), if_neg (by omega)]
  · obtain rfl : t = 9 := by omega
    unfold rootOp
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    show hv f pk m bits pkCell = hv f pk m bits (stCell 8) + hv f pk m bits zCell
    rw [hv_z, add_zero, hv_st (by omega), show pkCell = 0 from rfl, hv_lt f pk m bits (by omega),
      inputWord_pk]
    have hlo : (RAF f pk m bits 8).extractLsb' 0 128 = pk := by
      rw [RAF_eq (by omega)]
      show rootValue f FP (topsOfV bits (y0F f pk m bits) (AF f pk m bits)) = pk
      rw [topsOfV_eq]
      exact hroot
    unfold loC
    exact (congrArg cellOfBits hlo).symm

include hlen hacc hroot in
/-- **The honest path.** Every slot on the path of the index digits holds on the loaded honest
image. -/
theorem honest_path : PathFacts (HR f pk m bits) (dg (y0F f pk m bits)) :=
  ⟨honest_pro hlen, honest_blk hlen hacc, honest_root hroot⟩

include hlen hacc hroot in
/-- **Honest run.** When the verifier accepts under the table, the honest image completes in
`253` instructions. -/
theorem honest_run :
    simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost program (LeanIsa.loadInput pk m bits (imageF f pk m bits)) 253
          Regs.initial) = pure (some 1270) := by
  obtain ⟨n, c, hw⟩ := walk_mk (dF_valid f pk m bits) (honest_path hlen hacc hroot)
    (fun g hg => hv_h1 hg) hv_k0
  have hpin : Pinned (hv f pk m bits) := ⟨hv_one, fun g hg => hv_frame hg⟩
  obtain ⟨hV, hP, -, rfl, rfl⟩ := walk_full (fun t h => CInstr.relNH_of_relB h) hw
  have hsum := layer_of_facts (fun t h => CInstr.relNH_of_relB h) hV hP
  have := sim_of_walk (le_refl 16) (by decide) f hpin hw
  rw [initial_eq]
  rw [totalSteps_eq hsum, totalCost_eq hsum] at this
  exact this

end Accepted

end Honest

end

end OptimalOTS.HLFlat
