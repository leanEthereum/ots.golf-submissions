import Submissions.UpperLeanIsa.MachineRun

/-!
# The forced path of the HL-TRI bytecode

Every walk from slot `0` is the forced walk of one digit vector `s = digitOf v` (read off the
landing hints of the 14 groups): the prologue `0 … 27`, then for each group `g` the dispatch at
its control slot, the landing at `entryOf g s = BASE g + SP g · rank`, the block's straight-line
ops (`NH g - 1` pre ops and pads, the `sig s g` chain steps and the next group's `MUL(H, g, H')`),
and finally the exit into the root segment `rootSlot … rootSlot + 9`, which falls through to the
sentinel.

A landing is forced to an entry by the frame lemma (`runCost_dispatch`), and the entry `I0`
returns to frame `1` at `H'_g = H_g · g`, the slot after the entry: no suffix of a block can be
entered.

* `walk_full`: a walk of any relation `R` implying the hash-free one yields the digit vector,
  the relation at every slot of its path (`PathFacts`), the landings (`Landing`), and the exact
  step count and cost `totalSteps s`, `totalCost s`.
* `walk_mk`: conversely, those facts assemble the walk (the honest direction).
* `cinstrAt_blk`, `cinstrAt_step`, `preOp_tie`, `preOp_zc`, `preOp_lay`: the ops at the slots of
  a path.
-/

namespace OptimalOTS.HLFlat

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

/-! ## Digit vectors and block shape -/

/-- The digit vector is in range. -/
def Valid (s : ℕ → ℕ) : Prop := ∀ k < 42, s k < W k

/-- The digits of group `g` are in range. -/
def GValid (s : ℕ → ℕ) (g : ℕ) : Prop := s (gch g 0) < 8 ∧ s (gch g 1) < 8 ∧ s (gch g 2) < Wc g

theorem gvalid_of_valid {s : ℕ → ℕ} (hV : Valid s) {g : ℕ} (hg : g < 14) : GValid s g := by
  have h0 := hV _ (gch_lt hg (show 0 < 3 by omega))
  have h1 := hV _ (gch_lt hg (show 1 < 3 by omega))
  have h2 := hV _ (gch_lt hg (show 2 < 3 by omega))
  rw [W_gch hg (by omega), if_pos (by omega)] at h0 h1
  rw [W_gch hg (by omega), if_neg (by omega)] at h2
  exact ⟨h0, h1, h2⟩

theorem valid_of_gvalid {s : ℕ → ℕ} (h : ∀ g < 14, GValid s g) : Valid s := by
  intro k hk
  obtain ⟨hg, hj⟩ := grp_lt hk
  have e := gch_grp hk
  have hW := W_gch hg hj
  rw [e] at hW
  obtain ⟨h0, h1, h2⟩ := h _ hg
  rw [hW]
  rcases (show gpos k = 0 ∨ gpos k = 1 ∨ gpos k = 2 by omega) with hp | hp | hp <;>
    rw [hp] at e
  · rw [if_pos (by omega)]; rwa [e] at h0
  · rw [if_pos (by omega)]; rwa [e] at h1
  · rw [if_neg (by omega)]; rwa [e] at h2

/-- The digit sum of group `g`. -/
def sig (s : ℕ → ℕ) (g : ℕ) : ℕ := s (gch g 0) + s (gch g 1) + s (gch g 2)

/-- The entry slot of group `g` on the digit vector `s`. -/
def entryOf (g : ℕ) (s : ℕ → ℕ) : ℕ :=
  BASE g + SP g * grank g (s (gch g 0)) (s (gch g 1)) (s (gch g 2))

/-- The block offset of the control op after the block: the next dispatch, or the exit. -/
def ctlOff (g σ : ℕ) : ℕ := NH g + σ + (if g < 13 then 1 else 0)

/-- The control slot after the block of group `g`. -/
def ctlAfter (g : ℕ) (s : ℕ → ℕ) : ℕ := entryOf g s + ctlOff g (sig s g)

/-- Walk steps of group `g`'s segment (dispatch, entry, block, and for group 13 the exit). -/
def segSteps (g σ : ℕ) : ℕ := NH g + 2 + σ

/-- Cycles of group `g`'s segment. -/
def segCost (g σ : ℕ) : ℕ := NH g + 2 + 10 * σ

section Shape

variable {s : ℕ → ℕ} {g : ℕ} (hG : GValid s g) (hg : g < 14)
include hG hg

theorem pre_fit' : 1 + preLen g (s (gch g 0)) (s (gch g 1)) (s (gch g 2)) ≤
    NH g := pre_fit hg hG.1 hG.2.1 hG.2.2

theorem ctlOff_lt : ctlOff g (sig s g) < SP g := blk_fit hg hG.1 hG.2.1 hG.2.2

theorem cinstrAt_blk {i : ℕ} (hi0 : 0 < i) (hi : i ≤ ctlOff g (sig s g)) :
    cinstrAt (entryOf g s + i) = blockOp g (s (gch g 0)) (s (gch g 1)) (s (gch g 2)) i :=
  cinstrAt_block hg hG.1 hG.2.1 hG.2.2 hi0 (lt_of_le_of_lt hi (ctlOff_lt hG hg))

theorem entryOf_isEntry : IsEntry g (entryOf g s) := by
  have hr := grank_lt hg hG.1 hG.2.1 hG.2.2
  have hsp : 0 < SP g := by unfold SP; split_ifs <;> omega
  refine ⟨hg, Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hr hsp) _, ?_⟩
  unfold entryOf; rw [Nat.add_sub_cancel_left, Nat.mul_mod_right]

theorem entryOf_lt : entryOf g s + SP g ≤ 255005 := by
  obtain ⟨h0, h1, h2⟩ := hG
  unfold entryOf grank
  rcases grp_consts hg with ⟨h, hw, -, hs, hb⟩ | ⟨rfl, hw, -, hs, hb⟩ | ⟨rfl, hw, -, hs, hb⟩ <;>
    rw [hw] at h2 <;> rw [hs, hb] <;> split_ifs <;> omega

/-- Ops `[1, NH g)`: the pre ops and the pads. -/
theorem seg_pre {i : ℕ} (hi0 : 0 < i) (hi : i < NH g) :
    (cinstrAt (entryOf g s + i)).straight = true ∧ (cinstrAt (entryOf g s + i)).cost = 1 := by
  have hb := pre_fit' hG hg
  rw [cinstrAt_blk hG hg hi0 (by unfold ctlOff; omega)]
  by_cases h : i < 1 + preLen g (s (gch g 0)) (s (gch g 1)) (s (gch g 2))
  · obtain ⟨q, rfl⟩ : ∃ q, i = 1 + q := ⟨i - 1, by omega⟩
    rw [blockOp_pre (by omega)]; exact preOp_straight _ _ _ _ _
  · rw [blockOp_nop (by omega) hi]; exact ⟨rfl, rfl⟩

/-- Op `NH g + t`: chain step `t`. -/
theorem seg_step {t : ℕ} (ht : t < sig s g) :
    cinstrAt (entryOf g s + (NH g + t)) =
      stepOp g (s (gch g 0)) (s (gch g 1)) (s (gch g 2)) t := by
  have hb := pre_fit' hG hg
  unfold sig at ht
  rw [cinstrAt_blk hG hg (by omega) (by unfold ctlOff sig; omega),
    blockOp_step (pre_fit' hG hg) ht]

/-- Ops `[NH g + σ, ctlOff)`: the next group's `MUL(H, g, H')` (none for group 13). -/
theorem seg_post {i : ℕ} (h1 : NH g + sig s g ≤ i)
    (h2 : i < ctlOff g (sig s g)) :
    (cinstrAt (entryOf g s + i)).straight = true ∧ (cinstrAt (entryOf g s + i)).cost = 1 := by
  have hb := pre_fit' hG hg
  unfold sig at h1
  unfold ctlOff sig at h2
  rw [cinstrAt_blk hG hg (by omega) (by unfold ctlOff sig; omega)]
  have h13 : g < 13 := by by_contra h13; rw [if_neg h13] at h2; omega
  rw [if_pos h13] at h2
  obtain rfl : i = NH g + (s (gch g 0) + s (gch g 1) + s (gch g 2)) := by omega
  rw [blockOp_tail (pre_fit' hG hg), if_pos h13]; exact ⟨rfl, rfl⟩

/-- The last op before the control op of group `g < 13`: the next group's `MUL(H, g, H')`. -/
theorem seg_hmul (h13 : g < 13) :
    cinstrAt (entryOf g s + (ctlOff g (sig s g) - 1)) = .mul (hCell (g + 1)) gCell (h1Cell (g + 1)) := by
  have hb := pre_fit' hG hg
  rw [cinstrAt_blk hG hg (by unfold ctlOff; rw [if_pos h13]; omega) (by omega)]
  unfold ctlOff sig; rw [if_pos h13, Nat.add_sub_cancel, blockOp_tail (pre_fit' hG hg), if_pos h13]

/-- The control op after the block: the next dispatch, or the exit. -/
theorem seg_ctl : cinstrAt (entryOf g s + ctlOff g (sig s g)) =
    if g < 13 then .dispatch (g + 1) else .exit := by
  rw [cinstrAt_blk hG hg (by unfold ctlOff; have := pre_fit' hG hg; omega) le_rfl]
  unfold ctlOff sig
  by_cases h13 : g < 13
  · rw [if_pos h13, if_pos h13, blockOp_disp (pre_fit' hG hg) h13]
  · rw [if_neg h13, if_neg h13, Nat.add_zero, blockOp_tail (pre_fit' hG hg), if_neg h13]

end Shape

/-! ## Pre ops -/

theorem preOp_tie {g a b c q : ℕ} (hq : q < tieLen g (a + b + c)) :
    preOp g a b c q = tieOp g a b c q := by
  unfold preOp; rw [if_pos hq]

theorem preOp_zc {g a b c q : ℕ} (hq : q < zeroCount a b c) :
    preOp g a b c (tieLen g (a + b + c) + q) = zcOp g a b q := by
  unfold preOp; rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem preOp_lay {g a b c q : ℕ} :
    preOp g a b c (tieLen g (a + b + c) + zeroCount a b c + q) = layOp g (a + b + c) q := by
  unfold preOp; rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega

theorem zeroIdx_a {a b c : ℕ} (ha : a = 0) : ∃ q < zeroCount a b c, zeroIdx a b q = 0 :=
  ⟨0, by unfold zeroCount; split_ifs <;> omega, by unfold zeroIdx; rw [if_pos rfl, if_pos ha]⟩

theorem zeroIdx_b {a b c : ℕ} (hb : b = 0) : ∃ q < zeroCount a b c, zeroIdx a b q = 1 := by
  by_cases ha : a = 0
  · exact ⟨1, by unfold zeroCount; split_ifs <;> omega, by unfold zeroIdx; simp [ha, hb]⟩
  · exact ⟨0, by unfold zeroCount; split_ifs <;> omega, by unfold zeroIdx; simp [ha, hb]⟩

theorem zeroIdx_c {a b c : ℕ} (hc : c = 0) : ∃ q < zeroCount a b c, zeroIdx a b q = 2 := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · exact ⟨2, by unfold zeroCount; split_ifs; omega, by unfold zeroIdx; simp⟩
  · exact ⟨1, by unfold zeroCount; split_ifs; omega, by unfold zeroIdx; simp [hb]⟩
  · exact ⟨1, by unfold zeroCount; split_ifs; omega, by unfold zeroIdx; simp [ha]⟩
  · exact ⟨0, by unfold zeroCount; split_ifs; omega, by unfold zeroIdx; simp [ha, hb]⟩

/-- Every zero digit of a block has its zero copy. -/
theorem zeroIdx_of_zero {g j : ℕ} {s : ℕ → ℕ} (hj : j < 3) (h0 : s (gch g j) = 0) :
    ∃ q < zeroCount (s (gch g 0)) (s (gch g 1)) (s (gch g 2)),
      zeroIdx (s (gch g 0)) (s (gch g 1)) q = j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · exact zeroIdx_a h0
  · exact zeroIdx_b h0
  · exact zeroIdx_c h0

theorem tieLen_le (g σ : ℕ) : tieLen g σ ≤ 2 := by unfold tieLen; split_ifs <;> omega

/-! ## Chain steps -/

/-- The block offset of step `t` of chain `k`. -/
def stepOff (s : ℕ → ℕ) (k t : ℕ) : ℕ :=
  NH (grp k) +
    (if gpos k = 0 then 0
     else if gpos k = 1 then s (gch (grp k) 0) else s (gch (grp k) 0) + s (gch (grp k) 1)) + t

theorem stepOp_at {g j t : ℕ} {s : ℕ → ℕ} (hj : j < 3) (ht : t < s (gch g j)) :
    stepOp g (s (gch g 0)) (s (gch g 1)) (s (gch g 2))
      ((if j = 0 then 0 else if j = 1 then s (gch g 0) else s (gch g 0) + s (gch g 1)) + t) =
      chainOp (gch g j) (s (gch g j)) t := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · rw [if_pos rfl, Nat.zero_add]; unfold stepOp; rw [if_pos ht]
  · rw [if_neg (by omega), if_pos rfl]; unfold stepOp
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · rw [if_neg (by omega), if_neg (by omega)]; unfold stepOp
    rw [if_neg (by omega), if_neg (by omega), show s (gch g 0) + s (gch g 1) + t - s (gch g 0) -
      s (gch g 1) = t by omega]

theorem stepOff_range {s : ℕ → ℕ} (hV : Valid s) {k t : ℕ} (hk : k < 42) (ht : t < s k) :
    0 < stepOff s k t ∧ stepOff s k t ≤ ctlOff (grp k) (sig s (grp k)) := by
  obtain ⟨hg, hj⟩ := grp_lt hk
  have hG := gvalid_of_valid hV hg
  have hb := pre_fit' hG hg
  have e := gch_grp hk
  unfold stepOff ctlOff sig
  rcases (show gpos k = 0 ∨ gpos k = 1 ∨ gpos k = 2 by omega) with hp | hp | hp <;>
    rw [hp] at e ⊢ <;> rw [← e] at ht <;> split_ifs <;> omega

/-- **Chain steps.** Step `t < s k` of chain `k` sits at `entryOf (grp k) s + stepOff s k t`. -/
theorem cinstrAt_step {s : ℕ → ℕ} (hV : Valid s) {k t : ℕ} (hk : k < 42) (ht : t < s k) :
    cinstrAt (entryOf (grp k) s + stepOff s k t) = chainOp k (s k) t := by
  obtain ⟨hg, hj⟩ := grp_lt hk
  have hG := gvalid_of_valid hV hg
  have e := gch_grp hk
  have hkt : t < s (gch (grp k) (gpos k)) := by rw [e]; exact ht
  have hoff : (if gpos k = 0 then 0 else if gpos k = 1 then s (gch (grp k) 0)
      else s (gch (grp k) 0) + s (gch (grp k) 1)) + t < sig s (grp k) := by
    unfold sig
    rcases (show gpos k = 0 ∨ gpos k = 1 ∨ gpos k = 2 by omega) with hp | hp | hp <;>
      rw [hp] at hkt ⊢ <;> simp <;> omega
  unfold stepOff
  rw [Nat.add_assoc, seg_step hG hg hoff, stepOp_at hj hkt, e]

/-! ## Prologue shape -/

/-- Cycles of prologue op `t`. -/
def proW (t : ℕ) : ℕ := if t = 26 then 10 else 1

/-- Cycles of root op `t`. -/
def rootW (t : ℕ) : ℕ := if t < 9 then 10 else 1

theorem prologue_setc {t : ℕ} (ht : t < 26) :
    (prologue t).straight = true ∧ (prologue t).cost = 1 := by
  unfold prologue
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem cinstrAt_28 : cinstrAt 28 = .dispatch 0 := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_27 : cinstrAt 27 = .mul (hCell 0) gCell (h1Cell 0) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_26 : cinstrAt 26 = .blake msgLo msgHi nonceCell pkCell zCell idxCell tidxCell := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set0 : cinstrAt 0 = .setc zCell 0 := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set1 : cinstrAt 1 = .setc oneCell oneV := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set2 : cinstrAt 2 = .setc lenCell (natV 5504) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set3 : cinstrAt 3 = .setc tidxCell (natV 10) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set4 : cinstrAt 4 = .setc gCell gV := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set5 : cinstrAt 5 = .setc k0Cell k0V := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_frame {k : ℕ} (hk : k < 14) : cinstrAt (6 + k) = .setc (fCell k) (frameV k) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega), show 6 + k - 6 = k by omega]

/-- The prologue constants `g ^ v`, `2 ≤ v ≤ 7`. -/
theorem cinstrAt_gp {v : ℕ} (h2 : 2 ≤ v) (h7 : v ≤ 7) :
    cinstrAt (18 + v) = .setc (gpCell v) (ofK (gpow v)) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 18 + v - 18 = v by omega]

theorem prologue_straight {t : ℕ} (ht : t < 28) :
    (cinstrAt t).straight = true ∧ (cinstrAt t).cost = proW t := by
  by_cases h26 : t = 26
  · subst h26; rw [cinstrAt_26]; exact ⟨rfl, rfl⟩
  by_cases h27 : t = 27
  · subst h27; rw [cinstrAt_27]; exact ⟨rfl, rfl⟩
  rw [show proW t = 1 from if_neg h26, cinstrAt_pro (by omega)]
  exact prologue_setc (by omega)

/-- The root segment is straight: nine `BLAKE2S` and the pk `XOR`. -/
theorem root_straight {t : ℕ} (ht : t < 10) :
    (cinstrAt (rootSlot + t)).straight = true ∧
      (cinstrAt (rootSlot + t)).cost = rootW t := by
  rw [cinstrAt_root ht]; unfold rootOp rootW
  split_ifs <;> first | exact ⟨rfl, rfl⟩ | (exfalso; omega)

/-! ## Walk lemmas -/

section Walks

variable {R : ℕ → Prop} {v : ℕ → E}

theorem Walk.inv {n t c : ℕ} (h : Walk R v n t c) (ht : t ≠ sentinel) :
    t < sentinel ∧ R t ∧ ∃ n' c', n = n' + (cinstrAt t).steps ∧ c = (cinstrAt t).cost + c' ∧
      Walk R v n' (nextSlot v t) c' := by
  cases h with
  | done => exact absurd rfl ht
  | step hs hR hw => exact ⟨hs, hR, _, _, rfl, rfl, hw⟩

theorem Walk.at_sentinel {n c : ℕ} (h : Walk R v n sentinel c) : n = 0 ∧ c = 0 := by
  cases h with
  | done => exact ⟨rfl, rfl⟩
  | step hs _ _ => exact absurd hs (lt_irrefl _)

/-- A straight segment of `a` ops of cost `w` each. -/
theorem walk_seg {a t w : ℕ} (hst : ∀ i < a, (cinstrAt (t + i)).straight = true ∧
    (cinstrAt (t + i)).cost = w) (hta : t + a ≤ sentinel) :
    ∀ {n c : ℕ}, Walk R v n t c → (∀ i < a, R (t + i)) ∧
      ∃ n' c', n = n' + a ∧ c = a * w + c' ∧ Walk R v n' (t + a) c' := by
  induction a generalizing t with
  | zero => intro n c h; exact ⟨fun i hi => absurd hi (by omega), n, c, rfl, by simp, h⟩
  | succ a ih =>
    intro n c h
    obtain ⟨hs1, hc1⟩ := hst 0 (by omega)
    rw [Nat.add_zero] at hs1 hc1
    obtain ⟨-, hR, n1, c1, rfl, rfl, hw⟩ := h.inv (by omega)
    rw [nextSlot_straight v hs1] at hw
    have hst' : ∀ i < a, (cinstrAt (t + 1 + i)).straight = true ∧
        (cinstrAt (t + 1 + i)).cost = w := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact hst (i + 1) (by omega)
    obtain ⟨hRs, n2, c2, rfl, rfl, hw2⟩ := ih hst' (by omega) hw
    refine ⟨fun i hi => ?_, n2, c2, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rwa [Nat.add_zero]
      · have := hRs (i - 1) (by omega)
        rwa [show t + 1 + (i - 1) = t + i by omega] at this
    · rw [straight_steps hs1]; ring
    · rw [hc1]; ring
    · rwa [show t + 1 + a = t + (a + 1) by omega] at hw2

theorem walk_seg_mk {a t w : ℕ} (hst : ∀ i < a, (cinstrAt (t + i)).straight = true ∧
    (cinstrAt (t + i)).cost = w) (hta : t + a ≤ sentinel) (hR : ∀ i < a, R (t + i))
    {n c : ℕ} (h : Walk R v n (t + a) c) : Walk R v (n + a) t (a * w + c) := by
  induction a generalizing t n c with
  | zero => simpa using h
  | succ a ih =>
    obtain ⟨hs1, hc1⟩ := hst 0 (by omega)
    rw [Nat.add_zero] at hs1 hc1
    have hst' : ∀ i < a, (cinstrAt (t + 1 + i)).straight = true ∧
        (cinstrAt (t + 1 + i)).cost = w := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact hst (i + 1) (by omega)
    have hR' : ∀ i < a, R (t + 1 + i) := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact hR (i + 1) (by omega)
    have hw := ih hst' (by omega) hR' (by rwa [show t + 1 + a = t + (a + 1) by omega])
    rw [← nextSlot_straight v hs1] at hw
    have := Walk.step (by omega) (by simpa using hR 0 (by omega)) hw
    rw [straight_steps hs1, hc1] at this
    convert this using 1 <;> ring

/-- A straight segment of non-uniform costs. -/
theorem walk_seg' {a t : ℕ} (w : ℕ → ℕ) (hst : ∀ i < a, (cinstrAt (t + i)).straight = true ∧
    (cinstrAt (t + i)).cost = w i) (hta : t + a ≤ sentinel) :
    ∀ {n c : ℕ}, Walk R v n t c → (∀ i < a, R (t + i)) ∧
      ∃ n' c', n = n' + a ∧ c = (∑ i ∈ Finset.range a, w i) + c' ∧ Walk R v n' (t + a) c' := by
  induction a generalizing t w with
  | zero => intro n c h; exact ⟨fun i hi => absurd hi (by omega), n, c, rfl, by simp, h⟩
  | succ a ih =>
    intro n c h
    obtain ⟨hs1, hc1⟩ := hst 0 (by omega)
    rw [Nat.add_zero] at hs1 hc1
    obtain ⟨-, hR0, n1, c1, rfl, rfl, hw⟩ := h.inv (by omega)
    rw [nextSlot_straight v hs1] at hw
    have hst' : ∀ i < a, (cinstrAt (t + 1 + i)).straight = true ∧
        (cinstrAt (t + 1 + i)).cost = w (i + 1) := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact hst (i + 1) (by omega)
    obtain ⟨hRs, n2, c2, rfl, rfl, hw2⟩ := ih (fun i => w (i + 1)) hst' (by omega) hw
    refine ⟨fun i hi => ?_, n2, c2, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rwa [Nat.add_zero]
      · have := hRs (i - 1) (by omega)
        rwa [show t + 1 + (i - 1) = t + i by omega] at this
    · rw [straight_steps hs1]; ring
    · rw [hc1, Finset.sum_range_succ']; ring
    · rwa [show t + 1 + a = t + (a + 1) by omega] at hw2

/-- A straight segment whose relations hold extends a walk backwards. -/
theorem walk_seg_ex {a t : ℕ} (hst : ∀ i < a, (cinstrAt (t + i)).straight = true)
    (hR : ∀ i < a, R (t + i)) (hta : t + a ≤ sentinel)
    (h : ∃ n c, Walk R v n (t + a) c) : ∃ n c, Walk R v n t c := by
  induction a generalizing t with
  | zero => simpa using h
  | succ a ih =>
    have h1 := ih (t := t + 1) (fun i hi => by
        rw [show t + 1 + i = t + (i + 1) by omega]; exact hst (i + 1) (by omega))
      (fun i hi => by rw [show t + 1 + i = t + (i + 1) by omega]; exact hR (i + 1) (by omega))
      (by omega) (by rwa [show t + 1 + a = t + (a + 1) by omega])
    obtain ⟨n, c, hw⟩ := h1
    have hs0 : (cinstrAt t).straight = true := by simpa using hst 0 (by omega)
    rw [← nextSlot_straight v hs0] at hw
    exact ⟨_, _, Walk.step (by omega) (by simpa using hR 0 (by omega)) hw⟩

end Walks

/-! ## The digit vector of an image -/

/-- The rank of group `g`'s landing. -/
def rankOf (v : ℕ → E) (g : ℕ) : ℕ := (slotOf ((v (hCell g)).limb 0) - BASE g) / SP g

/-- Digit `j` of rank `r` of group `g`. -/
def gdig (g r j : ℕ) : ℕ :=
  if j = 0 then r / (8 * Wc g) else if j = 1 then r / Wc g % 8 else r % Wc g

/-- The digit of chain `k` read off its group's landing hint. -/
def digitOf (v : ℕ → E) (k : ℕ) : ℕ := gdig (grp k) (rankOf v (grp k)) (gpos k)

theorem digitOf_gch {v : ℕ → E} {g j : ℕ} (hg : g < 14) (hj : j < 3) :
    digitOf v (gch g j) = gdig g (rankOf v g) j := by
  unfold digitOf; obtain ⟨h1, h2⟩ := grp_gch hg hj; rw [h1, h2]

theorem rank_gdig {g r : ℕ} (hg : g < 14) (hr : r < NT g) :
    gdig g r 0 < 8 ∧ gdig g r 1 < 8 ∧ gdig g r 2 < Wc g ∧
      grank g (gdig g r 0) (gdig g r 1) (gdig g r 2) = r := by
  unfold gdig grank
  simp only [show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
    show (2 : ℕ) ≠ 1 by omega, if_false, if_true]
  unfold NT at hr
  rcases grp_consts hg with ⟨h, hw, -⟩ | ⟨rfl, hw, -⟩ | ⟨rfl, hw, -⟩ <;> rw [hw] at hr ⊢
  · rw [if_pos h]; omega
  · rw [if_neg (by omega)]; omega
  · rw [if_neg (by omega)]; omega

/-- The landing hints of the digit vector `s`. -/
def Landing (v : ℕ → E) (s : ℕ → ℕ) : Prop := ∀ g < 14, v (hCell g) = ofK (gpow (entryOf g s))

/-- A landing at an entry of group `g` determines its digits. -/
theorem digitOf_eq {v : ℕ → E} {g e : ℕ} (he : IsEntry g e) (hx : (v (hCell g)).limb 0 = gpow e) :
    e = entryOf g (digitOf v) ∧ GValid (digitOf v) g := by
  have hlt := isEntry_lt he
  obtain ⟨he', hr⟩ := isEntry_eq he
  have hrank : rankOf v g = (e - BASE g) / SP g := by
    unfold rankOf; rw [hx, slotOf_gpow (by omega)]
  obtain ⟨h0, h1, h2, hgr⟩ := rank_gdig he.1 hr
  unfold GValid entryOf
  rw [digitOf_gch he.1 (show 0 < 3 by omega), digitOf_gch he.1 (show 1 < 3 by omega),
    digitOf_gch he.1 (show 2 < 3 by omega), hrank]
  exact ⟨by rw [hgr]; exact he', h0, h1, h2⟩

/-- The relation holds at every slot of the path of `s`. -/
structure PathFacts (R : ℕ → Prop) (s : ℕ → ℕ) : Prop where
  pro : ∀ t < 29, R t
  blk : ∀ g < 14, ∀ i, 0 < i → i ≤ ctlOff g (sig s g) → R (entryOf g s + i)
  root : ∀ t < 10, R (rootSlot + t)

/-- The dispatch slot of group `j` on the path of `s`. -/
def ctl (s : ℕ → ℕ) (j : ℕ) : ℕ := if j = 0 then 28 else ctlAfter (j - 1) s

theorem ctl_succ (s : ℕ → ℕ) (j : ℕ) : ctl s (j + 1) = ctlAfter j s := by
  unfold ctl; rw [if_neg (by omega), Nat.add_sub_cancel]

theorem cinstrAt_ctl {s : ℕ → ℕ} {j : ℕ} (hj : j < 14) (hs : ∀ g < j, GValid s g) :
    cinstrAt (ctl s j) = .dispatch j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact cinstrAt_28
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [ctl_succ, ctlAfter, seg_ctl (hs k (by omega)) (by omega), if_pos (by omega)]

theorem ctl_lt {s : ℕ → ℕ} {j : ℕ} (hj : j < 14) (hs : ∀ g < j, GValid s g) : ctl s j < sentinel := by
  unfold ctl ctlAfter
  split_ifs
  · unfold sentinel; omega
  · have := entryOf_lt (hs (j - 1) (by omega)) (by omega)
    have := ctlOff_lt (hs (j - 1) (by omega)) (by omega)
    unfold sentinel; omega

section Groups

variable {R : ℕ → Prop} {v : ℕ → E} (hR : ∀ t, R t → (cinstrAt t).RelNH v)
include hR

/-- The dispatch step: a landing on an entry of group `g`, and the walk resumes after it. -/
theorem walk_disp {d g n c : ℕ} (hci : cinstrAt d = .dispatch g) (hg : v gCell = gV)
    (hmul : v (h1Cell g) = v (hCell g) * v gCell) (h : Walk R v n d c) :
    R d ∧ GValid (digitOf v) g ∧ v (hCell g) = ofK (gpow (entryOf g (digitOf v))) ∧
      ∃ n' c', n = n' + 2 ∧ c = 2 + c' ∧ Walk R v n' (entryOf g (digitOf v) + 1) c' := by
  have hdne : d ≠ sentinel := fun e => by rw [e, cinstrAt_sentinel] at hci; cases hci
  obtain ⟨-, hRd, n', c', rfl, rfl, hw⟩ := h.inv hdne
  have hrel := hR d hRd
  rw [hci] at hrel
  obtain ⟨hH, -, e, he, hx⟩ := hrel
  obtain ⟨he', hG⟩ := digitOf_eq he hx
  have hHv : v (hCell g) = ofK (gpow (entryOf g (digitOf v))) := by
    rw [ofK_limb hH, hx, ← he']
  have hlt := isEntry_lt he
  have hnext : nextSlot v d = entryOf g (digitOf v) + 1 := by
    unfold nextSlot; rw [hci]
    show slotOf _ = _
    rw [hmul, hHv, hg, gV, ← ofK_mul, limb_ofK_zero, mul_comm, g_mul_gpow,
      slotOf_gpow (by omega)]
  rw [hnext] at hw
  exact ⟨hRd, hG, hHv, n', c', by rw [hci]; rfl, by rw [hci]; rfl, hw⟩

/-- One group segment, from its dispatch to the next control slot (or the root). -/
theorem walk_group {j n c : ℕ} (hj : j < 14) {d : ℕ} (hci : cinstrAt d = .dispatch j)
    (hg : v gCell = gV) (hk0 : v k0Cell = k0V) (hmul : v (h1Cell j) = v (hCell j) * v gCell)
    (h : Walk R v n d c) :
    R d ∧ GValid (digitOf v) j ∧ v (hCell j) = ofK (gpow (entryOf j (digitOf v))) ∧
      (∀ i, 0 < i → i ≤ ctlOff j (sig (digitOf v) j) → R (entryOf j (digitOf v) + i)) ∧
      ∃ n' c', n = n' + segSteps j (sig (digitOf v) j) ∧ c = segCost j (sig (digitOf v) j) + c' ∧
        Walk R v n' (if j < 13 then ctlAfter j (digitOf v) else rootSlot) c' := by
  obtain ⟨hRd, hG, hHv, n1, c1, rfl, rfl, hw1⟩ := walk_disp hR hci hg hmul h
  have hb := pre_fit' hG hj
  have hlt := entryOf_lt hG hj
  have hco := ctlOff_lt hG hj
  generalize hsb : NH j = sb at hb
  generalize hσ : sig (digitOf v) j = σ at hco ⊢
  generalize hco' : ctlOff j σ = co at hco ⊢
  generalize he : entryOf j (digitOf v) = e at hlt hw1 hHv ⊢
  have hcoσ : co = NH j + σ + (if j < 13 then 1 else 0) := by rw [← hco']; rfl
  have hcoge : sb + σ ≤ co := by rw [hcoσ]; split_ifs <;> omega
  have hA : ∀ i < sb - 1, (cinstrAt (e + 1 + i)).straight = true ∧
      (cinstrAt (e + 1 + i)).cost = 1 := fun i hi => by
    rw [← he, Nat.add_assoc]; exact seg_pre hG hj (by omega) (by rw [hsb]; omega)
  have hB : ∀ t < σ, (cinstrAt (e + sb + t)).straight = true ∧
      (cinstrAt (e + sb + t)).cost = 10 := fun t ht => by
    rw [← he, ← hsb, Nat.add_assoc, seg_step hG hj (by rw [hσ]; exact ht)]
    exact stepOp_straight _ _ _ _ _
  have hC : ∀ i < co - sb - σ, (cinstrAt (e + sb + σ + i)).straight = true ∧
      (cinstrAt (e + sb + σ + i)).cost = 1 := fun i hi => by
    rw [← he, show entryOf j (digitOf v) + sb + σ + i = entryOf j (digitOf v) + (sb + σ + i) by
      ring]
    exact seg_post hG hj (by rw [hsb, hσ]; omega) (by rw [hσ, hco']; omega)
  obtain ⟨hR1, n2, c2, rfl, rfl, hw2⟩ := walk_seg hA (by unfold sentinel; omega) hw1
  rw [show e + 1 + (sb - 1) = e + sb by omega] at hw2
  obtain ⟨hR2, n3, c3, rfl, rfl, hw3⟩ := walk_seg hB (by unfold sentinel; omega) hw2
  obtain ⟨hR3, n4, c4, rfl, rfl, hw4⟩ := walk_seg hC (by unfold sentinel; omega) hw3
  rw [show e + sb + σ + (co - sb - σ) = e + co by omega] at hw4
  have hctl : cinstrAt (e + co) = if j < 13 then .dispatch (j + 1) else .exit := by
    rw [← he, ← hco', ← hσ]; exact seg_ctl hG hj
  have hfacts : ∀ i, 0 < i → i < co → R (e + i) := fun i hi0 hi2 => by
    by_cases a : i < sb
    · have := hR1 (i - 1) (by omega); rwa [show e + 1 + (i - 1) = e + i by omega] at this
    by_cases b : i < sb + σ
    · have := hR2 (i - sb) (by omega); rwa [show e + sb + (i - sb) = e + i by omega] at this
    · have := hR3 (i - sb - σ) (by omega)
      rwa [show e + sb + σ + (i - sb - σ) = e + i by omega] at this
  by_cases h13 : j < 13
  · rw [if_pos h13] at hctl hcoσ ⊢
    refine ⟨hRd, hG, hHv, fun i hi0 hi1 => ?_, n4, c4, ?_, ?_, ?_⟩
    · by_cases hi : i < co
      · exact hfacts i hi0 hi
      · obtain rfl : i = co := by omega
        exact (hw4.inv (by unfold sentinel; omega)).2.1
    · unfold segSteps; omega
    · unfold segCost; omega
    · unfold ctlAfter; rw [he, hσ, hco']; exact hw4
  · rw [if_neg h13] at hctl hcoσ ⊢
    have hne : e + co ≠ sentinel := by unfold sentinel; omega
    obtain ⟨-, hRx, n5, c5, rfl, rfl, hw5⟩ := hw4.inv hne
    have hnext : nextSlot v (e + co) = rootSlot := by
      unfold nextSlot; rw [hctl]
      show slotOf _ = _
      rw [hk0, k0V, limb_ofK_zero, slotOf_gpow (by unfold rootSlot; omega)]
    rw [hnext] at hw5
    refine ⟨hRd, hG, hHv, fun i hi0 hi1 => ?_, n5, c5, ?_, ?_, hw5⟩
    · by_cases hi : i < co
      · exact hfacts i hi0 hi
      · obtain rfl : i = co := by omega
        exact hRx
    · rw [hctl]; unfold segSteps; simp only [CInstr.steps]; omega
    · rw [hctl]; unfold segCost; simp only [CInstr.cost]; omega

end Groups

/-! ## The full path -/

/-- Steps of the whole path. -/
def totalSteps (s : ℕ → ℕ) : ℕ := 28 + ∑ g ∈ Finset.range 14, segSteps g (sig s g) + 10

/-- Cycles of the whole path. -/
def totalCost (s : ℕ → ℕ) : ℕ := 37 + ∑ g ∈ Finset.range 14, segCost g (sig s g) + 91

theorem prologue_cost : ∑ i ∈ Finset.range 28, proW i = 37 := by decide

theorem root_cost : ∑ i ∈ Finset.range 10, rootW i = 91 := by decide

section Full

variable {R : ℕ → Prop} {v : ℕ → E} (hR : ∀ t, R t → (cinstrAt t).RelNH v)
include hR

/-- **The forced path.** Every walk from slot `0` is the path of the digit vector `digitOf v`,
with its exact step count and cost. -/
theorem walk_full {n c : ℕ} (h : Walk R v n 0 c) :
    Valid (digitOf v) ∧ PathFacts R (digitOf v) ∧ Landing v (digitOf v) ∧
      n = totalSteps (digitOf v) ∧ c = totalCost (digitOf v) := by
  -- the prologue
  obtain ⟨hRp, n0, c0, rfl, rfl, hw0⟩ := walk_seg' proW
    (fun i hi => by simpa using prologue_straight (t := i) hi) (by unfold sentinel; omega) h
  rw [Nat.zero_add] at hw0
  simp only [Nat.zero_add] at hRp
  have hg : v gCell = gV := by have := hR 4 (hRp 4 (by omega)); rwa [cinstrAt_set4] at this
  have hk0 : v k0Cell = k0V := by have := hR 5 (hRp 5 (by omega)); rwa [cinstrAt_set5] at this
  have hmul0 : v (h1Cell 0) = v (hCell 0) * v gCell := by
    have := hR 27 (hRp 27 (by omega)); rwa [cinstrAt_27] at this
  -- the groups, by induction
  have key : ∀ j ≤ 14, (∀ k < j, GValid (digitOf v) k ∧
      v (hCell k) = ofK (gpow (entryOf k (digitOf v))) ∧ R (ctl (digitOf v) k) ∧
      ∀ i, 0 < i → i ≤ ctlOff k (sig (digitOf v) k) → R (entryOf k (digitOf v) + i)) ∧
      ∃ n' c', n0 = n' + ∑ k ∈ Finset.range j, segSteps k (sig (digitOf v) k) ∧
        c0 = (∑ k ∈ Finset.range j, segCost k (sig (digitOf v) k)) + c' ∧
        Walk R v n' (if j < 14 then ctl (digitOf v) j else rootSlot) c' ∧
        (j < 14 → v (h1Cell j) = v (hCell j) * v gCell) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun k hk => absurd hk (by omega), n0, c0, by simp, by simp, ?_, fun _ => hmul0⟩
      rw [if_pos (by omega)]; unfold ctl; rwa [if_pos rfl]
    | succ j ih =>
      intro hj
      obtain ⟨hprev, n', c', hn, hc, hw, hm⟩ := ih (by omega)
      rw [if_pos (by omega)] at hw
      have hci := cinstrAt_ctl (s := digitOf v) (j := j) (by omega) (fun k hk => (hprev k hk).1)
      obtain ⟨hRd, hG, hHv, hblk, n'', c'', rfl, rfl, hw'⟩ :=
        walk_group hR (by omega) hci hg hk0 (hm (by omega)) hw
      refine ⟨fun k hk => ?_, n'', c'', ?_, ?_, ?_, fun hj' => ?_⟩
      · by_cases hkj : k < j
        · exact hprev k hkj
        · obtain rfl : k = j := by omega
          exact ⟨hG, hHv, hRd, hblk⟩
      · rw [hn, Finset.sum_range_succ]; ring
      · rw [hc, Finset.sum_range_succ]; ring
      · by_cases h13 : j < 13
        · rw [if_pos h13] at hw'; rw [if_pos (by omega), ctl_succ]; exact hw'
        · rw [if_neg h13] at hw'; rw [if_neg (by omega)]; exact hw'
      · have hb := pre_fit' hG (by omega)
        have hlast := hblk (ctlOff j (sig (digitOf v) j) - 1)
          (by unfold ctlOff; rw [if_pos (by omega)]; omega) (by omega)
        have := hR _ hlast
        rwa [seg_hmul hG (by omega) (by omega)] at this
  obtain ⟨hall, n1, c1, hn1, hc1, hw1, -⟩ := key 14 (le_refl 14)
  rw [if_neg (by omega)] at hw1
  -- the root
  obtain ⟨hRr, n2, c2, hn2, hc2, hw2⟩ := walk_seg' rootW
    (fun i hi => root_straight hi) (by unfold rootSlot sentinel; omega) hw1
  rw [show rootSlot + 10 = sentinel from rfl] at hw2
  obtain ⟨h0n, h0c⟩ := hw2.at_sentinel
  refine ⟨valid_of_gvalid fun k hk => (hall k hk).1,
    ⟨fun t ht => ?_, fun k hk => (hall k hk).2.2.2, hRr⟩, fun k hk => (hall k hk).2.1, ?_, ?_⟩
  · by_cases h28 : t < 28
    · exact hRp t h28
    · obtain rfl : t = 28 := by omega
      have := (hall 0 (by omega)).2.2.1
      unfold ctl at this; rwa [if_pos rfl] at this
  · unfold totalSteps; omega
  · rw [root_cost] at hc2; rw [prologue_cost]; unfold totalCost; omega

end Full

/-! ## Assembling a walk (the honest direction) -/

section Mk

variable {R : ℕ → Prop} {v : ℕ → E}

/-- One group segment, assembled backwards from its successor. -/
theorem group_mk {s : ℕ → ℕ} {k : ℕ} (hk : k < 14) (hs : ∀ j ≤ k, GValid s j)
    (hblk : ∀ i, 0 < i → i ≤ ctlOff k (sig s k) → R (entryOf k s + i))
    (hRd : R (ctl s k)) (hH1 : v (h1Cell k) = ofK (gpow (entryOf k s + 1)))
    (hk0 : v k0Cell = k0V)
    (h : ∃ n c, Walk R v n (if k < 13 then ctlAfter k s else rootSlot) c) :
    ∃ n c, Walk R v n (ctl s k) c := by
  have hG := hs k le_rfl
  have hb := pre_fit' hG hk
  have hlt := entryOf_lt hG hk
  have hco := ctlOff_lt hG hk
  set e := entryOf k s with he
  set co := ctlOff k (sig s k) with hco'
  set sb := NH k with hsb
  set σ := sig s k with hσ
  have hcoσ : co = NH k + σ + (if k < 13 then 1 else 0) := rfl
  have hcoge : sb + σ ≤ co := by rw [hcoσ]; split_ifs <;> omega
  -- the control slot after the block
  have hctl : ∃ n c, Walk R v n (e + co) c := by
    by_cases h13 : k < 13
    · rw [if_pos h13] at h; exact h
    · rw [if_neg h13] at h
      obtain ⟨n, c, hw⟩ := h
      have hci : cinstrAt (e + co) = .exit := by
        rw [seg_ctl hG hk, if_neg h13]
      have hnext : nextSlot v (e + co) = rootSlot := by
        unfold nextSlot; rw [hci]
        show slotOf _ = _
        rw [hk0, k0V, limb_ofK_zero, slotOf_gpow (by unfold rootSlot; omega)]
      rw [← hnext] at hw
      exact ⟨_, _, Walk.step (by unfold sentinel; omega) (hblk co (by omega) le_rfl) hw⟩
  -- the tail, chain and pre segments
  have h3 := walk_seg_ex (t := e + sb + σ) (a := co - sb - σ)
    (fun i hi => by
      rw [show e + sb + σ + i = e + (sb + σ + i) by ring]
      exact (seg_post hG hk (by omega) (by omega)).1)
    (fun i hi => by
      have := hblk (sb + σ + i) (by omega) (by omega)
      rwa [show e + (sb + σ + i) = e + sb + σ + i by ring] at this)
    (by unfold sentinel; omega) (by rwa [show e + sb + σ + (co - sb - σ) = e + co by omega])
  have h2 := walk_seg_ex (t := e + sb) (a := σ)
    (fun i hi => by
      rw [Nat.add_assoc, seg_step hG hk hi]; exact (stepOp_straight _ _ _ _ _).1)
    (fun i hi => by
      have := hblk (sb + i) (by omega) (by omega)
      rwa [← Nat.add_assoc] at this)
    (by unfold sentinel; omega) h3
  have h1 := walk_seg_ex (t := e + 1) (a := sb - 1)
    (fun i hi => by rw [Nat.add_assoc]; exact (seg_pre hG hk (by omega) (by omega)).1)
    (fun i hi => by
      have := hblk (1 + i) (by omega) (by omega)
      rwa [← Nat.add_assoc] at this)
    (by unfold sentinel; omega) (by rwa [show e + 1 + (sb - 1) = e + sb by omega])
  -- the dispatch
  obtain ⟨n, c, hw⟩ := h1
  have hci := cinstrAt_ctl (s := s) (j := k) hk (fun j hj => hs j (by omega))
  have hnext : nextSlot v (ctl s k) = e + 1 := by
    unfold nextSlot; rw [hci]
    show slotOf _ = _
    rw [hH1, limb_ofK_zero, slotOf_gpow (by omega)]
  rw [← hnext] at hw
  exact ⟨_, _, Walk.step (ctl_lt hk fun j hj => hs j (by omega)) hRd hw⟩

/-- **Assembling the forced path.** The relations along the path of `s`, with its return
hints and `K0`, give a walk from slot `0`. -/
theorem walk_mk {s : ℕ → ℕ} (hV : Valid s) (hP : PathFacts R s)
    (hH1 : ∀ g < 14, v (h1Cell g) = ofK (gpow (entryOf g s + 1)))
    (hk0 : v k0Cell = k0V) : ∃ n c, Walk R v n 0 c := by
  -- the root
  have hroot : ∃ n c, Walk R v n rootSlot c :=
    walk_seg_ex (a := 10) (fun i hi => (root_straight hi).1) hP.root
      (by unfold rootSlot sentinel; omega) ⟨0, 0, Walk.done⟩
  -- the groups, backwards
  have key : ∀ d ≤ 14, ∃ n c, Walk R v n (if 14 - d < 14 then ctl s (14 - d) else rootSlot) c := by
    intro d
    induction d with
    | zero => intro _; simpa using hroot
    | succ d ih =>
      intro hd
      obtain ⟨n, c, hw⟩ := ih (by omega)
      rw [if_pos (by omega)]
      have hk : 14 - (d + 1) < 14 := by omega
      refine group_mk hk (fun j hj => gvalid_of_valid hV (by omega)) (hP.blk _ hk) ?_
        (hH1 _ hk) hk0 ?_
      · rcases Nat.eq_zero_or_pos (14 - (d + 1)) with h0 | h0
        · rw [h0]; unfold ctl; rw [if_pos rfl]; exact hP.pro 28 (by omega)
        · obtain ⟨j, hj⟩ : ∃ j, 14 - (d + 1) = j + 1 := ⟨14 - (d + 1) - 1, by omega⟩
          rw [hj, ctl_succ]
          exact hP.blk j (by omega) _ (by unfold ctlOff NH; split_ifs <;> omega) le_rfl
      · by_cases h13 : 14 - (d + 1) < 13
        · rw [if_pos h13]
          have hd' : 14 - d = 14 - (d + 1) + 1 := by omega
          rw [hd', if_pos (by omega), ctl_succ] at hw
          exact ⟨n, c, hw⟩
        · rw [if_neg h13]
          rw [show 14 - d = 14 by omega, if_neg (by omega)] at hw
          exact ⟨n, c, hw⟩
  obtain ⟨n, c, hw⟩ := key 14 le_rfl
  rw [if_pos (by omega), show 14 - 14 = 0 from rfl] at hw
  unfold ctl at hw
  rw [if_pos rfl] at hw
  -- the prologue
  exact walk_seg_ex (t := 0) (a := 28) (fun i hi => (prologue_straight (t := 0 + i) (by omega)).1)
    (fun i hi => hP.pro _ (by omega)) (by unfold sentinel; omega) ⟨n, c, hw⟩

end Mk

/-! ## The pinned constants of a completing run -/

section Prefix

variable {κ : ℕ} {L : MemImage κ}

/-- The relations of a straight prefix of a completing run. -/
theorem rel_prefix (Sm : Sem) (B : BlakeRel)
    (hst : ∀ s pc x, (cinstrAt s).straight = true →
      x ∈ Sm.S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt s).toInstr) →
        x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt s).RelB B (Lx L))) :
    ∀ a t n c, (∀ i < a, (cinstrAt (t + i)).straight = true) → t + a < sentinel →
      some c ∈ Sm.S (LeanIsa.runCost program L n ⟨gpow t, 1⟩) →
        ∀ i < a, (cinstrAt (t + i)).RelB B (Lx L) := by
  intro a
  induction a with
  | zero => intro t n c _ _ _ i hi; omega
  | succ a ih =>
    intro t n c hstr hta h i hi
    cases n with
    | zero => rw [runCost_zero_slot L (by omega)] at h; exact absurd h Sm.some_not_pure_none
    | succ m =>
      have hs0 : (cinstrAt t).straight = true := by simpa using hstr 0 (by omega)
      rw [runCost_slot L m (by omega), Sm.bind_iff] at h
      obtain ⟨x, hx, hc⟩ := h
      rcases hst t _ x hs0 hx with rfl | ⟨rfl, hrel⟩
      · exact absurd hc Sm.some_not_pure_none
      · rw [Option.elim_some, g_mul_gpow] at hc
        obtain ⟨c', -, hc'⟩ := Sm.some_map_add hc
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · simpa using hrel
        · have := ih (t + 1) m c' (fun j hj => by
            rw [show t + 1 + j = t + (j + 1) by omega]; exact hstr (j + 1) (by omega))
            (by omega) hc' (i - 1) (by omega)
          rwa [show t + 1 + (i - 1) = t + i by omega] at this

/-- A completing run from slot `0` has the constants `ONE` and `F_g` pinned. -/
theorem pinned_of_sem (Sm : Sem) (B : BlakeRel)
    (hst : ∀ s pc x, (cinstrAt s).straight = true →
      x ∈ Sm.S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt s).toInstr) →
        x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt s).RelB B (Lx L)))
    {n c : ℕ} (h : some c ∈ Sm.S (LeanIsa.runCost program L n ⟨gpow 0, 1⟩)) : Pinned (Lx L) := by
  have hp := rel_prefix Sm B hst 28 0 n c
    (fun i hi => (prologue_straight (t := 0 + i) (by omega)).1) (by unfold sentinel; omega) h
  refine ⟨?_, fun k hk => ?_⟩
  · have := hp 1 (by omega); rwa [Nat.zero_add, cinstrAt_set1] at this
  · have := hp (6 + k) (by omega); rwa [Nat.zero_add, cinstrAt_frame hk] at this

end Prefix

end

end OptimalOTS.HLFlat
