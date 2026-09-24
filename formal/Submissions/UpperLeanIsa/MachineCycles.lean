import Submissions.UpperLeanIsa.MachinePath
import OptimalOTS.LeanIsa

/-!
# The hash-free facts and the cycle bound

`CyclesAtMost 1439` for the HL-TRI bytecode, over every admissible memory size, every committed
image and every step count, in the cache-free `support` semantics.

* `layer_of_facts`: the layer products along the path force `L_13 = g ^ (rootSlot - 106 + Σ σ)`,
  and `L_13 = K0 = g ^ rootSlot`; `gpow` is injective below the group order, so `Σ_k s k = 106`.
* `tie_of_facts`: the tie accumulators hold the sums of the group words; `acc_13` is the index
  cell (`idx_of_facts`).
* `zero_copy_of_facts`, `copy0_of_facts`: the copies the root reads for zero digits and chain 0.
* `totalCost_eq`, `totalSteps_eq`: every path of a layer vector costs exactly `1319` cycles in
  `266` instructions: each block's non-hash cost is independent of its digits, and the hashes
  number `1 + 106 + 10`.
* `cycles`: a completing run is a walk (`walk_of_supp`), the walk is a path (`walk_full`), and
  the two facts give its cost. No hash binding is used.
-/

namespace OptimalOTS.HLFlat

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

/-- The tie word of group `g` on the digit vector `s`. -/
def gwordS (s : ℕ → ℕ) (g : ℕ) : ℕ := gword g (s (gch g 0)) (s (gch g 1)) (s (gch g 2))

/-- The group sums are the chain sum. -/
theorem sum_sig (s : ℕ → ℕ) : ∑ g ∈ Finset.range 14, sig s g = ∑ k ∈ Finset.range 42, s k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sig, gch]
  norm_num
  ring

/-! ## The hash-free facts -/

section Facts

variable {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ t, R t → (cinstrAt t).RelNH v)
  {s : ℕ → ℕ} (hV : Valid s) (hP : PathFacts R s)
include hR hP

theorem pro_relNH {t : ℕ} {ci : CInstr} (ht : t < 36) (hc : cinstrAt t = ci) : ci.RelNH v := by
  have := hR t (hP.pro t ht); rwa [hc] at this

theorem fact_z : v zCell = 0 := pro_relNH hR hP (by omega) cinstrAt_set0
theorem fact_one : v oneCell = oneV := pro_relNH hR hP (by omega) cinstrAt_set1
theorem fact_g : v gCell = gV := pro_relNH hR hP (by omega) cinstrAt_set4
theorem fact_k0 : v k0Cell = k0V := pro_relNH hR hP (by omega) cinstrAt_set5

/-- The prologue constants `g ^ w`, `1 ≤ w ≤ 7`. -/
theorem fact_gp {w : ℕ} (h1 : 1 ≤ w) (h7 : w ≤ 7) : v (gpCell w) = ofK (gpow w) := by
  by_cases hw : w = 1
  · subst hw
    rw [show gpCell 1 = gCell from rfl, fact_g hR hP, gV, gpow, pow_one]
  · have := pro_relNH hR hP (t := 25 + w) (by omega) (cinstrAt_gp (by omega) h7)
    exact this

include hV

/-- Op `i` of group `g`'s block on the path. -/
theorem blk_relNH {g i : ℕ} (hg : g < 14) (hi0 : 0 < i) (hi : i ≤ ctlOff g (sig s g)) :
    (blockOp g (s (gch g 0)) (s (gch g 1)) (s (gch g 2)) i).RelNH v := by
  have := hR _ (hP.blk g hg i hi0 hi)
  rwa [cinstrAt_blk (gvalid_of_valid hV hg) hg hi0 hi] at this

/-- Pre op `q` of group `g`'s block on the path. -/
theorem pre_relNH {g q : ℕ} (hg : g < 14)
    (hq : q < preLen g (s (gch g 0)) (s (gch g 1)) (s (gch g 2))) :
    (preOp g (s (gch g 0)) (s (gch g 1)) (s (gch g 2)) q).RelNH v := by
  have hG := gvalid_of_valid hV hg
  have hb := stepBase_bounds hG hg
  have hf := pre_fit' hG hg
  have := blk_relNH hR hV hP hg (i := 1 + q) (by omega) (by unfold ctlOff; omega)
  rwa [blockOp_pre hq] at this

/-- The layer factor of group `g ≥ 1`. -/
theorem lay_step {g : ℕ} (hg : g < 14) (hg0 : g ≠ 0) :
    v (layCell g) = v (layCell (g - 1)) * ofK (gpow (sig s g)) := by
  have hG := gvalid_of_valid hV hg
  have hlay : ∀ q < layLen g (sig s g), (layOp g (sig s g) q).RelNH v := fun q hq => by
    have := pre_relNH hR hV hP hg (q := tieLen g (sig s g) +
      zeroCount (s (gch g 0)) (s (gch g 1)) (s (gch g 2)) + q) (by unfold preLen sig at *; omega)
    unfold sig at this ⊢
    rwa [preOp_lay] at this
  by_cases h0 : sig s g = 0
  · have h := hlay 0 (by unfold layLen; split_ifs <;> omega)
    unfold layOp at h
    rw [if_neg hg0, if_pos h0] at h
    have h' : v (layCell g) = v (layCell (g - 1)) * v oneCell := h
    rw [h', fact_one hR hP, oneV, h0, gpow, pow_zero]
  by_cases h7 : sig s g ≤ 7
  · have h := hlay 0 (by unfold layLen; split_ifs <;> omega)
    unfold layOp at h
    rw [if_neg hg0, if_neg h0, if_pos h7] at h
    have h' : v (layCell g) = v (layCell (g - 1)) * v (gpCell (sig s g)) := h
    rw [h', fact_gp hR hP (by omega) h7]
  · have hc := hlay 0 (by unfold layLen; rw [if_pos ⟨hg0, by omega⟩]; omega)
    have hm := hlay 1 (by unfold layLen; rw [if_pos ⟨hg0, by omega⟩]; omega)
    unfold layOp at hc hm
    rw [if_neg hg0, if_neg h0, if_neg h7, if_pos rfl] at hc
    rw [if_neg hg0, if_neg h0, if_neg h7, if_neg (by omega)] at hm
    have hc' : v (cCell g) = ofK (gpow (sig s g)) := hc
    have hm' : v (layCell g) = v (layCell (g - 1)) * v (cCell g) := hm
    rw [hm', hc']

/-- The layer products along the path. -/
theorem lay_val : ∀ g < 14,
    v (layCell g) = ofK (gpow (rootSlot - 106 + ∑ j ∈ Finset.range (g + 1), sig s j)) := by
  intro g
  induction g with
  | zero =>
    intro _
    have h := pre_relNH hR hV hP (g := 0)
      (q := tieLen 0 (s (gch 0 0) + s (gch 0 1) + s (gch 0 2)) +
        zeroCount (s (gch 0 0)) (s (gch 0 1)) (s (gch 0 2)) + 0) (by omega)
      (by unfold preLen layLen; rw [if_neg (by omega)]; omega)
    unfold sig at h ⊢
    rw [preOp_lay] at h
    unfold layOp at h
    rw [if_pos rfl] at h
    rw [Finset.sum_range_one]
    exact h
  | succ g ih =>
    intro hg
    rw [lay_step hR hV hP hg (by omega), Nat.add_sub_cancel, ih (by omega), ← ofK_mul,
      gpow_mul_gpow, Finset.sum_range_succ _ (g + 1), Nat.add_assoc]

/-- **The layer.** The hash-free relations on any path force `Σ s = 106`. -/
theorem layer_of_facts : ∑ k ∈ Finset.range 42, s k = 106 := by
  have h13 := lay_val hR hV hP 13 (by omega)
  simp only [show (13 : ℕ) + 1 = 14 from rfl] at h13
  rw [show layCell 13 = k0Cell from rfl, fact_k0 hR hP, k0V] at h13
  have hbound : ∑ j ∈ Finset.range 14, sig s j ≤ ∑ _j ∈ Finset.range 14, 29 :=
    Finset.sum_le_sum fun j hj => by
      obtain ⟨h0, h1, h2⟩ := gvalid_of_valid hV (Finset.mem_range.mp hj)
      have : Wc j ≤ 16 := by unfold Wc; split_ifs <;> omega
      unfold sig; omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hbound
  have heq := gpow_inj (show rootSlot < 2 ^ 64 - 1 by unfold rootSlot; omega)
    (show rootSlot - 106 + ∑ j ∈ Finset.range 14, sig s j < 2 ^ 64 - 1 by
      unfold rootSlot; omega) (ofK_injective h13)
  rw [← sum_sig]
  unfold rootSlot at heq
  omega

/-- The tie op `q` of group `g`'s block on the path. -/
theorem tie_rel {g q : ℕ} (hg : g < 14) (hq : q < tieLen g (sig s g)) :
    (tieOp g (s (gch g 0)) (s (gch g 1)) (s (gch g 2)) q).RelNH v := by
  have := pre_relNH hR hV hP hg (q := q) (by unfold preLen; unfold sig at hq; omega)
  unfold sig at hq
  rwa [preOp_tie hq] at this

/-- **The tie.** The accumulator after group `g` holds the sum of the words of groups `≤ g`. -/
theorem tie_of_facts : ∀ g < 14,
    v (accCell g) = ∑ j ∈ Finset.range (g + 1), natV (gwordS s j) := by
  intro g
  induction g with
  | zero =>
    intro _
    have h := tie_rel hR hV hP (g := 0) (q := 0) (by omega) (by unfold tieLen; simp)
    unfold tieOp at h
    rw [if_pos rfl] at h
    rw [Finset.sum_range_one]
    exact h
  | succ g ih =>
    intro hg
    rw [Finset.sum_range_succ, ← ih (by omega)]
    by_cases h0 : sig s (g + 1) = 0
    · have h := tie_rel hR hV hP (g := g + 1) (q := 0) hg (by unfold tieLen; split_ifs <;> omega)
      unfold tieOp at h
      unfold sig at h0
      rw [if_neg (by omega), if_pos h0] at h
      have h' : v (accCell (g + 1)) = v (accCell g) + v zCell := h
      have hw : gwordS s (g + 1) = 0 := by
        unfold gwordS gword
        rw [show s (gch (g + 1) 0) = 0 by omega, show s (gch (g + 1) 1) = 0 by omega,
          show s (gch (g + 1) 2) = 0 by omega]
        simp
      rw [h', fact_z hR hP, hw, natV_zero]
    · have hlen : tieLen (g + 1) (sig s (g + 1)) = 2 := by
        unfold tieLen; rw [if_pos ⟨by omega, h0⟩]
      have ht := tie_rel hR hV hP (g := g + 1) (q := 0) hg (by omega)
      have hx := tie_rel hR hV hP (g := g + 1) (q := 1) hg (by omega)
      unfold sig at h0
      unfold tieOp at ht hx
      rw [if_neg (by omega), if_neg h0, if_pos rfl] at ht
      rw [if_neg (by omega), if_neg h0, if_neg (by omega)] at hx
      have ht' : v (tCell (g + 1)) = natV (gwordS s (g + 1)) := ht
      have hx' : v (accCell (g + 1)) = v (accCell g) + v (tCell (g + 1)) := hx
      rw [hx', ht']

/-- The index cell is the tie accumulator after group 13. -/
theorem idx_of_facts : v idxCell = ∑ j ∈ Finset.range 14, natV (gwordS s j) :=
  tie_of_facts hR hV hP 13 (by omega)

/-- **Zero copies.** For a zero digit the root reads the revealed word. -/
theorem zero_copy_of_facts {k : ℕ} (hk : k < 42) (h0 : s k = 0) :
    v (rootTop k) = v (wCell k) + v zCell := by
  obtain ⟨hg, hj⟩ := grp_lt hk
  have e := gch_grp hk
  obtain ⟨q, hq, hz⟩ := zeroIdx_of_zero (g := grp k) (s := s) hj (by rw [e]; exact h0)
  have hpre := pre_relNH hR hV hP hg
    (q := tieLen (grp k) (s (gch (grp k) 0) + s (gch (grp k) 1) + s (gch (grp k) 2)) + q)
    (by unfold preLen; omega)
  rw [preOp_zc hq] at hpre
  unfold zcOp at hpre
  rw [hz, e] at hpre
  exact hpre

/-- **Chain 0's copy.** For `s 0 > 0` the root's first cv cell is chain 0's top. -/
theorem copy0_of_facts (h0 : s 0 ≠ 0) : v cvCell = v (topCell 0) + v zCell := by
  have hG := gvalid_of_valid hV (g := 0) (by omega)
  have hb := stepBase_bounds hG (by omega)
  have hf := pre_fit' hG (by omega)
  have hg00 : gch 0 0 = 0 := rfl
  have hpost : stepBase 0 (s (gch 0 0)) + 1 = NH 0 := by
    unfold stepBase postLen; rw [if_pos ⟨rfl, by rw [hg00]; exact h0⟩]
    unfold NH; simp
  have h := blk_relNH hR hV hP (g := 0) (i := stepBase 0 (s (gch 0 0)) + sig s 0) (by omega)
    (by omega) (by unfold ctlOff; omega)
  unfold sig at h
  rw [blockOp_post hf le_rfl (by omega)] at h
  exact h

end Facts

/-! ## The cost -/

theorem segBase_sum : ∑ g ∈ Finset.range 14, (NH g + 2) = 114 := by decide

/-- On the layer, every path costs `1319` cycles. -/
theorem totalCost_eq {s : ℕ → ℕ} (h : ∑ k ∈ Finset.range 42, s k = 106) : totalCost s = 1319 := by
  rw [← sum_sig] at h
  unfold totalCost segCost
  rw [Finset.sum_add_distrib, segBase_sum, ← Finset.mul_sum, h]; norm_num

/-- On the layer, every path executes `266` instructions. -/
theorem totalSteps_eq {s : ℕ → ℕ} (h : ∑ k ∈ Finset.range 42, s k = 106) : totalSteps s = 266 := by
  rw [← sum_sig] at h
  unfold totalSteps segSteps
  rw [Finset.sum_add_distrib, segBase_sum, h]; norm_num

/-- The claim: `boundaryCycles + 1319`. -/
def claim : ℕ := 1439

theorem boundary_eq : LeanIsa.boundaryCycles = 120 := by decide

/-! ## The certificate clauses -/

/-- **Cycles.** Every completing execution of the bytecode, under every admissible memory size,
every committed image and every step count, costs exactly `1319` plus the boundary. -/
theorem cycles (S : LeanIsa.Submission) (hS : S.program = program) : S.CyclesAtMost claim := by
  intro pk m σ κ h16 hκ L n cost h
  unfold LeanIsa.Submission.exec at h
  rw [hS, initial_eq] at h
  have hpin := pinned_of_sem suppSem trueRel (supp_straight h16 hκ) h
  obtain ⟨hV, hP, -, -, rfl⟩ :=
    walk_full (fun _ h => h) (walk_of_supp h16 hκ hpin (by norm_num) h)
  rw [totalCost_eq (layer_of_facts (fun _ h => h) hV hP), boundary_eq]
  unfold claim; omega

/-- The seeded rows of a submission running this bytecode at memory size `2 ^ 16`. -/
theorem seededRows_lt (S : LeanIsa.Submission) (hS : S.program = program) (hm : S.memLog = 16) :
    S.seededRows < LeanIsa.maxSeededRows := by
  unfold LeanIsa.Submission.seededRows
  rw [hS, hm, program_logSize]
  decide

end

end OptimalOTS.HLFlat
