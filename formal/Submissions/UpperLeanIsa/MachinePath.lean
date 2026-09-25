import Submissions.UpperLeanIsa.MachineRun

/-!
# Forced paths and the landing exit

Every completing walk follows the 20 straight prologue instructions, the free dispatch,
then fourteen frame-isolated blocks and the exit. Unit `j` runs in frame `frU s j`: the first
group's unit runs in frame 14 when the free digit `s` is `0`, in frame 1 otherwise. The block relations give
GP_u = initialProduct(88,s) * C_(sum of preceding group costs), so the exit target is
GP_13 = g ^ seedExp t with t = s + Σ costs. The exit table (`seed_table`, a hash-free identity)
shows that only t = 88 lands on the sentinel; every other total lands on a pad or past the
bytecode (`exit_forced`).

walk_full extracts the path facts, landings, exact instruction count and cycle cost.
walk_mk assembles them in the honest direction. No hash binding is needed for these results.
-/

namespace OptimalOTS.HLG3

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

variable {T : Tab}

/-! ## Walk lemmas -/

section Walks

variable {B : BlakeRel} {v : ℕ → E}

theorem Walk.inv {n t c : ℕ} (h : Walk T B v n t c) (ht : t ≠ sentinel) :
    t < sentinel ∧ (cinstrAt T t).RelB B v ∧ ∃ n' c', n = n' + (cinstrAt T t).steps ∧
      c = (cinstrAt T t).cost + c' ∧ Walk T B v n' (nextSlot T v t) c' := by
  cases h with
  | done => exact absurd rfl ht
  | step hs hR hw => exact ⟨hs, hR, _, _, rfl, rfl, hw⟩

theorem Walk.at_sentinel {n c : ℕ} (h : Walk T B v n sentinel c) : n = 0 ∧ c = 0 := by
  cases h with
  | done => exact ⟨rfl, rfl⟩
  | step hs _ _ => exact absurd hs (lt_irrefl _)

/-- A straight list of ops at consecutive slots: a walk through it yields each op's relation. -/
theorem walk_list {l : List CInstr} {t : ℕ}
    (hl : ∀ i (hi : i < l.length), cinstrAt T (t + i) = l[i])
    (hst : ∀ x ∈ l, x.straight = true) (hta : t + l.length ≤ sentinel) :
    ∀ {n c : ℕ}, Walk T B v n t c → (∀ x ∈ l, x.RelB B v) ∧
      ∃ n' c', n = n' + l.length ∧ c = lcost l + c' ∧ Walk T B v n' (t + l.length) c' := by
  induction l generalizing t with
  | nil =>
    intro n c h
    exact ⟨fun x hx => absurd hx List.not_mem_nil, n, c, rfl, by rw [lcost_nil, Nat.zero_add], h⟩
  | cons x l ih =>
    intro n c h
    have h0 : cinstrAt T t = x := by
      have := hl 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at this
    have hsx : x.straight = true := hst x (List.mem_cons_self)
    rw [List.length_cons] at hta
    obtain ⟨-, hR, n1, c1, rfl, rfl, hw⟩ := h.inv (by omega)
    rw [nextSlot_straight v (by rw [h0]; exact hsx)] at hw
    have hl' : ∀ i (hi : i < l.length), cinstrAt T (t + 1 + i) = l[i] := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega, hl (i + 1) (by simp; omega)]
      simp
    obtain ⟨hRs, n2, c2, rfl, rfl, hw2⟩ := ih hl' (fun y hy => hst y (List.mem_cons_of_mem _ hy))
      (by omega) hw
    refine ⟨fun y hy => ?_, n2, c2, ?_, ?_, ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · rwa [h0] at hR
      · exact hRs y hy
    · rw [h0, straight_steps hsx, List.length_cons]; ring
    · rw [h0, lcost_cons]; ring
    · rwa [List.length_cons, show t + (l.length + 1) = t + 1 + l.length by ring]

/-- A straight list whose relations hold extends a walk backwards. -/
theorem walk_list_mk {l : List CInstr} {t : ℕ}
    (hl : ∀ i (hi : i < l.length), cinstrAt T (t + i) = l[i])
    (hst : ∀ x ∈ l, x.straight = true) (hta : t + l.length ≤ sentinel)
    (hR : ∀ x ∈ l, x.RelB B v) {n c : ℕ} (h : Walk T B v n (t + l.length) c) :
    Walk T B v (n + l.length) t (lcost l + c) := by
  induction l generalizing t n c with
  | nil => simpa [lcost] using h
  | cons x l ih =>
    have h0 : cinstrAt T t = x := by
      have := hl 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at this
    have hsx : x.straight = true := hst x (List.mem_cons_self)
    rw [List.length_cons] at hta h
    have hl' : ∀ i (hi : i < l.length), cinstrAt T (t + 1 + i) = l[i] := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega, hl (i + 1) (by simp; omega)]
      simp
    have hw := ih hl' (fun y hy => hst y (List.mem_cons_of_mem _ hy)) (by omega)
      (fun y hy => hR y (List.mem_cons_of_mem _ hy))
      (by rwa [show t + 1 + l.length = t + (l.length + 1) by ring])
    rw [← nextSlot_straight v (by rw [h0]; exact hsx)] at hw
    have := Walk.step (by omega) (by rw [h0]; exact hR x List.mem_cons_self) hw
    rw [h0, straight_steps hsx, lcost_cons, List.length_cons] at *
    convert this using 1 <;> ring

end Walks

/-! ## The prologue -/

theorem proList_lcost : lcost proList = 29 := by unfold proList; rfl

theorem cinstrAt_proList (T : Tab) {t : ℕ} (ht : t < proList.length) :
    cinstrAt T (0 + t) = proList[t] := by
  rw [Nat.zero_add, cinstrAt_pro T (by rw [proList_length] at ht; omega)]
  unfold prologue
  rw [if_pos (by rw [proList_length] at ht; exact ht), List.getD_eq_getElem _ _ ht]

theorem cinstrAt_20 (T : Tab) : cinstrAt T 20 = .dispatch 0 := by
  rw [cinstrAt_pro T (by omega)]; unfold prologue; rw [if_neg (by omega), if_pos rfl]

theorem pro_mem_one : CInstr.setc oneCell oneV ∈ proList := by unfold proList; simp
theorem pro_mem_len : CInstr.setc lenCell (natV 5503) ∈ proList := by unfold proList; simp
theorem pro_mem_g : CInstr.setc gCell gV ∈ proList := by unfold proList; simp
theorem pro_mem_c {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ 16) (h16 : c ≠ 16) :
    CInstr.setc (cCell c) (cV c) ∈ proList := by
  unfold proList
  simp only [List.mem_append, List.mem_map, List.mem_range]
  left; right
  exact ⟨c - 1, by omega, by rw [Nat.sub_add_cancel h1]⟩

theorem pro_mem_frame {f : ℕ} (hf : f < 15) : CInstr.setc (fCell f) (frameV f) ∈ proList := by
  rw [fCell, frameV_eq_cV]
  exact pro_mem_c (by omega) (by omega) (by omega)

theorem pro_mem_idx : CInstr.blake msgLo msgHi nonceCell pkCell oneCell idxCell gCell ∈ proList := by
  unfold proList; simp
theorem pro_mem_h0 : CInstr.mul (hCell 0) gCell (h1Cell 0) ∈ proList := by unfold proList; simp

/-! ## Units and frames -/

/-- The frame of unit `j` (`j < 14`) on the path of free digit `s`: unit 1 (the first group) runs
in frame 14 when `s = 0`. -/
def frU (s j : ℕ) : ℕ := if j = 1 then frG0 s else j

theorem frU_zero (s : ℕ) : frU s 0 = 0 := by unfold frU; rw [if_neg (by omega)]

theorem frU_ne {s j : ℕ} (hj : j ≠ 1) : frU s j = j := by unfold frU; rw [if_neg hj]

theorem frU_lt (s : ℕ) {j : ℕ} (hj : j < 14) : frU s j < 15 := by
  unfold frU frG0; split_ifs <;> omega

theorem frU_pos (s : ℕ) {j : ℕ} (hj : j ≠ 0) : frU s j ≠ 0 := by
  unfold frU frG0; split_ifs <;> omega

theorem gOf_frU (s : ℕ) {j : ℕ} (h1 : j ≠ 0) (hj : j < 14) : gOf (frU s j) = j - 1 := by
  unfold frU frG0 gOf; split_ifs <;> omega

theorem Wf_frU (s : ℕ) {j : ℕ} (hj : j < 14) : Wf (frU s j) = Wf j := by
  by_cases h0 : j = 0
  · subst h0; rw [frU_zero]
  · rw [Wf_pos (frU_pos s h0), Wf_pos h0, gOf_frU s h0 hj]
    unfold gOf; rw [if_neg (by omega)]

/-- The block variant of group `u` on the path of free digit `s`. -/
def zU (s u : ℕ) : Bool := decide (u = 0 ∧ s = 0)

theorem bodyF_frU_succ (T : Tab) (s : ℕ) {u : ℕ} (hu : u < 13) (x : ℕ) :
    bodyF T (frU s (u + 1)) x = body T u x (zU s u) := by
  by_cases h0 : u = 0
  · subst h0
    by_cases hs : s = 0
    · subst hs
      have : zU 0 0 = true := by decide
      rw [this]; exact bodyF_14 T x
    · have h1 : frU s (0 + 1) = 0 + 1 := by unfold frU frG0; rw [if_pos rfl, if_neg hs]
      have h2 : zU s 0 = false := decide_eq_false (by omega)
      rw [h1, h2, bodyF_succ T hu]
  · rw [frU_ne (by omega), bodyF_succ T hu, show zU s u = false from decide_eq_false (by omega)]

theorem bodyF_frU_zero (T : Tab) (s x : ℕ) : bodyF T (frU s 0) x = fbody x := by
  rw [frU_zero, bodyF_zero]

/-- The control op after unit `j - 1`: the dispatch of unit `j`, or the exit. -/
def ctlF' (s j : ℕ) : CInstr := if j < 14 then .dispatch (frU s j) else .exit

theorem ctlOf_frU (s : ℕ) {j x : ℕ} (hj : j < 14) (hx : j = 0 → x = s) :
    ctlOf (frU s j) x = ctlF' s (j + 1) := by
  by_cases h0 : j = 0
  · subst h0
    rw [frU_zero, hx rfl]
    unfold ctlOf ctlF'
    rw [if_pos rfl, if_pos (by omega)]
    unfold frU; rw [if_pos rfl]
  · unfold ctlOf ctlF'
    rw [if_neg (frU_pos s h0), gOf_frU s h0 hj, Nat.sub_add_cancel (by omega)]
    unfold ctlF
    split_ifs <;> first | rfl | omega | (rw [frU_ne (by omega)])

/-! ## The index vector of an image -/

/-- The free digit read off the free landing hint. -/
def x0Of (v : ℕ → E) : ℕ := xOf 0 (slotOf ((v (hCell 0)).limb 0))

/-- The index of unit `f` read off its frame's landing hint. -/
def xsOf (v : ℕ → E) (f : ℕ) : ℕ := xOf (frU (x0Of v) f) (slotOf ((v (hCell (frU (x0Of v) f))).limb 0))

theorem xsOf_zero (v : ℕ → E) : xsOf v 0 = x0Of v := by
  unfold xsOf; rw [frU_zero]; rfl

/-- The landing hints of the index vector `xs`. -/
def Landing (v : ℕ → E) (xs : ℕ → ℕ) : Prop :=
  ∀ f < 14, v (hCell (frU (xs 0) f)) = ofK (gpow (ent (frU (xs 0) f) (xs f)))

/-- The index vector is in range. -/
def Valid (xs : ℕ → ℕ) : Prop := ∀ f < 14, xs f < Wf f

/-- The relation holds at every op on the path of `xs`. -/
structure PathFacts (T : Tab) (B : BlakeRel) (v : ℕ → E) (xs : ℕ → ℕ) : Prop where
  pro : ∀ y ∈ proList, y.RelB B v
  disp : ∀ f < 14, (CInstr.dispatch (frU (xs 0) f)).RelB B v
  blk : ∀ f < 14, ∀ y ∈ bodyF T (frU (xs 0) f) (xs f), y.RelB B v
  exit : CInstr.exit.RelB B v
  /-- The exit lands on the sentinel. -/
  gp13 : v (gpCell 13) = ofK (gpow sentinel)

/-- The dispatch slot of unit `f` on the path of `xs` (for `f = 14`, the exit). -/
def ctlSlot (T : Tab) (xs : ℕ → ℕ) (f : ℕ) : ℕ :=
  if f = 0 then 20 else ent (frU (xs 0) (f - 1)) (xs (f - 1)) + 1 +
    (bodyF T (frU (xs 0) (f - 1)) (xs (f - 1))).length

theorem ctlSlot_succ (T : Tab) (xs : ℕ → ℕ) (f : ℕ) :
    ctlSlot T xs (f + 1) = ent (frU (xs 0) f) (xs f) + 1 + (bodyF T (frU (xs 0) f) (xs f)).length := by
  unfold ctlSlot; rw [if_neg (by omega), Nat.add_sub_cancel]

theorem cinstrAt_ctlSlot (hT : T.Hyp) {xs : ℕ → ℕ} {f : ℕ} (hf : f ≤ 14)
    (hV : ∀ j < f, xs j < Wf j) :
    cinstrAt T (ctlSlot T xs f) = ctlF' (xs 0) f ∧ ctlSlot T xs f < sentinel := by
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · refine ⟨?_, by unfold ctlSlot sentinel; simp⟩
    unfold ctlSlot ctlF'; rw [if_pos rfl, if_pos (by omega), frU_zero]; exact cinstrAt_20 T
  · obtain ⟨j, rfl⟩ : ∃ j, f = j + 1 := ⟨f - 1, by omega⟩
    rw [ctlSlot_succ]
    have hx : xs j < Wf (frU (xs 0) j) := by rw [Wf_frU _ (by omega)]; exact hV j (by omega)
    obtain ⟨-, -, h3, h4⟩ := cinstrAt_blk hT (frU_lt (xs 0) (show j < 14 by omega)) hx
    refine ⟨?_, h4⟩
    rw [h3, ctlOf_frU (xs 0) (by omega) (fun h => by rw [h])]

/-- A landing in frame `f` names an entry of that frame. -/
theorem digit_eq_of_entry {v : ℕ → E} {f e : ℕ} (he : IsEntry f e)
    (hx : (v (hCell f)).limb 0 = gpow e) :
    e = ent f (xOf f (slotOf ((v (hCell f)).limb 0))) ∧ xOf f (slotOf ((v (hCell f)).limb 0)) < Wf f := by
  have hlt := isEntry_lt he
  rw [hx, slotOf_gpow (by unfold sentinel at hlt; omega)]
  exact ⟨(isEntry_eq he).2, (isEntry_eq he).1⟩

/-- `H_f · g` lands after the entry. -/
theorem slot_h1 {v : ℕ → E} {f x : ℕ} (hg : v gCell = gV)
    (hmul : v (h1Cell f) = v (hCell f) * v gCell) (hH : v (hCell f) = ofK (gpow (ent f x)))
    (hlt : ent f x + 1 < 2 ^ 18) : slotOf ((v (h1Cell f)).limb 0) = ent f x + 1 := by
  rw [hmul, hH, hg, gV, ← ofK_mul, limb_ofK_zero, mul_comm, g_mul_gpow, slotOf_gpow hlt]

/-- The last straight op of unit `j < 13`'s block is the next unit's `MUL(H, g, H')`. -/
theorem nextMul_mem (T : Tab) (s : ℕ) {j x : ℕ} (hj : j < 13) (hx : j = 0 → x = s) :
    CInstr.mul (hCell (frU s (j + 1))) gCell (h1Cell (frU s (j + 1))) ∈ bodyF T (frU s j) x := by
  by_cases h0 : j = 0
  · subst h0
    rw [bodyF_frU_zero, hx rfl]
    have : frU s (0 + 1) = frG0 s := by unfold frU; rw [if_pos rfl]
    rw [this]; unfold fbody; simp
  · obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    rw [bodyF_frU_succ T s (by omega), frU_ne (by omega)]
    unfold body
    simp only [List.mem_append, List.mem_singleton]
    right
    unfold nextOp; rw [if_pos (by omega)]

section Units

variable {B : BlakeRel} {v : ℕ → E}

/-- One unit, from its dispatch to its control op: the landing, the block's relations. -/
theorem walk_unit (hT : T.Hyp) {d f n c x : ℕ} (hf : f < 15) (hci : cinstrAt T d = .dispatch f)
    (hg : v gCell = gV) (hmul : v (h1Cell f) = v (hCell f) * v gCell) (h : Walk T B v n d c)
    (hxd : xOf f (slotOf ((v (hCell f)).limb 0)) = x) :
    x < Wf f ∧ v (hCell f) = ofK (gpow (ent f x)) ∧
      (CInstr.dispatch f).RelB B v ∧ (∀ y ∈ bodyF T f x, y.RelB B v) ∧
      ∃ n' c', n = n' + (2 + (bodyF T f x).length) ∧
        c = 2 + lcost (bodyF T f x) + c' ∧
        Walk T B v n' (ent f x + 1 + (bodyF T f x).length) c' := by
  have hdne : d ≠ sentinel := fun e => by rw [e, cinstrAt_sentinel] at hci; cases hci
  obtain ⟨-, hRd, n1, c1, rfl, rfl, hw⟩ := h.inv hdne
  have hrel := hRd
  rw [hci] at hrel
  obtain ⟨hH, -, e, he, hx⟩ := hrel
  obtain ⟨he', hdig⟩ := digit_eq_of_entry he hx
  rw [hxd] at he' hdig
  have hHv : v (hCell f) = ofK (gpow (ent f x)) := by rw [ofK_limb hH, hx, ← he']
  obtain ⟨-, hbl, -, hlt⟩ := cinstrAt_blk hT hf hdig
  have hnext : nextSlot T v d = ent f x + 1 := by
    unfold nextSlot; rw [hci]
    exact slot_h1 hg hmul hHv (by unfold sentinel at hlt; omega)
  rw [hnext] at hw
  obtain ⟨hR, n2, c2, rfl, rfl, hw2⟩ := walk_list (l := bodyF T f x) (t := ent f x + 1) hbl
    (bodyF_straight T f x) (by omega) hw
  refine ⟨hdig, hHv, by rw [hci] at hRd; exact hRd, hR, n2, c2, ?_, ?_, hw2⟩
  · rw [hci]; show n2 + (bodyF T f x).length + 2 = _; ring
  · rw [hci]; show 2 + (lcost (bodyF T f x) + c2) = _; ring

end Units

/-! ## The full path -/

/-- Steps of the whole path. -/
def totalSteps (T : Tab) (xs : ℕ → ℕ) : ℕ :=
  21 + ∑ f ∈ Finset.range 14, (2 + (bodyF T (frU (xs 0) f) (xs f)).length)

/-- Cycles of the whole path. -/
def totalCost (T : Tab) (xs : ℕ → ℕ) : ℕ :=
  30 + ∑ f ∈ Finset.range 14, (2 + lcost (bodyF T (frU (xs 0) f) (xs f)))

/-! ### The landing product -/

theorem prodOp_mem (T : Tab) (s : ℕ) {u : ℕ} (hu : u < 13) (x : ℕ) :
    prodOp T u x ∈ bodyF T (frU s (u + 1)) x := by
  rw [bodyF_frU_succ T s hu]; unfold body; simp

theorem cCell_val {B : BlakeRel} {v : ℕ → E} (hpro : ∀ y ∈ proList, y.RelB B v) {c : ℕ}
    (hc : c ≤ 16) : v (cCell c) = cV c := by
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · rw [cV_zero]; exact hpro _ pro_mem_one
  · by_cases h16 : c = 16
    · subst c; rw [cV_sixteen]; exact hpro _ pro_mem_g
    · exact hpro _ (pro_mem_c h0 hc h16)

theorem cost_le (hT : T.Hyp) {u x : ℕ} (hu : u < 13) (hx : x < VF u) : cost T u x ≤ 16 := by
  rw [hT.cost_eq u hu x hx]; have := band_lt_17 hu hx; omega

/-- The landing product before group `u`: the free landing times the cost constants. -/
theorem prod_eq {B : BlakeRel} {v : ℕ → E} (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs)
    (hpro : ∀ y ∈ proList, y.RelB B v)
    (hblk : ∀ f < 14, ∀ y ∈ bodyF T (frU (xs 0) f) (xs f), y.RelB B v) : ∀ u ≤ 13,
      v (gpCell u) = ofK (LeanIsaFieldRescale.initialProduct 88 (xs 0) *
        LeanIsaFieldRescale.costFactor (∑ w ∈ Finset.range u, cost T w (xs (w + 1)))) := by
  intro u
  induction u with
  | zero =>
    intro _
    have hseed : CInstr.setc (gpCell 0) (ofK (LeanIsaFieldRescale.initialProduct 88 (xs 0))) ∈
        bodyF T (frU (xs 0) 0) (xs 0) := by rw [bodyF_frU_zero]; unfold fbody; simp
    have h : v (gpCell 0) = ofK (LeanIsaFieldRescale.initialProduct 88 (xs 0)) :=
      hblk 0 (by omega) _ hseed
    rw [Finset.sum_range_zero]
    change v (gpCell 0) = ofK (_ * gpow 0)
    rw [gpow_zero', mul_one]
    exact h
  | succ u ih =>
    intro hu
    have hx : xs (u + 1) < VF u := by have := hV (u + 1) (by omega); rwa [Wf_succ (by omega)] at this
    have hrel := CInstr.relNH_of_relB
      (hblk (u + 1) (by omega) _ (prodOp_mem T (xs 0) (by omega) (xs (u + 1))))
    have hrel' : v (gpCell (u + 1)) = v (gpCell u) * v (cCell (cost T u (xs (u + 1)))) := hrel
    rw [hrel', ih (by omega), cCell_val hpro (cost_le hT (by omega) hx), cV, ← ofK_mul,
      Finset.sum_range_succ]
    change ofK ((_ * LeanIsaFieldRescale.costFactor _) * LeanIsaFieldRescale.costFactor _) = _
    rw [mul_assoc, LeanIsaFieldRescale.factor_add]

/-- The exponent of the landing product for the total `t`: `sentinel + Q (t − 88)` modulo the
order of `g`. -/
def seedExp (t : ℕ) : ℕ := (9223372036855037945 + LeanIsaFieldRescale.stride * t) % ordG

theorem seed_lt (t : ℕ) : seedExp t < ordG := Nat.mod_lt _ (by decide)

theorem seedExp_88 : seedExp 88 = sentinel := by
  norm_num [seedExp, ordG, sentinel, LeanIsaFieldRescale.stride]

/-- The free seed times `C_c` is `g ^ seedExp (s + c)`. -/
theorem initialProduct_mul (s c : ℕ) :
    LeanIsaFieldRescale.initialProduct 88 s * LeanIsaFieldRescale.costFactor c =
      gpow (seedExp (s + c)) := by
  have hl : LeanIsaFieldRescale.costFactor 88 ≠ 0 := pow_ne_zero _ g_ne_zero
  rw [LeanIsaFieldRescale.initialProduct, mul_assoc, LeanIsaFieldRescale.factor_add,
    div_mul_eq_mul_div, div_eq_iff hl, LeanIsaFieldRescale.costFactor,
    LeanIsaFieldRescale.costFactor, gpow_mul_gpow, gpow_mul_gpow, seedExp,
    ← gpow_mod (_ % ordG + _), Nat.mod_add_mod, ← gpow_mod (LeanIsaFieldRescale.sentinel + _)]
  have he : (LeanIsaFieldRescale.sentinel + LeanIsaFieldRescale.stride * (s + c)) % ordG =
      (9223372036855037945 + LeanIsaFieldRescale.stride * (s + c) +
        LeanIsaFieldRescale.stride * 88) % ordG := by
    unfold LeanIsaFieldRescale.stride ordG LeanIsaFieldRescale.sentinel; omega
  rw [he]

/-- **The exit table.** For every reachable total `t ≤ 284`, the exit target `g ^ seedExp t` is
the sentinel only at the layer `t = 88`; otherwise it is past the bytecode or one of the pads
`sentinel − 5 … sentinel − 1` (the totals `88 − 16 j`, since `16 Q ≡ 1`). -/
theorem seed_table : ∀ t < 285,
    t = 88 ∨ 2 ^ 18 ≤ seedExp t ∨ (262137 ≤ seedExp t ∧ seedExp t < 262143) := by
  decide +kernel

theorem slotOf_high {x : ℕ} (h1 : 2 ^ 18 ≤ x) (h2 : x < 2 ^ 64 - 1) : slotOf (gpow x) = 2 ^ 18 := by
  unfold slotOf
  rw [dif_neg]
  rintro ⟨i, hi, he⟩
  have := gpow_inj h2 (by omega) he
  omega

/-- **The exit is forced.** From the exit, a walk to the sentinel exists only when the last
landing product `g ^ seedExp t` is `g ^ sentinel`: every other target is a pad (it fails) or past
the bytecode. -/
theorem exit_forced {B : BlakeRel} {v : ℕ → E} {t n c : ℕ} (ht : t ≤ 284)
    (h : Walk T B v n (slotOf (gpow (seedExp t))) c) : t = 88 := by
  rcases seed_table t (by omega) with h96 | hhi | ⟨hlo, hlt⟩
  · exact h96
  · rw [slotOf_high hhi (by have := seed_lt t; unfold ordG at this; omega)] at h
    have := h.le_sentinel
    unfold sentinel at this; omega
  · rw [slotOf_gpow (by omega)] at h
    obtain ⟨-, hR, -⟩ := h.inv (by unfold sentinel; omega)
    rcases cinstrAt_cases T (seedExp t) with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | h1
    · omega
    · unfold gEnd at h1; omega
    · unfold zEnd at h1; omega
    · unfold baseF at h1; omega
    · rw [h1] at hR; exact (show False from hR).elim

section Full

variable {B : BlakeRel} {v : ℕ → E}

/-- **The forced path.** Every walk from slot `0` is the path of the index vector `xsOf v`, with
its exact step count and cost. -/
theorem walk_full (hT : T.Hyp) {n c : ℕ} (h : Walk T B v n 0 c) :
    Valid (xsOf v) ∧ PathFacts T B v (xsOf v) ∧ Landing v (xsOf v) ∧
      n = totalSteps T (xsOf v) ∧ c = totalCost T (xsOf v) := by
  -- the prologue
  obtain ⟨hRp, n0, c0, rfl, rfl, hw0⟩ := walk_list (l := proList) (t := 0)
    (fun i hi => cinstrAt_proList T hi) proList_straight (by rw [proList_length]; decide) h
  rw [proList_length, Nat.zero_add] at hw0
  have hg : v gCell = gV := hRp _ pro_mem_g
  have hmul0 : v (h1Cell 0) = v (hCell 0) * v gCell := hRp _ pro_mem_h0
  set xs := xsOf v with hxs
  have hxsf : ∀ f, xs f = xOf (frU (xs 0) f) (slotOf ((v (hCell (frU (xs 0) f))).limb 0)) := by
    intro f; rw [hxs, xsOf_zero]; rfl
  -- the units, by induction
  have key : ∀ j ≤ 14, (∀ f < j, xs f < Wf f ∧
      v (hCell (frU (xs 0) f)) = ofK (gpow (ent (frU (xs 0) f) (xs f))) ∧
      (CInstr.dispatch (frU (xs 0) f)).RelB B v ∧
      ∀ y ∈ bodyF T (frU (xs 0) f) (xs f), y.RelB B v) ∧
      ∃ n' c', n0 = n' + ∑ f ∈ Finset.range j, (2 + (bodyF T (frU (xs 0) f) (xs f)).length) ∧
        c0 = (∑ f ∈ Finset.range j, (2 + lcost (bodyF T (frU (xs 0) f) (xs f)))) + c' ∧
        Walk T B v n' (ctlSlot T xs j) c' ∧
        (j < 14 → v (h1Cell (frU (xs 0) j)) = v (hCell (frU (xs 0) j)) * v gCell) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun f hf => absurd hf (by omega), n0, c0, by simp, by simp, ?_, fun _ => ?_⟩
      · unfold ctlSlot; rwa [if_pos rfl]
      · rw [frU_zero]; exact hmul0
    | succ j ih =>
      intro hj
      obtain ⟨hprev, n', c', hn, hc, hw, hm⟩ := ih (by omega)
      have hci := (cinstrAt_ctlSlot hT (xs := xs) (f := j) (by omega)
        (fun f hf => (hprev f hf).1)).1
      have hci' : cinstrAt T (ctlSlot T xs j) = .dispatch (frU (xs 0) j) := by
        rw [hci]; unfold ctlF'; rw [if_pos (by omega)]
      obtain ⟨hdig, hHv, hRd, hblk, n'', c'', rfl, rfl, hw'⟩ :=
        walk_unit hT (frU_lt _ (by omega)) hci' hg (hm (by omega)) hw (hxsf j).symm
      refine ⟨fun f hf => ?_, n'', c'', ?_, ?_, ?_, fun hj' => ?_⟩
      · by_cases hfj : f < j
        · exact hprev f hfj
        · obtain rfl : f = j := by omega
          exact ⟨by rwa [Wf_frU _ (by omega)] at hdig, hHv, hRd, hblk⟩
      · rw [hn, Finset.sum_range_succ]; ring
      · rw [hc, Finset.sum_range_succ]; ring
      · rw [ctlSlot_succ]; exact hw'
      · exact hblk _ (nextMul_mem T (xs 0) (by omega) (fun h => by rw [h]))
  obtain ⟨hall, n1, c1, hn1, hc1, hw1, -⟩ := key 14 (le_refl 14)
  -- the exit
  obtain ⟨hci, hlt⟩ := cinstrAt_ctlSlot hT (xs := xs) (f := 14) le_rfl (fun f hf => (hall f hf).1)
  have hci' : cinstrAt T (ctlSlot T xs 14) = .exit := by
    rw [hci]; unfold ctlF'; rw [if_neg (by omega)]
  obtain ⟨-, hRx, n2, c2, rfl, rfl, hw2⟩ := hw1.inv (by omega)
  have hV : Valid xs := fun f hf => (hall f hf).1
  have hgp := prod_eq hT hV hRp (fun f hf => (hall f hf).2.2.2) 13 le_rfl
  set t := xs 0 + ∑ w ∈ Finset.range 13, cost T w (xs (w + 1)) with htdef
  have hbound : ∑ w ∈ Finset.range 13, cost T w (xs (w + 1)) ≤ ∑ _w ∈ Finset.range 13, 16 :=
    Finset.sum_le_sum fun w hw => by
      have hw' := Finset.mem_range.mp hw
      have := hV (w + 1) (by omega); rw [Wf_succ hw'] at this
      exact cost_le hT hw' this
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hbound
  have hx0 : xs 0 < 64 := by have := hV 0 (by omega); rwa [Wf_zero] at this
  have hgp' : v (gpCell 13) = ofK (gpow (seedExp t)) := by rw [hgp, initialProduct_mul]
  have hnext0 : nextSlot T v (ctlSlot T xs 14) = slotOf (gpow (seedExp t)) := by
    unfold nextSlot; rw [hci']
    show slotOf _ = _
    rw [hgp', limb_ofK_zero]
  rw [hnext0] at hw2
  have ht96 : t = 88 := exit_forced (by omega) hw2
  have hsen : seedExp t = sentinel := by rw [ht96]; exact seedExp_88
  rw [hsen, slotOf_gpow (by unfold sentinel; omega)] at hw2
  obtain ⟨rfl, rfl⟩ := hw2.at_sentinel
  refine ⟨hV, ⟨hRp, fun f hf => (hall f hf).2.2.1,
    fun f hf => (hall f hf).2.2.2, by rw [hci'] at hRx; exact hRx, by rw [hgp', hsen]⟩,
    fun f hf => (hall f hf).2.1, ?_, ?_⟩
  · have hs1 : (cinstrAt T (ctlSlot T xs 14)).steps = 1 := by rw [hci']; rfl
    rw [hn1, hs1, proList_length]; unfold totalSteps; omega
  · have hc1' : (cinstrAt T (ctlSlot T xs 14)).cost = 1 := by rw [hci']; rfl
    rw [hc1, hc1', proList_lcost]; unfold totalCost; omega

/-- **Assembling the forced path.** The relations along the path of `xs`, with its return hints,
give a walk from slot `0`. -/
theorem walk_mk (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs) (hP : PathFacts T B v xs)
    (hH1 : ∀ f < 14, v (h1Cell (frU (xs 0) f)) = ofK (gpow (ent (frU (xs 0) f) (xs f) + 1))) :
    ∃ n c, Walk T B v n 0 c := by
  -- the exit
  have hexit : ∃ n c, Walk T B v n (ctlSlot T xs 14) c := by
    obtain ⟨hci, hlt⟩ := cinstrAt_ctlSlot hT (xs := xs) (f := 14) le_rfl (fun f hf => hV f hf)
    have hci' : cinstrAt T (ctlSlot T xs 14) = .exit := by
      rw [hci]; unfold ctlF'; rw [if_neg (by omega)]
    have hnext : nextSlot T v (ctlSlot T xs 14) = sentinel := by
      unfold nextSlot; rw [hci']
      show slotOf _ = _
      rw [hP.gp13, limb_ofK_zero, slotOf_gpow (by unfold sentinel; omega)]
    have := Walk.step (T := T) (B := B) (v := v) hlt (by rw [hci']; exact hP.exit)
      (by rw [hnext]; exact Walk.done)
    exact ⟨_, _, this⟩
  -- the units, backwards
  have key : ∀ d ≤ 14, ∃ n c, Walk T B v n (ctlSlot T xs (14 - d)) c := by
    intro d
    induction d with
    | zero => intro _; simpa using hexit
    | succ d ih =>
      intro hd
      obtain ⟨n, c, hw⟩ := ih (by omega)
      set f := 14 - (d + 1) with hfdef
      have hf : f < 14 := by omega
      have hf1 : 14 - d = f + 1 := by omega
      rw [hf1, ctlSlot_succ] at hw
      have hxf : xs f < Wf (frU (xs 0) f) := by rw [Wf_frU _ hf]; exact hV f hf
      obtain ⟨-, hbl, -, hlt⟩ := cinstrAt_blk hT (frU_lt (xs 0) hf) hxf
      have hw2 := walk_list_mk (l := bodyF T (frU (xs 0) f) (xs f))
        (t := ent (frU (xs 0) f) (xs f) + 1) hbl
        (bodyF_straight T _ (xs f)) (by omega) (hP.blk f hf) hw
      obtain ⟨hci, hlt'⟩ := cinstrAt_ctlSlot hT (xs := xs) (f := f) (by omega)
        (fun j _ => hV j (by omega))
      have hci' : cinstrAt T (ctlSlot T xs f) = .dispatch (frU (xs 0) f) := by
        rw [hci]; unfold ctlF'; rw [if_pos hf]
      have hnext : nextSlot T v (ctlSlot T xs f) = ent (frU (xs 0) f) (xs f) + 1 := by
        unfold nextSlot; rw [hci']
        show slotOf _ = _
        have := ent_lt (frU_lt (xs 0) hf) hxf
        rw [hH1 f hf, limb_ofK_zero, slotOf_gpow (by unfold sentinel at this; omega)]
      rw [← hnext] at hw2
      exact ⟨_, _, Walk.step hlt' (by rw [hci']; exact hP.disp f hf) hw2⟩
  obtain ⟨n, c, hw⟩ := key 14 le_rfl
  rw [show 14 - 14 = 0 from rfl] at hw
  unfold ctlSlot at hw
  rw [if_pos rfl] at hw
  have := walk_list_mk (l := proList) (t := 0) (fun i hi => cinstrAt_proList T hi)
    proList_straight (by rw [proList_length]; decide) hP.pro
    (by rwa [proList_length])
  exact ⟨_, _, this⟩

end Full

/-! ## The pinned constants of a completing run -/

section Prefix

variable {κ : ℕ} {L : MemImage κ}

/-- The relations of a straight prefix of a completing run. -/
theorem rel_prefix (Sm : Sem) (B : BlakeRel)
    (hst : ∀ s pc x, (cinstrAt T s).straight = true →
      x ∈ Sm.S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt T s).toInstr) →
        x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt T s).RelB B (Lx L))) :
    ∀ a t n c, (∀ i < a, (cinstrAt T (t + i)).straight = true) → t + a < sentinel →
      some c ∈ Sm.S (LeanIsa.runCost (program T) L n ⟨gpow t, 1⟩) →
        ∀ i < a, (cinstrAt T (t + i)).RelB B (Lx L) := by
  intro a
  induction a with
  | zero => intro t n c _ _ _ i hi; omega
  | succ a ih =>
    intro t n c hstr hta h i hi
    cases n with
    | zero => rw [runCost_zero_slot L (by omega)] at h; exact absurd h Sm.some_not_pure_none
    | succ m =>
      have hs0 : (cinstrAt T t).straight = true := by simpa using hstr 0 (by omega)
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

/-- A completing run from slot `0` has the constants `ONE` and `F_f` pinned. -/
theorem pinned_of_sem (Sm : Sem) (B : BlakeRel)
    (hst : ∀ s pc x, (cinstrAt T s).straight = true →
      x ∈ Sm.S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt T s).toInstr) →
        x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt T s).RelB B (Lx L)))
    {n c : ℕ} (h : some c ∈ Sm.S (LeanIsa.runCost (program T) L n ⟨gpow 0, 1⟩)) :
    Pinned (Lx L) := by
  have hp := rel_prefix Sm B hst 20 0 n c
    (fun i hi => by
      rw [cinstrAt_proList T (by rw [proList_length]; exact hi)]
      exact proList_straight _ (List.getElem_mem _))
    (by unfold sentinel; omega) h
  have hall : ∀ y ∈ proList, y.RelB B (Lx L) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have := hp i (by rw [proList_length] at hi; exact hi)
    rwa [cinstrAt_proList T hi] at this
  refine ⟨hall _ pro_mem_one, fun f hf => ?_⟩
  exact hall _ (pro_mem_frame hf)

end Prefix

end

end OptimalOTS.HLG3
