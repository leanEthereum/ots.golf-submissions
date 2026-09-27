import Submissions.UpperLeanIsa.FusionMachineTable

/-! Local block lengths and costs. These bounds will be applied to the certified machine walk. -/
namespace OptimalOTS.HLFusion
open LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer

def lcost (l : List CInstr) : ℕ := (l.map CInstr.cost).sum

theorem lcost_append (a b : List CInstr) : lcost (a ++ b) = lcost a + lcost b := by
  unfold lcost; rw [List.map_append, List.sum_append]

theorem lcost_cons (x : CInstr) (l : List CInstr) : lcost (x :: l) = x.cost + lcost l := by
  unfold lcost; rw [List.map_cons, List.sum_cons]

theorem lcost_nil : lcost [] = 0 := rfl

theorem lcost_flatMap (f : ℕ → List CInstr) (l : List ℕ) :
    lcost (l.flatMap f) = (l.map (fun i => lcost (f i))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, lcost_append, ih, List.map_cons, List.sum_cons]

theorem lcost_replicate (n : ℕ) (x : CInstr) : lcost (List.replicate n x) = n * x.cost := by
  unfold lcost; rw [List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem chainOps_length (k d dst : ℕ) : (chainOps k d dst).length = d := by
  unfold chainOps; rw [List.length_map, List.length_range]

theorem chainOps_lcost (k d dst : ℕ) : lcost (chainOps k d dst) = 10 * d := by
  unfold chainOps lcost
  rw [List.map_map]
  have : (CInstr.cost ∘ fun t => chainOp k d t dst) = fun _ => 10 := by
    funext t; dsimp only [Function.comp_def]; unfold chainOp; split_ifs <;> rfl
  rw [this, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, mul_comm]

theorem mem_chainOps {k d dst : ℕ} {x : CInstr} :
    x ∈ chainOps k d dst ↔ ∃ t < d, x = chainOp k d t dst := by
  unfold chainOps
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, List.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, List.mem_range.mpr ht, rfl⟩

theorem chainOp_straight (k d t dst : ℕ) : (chainOp k d t dst).straight = true := by unfold chainOp; split_ifs <;> rfl

theorem tie_straight {u v : ℕ} : ∀ x ∈ tie u v, x.straight = true := by
  intro x hx; unfold tie at hx; split_ifs at hx <;> simp at hx <;>
    (try rcases hx with rfl | rfl) <;> rfl

theorem seg_straight (T : Tab) {u v i : ℕ} : ∀ x ∈ seg T u v i, x.straight = true := by
  intro x hx
  unfold seg at hx
  split_ifs at hx
  · simp at hx; subst hx; rfl
  · obtain ⟨t, -, rfl⟩ := mem_chainOps.mp hx; exact chainOp_straight ..
  · obtain ⟨t, -, rfl⟩ := mem_chainOps.mp hx; exact chainOp_straight ..

theorem mem_segs {T : Tab} {u v : ℕ} {x : CInstr} :
    x ∈ segs T u v ↔ ∃ i < gk u, x ∈ seg T u v i := by
  unfold segs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨i, hi, hx⟩; exact ⟨i, List.mem_range.mp hi, hx⟩
  · rintro ⟨i, hi, hx⟩; exact ⟨i, List.mem_range.mpr hi, hx⟩

theorem rootIns_straight (T : Tab) {u v : ℕ} {z : Bool} : ∀ x ∈ rootIns T u v z, x.straight = true := by
  intro x hx
  unfold rootIns at hx
  split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl <;> rfl

theorem nextOp_straight (u : ℕ) : (nextOp u).straight = true := by
  unfold nextOp; split_ifs <;> rfl

/-- Every op of a group block's straight part is straight. -/
theorem body_straight (T : Tab) (u v : ℕ) (z : Bool) : ∀ x ∈ body T u v z, x.straight = true := by
  intro x hx
  unfold body padOps at hx
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hx
  rcases hx with ((((h | h) | h) | h) | h | h) | h
  · exact tie_straight x h
  · subst h; unfold prodOp; split_ifs <;> rfl
  · obtain ⟨i, -, hi⟩ := mem_segs.mp h; exact seg_straight T x hi
  · exact rootIns_straight T x h
  · rw [h.2]; rfl
  · rw [h.2]; rfl
  · subst h; exact nextOp_straight u

theorem tie_len (u v : ℕ) : (tie u v).length = if u ≠ 0 ∧ v ≠ 0 then 2 else 1 := by
  unfold tie; split_ifs <;> simp_all

theorem tie_lcost (u v : ℕ) : lcost (tie u v) = (tie u v).length := by
  unfold tie; split_ifs <;> rfl

theorem seg_len (T : Tab) (u v i : ℕ) :
    (seg T u v i).length = T u v i + (if copied u i ∧ T u v i = 0 then 1 else 0) := by
  unfold seg; split_ifs with h1 h2 <;> simp_all [chainOps_length]

theorem seg_lcost (T : Tab) (u v i : ℕ) :
    lcost (seg T u v i) = 10 * T u v i + (if copied u i ∧ T u v i = 0 then 1 else 0) := by
  unfold seg
  by_cases h1 : copied u i
  · rw [if_pos h1]
    by_cases h2 : T u v i = 0
    · rw [if_pos h2, if_pos ⟨h1, h2⟩, h2]; rfl
    · rw [if_neg h2, chainOps_lcost, if_neg (fun h => h2 h.2), Nat.add_zero]
  · rw [if_neg h1, chainOps_lcost, if_neg (fun h => h1 h.1), Nat.add_zero]

theorem segs_len (T : Tab) (u v : ℕ) : (segs T u v).length = cost T u v + zexp T u v := by
  unfold segs cost zexp
  rw [List.length_flatMap, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  exact seg_len T u v i

theorem segs_lcost (T : Tab) (u v : ℕ) : lcost (segs T u v) = 10 * cost T u v + zexp T u v := by
  unfold segs cost zexp
  rw [lcost_flatMap, ← List.sum_map_mul_left, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  exact seg_lcost T u v i

theorem rootIns_len (T : Tab) (u v : ℕ) (z : Bool) : (rootIns T u v z).length = hm u := by
  unfold rootIns hm; split_ifs <;> (try omega) <;> rfl

theorem rootIns_lcost (T : Tab) (u v : ℕ) (z : Bool) : lcost (rootIns T u v z) = 10 * hm u := by
  unfold rootIns hm; split_ifs <;> (try omega) <;> rfl

/-- Home groups copy nothing: their zero-digit tops are read from the signature cells. -/
theorem zexp_home (T : Tab) {u v : ℕ} (hu : ¬ isExp u) : zexp T u v = 0 := by
  have hcopy : ∀ i, ¬ copied u i := fun _ => hu
  simp [zexp, hcopy]

/-- A tuple of positive cost has at most `gk u − 1` zero coordinates. -/
theorem zexp_le (T : Tab) (u v : ℕ) (hc : 1 ≤ cost T u v) : zexp T u v + 1 ≤ gk u := by
  unfold cost at hc
  unfold zexp
  unfold gk at hc ⊢
  split_ifs at hc ⊢ <;>
    simp only [show List.range 3 = [0, 1, 2] from rfl, show List.range 4 = [0, 1, 2, 3] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc ⊢ <;>
    split_ifs <;> omega

theorem zexp_le_gk (T : Tab) (u v : ℕ) : zexp T u v ≤ gk u := by
  unfold zexp gk
  split_ifs <;>
    simp only [show List.range 3 = [0, 1, 2] from rfl, show List.range 4 = [0, 1, 2, 3] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
    split_ifs <;> omega

theorem fbody_len (s : ℕ) : (fbody s).length = 3+s := by
  unfold fbody
  simp only [List.length_append,chainOps_length,List.length_cons,List.length_nil]
  omega

theorem fbody_lcost (s : ℕ) : lcost (fbody s) = 3+10*s := by
  unfold fbody
  rw [lcost_append,lcost_append,chainOps_lcost]
  have h1 : lcost [.setc (gpCell 0) (ofK (LeanIsaFieldRescale.initialProduct 80 s))] = 1 := rfl
  have h2 : lcost [copy (if s = 0 then wCell 0 else tfCell) tfCell,.mul (hCell 1) gCell (h1Cell 1)] = 2 := rfl
  rw [h1,h2]
  omega

theorem fbody_straight (s : ℕ) : ∀ x ∈ fbody s, x.straight = true := by
  intro x hx
  unfold fbody at hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with (rfl | h) | rfl | rfl
  · rfl
  · obtain ⟨t,-,rfl⟩ := mem_chainOps.mp h
    exact chainOp_straight ..
  · rfl
  · rfl

theorem origin_count : ∀ u < 13, pn u 0 ≤ 1 := by decide

/-- A nonzero raw field cannot encode an origin tuple. -/
theorem band_pos {u v : ℕ} (hu : u < 13) (hv : v < VF u) (hz : v ≠ 0) :
    1 ≤ band u v := by
  obtain ⟨-,-,h2⟩ := band_spec hu hv
  by_contra hn
  have hb : band u v = 0 := by omega
  rw [hb,A_succ,show A u 0 = 0 from rfl,Nat.zero_add] at h2
  have := origin_count u hu
  omega

/-- The binding units have no cost-0 tuple. -/
theorem origin_empty : ∀ u < 13, (u = 0 ∨ 5 ≤ u) → pn u 0 = 0 := by decide

/-- Every live tuple of a binding unit has positive cost. -/
theorem bind_band_pos {u v : ℕ} (hu : u < 13) (hb : u = 0 ∨ 5 ≤ u) (hv : v < VF u) :
    1 ≤ band u v := by
  obtain ⟨-,-,h2⟩ := band_spec hu hv
  by_contra hn
  have hz : band u v = 0 := by omega
  rw [hz,A_succ,show A u 0 = 0 from rfl,origin_empty u hu hb] at h2
  omega

theorem bind_cost_pos {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hb : u = 0 ∨ 5 ≤ u)
    (hv : v < VF u) : 1 ≤ cost T u v := by
  rw [hT.cost_eq u hu v hv]; exact bind_band_pos hu hb hv

/-- The fixed ordinary-instruction allowance includes all zero-digit copies. -/
theorem pad_fit0 {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    (tie u v).length + zexp T u v + 4 ≤ gcu u := by
  rw [tie_len]
  have hgcu : gcu u = if u = 0 then 7 else if u = 6 then 9 else if u = 5 then 6 else 8 := by
    unfold gcu
    by_cases h : isExp u <;> simp only [h, if_true, if_false] <;> unfold isExp at h <;>
      split_ifs <;> omega
  have hgk : gk u = if u = 5 ∨ u = 6 then 4 else 3 := rfl
  have hk := zexp_le_gk T u v
  have h5 : u ≠ 5 ∨ zexp T u v = 0 := by
    by_cases h : u = 5
    · exact Or.inr (zexp_home T (by unfold isExp; omega))
    · exact Or.inl h
  rw [hgcu]; rw [hgk] at hk
  by_cases hb : u = 0 ∨ 5 ≤ u
  · have hh := zexp_le T u v (bind_cost_pos hT hu hb hv)
    rw [hgk] at hh
    split_ifs at * <;> omega
  · by_cases hz : v = 0
    · split_ifs at * <;> omega
    · have hh := zexp_le T u v (by rw [hT.cost_eq u hu v hv]; exact band_pos hu hv hz)
      rw [hgk] at hh
      split_ifs at * <;> omega

/-- Unshifted units stay below cost `15`. -/
theorem nb_unshifted : ∀ u < 13, ¬ shifted u → nb u ≤ 15 := by decide

/-- A product exponent `15` occurs only at cost `16` of a shifted unit, whose digits are at most
`15`, so the block has at most one zero digit. -/
theorem split15_spec {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hv : v < VF u)
    (h : split15 T u v = 1) : shifted u ∧ zexp T u v ≤ 1 := by
  have hp : pcost T u v = 15 := by unfold split15 at h; split_ifs at h with h' <;> omega
  have hb := (band_spec hu hv).1
  have hc := hT.cost_eq u hu v hv
  by_cases hs : shifted u
  · refine ⟨hs, ?_⟩
    have h7 : 7 ≤ u := by unfold shifted at hs; omega
    have hgk : gk u = 3 := by unfold gk; rw [if_neg (by omega)]
    have hVF := VF_le u hu
    have hd := fun i hi => hT.coord_lt16 u hu h7 v (by omega) i hi
    have h0 := hd 0 (by omega); have h1 := hd 1 (by omega); have h2 := hd 2 (by omega)
    unfold pcost at hp; rw [if_pos hs] at hp
    unfold cost at hp; unfold zexp
    rw [hgk] at hp ⊢
    simp only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hp ⊢
    split_ifs <;> omega
  · unfold pcost at hp; rw [if_neg hs] at hp
    have := nb_unshifted u hu hs
    omega

/-- The fixed ordinary-instruction allowance includes all zero-digit copies and the second
product factor. -/
theorem pad_fit {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    (tie u v).length + zexp T u v + split15 T u v + 4 ≤ gcu u := by
  by_cases h15 : split15 T u v = 1
  · obtain ⟨hs, hz⟩ := split15_spec hT hu hv h15
    have ht := tie_len u v
    have hg : gcu u = 8 := by
      unfold shifted at hs; unfold gcu isExp
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> rfl
    split_ifs at ht <;> omega
  · have h0 : split15 T u v = 0 := by unfold split15 at *; split_ifs at * <;> omega
    rw [h0]
    have := pad_fit0 hT hu hv
    omega

theorem body_len {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    (body T u v z).length = gcu u - 2 + cost T u v + hm u := by
  have hfit := pad_fit hT hu hv
  unfold body padOps npad
  simp only [List.length_append, List.length_singleton, List.length_replicate, segs_len,
    rootIns_len]
  omega

theorem body_lcost {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    lcost (body T u v z) = gcu u - 2 + 10 * (cost T u v + hm u) := by
  have hfit := pad_fit hT hu hv
  unfold body padOps npad
  rw [lcost_append, lcost_append, lcost_append, lcost_append, lcost_append, lcost_append, tie_lcost,
    segs_lcost, rootIns_lcost, lcost_replicate, lcost_replicate]
  have h1 : lcost [prodOp T u v] = 1 := by unfold prodOp; split_ifs <;> rfl
  have h4 : (fixOp u).cost = 1 := rfl
  have h2 : lcost [nextOp u] = 1 := by unfold nextOp; split_ifs <;> rfl
  have h3 : NOP.cost = 1 := rfl
  rw [h1, h2, h3, h4]
  omega

theorem proList_length : proList.length = 18 := by unfold proList; rfl

theorem proList_lcost : lcost proList = 27 := by unfold proList lcost; rfl

theorem cinstrAt_sentinel (T : Tab) : cinstrAt T sentinel = .pad := by
  unfold cinstrAt
  norm_num [sentinel,gEnd,baseF]

theorem valid (T : Tab) : LeanIsa.BytecodeValid (program T) := by
  refine ⟨le_refl _,?_⟩
  show (cinstrAt T (2^18-1)).toInstr.opcode ≠ .jump
  rw [show 2^18-1 = sentinel from rfl,cinstrAt_sentinel]
  decide

end OptimalOTS.HLFusion
