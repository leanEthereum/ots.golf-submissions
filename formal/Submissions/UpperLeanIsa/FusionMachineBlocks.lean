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
  unfold body at hx
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hx
  rcases hx with ((((h | h) | h) | h) | h) | h
  · exact tie_straight x h
  · subst h; rfl
  · obtain ⟨i, -, hi⟩ := mem_segs.mp h; exact seg_straight T x hi
  · exact rootIns_straight T x h
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

theorem zexp_le (T : Tab) (u v : ℕ) (hc : 1 ≤ cost T u v) : zexp T u v ≤ 2 := by
  by_cases hu : isExp u
  · have hk : gk u = 3 := by unfold gk; rw [if_neg (by unfold isExp at hu; omega)]
    have hcopy : ∀ i, copied u i := fun _ => hu
    unfold cost at hc
    simp only [zexp, hk, hcopy, true_and, show List.range 3 = [0, 1, 2] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc ⊢
    split_ifs <;> omega
  · rw [zexp_home T hu]; omega

theorem zexp_le3 (T : Tab) (u v : ℕ) : zexp T u v ≤ 3 := by
  by_cases hu : isExp u
  · have hk : gk u = 3 := by unfold gk; rw [if_neg (by unfold isExp at hu; omega)]
    have hcopy : ∀ i, copied u i := fun _ => hu
    simp only [zexp, hk, hcopy, true_and, show List.range 3 = [0, 1, 2] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega
  · rw [zexp_home T hu]; omega

theorem fbody_len (s : ℕ) : (fbody s).length = 3+s := by
  unfold fbody
  simp only [List.length_append,chainOps_length,List.length_cons,List.length_nil]
  omega

theorem fbody_lcost (s : ℕ) : lcost (fbody s) = 3+10*s := by
  unfold fbody
  rw [lcost_append,lcost_append,chainOps_lcost]
  have h1 : lcost [.setc (gpCell 0) (ofK (LeanIsaFieldRescale.initialProduct 86 s))] = 1 := rfl
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

theorem origin_first : pn 0 0 = 0 := rfl

/-- A nonzero raw field cannot encode an origin tuple. -/
theorem band_pos {u v : ℕ} (hu : u < 13) (hv : v < VF u) (hz : v ≠ 0) :
    1 ≤ band u v := by
  obtain ⟨-,-,h2⟩ := band_spec hu hv
  by_contra hn
  have hb : band u v = 0 := by omega
  rw [hb,A_succ,show A u 0 = 0 from rfl,Nat.zero_add] at h2
  have := origin_count u hu
  omega

theorem first_band_pos {v : ℕ} (hv : v < VF 0) : 1 ≤ band 0 v := by
  obtain ⟨-,-,h2⟩ := band_spec (by decide : 0 < 13) hv
  by_contra hn
  have hb : band 0 v = 0 := by omega
  rw [hb,A_succ,show A 0 0 = 0 from rfl,origin_first] at h2
  omega

/-- The fixed ordinary-instruction allowance includes all zero-digit copies. -/
theorem pad_fit {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    (tie u v).length + zexp T u v + 4 ≤ gcu u := by
  rw [tie_len]
  by_cases h0 : u = 0
  · subst u
    have hc : 1 ≤ cost T 0 v := by rw [hT.cost_eq 0 (by decide) v hv]; exact first_band_pos hv
    have hh := zexp_le T 0 v hc
    simp only [ne_eq,not_true_eq_false,false_and,if_false,gcu,if_true]
    omega
  · by_cases he : isExp u
    · have h3 := zexp_le3 T u v
      have hg : gcu u = 8 := by simp only [gcu,if_neg h0,if_pos he]
      rw [hg]
      by_cases hz : v ≠ 0
      · have hc : 1 ≤ cost T u v := by rw [hT.cost_eq u hu v hv]; exact band_pos hu hv hz
        have hh := zexp_le T u v hc
        split_ifs <;> omega
      · split_ifs <;> omega
    · have hz := zexp_home T (v := v) he
      simp only [gcu,if_neg h0,if_neg he]
      split_ifs <;> omega

theorem body_len {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    (body T u v z).length = gcu u - 2 + cost T u v + hm u := by
  have hfit := pad_fit hT hu hv
  unfold body npad
  simp only [List.length_append, List.length_singleton, List.length_replicate, segs_len,
    rootIns_len]
  omega

theorem body_lcost {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    lcost (body T u v z) = gcu u - 2 + 10 * (cost T u v + hm u) := by
  have hfit := pad_fit hT hu hv
  unfold body npad
  rw [lcost_append, lcost_append, lcost_append, lcost_append, lcost_append, tie_lcost,
    segs_lcost, rootIns_lcost, lcost_replicate]
  have h1 : lcost [prodOp T u v] = 1 := rfl
  have h2 : lcost [nextOp u] = 1 := by unfold nextOp; split_ifs <;> rfl
  have h3 : NOP.cost = 1 := rfl
  rw [h1, h2, h3]
  omega


theorem proList_length : proList.length = 25 := by unfold proList; rfl

theorem proList_lcost : lcost proList = 34 := by unfold proList lcost; rfl

theorem cinstrAt_sentinel (T : Tab) : cinstrAt T sentinel = .pad := by
  unfold cinstrAt
  norm_num [sentinel,gEnd,baseF]

theorem valid (T : Tab) : LeanIsa.BytecodeValid (program T) := by
  refine ⟨le_refl _,?_⟩
  show (cinstrAt T (2^18-1)).toInstr.opcode ≠ .jump
  rw [show 2^18-1 = sentinel from rfl,cinstrAt_sentinel]
  decide

/-- This is the cost of the intended walk, with dispatch charging its landing entry. -/
def canonicalCost (T : Tab) (xs : ℕ → ℕ) : ℕ :=
  lcost proList + 2 + lcost (fbody (xs 0)) + 2 +
    ∑ u ∈ Finset.range 13, (lcost (body T u (xs (u+1)) false) + (ctlF (u+1)).cost)

def canonicalSteps (T : Tab) (xs : ℕ → ℕ) : ℕ :=
  proList.length + 2 + (fbody (xs 0)).length + 2 +
    ∑ u ∈ Finset.range 13, ((body T u (xs (u+1)) false).length + (ctlF (u+1)).steps)

theorem sum_ordinary_bodies : (∑ u ∈ Finset.range 13, (gcu u - 2)) = 73 := by decide
theorem sum_roots : (∑ u ∈ Finset.range 13, hm u) = 3 := by decide
theorem sum_controls : (∑ u ∈ Finset.range 13, (ctlF (u+1)).cost) = 25 := by decide
theorem sum_control_steps : (∑ u ∈ Finset.range 13, (ctlF (u+1)).steps) = 25 := by decide

theorem canonical_cost (T : Tab) (hT : T.Hyp) (xs : ℕ → ℕ)
    (hx : ∀ u < 13, xs (u+1) < VF u)
    (hlayer : xs 0 + ∑ u ∈ Finset.range 13, cost T u (xs (u+1)) = 86) :
    canonicalCost T xs + 120 = 1149 := by
  have hb : ∀ u ∈ Finset.range 13, lcost (body T u (xs (u+1)) false) =
      gcu u - 2 + 10 * cost T u (xs (u+1)) + 10 * hm u := by
    intro u hu
    rw [body_lcost hT (Finset.mem_range.mp hu) (hx u (Finset.mem_range.mp hu))]
    omega
  unfold canonicalCost
  rw [proList_lcost,fbody_lcost]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl hb]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,sum_ordinary_bodies,sum_roots,sum_controls]
  omega

theorem canonical_steps (T : Tab) (hT : T.Hyp) (xs : ℕ → ℕ)
    (hx : ∀ u < 13, xs (u+1) < VF u)
    (hlayer : xs 0 + ∑ u ∈ Finset.range 13, cost T u (xs (u+1)) = 86) :
    canonicalSteps T xs = 219 := by
  have hb : ∀ u ∈ Finset.range 13, (body T u (xs (u+1)) false).length =
      gcu u - 2 + cost T u (xs (u+1)) + hm u :=
    fun u hu => body_len hT (Finset.mem_range.mp hu) (hx u (Finset.mem_range.mp hu))
  unfold canonicalSteps
  rw [proList_length,fbody_len,Finset.sum_add_distrib,Finset.sum_congr rfl hb]
  simp only [Finset.sum_add_distrib,sum_ordinary_bodies,sum_roots,sum_control_steps]
  omega

theorem seeded_size : 2 ^ (program fusionTab).logSize + 2 ^ 16 < LeanIsa.maxSeededRows := by decide

end OptimalOTS.HLFusion
