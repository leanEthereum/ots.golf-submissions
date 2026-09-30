import Submissions.UpperLeanIsa.FourMachineProgram

/-! Local block lengths and costs. These bounds will be applied to the certified machine walk. -/
namespace OptimalOTS.HLFour
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

theorem chainOps_length (readTop : ℕ → ℕ) (k d dst : ℕ) : (chainOps readTop k d dst).length = d := by
  unfold chainOps; rw [List.length_map, List.length_range]

theorem chainOps_lcost (readTop : ℕ → ℕ) (k d dst : ℕ) : lcost (chainOps readTop k d dst) = 10 * d := by
  unfold chainOps lcost
  rw [List.map_map]
  have : (CInstr.cost ∘ fun t => chainOp readTop k d t dst) = fun _ => 10 := by
    funext t; dsimp only [Function.comp_def]; unfold chainOp; split_ifs <;> rfl
  rw [this, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, mul_comm]

theorem mem_chainOps {readTop : ℕ → ℕ} {k d dst : ℕ} {x : CInstr} :
    x ∈ chainOps readTop k d dst ↔ ∃ t < d, x = chainOp readTop k d t dst := by
  unfold chainOps
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, List.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, List.mem_range.mpr ht, rfl⟩

theorem chainOp_straight (readTop : ℕ → ℕ) (k d t dst : ℕ) : (chainOp readTop k d t dst).straight = true := by unfold chainOp; split_ifs <;> rfl

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

theorem tie_len (u v : ℕ) : (tie u v).length = if u ≠ 0 ∧ u ≠ 11 ∧ v ≠ 0 then 2 else 1 := by
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
  unfold segs cost zexp copyCount
  rw [List.length_flatMap, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  exact seg_len T u v i

theorem segs_lcost (T : Tab) (u v : ℕ) : lcost (segs T u v) = 10 * cost T u v + zexp T u v := by
  unfold segs cost zexp copyCount
  rw [lcost_flatMap, ← List.sum_map_mul_left, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  exact seg_lcost T u v i

theorem rootIns_len (T : Tab) (u v : ℕ) (z : Bool) : (rootIns T u v z).length = hm u := by
  unfold rootIns hm; split_ifs <;> (try omega) <;> rfl

theorem rootIns_lcost (T : Tab) (u v : ℕ) (z : Bool) : lcost (rootIns T u v z) = 10 * hm u := by
  unfold rootIns hm; split_ifs <;> (try omega) <;> rfl

theorem fbody_len (s : ℕ) : (fbody s).length = 3+s := by
  unfold fbody
  simp only [List.length_append,chainOps_length,List.length_cons,List.length_nil]
  omega

theorem fbody_lcost (s : ℕ) : lcost (fbody s) = 3+10*s := by
  unfold fbody
  rw [lcost_append,lcost_append,chainOps_lcost]
  have h1 : lcost [.setc (gpCell 0) (ofK (LeanIsaFieldRescale.initialProduct 77 s))] = 1 := rfl
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

theorem prodOps_len (T : Tab) (u v : ℕ) :
    (prodOps T u v).length = 1 + extraMul T u v := by
  unfold prodOps extraMul chargedCost
  split_ifs <;> simp

theorem prodOps_lcost (T : Tab) (u v : ℕ) :
    lcost (prodOps T u v) = 1 + extraMul T u v := by
  unfold prodOps extraMul chargedCost prodOp
  split_ifs <;> rfl

theorem prodOps_straight (T : Tab) (u v : ℕ) :
    ∀ x ∈ prodOps T u v, x.straight = true := by
  intro x hx
  unfold prodOps at hx
  split_ifs at hx <;> simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hx
  · rcases hx with rfl | rfl
    · exact prodOp_straight T u v
    · rfl
  · subst x; exact prodOp_straight T u v

theorem body_straight (T : Tab) (u v : ℕ) (z : Bool) :
    ∀ x ∈ body T u v z, x.straight = true := by
  intro x hx
  unfold body at hx
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hx
  rcases hx with ((((h | h) | h) | h) | h) | h
  · exact tie_straight x h
  · exact prodOps_straight T u v x h
  · obtain ⟨i, -, hi⟩ := mem_segs.mp h; exact seg_straight T x hi
  · exact rootIns_straight T x h
  · rw [h.2]; rfl
  · subst h; exact nextOp_straight u

/-- Padding budgets retain the former extra slot on charged costs 15 and 16. -/
theorem pad_fit {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    (tie u v).length + zexp T u v + 4 + extraMul T u v ≤ gcu u := by
  have h := hT.ordinary_le u hu v hv
  rw [tie_len]
  change (if u ≠ 0 ∧ u ≠ 11 ∧ v ≠ 0 then 2 else 1) + copyCount T u v + 4 +
    (if 14 < cost T u v - bindingDeduction u then 1 else 0) ≤ gcu u
  unfold machineOrdinary at h
  have := gcu_ge u
  omega

theorem body_len {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    (body T u v z).length = gcu u - 2 + cost T u v + hm u := by
  have hfit := pad_fit hT hu hv
  unfold body npad
  simp only [List.length_append, List.length_singleton, List.length_replicate, prodOps_len, segs_len,
    rootIns_len]
  omega

theorem body_lcost {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    lcost (body T u v z) = gcu u - 2 + 10 * (cost T u v + hm u) := by
  have hfit := pad_fit hT hu hv
  unfold body npad
  rw [lcost_append, lcost_append, lcost_append, lcost_append, lcost_append, tie_lcost,
    segs_lcost, rootIns_lcost, lcost_replicate]
  have h1 := prodOps_lcost T u v
  have h2 : lcost [nextOp u] = 1 := by unfold nextOp; split_ifs <;> rfl
  have h3 : NOP.cost = 1 := rfl
  rw [h1, h2, h3]
  omega


theorem proList_length : proList.length = 17 := by unfold proList; rfl

theorem proList_lcost : lcost proList = 26 := by unfold proList lcost; rfl

theorem cinstrAt_sentinel (T : Tab) : cinstrAt T sentinel = .pad := by
  unfold cinstrAt
  norm_num [sentinel,gEnd,baseF]

theorem valid (T : Tab) : LeanIsa.BytecodeValid (program T) := by
  refine ⟨le_refl _,?_⟩
  show (cinstrAt T (2^18-1)).toInstr.opcode ≠ .jump
  rw [show 2^18-1 = sentinel from rfl,cinstrAt_sentinel]
  decide

end OptimalOTS.HLFour
