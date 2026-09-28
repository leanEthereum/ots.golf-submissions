import Submissions.UpperLeanIsa.PackedSupport
import Submissions.UpperLeanIsa.FourCorrectness

/-! The cell values along a completing path implement the dependency-aware chains. -/
set_option maxRecDepth 2000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

namespace OptimalOTS.HLFour
open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV hi_append_lo out_pair natV_add_disjoint)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
variable {T : Tab} {P : FourFusion.Params}

theorem blake2sQuery_eq (a b c d cv0 cv1 md : E) :
    blake2sQuery ![a, b, c, d] cv0 cv1 md =
      hashInput (cellBits cv1 ++ cellBits cv0) (cellBits d ++ cellBits c ++ cellBits b ++ cellBits a)
        (cellBits md) := rfl

theorem msg_split (a b : BitVec 128) (m : Message) :
    a ++ b ++ m.extractLsb' 128 128 ++ m.extractLsb' 0 128 = a ++ b ++ m := by
  have h := hi_append_lo m
  conv_rhs => rw [← h]
  rw [BitVec.append_assoc (x₁ := a ++ b)]
  exact BitVec.cast_eq _ _

/-- The oracle relation of a `BLAKE2S` gives its low output half. -/
theorem oracle_lo {f : HashTable} {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}
    (h : oracleRel f m cv0 cv1 o0 o1 md) :
    cellBits o0 = (f ⟨896, blake2sQuery m cv0 cv1 md⟩).extractLsb' 0 128 := h.2.2.2.2.2.2.1

/-- The oracle relation of a `BLAKE2S` gives its whole output pair. -/
theorem oracle_pair {f : HashTable} {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}
    (h : oracleRel f m cv0 cv1 o0 o1 md) :
    cellBits o1 ++ cellBits o0 = f ⟨896, blake2sQuery m cv0 cv1 md⟩ :=
  out_pair _ _ _ h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

theorem ofK_one : ofK (1 : K) = 1 := by
  have h := ofK_mul 1 1
  rw [mul_one] at h
  exact (mul_eq_left₀ ofK_one_ne_zero).mp h.symm

theorem mul_oneV (x : E) : x * oneV = x := by unfold oneV; rw [ofK_one, mul_one]

theorem chainValue_of_seq (f : HashTable) (P : FourFusion.Params) (ctx : FourFusion.Tops) (k : Fin numChains) :
    ∀ (n j0 : ℕ) (X : ℕ → Word),
      (∀ t < n, X (t + 1) = P.codec.slice k (j0 + t) (f ⟨896, P.chainInput ctx k (j0 + t) (X t)⟩)) →
        X n = P.chainValue f ctx k j0 n (X 0) := by
  intro n
  induction n with
  | zero => intro j0 X _; rfl
  | succ n ih =>
    intro j0 X h
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    have := ih (j0 + 1) (fun t => X (t + 1)) (fun t ht => by
      rw [h (t + 1) (by omega), show j0 + (t + 1) = j0 + 1 + t by ring])
    rw [this, h0]
    rfl

def dg (T : Tab) (xs : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k = 0 then xs 0 else T (unitOf k) (xs (unitOf k + 1)) (coordOf k)

theorem dg_chainOf (T : Tab) (xs : ℕ → ℕ) {u i : ℕ} (hu : u < 13) (hi : i < gk u) :
    dg T xs (chainOf u i) = T u (xs (u + 1)) i := by
  unfold dg
  rw [if_neg (by have := chainOf_pos u hu i hi; omega), unitOf_chainOf u hu i hi,
    coordOf_chainOf u hu i hi]

/-- Digits are below the chain lengths, for any in-range raw index vector. -/
theorem dg_lt_raw (hT : T.Hyp) {xs : ℕ → ℕ} (h0 : xs 0 < 64) (hr : ∀ u < 13, xs (u + 1) < 2 ^ gb u)
    {k : ℕ} (hk : k < 42) : dg T xs k < LEN k := by
  unfold dg
  split_ifs with hk0
  · subst hk0; exact h0
  · obtain ⟨hu, hi, hc⟩ := chainOf_unitOf k hk (by omega)
    have := hT.coord_lt _ hu _ (hr _ hu) _ hi
    rwa [hc] at this

theorem dg_lt (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs) {k : ℕ} (hk : k < 42) :
    dg T xs k < LEN k :=
  dg_lt_raw hT (by have := hV 0 (by omega); rwa [Wf_zero] at this)
    (fun u hu => by
      have := hV (u + 1) (by omega); rw [Wf_succ hu] at this
      exact lt_of_lt_of_le this (VF_le u hu)) hk

/-- The chain digits regroup into the free digit and the group costs. -/
theorem dg_sum (T : Tab) (xs : ℕ → ℕ) :
    ∑ k ∈ Finset.range 42, dg T xs k = xs 0 + ∑ u ∈ Finset.range 13, cost T u (xs (u + 1)) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, dg, cost, gk, unitOf, coordOf]
  norm_num
  simp only [show List.range 3 = [0, 1, 2] from rfl, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem rtopCell_exported {k d : ℕ} (he : exported k) : rtopCell k d = topCell k := by
  unfold rtopCell; rw [if_neg (by tauto)]

def topsV (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) : FourFusion.Tops :=
  fun k => if k < 42 then cellBits (v (rtopCell k (dg T xs k))) else 0

theorem topsV_at (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) {k : ℕ} (hk : k < 42) :
    topsV T v xs k = cellBits (v (rtopCell k (dg T xs k))) := by simp only [topsV,if_pos hk]

theorem topsV_top (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) {k : ℕ} (hk : k < 42) (he : exported k) :
    topsV T v xs k = cellBits (v (topCell k)) := by rw [topsV_at T v xs hk,rtopCell_exported he]

theorem binds_owner : ∀ k : Fin 42, binds k.val ↔ FourFusion.owner k ≠ none := by decide

theorem chainInput_fused {t : FourFusion.Tops} {k : Fin 42} {j : ℕ} {u : Fin 8}
    (ha : P.active k j = some u) (x : Word) :
    P.chainInput t k j x = FourFusion.packet (FourFusion.fusionWords t u x (P.fusedTag k) (P.fusedMd k)) := by
  unfold FourFusion.Params.chainInput FourFusion.Params.groupInput
  rw [ha]

theorem fusion_cells : ∀ k : Fin 42, binds k.val → ∀ u : Fin 8, FourFusion.owner k = some u →
    depCv k.val = topCell ((FourFusion.children u).getD 0 0) ∧
    depCv k.val+1 = topCell ((FourFusion.children u).getD 1 0) ∧
    ∀ i < (FourFusion.children u).length,
      depTop k.val i = (FourFusion.children u).getD i 0 ∧
      ((internal ((FourFusion.children u).getD i 0) ∧
        unitOf ((FourFusion.children u).getD i 0) = unitOf k.val) ∨
        exported ((FourFusion.children u).getD i 0)) ∧
      (FourFusion.children u).getD i 0 < 42 := by
  have hf : ∀ (k : Fin 42) (u : Fin 8), binds k.val → FourFusion.owner k = some u →
      depCv k.val = topCell ((FourFusion.children u).getD 0 0) ∧
      depCv k.val+1 = topCell ((FourFusion.children u).getD 1 0) ∧
      ∀ i : Fin 5, i.val < (FourFusion.children u).length →
        depTop k.val i = (FourFusion.children u).getD i 0 ∧
        ((internal ((FourFusion.children u).getD i 0) ∧
          unitOf ((FourFusion.children u).getD i 0) = unitOf k.val) ∨
          exported ((FourFusion.children u).getD i 0)) ∧
        (FourFusion.children u).getD i 0 < 42 := by decide
  intro k hk u ho
  have hh := hf k u hk ho
  refine ⟨hh.1,hh.2.1,?_⟩
  intro i hi
  have hl : ∀ u : Fin 8, (FourFusion.children u).length ≤ 5 := by decide
  exact hh.2.2 ⟨i,by have := hl u; omega⟩ hi

theorem fusion_cv_exported : ∀ k : Fin 42, binds k.val → ∀ u : Fin 8,
    FourFusion.owner k = some u →
    exported ((FourFusion.children u).getD 0 0) ∧
    exported ((FourFusion.children u).getD 1 0) := by decide

theorem fiveChildren_owner : ∀ k : Fin 42, ∀ u : Fin 8, FourFusion.owner k = some u →
    (fiveChildren k.val ↔ FourFusion.five u = true) := by decide

theorem internal_facts : ∀ k < 42, internal k → k ≠ 0 ∧ ¬ exported k := by decide

theorem groupRead_rtop (T : Tab) (xs : ℕ → ℕ) {u k : ℕ} (hk : k < 42)
    (hh : (internal k ∧ unitOf k = u) ∨ exported k) :
    groupRead T u (xs (u+1)) k = rtopCell k (dg T xs k) := by
  rcases hh with ⟨hi,hu⟩ | he
  · have hf := internal_facts k hk hi
    simp only [groupRead, hu, hi, true_and, dg, if_neg hf.1, rtopCell, hf.2, not_false_eq_true, and_true]
  · have hn : ¬ internal k := fun hi => (internal_facts k hk hi).2 he
    simp only [groupRead, hn, and_false, false_and, if_false, rtopCell_exported he]

/-- A block's local selector reads the abstract dependency top even when an internal
child has zero remaining steps and is read directly from the signature. -/
theorem groupRead_fusion (T : Tab) (xs : ℕ → ℕ) (v : ℕ → E)
    (k : Fin 42) (hk : binds k.val) (u : Fin 8) (ho : FourFusion.owner k = some u)
    {i : ℕ} (hi : i < (FourFusion.children u).length) :
    cellBits (v (groupRead T (unitOf k.val) (xs (unitOf k.val+1))
      ((FourFusion.children u).getD i 0))) =
      topsV T v xs ((FourFusion.children u).getD i 0) := by
  have hd := (fusion_cells k hk u ho).2.2 i hi
  rw [groupRead_rtop T xs hd.2.2 hd.2.1, topsV_at T v xs hd.2.2]

end
end OptimalOTS.HLFour
