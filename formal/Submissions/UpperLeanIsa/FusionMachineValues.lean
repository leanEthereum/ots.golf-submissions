import Submissions.UpperLeanIsa.FusionMachineCycles
import Submissions.UpperLeanIsa.FusionCorrectness

/-! The cell values along a completing path implement the dependency-aware chains. -/
set_option maxRecDepth 2000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

namespace OptimalOTS.HLFusion
open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV hi_append_lo out_pair natV_add_disjoint)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
variable {T : Tab} {P : Fusion.Params}

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

theorem chainValue_of_seq (f : HashTable) (P : Fusion.Params) (ctx : Fusion.Tops) (k : Fin numChains) :
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

def topsV (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) : Fusion.Tops :=
  fun k => if k < 42 then cellBits (v (rtopCell k (dg T xs k))) else 0

theorem topsV_at (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) {k : ℕ} (hk : k < 42) :
    topsV T v xs k = cellBits (v (rtopCell k (dg T xs k))) := by simp only [topsV,if_pos hk]

theorem topsV_top (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) {k : ℕ} (hk : k < 42) (he : exported k) :
    topsV T v xs k = cellBits (v (topCell k)) := by rw [topsV_at T v xs hk,rtopCell_exported he]

theorem binds_owner : ∀ k : Fin 42, binds k.val ↔ Fusion.owner k ≠ none := by decide

theorem fusion_cells : ∀ k : Fin 42, ∀ u : Fin 6, Fusion.owner k = some u →
    depCv k.val = topCell ((Fusion.children u).getD 0 0) ∧
    depCv k.val+1 = topCell ((Fusion.children u).getD 1 0) ∧
    ∀ i < 5, depTop k.val i = (Fusion.children u).getD i 0 ∧
      exported ((Fusion.children u).getD i 0) ∧ (Fusion.children u).getD i 0 < 42 := by decide

section Path
variable {f : HashTable} {v : ℕ → E} {xs : ℕ → ℕ}
  (hV : Valid xs) (hP : PathFacts T (oracleRel f) v xs)


include hP in
theorem v_one : v oneCell = oneV := (hP.pro _ pro_mem_init).1
include hP in
theorem v_len : v lenCell = natV 5503 := (hP.pro _ pro_mem_init).2
include hP in
theorem v_g : v gCell = gV := hP.pro _ pro_mem_g

theorem pro_mem_extra {c : ℕ} (hlo : 17 ≤ c) (hhi : c ≤ 22) :
    CInstr.setc (cCell c) (cV c) ∈ proList := by
  unfold proList
  simp only [List.mem_append,List.mem_map]
  left; right; refine ⟨c,?_,rfl⟩
  simp only [List.mem_cons,List.mem_singleton]
  omega

include hP in
theorem v_c {c : ℕ} (hc : c ≤ 22) : v (cCell c) = cV c := by
  by_cases hh : c ≤ 16
  · exact cCell_val hP.pro hh
  · exact hP.pro _ (pro_mem_extra (by omega) hc)

include hP in
theorem cb_cv (hC : Compat P T) : cellBits (v (oneCell+1)) ++ cellBits (v oneCell) = P.codec.cv := by
  rw [show oneCell+1 = gCell from rfl,v_g hP,v_one hP,hC.cv]

attribute [local irreducible] Fusion.tagWord LeanIsaFieldRescale.costFactor

theorem factor_bits (i : Fin 47) (hi : i.val < 45) : cellBits (cV i.val) = Fusion.tagWord i := by
  rw [Fusion.tagWord_small i hi,cV,HLG3.cellBits_ofK]
  unfold LeanIsaFieldRescale.costFactor
  rfl

theorem sentinel_bits : cellBits (ofK (gpow sentinel)) = Fusion.tagWord 46 := by
  rw [HLG3.cellBits_ofK]
  unfold Fusion.tagWord Fusion.domainTag
  rw [if_neg (by decide),if_neg (by decide)]
  rfl

theorem length_bits : cellBits (natV 5503) = Fusion.tagWord 45 := by
  rw [HLG3.cellBits_natV]
  unfold Fusion.tagWord Fusion.domainTag
  rw [if_neg (by decide),if_pos (by rfl)]
  rfl

include hP in
theorem fusedMd_cell (hC : Compat P T) (k : Fin 42) (hk : binds k.val) :
    cellBits (v (fusedMdCell k.val)) = P.fusedMd k := by
  rw [hC.fusedMd]
  have hsmall : ∀ k : Fin 42, binds k.val → k.val ≠ 5 → k.val ≠ 6 →
      fusedMdCell k.val = cCell (Fusion.tagIndex k).val ∧ (Fusion.tagIndex k).val ≤ 22 := by decide
  by_cases h5 : k.val = 5
  · have he : k = 5 := Fin.ext h5
    subst k
    change cellBits (v lenCell) = Fusion.tagWord 45
    rw [v_len hP,length_bits]
  · by_cases h6 : k.val = 6
    · have he : k = 6 := Fin.ext h6
      subst k
      change cellBits (v (gpCell 13)) = Fusion.tagWord 46
      rw [hP.gp13,sentinel_bits]
    · obtain ⟨he,hi⟩ := hsmall k hk h5 h6
      rw [he,v_c hP hi,factor_bits _ (by omega)]

include hP in
theorem fusion_query (hC : Compat P T) (k : Fin 42) (u : Fin 6) (hu : Fusion.owner k = some u) (x : E) :
    blake2sQuery ![x,v (topCell (depTop k.val 2)),v (topCell (depTop k.val 3)),v (topCell (depTop k.val 4))]
      (v (depCv k.val)) (v (depCv k.val+1)) (v (fusedMdCell k.val)) =
      Fusion.packet (Fusion.fusionWords (topsV T v xs) u (cellBits x) (P.fusedMd k)) := by
  obtain ⟨hc0,hc1,hd⟩ := fusion_cells k u hu
  have hk : binds k.val := (binds_owner k).mpr (by rw [hu]; simp)
  rw [blake2sQuery_eq,hc1,hc0,fusedMd_cell hP hC k hk]
  unfold Fusion.packet Fusion.fusionWords
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val,Fin.isValue]
  rw [(hd 2 (by omega)).1,(hd 3 (by omega)).1,(hd 4 (by omega)).1]
  rw [topsV_top T v xs (hd 0 (by omega)).2.2 (hd 0 (by omega)).2.1,
    topsV_top T v xs (hd 1 (by omega)).2.2 (hd 1 (by omega)).2.1,
    topsV_top T v xs (hd 2 (by omega)).2.2 (hd 2 (by omega)).2.1,
    topsV_top T v xs (hd 3 (by omega)).2.2 (hd 3 (by omega)).2.1,
    topsV_top T v xs (hd 4 (by omega)).2.2 (hd 4 (by omega)).2.1]
  rfl

theorem chainOp_plain_query (hP : PathFacts T (oracleRel f) v xs) (hC : Compat P T) {k : ℕ}
    (hk : k < 42) {d t : ℕ} (hd : d < LEN k) (ht : t < d) (x : E) :
    blake2sQuery ![x, v (cCell (tpos k d t % 9)), v (cCell (tpos k d t / 9 % 9)),
        v (cCell (tpos k d t / 81))] (v oneCell) (v (oneCell + 1)) (v oneCell) =
      P.codec.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t) (cellBits x) := by
  have hj : LEN k - 1 - d + t + 1 < LEN k := by omega
  obtain ⟨h0, h1, h2⟩ := hC.tag ⟨k, hk⟩ _ hj
  have hp : tpos k d t / 81 ≤ 16 := by
    have := OFFT_bound k hk; unfold tpos; omega
  rw [blake2sQuery_eq, v_c hP (c := tpos k d t % 9) (by omega),
    v_c hP (c := tpos k d t / 9 % 9) (by omega), v_c hP (by omega : tpos k d t / 81 ≤ 22), cb_cv hP hC, v_one hP]
  unfold Params.chainInput
  rw [h0, h1, h2, hC.chainMd]
  rfl

include hP in
theorem chainOp_pair (hC : Compat P T) {k d t dst : ℕ} (hk : k < 42)
    (hd : d < LEN k) (ht : t < d) (h : (chainOp k d t dst).Rel f v) :
    let out := if t+1=d then dst-topOff k else xcCell k t
    cellBits (v (out+1)) ++ cellBits (v out) = f ⟨896,
      P.chainInput (topsV T v xs) ⟨k,hk⟩ (LEN k-1-d+t)
        (cellBits (v (if t=0 then wCell k else xcCell k (t-1))))⟩ := by
  have ha : P.active ⟨k,hk⟩ (LEN k-1-d+t) = if t+1=d then Fusion.owner ⟨k,hk⟩ else none := by
    unfold Fusion.Params.active
    rw [hC.len]
    have he : LEN k-1-d+t+2 = LEN k ↔ t+1=d := by omega
    simp only [Fin.val_mk,he]
  dsimp only
  unfold chainOp at h
  dsimp only at h
  by_cases hb : t+1=d ∧ binds k
  · rw [if_pos hb] at h
    obtain ⟨u,hu⟩ : ∃ u, Fusion.owner ⟨k,hk⟩ = some u :=
      Option.ne_none_iff_exists'.mp ((binds_owner ⟨k,hk⟩).mp hb.2)
    have hp := oracle_pair h
    rw [fusion_query hP hC ⟨k,hk⟩ u hu] at hp
    have hs : P.active ⟨k,hk⟩ (LEN k-1-d+t) = some u := by
      rw [ha,if_pos hb.1,hu]
    rw [Fusion.Params.chainInput,hs]
    exact hp
  · rw [if_neg hb] at h
    have hp := oracle_pair h
    rw [chainOp_plain_query hP hC hk hd ht] at hp
    have hn : P.active ⟨k,hk⟩ (LEN k-1-d+t) = none := by
      rw [ha]
      split_ifs with hh
      · have hn : ¬ binds k := by tauto
        by_contra hh
        exact hn ((binds_owner ⟨k,hk⟩).mpr hh)
      · rfl
    rw [Fusion.Params.chainInput,hn]
    exact hp

def chainSeq (v : ℕ → E) (k d dst : ℕ) (t : ℕ) : Word :=
  cellBits (v (if t = 0 then wCell k else if t = d then dst else xcCell k (t - 1)))

theorem stepOff_eq (hC : Compat P T) {k d t : ℕ} (hk : k < 42) (hd : d < LEN k)
    (ht : t < d) : P.codec.stepOff ⟨k, hk⟩ (LEN k - 1 - d + t) =
      if t + 1 = d then 128 * topOff k else 0 := by
  unfold Params.stepOff
  rw [hC.hiTop, hC.len]
  have he : LEN k - 1 - d + t + 2 = LEN k ↔ t + 1 = d := by omega
  simp only [Fin.val_mk, decide_eq_true_eq, he]
  unfold topOff
  split_ifs <;> simp_all

theorem topCell_pos {k : ℕ} (hk : k < 42) : 1 ≤ topCell k := by
  have hh : ∀ k < 42, 1 ≤ topCell k := by decide
  exact hh k hk

theorem xhCell_pos {k : ℕ} (hk : k < 42) (hk0 : k ≠ 0) (he : ¬ exported k) : 1 ≤ xhCell k := by
  have h : ∀ k < 42, k ≠ 0 → ¬ exported k → 1 ≤ xhCell k := by decide
  exact h k hk hk0 he

include hP in
/-- **Chain value.** The `d` steps of chain `k` compute the verifier's chain from the revealed
word into `dst`. -/
theorem chain_val (hC : Compat P T) {k d dst : ℕ} (hk : k < 42) (hd : d < LEN k) (hd0 : d ≠ 0) (hdst : 1 ≤ dst)
    (hs : ∀ t < d, (chainOp k d t dst).Rel f v) :
    cellBits (v dst) = P.chainValue f (topsV T v xs) ⟨k, hk⟩ (LEN k - 1 - d) d (cellBits (v (wCell k))) := by
  have hstep : ∀ t < d, chainSeq v k d dst (t + 1) =
      P.codec.slice ⟨k, hk⟩ (LEN k - 1 - d + t)
        (f ⟨896, P.chainInput (topsV T v xs) ⟨k, hk⟩ (LEN k - 1 - d + t) (chainSeq v k d dst t)⟩) := by
    intro t ht
    have h := hs t ht
    have hp := chainOp_pair hP hC hk hd ht h
    have hlo := congrArg (fun a : BitVec 256 => a.extractLsb' 0 128) hp
    have hhi := congrArg (fun a : BitVec 256 => a.extractLsb' 128 128) hp
    simp only [BitVec.extractLsb'_append_eq_right] at hlo
    simp only [BitVec.extractLsb'_append_eq_left] at hhi
    have hsrc : cellBits (v (if t = 0 then wCell k else xcCell k (t - 1))) = chainSeq v k d dst t := by
      unfold chainSeq
      by_cases h0 : t = 0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0, if_neg (by omega)]
    rw [hsrc] at hlo hhi
    have hout : chainSeq v k d dst (t + 1) = cellBits (v (if t + 1 = d then dst else xcCell k t)) := by
      unfold chainSeq; rw [if_neg (by omega)]
      by_cases h' : t + 1 = d
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h', Nat.add_sub_cancel]
    rw [hout, Params.slice, stepOff_eq hC hk hd ht]
    by_cases hlast : t + 1 = d
    · rw [if_pos hlast] at hlo hhi ⊢
      have hoff := topOff_le k
      by_cases hz : topOff k = 0
      · simpa only [Word,hz, Nat.sub_zero, Nat.mul_zero, if_pos hlast] using hlo
      · have ho : topOff k = 1 := by omega
        simpa only [Word,ho, Nat.mul_one, Nat.sub_add_cancel hdst, if_pos hlast] using hhi
    · rw [if_neg hlast] at hlo ⊢
      simpa only [Word,if_neg hlast] using hlo
  have hend := chainValue_of_seq f P (topsV T v xs) ⟨k, hk⟩ d (LEN k - 1 - d) (chainSeq v k d dst) hstep
  have hl : chainSeq v k d dst d = cellBits (v dst) := by
    unfold chainSeq; rw [if_neg hd0, if_pos rfl]
  have h0 : chainSeq v k d dst 0 = cellBits (v (wCell k)) := by unfold chainSeq; rw [if_pos rfl]
  rw [hl, h0] at hend
  exact hend

include hV hP in
/-- **Chain tops.** The root reads the verifier's chain top of chain `k`. -/
theorem top_eq (hT : T.Hyp) (hC : Compat P T) {k : ℕ} (hk : k < 42) :
    cellBits (v (rtopCell k (dg T xs k))) =
      P.chainValue f (topsV T v xs) ⟨k, hk⟩ (LEN k - 1 - dg T xs k) (dg T xs k) (cellBits (v (wCell k))) := by
  have hd := dg_lt hT hV hk
  by_cases hk0 : k = 0
  · subst hk0
    have hx0 : xs 0 < 64 := by have := hV 0 (by omega); rwa [Wf_zero] at this
    have hb := hP.blk 0 (by omega)
    rw [bodyF_frU_zero] at hb
    rw [show dg T xs 0 = xs 0 from if_pos rfl]
    have hb' : ∀ y ∈ fbody (xs 0), y.Rel f v := hb
    unfold fbody at hb'
    have hrt : rtopCell 0 (xs 0) = tfCell := by simp [rtopCell,exported,topCell,tfCell]
    rw [hrt]
    by_cases hs0 : xs 0 = 0
    · have h : v tfCell = v (wCell 0) * v oneCell := hb' (copy (wCell 0) tfCell) (by simp [hs0])
      rw [h,v_one hP,mul_oneV,hs0]; rfl
    · refine chain_val hP hC (by omega) hd hs0 (by decide) (fun t ht => hb' _ ?_)
      simp only [List.mem_append,List.mem_singleton]
      left; right; exact mem_chainOps.mpr ⟨t,ht,rfl⟩
  · obtain ⟨hu, hi, hc⟩ := chainOf_unitOf k hk (by omega)
    set u := unitOf k with hudef
    set i := coordOf k with hidef
    have hdk : dg T xs k = T u (xs (u + 1)) i := by rw [← hc, dg_chainOf T xs hu hi]
    have hb : ∀ y ∈ seg T u (xs (u + 1)) i, y.Rel f v := fun y hy =>
      hP.blk (u + 1) (by omega) y (by
        rw [bodyF_frU_succ T _ hu]; unfold body
        simp only [List.mem_append]
        left; left; left; right
        exact mem_segs.mpr ⟨i, hi, hy⟩)
    unfold seg at hb
    rw [hc] at hb
    rw [hdk] at hd ⊢
    by_cases hx : copied u i
    · rw [if_pos hx] at hb
      have he : exported k := by rw [← hc]; exact (exported_iff u hu i hi).mpr hx
      rw [rtopCell_exported he]
      by_cases hd0 : T u (xs (u + 1)) i = 0
      · rw [if_pos hd0] at hb
        have h : v (topCell k) = v (wCell k) * v oneCell := hb (copy (wCell k) (topCell k)) (by simp)
        rw [h, v_one hP, mul_oneV, hd0]; rfl
      · rw [if_neg hd0] at hb
        exact chain_val hP hC hk hd hd0 (topCell_pos hk) (fun t ht => hb _ (mem_chainOps.mpr ⟨t, ht, rfl⟩))
    · rw [if_neg hx] at hb
      have he : ¬ exported k := by rw [← hc]; exact fun h => hx ((exported_iff u hu i hi).mp h)
      unfold rtopCell
      by_cases hd0 : T u (xs (u + 1)) i = 0
      · rw [if_pos ⟨hd0,he⟩,hd0]; rfl
      · rw [if_neg (by tauto : ¬ (T u (xs (u+1)) i = 0 ∧ ¬ exported k))]
        exact chain_val hP hC hk hd hd0 (xhCell_pos hk hk0 he) (fun t ht => hb _ (mem_chainOps.mpr ⟨t, ht, rfl⟩))

include hV hP in
/-- **The tie.** The accumulator after group `u` holds the field values `xs 1, …, xs (u + 1)`. -/
theorem acc_eq : ∀ u < 13,
    v (accCell u) = natV (ofDigitsW gb (fun w => xs (w + 1)) (u + 1)) := by
  have hlt : ∀ w, (fun w => if w < 13 then xs (w + 1) else 0) w < 2 ^ gb w := by
    intro w
    by_cases hw : w < 13
    · simp only [if_pos hw]; have := hV (w + 1) (by omega); rw [Wf_succ hw] at this
      exact lt_of_lt_of_le this (VF_le w hw)
    · simp only [if_neg hw]; positivity
  have hofd : ∀ n ≤ 13, ofDigitsW gb (fun w => xs (w + 1)) n =
      ofDigitsW gb (fun w => if w < 13 then xs (w + 1) else 0) n := by
    intro n hn
    unfold ofDigitsW
    exact Finset.sum_congr rfl fun w hw => by
      simp only [if_pos (show w < 13 by have := Finset.mem_range.mp hw; omega)]
  intro u
  induction u with
  | zero =>
    intro hu
    have hb := hP.blk 1 (by omega)
    rw [bodyF_frU_succ T _ (u := 0) (by omega)] at hb
    have h : v (accCell 0) = fpat 0 (xs (0 + 1)) := hb (.setc (accCell 0) (fpat 0 (xs (0 + 1)))) (by
      unfold body tie; simp)
    rw [h, ofDigitsW_succ, ofDigitsW_zero]
    unfold fpat POS; simp only [Nat.zero_add]
  | succ u ih =>
    intro hu
    have hb := hP.blk (u + 2) (by omega)
    rw [show u + 2 = (u + 1) + 1 by ring, bodyF_frU_succ T _ (by omega)] at hb
    have hmem : ∀ y ∈ tie (u + 1) (xs (u + 1 + 1)), y.Rel f v := fun y hy => hb y (by
      unfold body; simp only [List.mem_append]; left; left; left; left; left; exact hy)
    unfold tie at hmem
    rw [if_neg (by omega), Nat.add_sub_cancel] at hmem
    have hprev := ih (by omega)
    have hl1 := ofDigitsW_lt gb _ hlt (u + 1)
    have hl2 := ofDigitsW_lt gb _ hlt (u + 1 + 1)
    have hpos : 2 ^ posW gb (u + 1 + 1) ≤ 2 ^ 128 := by
      rw [← POS_13]; exact Nat.pow_le_pow_right (by norm_num) (posW_mono gb (by omega))
    rw [← hofd _ (by omega)] at hl1 hl2
    by_cases hx0 : xs (u + 1 + 1) = 0
    · rw [if_pos hx0] at hmem
      have h : v (accCell (u + 1)) = v (accCell u) * v oneCell :=
        hmem (copy (accCell u) (accCell (u + 1))) (by simp)
      rw [h, v_one hP, mul_oneV, hprev, ofDigitsW_succ _ _ (u + 1)]
      simp [hx0]
    · rw [if_neg hx0] at hmem
      have ht : v (tCell (u + 1)) = fpat (u + 1) (xs (u + 1 + 1)) :=
        hmem (.setc (tCell (u + 1)) (fpat (u + 1) (xs (u + 1 + 1)))) (by simp)
      have hx : v (accCell (u + 1)) = v (accCell u) + v (tCell (u + 1)) :=
        hmem (.xor (accCell u) (tCell (u + 1)) (accCell (u + 1))) (by simp)
      rw [hx, ht, hprev]
      unfold fpat POS
      rw [ofDigitsW_succ _ _ (u + 1)] at hl2 ⊢
      exact natV_add_disjoint hl1 (by omega)

end Path
end
end OptimalOTS.HLFusion
