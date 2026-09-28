import Submissions.UpperLeanIsa.AffineCore

/-! Completing affine paths compute the chains and index tie of the secure
abstract codec, with the new domain words. -/
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

namespace OptimalOTS.AffineVM
open OracleComp LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV hi_append_lo out_pair natV_add_disjoint)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
variable {T : Tab} {P : FourFusion.Params}

section Path
variable {f : HashTable} {v : ℕ → E} {xs : ℕ → ℕ}
  (hV : Valid xs) (hP : PathFacts T (oracleRel f) v xs)


include hP in
theorem v_one : v oneCell = oneV := pro_one hP.pro
include hP in
theorem v_len : v lenCell = natV 5504 := pro_length hP.pro

include hP in
theorem v_c {c : ℕ} (hc : c ≤ 13) : v (cCell c) = cV T c := pro_c hP.pro (by omega)

include hP in
theorem cb_cv (hC : Compat P T) : cellBits (v (cCell 1+1)) ++ cellBits (v (cCell 1)) = P.codec.cv := by
  rw [show cCell 1+1 = cCell 2 from rfl,v_c hP (by decide : 2 ≤ 13),
    v_c hP (by decide : 1 ≤ 13),hC.cv]

theorem factor_bits (T : Tab) (i : Fin 47) :
    cellBits (cV T i.val) = AffineCodec.word (layout T) i.val := rfl

include hP in
theorem fusedMd_cell (hC : Compat P T) (k : Fin 42) (_hk : binds k.val) :
    cellBits (v (fusedMdCell k.val)) = P.fusedMd k := by
  rw [hC.fusedMd]
  have he : ∀ k : Fin 42, fusedMdCell k.val =
      if (FourFusion.mdIndex k).val = 17 then lenCell else cCell (FourFusion.mdIndex k).val := by decide
  rw [he]
  unfold AffineCodec.domainWord
  by_cases h17 : (FourFusion.mdIndex k).val = 17
  · rw [if_pos h17, if_pos h17, v_len hP]
    rfl
  · have hi : (FourFusion.mdIndex k).val ≤ 13 := by
      have hb : ∀ k : Fin 42, (FourFusion.mdIndex k).val ≤ 13 ∨
          (FourFusion.mdIndex k).val = 17 := by decide
      exact (hb k).resolve_right h17
    rw [if_neg h17, if_neg h17, v_c hP hi, factor_bits T _]

include hP in
theorem fusedTag_cell (hC : Compat P T) (k : Fin 42) :
    cellBits (v (fusedTagCell k.val)) = P.fusedTag k := by
  rw [hC.fusedTag]
  have hsmall : ∀ k : Fin 42,
      fusedTagCell k.val = cCell (FourFusion.tagIndex k).val ∧ (FourFusion.tagIndex k).val ≤ 13 := by decide
  obtain ⟨he,hi⟩ := hsmall k
  rw [he,v_c hP hi,factor_bits T _]

/-- The selector used by a chain reads every child from its abstract top. -/
def ReadContext (readTop : ℕ → ℕ) (k : Fin 42) : Prop :=
  ∀ u : Fin 8, FourFusion.owner k = some u →
    ∀ i < (FourFusion.children u).length,
      cellBits (v (readTop ((FourFusion.children u).getD i 0))) =
        topsV T v xs ((FourFusion.children u).getD i 0)

include hP in
theorem fusion_query (hC : Compat P T) (readTop : ℕ → ℕ)
    (k : Fin 42) (hk : binds k.val) (u : Fin 8) (hu : FourFusion.owner k = some u)
    (hread : ReadContext (T:=T) (v:=v) (xs:=xs) readTop k) (x : E) :
    blake2sQuery ![x,v (readTop (depTop k.val 2)),v (readTop (depTop k.val 3)),
      v (if fiveChildren k.val then readTop (depTop k.val 4) else fusedTagCell k.val)]
      (v (depCv k.val)) (v (depCv k.val+1)) (v (fusedMdCell k.val)) =
      FourFusion.packet (FourFusion.fusionWords (topsV T v xs) u (cellBits x)
        (P.fusedTag k) (P.fusedMd k)) := by
  obtain ⟨hc0,hc1,hd⟩ := fusion_cells k hk u hu
  obtain ⟨he0,he1⟩ := fusion_cv_exported k hk u hu
  have hl : 4 ≤ (FourFusion.children u).length := by
    have hh : ∀ u : Fin 8, 4 ≤ (FourFusion.children u).length := by decide
    exact hh u
  have h2 := hread u hu 2 (by omega)
  have h3 := hread u hu 3 (by omega)
  rw [blake2sQuery_eq,hc1,hc0,fusedMd_cell hP hC k hk]
  unfold FourFusion.packet Fusion.packet FourFusion.fusionWords
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val,Fin.isValue]
  rw [(hd 2 (by omega)).1,(hd 3 (by omega)).1,h2,h3,
    ← topsV_top T v xs (hd 0 (by omega)).2.2 he0,
    ← topsV_top T v xs (hd 1 (by omega)).2.2 he1]
  by_cases hf : FourFusion.five u = true
  · have hf' := (fiveChildren_owner k u hu).mpr hf
    have hl5 : 4 < (FourFusion.children u).length := by
      rw [Fusion.SplitRoot.packet_lengths u u.isLt, if_pos hf]
      decide
    rw [if_pos hf', if_pos hf, (hd 4 hl5).1, hread u hu 4 hl5]
    rfl
  · have hf' : ¬ fiveChildren k.val := fun hh => hf ((fiveChildren_owner k u hu).mp hh)
    rw [if_neg hf', if_neg hf, fusedTag_cell hP hC k]
    rfl

theorem chainOp_plain_query (hP : PathFacts T (oracleRel f) v xs) (hC : Compat P T) {k : ℕ}
    (hk : k < 42) {d t : ℕ} (hd : d < LEN k) (ht : t < d) (x : E) :
    blake2sQuery ![x, v (cCell (tpos k d t % 9)), v (cCell (tpos k d t / 9 % 9)),
        v (cCell (tpos k d t / 81))] (v (cCell 1)) (v (cCell 1 + 1)) (v oneCell) =
      P.codec.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t) (cellBits x) := by
  have hj : LEN k - 1 - d + t + 1 < LEN k := by omega
  obtain ⟨h0, h1, h2⟩ := hC.tag ⟨k, hk⟩ _ hj
  have hp : tpos k d t / 81 ≤ 13 := by
    have := OFFT_bound k hk; unfold tpos; omega
  rw [blake2sQuery_eq, v_c hP (c := tpos k d t % 9) (by omega),
    v_c hP (c := tpos k d t / 9 % 9) (by omega), v_c hP (by omega : tpos k d t / 81 ≤ 13), cb_cv hP hC, v_one hP]
  unfold Params.chainInput
  rw [h0, h1, h2, hC.chainMd]
  rfl

include hP in
theorem chainOp_pair (hC : Compat P T) (readTop : ℕ → ℕ) {k d t dst : ℕ} (hk : k < 42)
    (hread : ReadContext (T:=T) (v:=v) (xs:=xs) readTop ⟨k,hk⟩)
    (hd : d < LEN k) (ht : t < d) (h : (chainOp readTop k d t dst).Rel f v) :
    let out := if t+1=d then dst-topOff k else xcCell k t
    cellBits (v (out+1)) ++ cellBits (v out) = f ⟨896,
      P.chainInput (topsV T v xs) ⟨k,hk⟩ (LEN k-1-d+t)
        (cellBits (v (if t=0 then wCell k else xcCell k (t-1))))⟩ := by
  have ha : P.active ⟨k,hk⟩ (LEN k-1-d+t) = if t+1=d then FourFusion.owner ⟨k,hk⟩ else none := by
    unfold FourFusion.Params.active
    rw [hC.len]
    have he : LEN k-1-d+t+2 = LEN k ↔ t+1=d := by omega
    simp only [Fin.val_mk,he]
  dsimp only
  unfold chainOp at h
  dsimp only at h
  by_cases hb : t+1=d ∧ binds k
  · rw [if_pos hb] at h
    obtain ⟨u,hu⟩ : ∃ u, FourFusion.owner ⟨k,hk⟩ = some u :=
      Option.ne_none_iff_exists'.mp ((binds_owner ⟨k,hk⟩).mp hb.2)
    have hp := oracle_pair h
    rw [fusion_query hP hC readTop ⟨k,hk⟩ hb.2 u hu hread] at hp
    have hs : P.active ⟨k,hk⟩ (LEN k-1-d+t) = some u := by
      rw [ha,if_pos hb.1,hu]
    rw [chainInput_fused hs]
    exact hp
  · rw [if_neg hb] at h
    have hp := oracle_pair h
    rw [chainOp_plain_query hP hC hk hd ht] at hp
    have hn : P.active ⟨k,hk⟩ (LEN k-1-d+t) = none := by
      rw [ha]
      split_ifs with hh
      · by_contra ho
        exact hb ⟨hh, (binds_owner ⟨k,hk⟩).mpr ho⟩
      · rfl
    rw [FourFusion.Params.chainInput,hn]
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
  have hoff : ∀ k < 42, topOff k = if k ∈ [1,19,25,34,12,16,23,33,8] then 1 else 0 := by decide
  rw [hoff k hk]
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
theorem chain_val (hC : Compat P T) (readTop : ℕ → ℕ) {k d dst : ℕ} (hk : k < 42)
    (hread : ReadContext (T:=T) (v:=v) (xs:=xs) readTop ⟨k,hk⟩) (hd : d < LEN k) (hd0 : d ≠ 0) (hdst : 1 ≤ dst)
    (hs : ∀ t < d, (chainOp readTop k d t dst).Rel f v) :
    cellBits (v dst) = P.chainValue f (topsV T v xs) ⟨k, hk⟩ (LEN k - 1 - d) d (cellBits (v (wCell k))) := by
  have hstep : ∀ t < d, chainSeq v k d dst (t + 1) =
      P.codec.slice ⟨k, hk⟩ (LEN k - 1 - d + t)
        (f ⟨896, P.chainInput (topsV T v xs) ⟨k, hk⟩ (LEN k - 1 - d + t) (chainSeq v k d dst t)⟩) := by
    intro t ht
    have h := hs t ht
    have hp := chainOp_pair hP hC readTop hk hread hd ht h
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
    rw [show dg T xs 0 = xs 0 from if_pos rfl]
    have hrt : rtopCell 0 (xs 0) = tfCell := by simp [rtopCell,exported,topCell,tfCell]
    rw [hrt]
    by_cases hs0 : xs 0 = 0
    · have h : v tfCell = v (wCell 0) * v oneCell := by
        have hh := hP.free_copy
        simpa only [if_pos hs0,copy,CInstr.RelB] using hh
      rw [h,v_one hP,mul_oneV,hs0]; rfl
    · exact chain_val hP hC topCell (by omega) (by
        intro u hu
        change none = some u at hu
        contradiction) hd hs0 (by decide) (fun _ ht => hP.free_chain ht)
  · obtain ⟨hu, hi, hc⟩ := chainOf_unitOf k hk (by omega)
    set u := unitOf k with hudef
    set i := coordOf k with hidef
    have hdk : dg T xs k = T u (xs (u + 1)) i := by rw [← hc, dg_chainOf T xs hu hi]
    have hread : ReadContext (T:=T) (v:=v) (xs:=xs)
        (groupRead T u (xs (u+1))) ⟨k,hk⟩ := by
      intro z hz j hj
      exact groupRead_fusion T xs v ⟨k,hk⟩
        ((binds_owner ⟨k,hk⟩).mpr (by rw [hz]; simp)) z hz hj
    have hb : ∀ y ∈ seg T u (xs (u+1)) i, y.Rel f v := fun _ hy => hP.seg_rel hu hi hy
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
        exact chain_val hP hC (groupRead T u (xs (u+1))) hk hread hd hd0 (topCell_pos hk) (fun t ht => hb _ (mem_chainOps.mpr ⟨t, ht, rfl⟩))
    · rw [if_neg hx] at hb
      have he : ¬ exported k := by rw [← hc]; exact fun h => hx ((exported_iff u hu i hi).mp h)
      unfold rtopCell
      by_cases hd0 : T u (xs (u + 1)) i = 0
      · rw [if_pos ⟨hd0,he⟩,hd0]; rfl
      · rw [if_neg (by tauto : ¬ (T u (xs (u+1)) i = 0 ∧ ¬ exported k))]
        exact chain_val hP hC (groupRead T u (xs (u+1))) hk hread hd hd0 (xhCell_pos hk hk0 he) (fun t ht => hb _ (mem_chainOps.mpr ⟨t, ht, rfl⟩))

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
    have h : v (accCell 0) = fpat 0 (xs (0+1)) :=
      hP.tie_rel (u:=0) (ci:=.setc (accCell 0) (fpat 0 (xs 1))) (by decide) (by unfold tie; simp)
    rw [h, ofDigitsW_succ, ofDigitsW_zero]
    unfold fpat POS; simp only [Nat.zero_add]
  | succ u ih =>
    intro hu
    have hmem : ∀ y ∈ tie (u+1) (xs (u+1+1)), y.Rel f v := fun _ hy => hP.tie_rel (by omega) hy
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
end OptimalOTS.AffineVM
