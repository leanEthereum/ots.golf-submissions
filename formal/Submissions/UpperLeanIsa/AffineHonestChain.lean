import Submissions.UpperLeanIsa.AffineHonest

/-! Honest chain assertions, including the fused dependency packet at each binding endpoint
using four or five children and separated domain words. -/
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OptimalOTS.AffineVM
open OracleComp LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV ans inputWord_len_of)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
variable {P : FourFusion.Params} {T : Tab} {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length=5504)
  (hacc : P.codec.Accepted (effective (IF P f pk m bits)))

include hT hC hacc in
theorem honest_topBits {k : ℕ} (hk : k<42) :
    cellBits (hv P T f pk m bits (topCell k)) = ctxF P f pk m bits k := by
  rw [(hv_top hk trivial).1,cellBits_cellOfBits]
  have hh := congrFun (topsOfV_eq hacc hT hC) k
  rw [topsOfV,if_pos hk] at hh
  exact hh


include hC hlen hacc in
theorem honest_fusedMd (k : Fin 42) (_hk : binds k.val) :
    cellBits (hv P T f pk m bits (fusedMdCell k.val)) = P.fusedMd k := by
  rw [hC.fusedMd]
  have he : ∀ k : Fin 42, fusedMdCell k.val =
      if (FourFusion.mdIndex k).val = 17 then lenCell else cCell (FourFusion.mdIndex k).val := by decide
  rw [he]
  unfold AffineCodec.domainWord
  by_cases h17 : (FourFusion.mdIndex k).val = 17
  · rw [if_pos h17, if_pos h17]
    have hl : hv P T f pk m bits lenCell = natV 5504 := by
      rw [hv_lt P T f pk m bits (by decide)]
      exact inputWord_len_of pk m bits hlen
    rw [hl]
    rfl
  · have hi : (FourFusion.mdIndex k).val ≤ 13 := by
      have hb : ∀ k : Fin 42, (FourFusion.mdIndex k).val ≤ 13 ∨
          (FourFusion.mdIndex k).val = 17 := by decide
      exact (hb k).resolve_right h17
    rw [if_neg h17, if_neg h17, hv_cc hi, factor_bits T _]

include hC in
theorem honest_fusedTag (k : Fin 42) :
    cellBits (hv P T f pk m bits (fusedTagCell k.val)) = P.fusedTag k := by
  rw [hC.fusedTag]
  have hsmall : ∀ k : Fin 42,
      fusedTagCell k.val = cCell (FourFusion.tagIndex k).val ∧ (FourFusion.tagIndex k).val≤13 := by decide
  obtain ⟨he,hi⟩ := hsmall k
  rw [he,hv_cc hi,factor_bits T _]

def HonestReadContext (readTop : ℕ → ℕ) (k : Fin 42) : Prop :=
  ∀ u : Fin 8, FourFusion.owner k = some u →
    ∀ i < (FourFusion.children u).length,
      cellBits (hv P T f pk m bits (readTop ((FourFusion.children u).getD i 0))) =
        ctxF P f pk m bits ((FourFusion.children u).getD i 0)

include hT hC hlen hacc in
theorem honest_groupRead_context (k : Fin 42) :
    HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits)
      (groupRead T (unitOf k.val) (XF P T f pk m bits (unitOf k.val+1))) k := by
  intro u ho i hi
  have hk : binds k.val := (binds_owner k).mpr (by rw [ho]; simp)
  have hdep := (fusion_cells k hk u ho).2.2 i hi
  rw [groupRead_rtop T (XF P T f pk m bits) hdep.2.2 hdep.2.1]
  change cellBits (hv P T f pk m bits (rtopCell _ (hd T (y0F P f pk m bits) _))) = _
  rw [hv_rtop hlen hdep.2.2,cellBits_cellOfBits]
  have hh := congrFun (topsOfV_eq hacc hT hC) ((FourFusion.children u).getD i 0)
  simpa only [topsOfV,if_pos hdep.2.2,ctxF,IF] using hh

include hT hC hlen hacc in
theorem honest_fusion_query (readTop : ℕ → ℕ) (k : Fin 42) (hk : binds k.val)
    (u : Fin 8) (hu : FourFusion.owner k = some u)
    (hread : HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) readTop k)
    (x : E) :
    blake2sQuery ![x,hv P T f pk m bits (readTop (depTop k.val 2)),
      hv P T f pk m bits (readTop (depTop k.val 3)),
      hv P T f pk m bits (if fiveChildren k.val then readTop (depTop k.val 4) else fusedTagCell k.val)]
      (hv P T f pk m bits (depCv k.val)) (hv P T f pk m bits (depCv k.val+1))
      (hv P T f pk m bits (fusedMdCell k.val)) =
      FourFusion.packet (FourFusion.fusionWords (ctxF P f pk m bits) u (cellBits x)
        (P.fusedTag k) (P.fusedMd k)) := by
  obtain ⟨hc0,hc1,hd⟩ := fusion_cells k hk u hu
  have hl : 4 ≤ (FourFusion.children u).length := by
    have hh : ∀ u : Fin 8, 4 ≤ (FourFusion.children u).length := by decide
    exact hh u
  rw [blake2sQuery_eq,hc1,hc0,honest_fusedMd hC hlen hacc k hk]
  unfold FourFusion.packet Fusion.packet FourFusion.fusionWords
  simp only [Matrix.cons_val,Fin.isValue]
  rw [(hd 2 (by omega)).1,(hd 3 (by omega)).1,hread u hu 2 (by omega),hread u hu 3 (by omega),
    honest_topBits hT hC hacc (hd 0 (by omega)).2.2,
    honest_topBits hT hC hacc (hd 1 (by omega)).2.2]
  by_cases hf : FourFusion.five u = true
  · have hf' := (fiveChildren_owner k u hu).mpr hf
    have hl5 : 4 < (FourFusion.children u).length := by
      rw [Fusion.SplitRoot.packet_lengths u u.isLt, if_pos hf]
      decide
    rw [if_pos hf', if_pos hf, (hd 4 hl5).1, hread u hu 4 hl5]
  · have hf' : ¬ fiveChildren k.val := fun hh => hf ((fiveChildren_owner k u hu).mp hh)
    rw [if_neg hf', if_neg hf, honest_fusedTag hC k]

include hT hC hlen hacc in
/-- The honest chain step `t` of chain `k` (the last writes `dst`). -/
theorem honest_chainOp (readTop : ℕ → ℕ) {k : ℕ} (hk : k < 42)
    (hread : HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) readTop ⟨k,hk⟩)
    {t dst : ℕ}
    (ht : t < hd T (y0F P f pk m bits) k)
    (hdstpos : 1 ≤ dst)
    (hdst : hv P T f pk m bits dst =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k dst) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k) :
    (chainOp readTop k (hd T (y0F P f pk m bits) k) t dst).Rel f (hv P T f pk m bits) := by
  set d := hd T (y0F P f pk m bits) k with hddef
  have hdl := hd_lt T hT (y0F P f pk m bits) hk
  rw [← hddef] at hdl
  have hsrc : IsCanonical128 (hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1))) ∧
      cellBits (hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1))) =
        P.chainValue f (ctxF P f pk m bits) ⟨k, hk⟩ (LEN k - 1 - d) t (sigW bits k) := by
    by_cases h0 : t = 0
    · rw [if_pos h0, hv_w hlen hk, cellBits_cellOfBits, h0]
      exact ⟨canon_cellOfBits _, rfl⟩
    · rw [if_neg h0, (hv_xc hk (show t - 1 < LEN k by omega)).1, cellBits_loC]
      refine ⟨canon_loC _, ?_⟩
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      rw [Nat.add_sub_cancel, AF_spec P T f pk m bits hk (by omega), chainValue_succ]
      simp only [Params.slice]
      rw [stepOff_eq hC hk hdl (by omega), if_neg (by omega)]
  have hout : hv P T f pk m bits (if t + 1 = d then dst - topOff k else xcCell k t) =
        loC (AF P T f pk m bits k t) ∧
      hv P T f pk m bits ((if t + 1 = d then dst - topOff k else xcCell k t) + 1) =
        hiC (AF P T f pk m bits k t) := by
    by_cases hl : t + 1 = d
    · rw [if_pos hl]
      have hsel := hdst.1
      have hjunk := hdst.2
      unfold topOf at hsel
      unfold hiOf at hjunk
      rw [← hddef, if_neg (by omega), show d - 1 = t by omega] at hsel hjunk
      have hoff := topOff_le k
      by_cases hz : topOff k = 0
      · simpa [junkCell, hz, loC, hiC] using And.intro hsel hjunk
      · have ho : topOff k = 1 := by omega
        have he : dst - 1 + 1 = dst := by omega
        simpa [junkCell, ho, loC, hiC, he]
          using And.intro hjunk hsel
    · rw [if_neg hl]; exact hv_xc hk (by omega)
  have hp : tpos k d t / 81 ≤ 13 := by
    have := OFFT_bound k hk; unfold tpos; omega
  have hq : blake2sQuery ![hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1)),
      hv P T f pk m bits (cCell (tpos k d t % 9)), hv P T f pk m bits (cCell (tpos k d t / 9 % 9)),
      hv P T f pk m bits (cCell (tpos k d t / 81))] (hv P T f pk m bits (cCell 1))
      (hv P T f pk m bits (cCell 1 + 1)) (hv P T f pk m bits oneCell) =
      P.codec.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t)
        (P.chainValue f (ctxF P f pk m bits) ⟨k, hk⟩ (LEN k - 1 - d) t (sigW bits k)) := by
    have hj : LEN k - 1 - d + t + 1 < LEN k := by omega
    obtain ⟨h0, h1, h2⟩ := hC.tag ⟨k, hk⟩ _ hj
    rw [blake2sQuery_eq, hv_cc (c := tpos k d t % 9) (by omega),
      hv_cc (c := tpos k d t / 9 % 9) (by omega), hv_cc hp, show cCell 1 + 1 = cCell 2 from rfl,
      hv_cc (c:=1) (by decide), hv_cc (c:=2) (by decide), hv_one, hsrc.2]
    unfold Params.chainInput
    rw [h0, h1, h2, hC.chainMd, hC.cv]
    rfl
  unfold chainOp
  dsimp only
  by_cases hb : t+1=d ∧ binds k
  · rw [if_pos hb]
    obtain ⟨u,hu⟩ : ∃ u, FourFusion.owner ⟨k,hk⟩ = some u :=
      Option.ne_none_iff_exists'.mp ((binds_owner ⟨k,hk⟩).mp hb.2)
    have ha : P.active ⟨k,hk⟩ (LEN k-1-d+t) = some u := by
      unfold FourFusion.Params.active
      rw [hC.len]
      change (if LEN k-1-d+t+2=LEN k then FourFusion.owner ⟨k,hk⟩ else none) = some u
      rw [if_pos (by omega),hu]
    refine blake_rel (a:=AF P T f pk m bits k t)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) ?_ hout.1 hout.2
    rw [honest_fusion_query hT hC hlen hacc readTop ⟨k,hk⟩ hb.2 u hu hread,hsrc.2,
      AF_spec P T f pk m bits hk ht,chainInput_fused ha]
  · rw [if_neg hb]
    have ha : P.active ⟨k,hk⟩ (LEN k-1-d+t) = none := by
      unfold FourFusion.Params.active
      rw [hC.len]
      change (if LEN k-1-d+t+2=LEN k then FourFusion.owner ⟨k,hk⟩ else none) = none
      split_ifs with hh
      · by_contra ho
        exact hb ⟨by omega, (binds_owner ⟨k,hk⟩).mpr ho⟩
      · rfl
    refine blake_rel (a:=AF P T f pk m bits k t)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) ?_ hout.1 hout.2
    rw [hq,AF_spec P T f pk m bits hk ht,FourFusion.Params.chainInput,ha]

include hT hC hlen hacc in
/-- The honest chain steps of chain `k` into `dst`. -/
theorem honest_chainOps (readTop : ℕ → ℕ) {k dst : ℕ} (hk : k < 42)
    (hread : HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) readTop ⟨k,hk⟩)
    (hdstpos : 1 ≤ dst)
    (hdst : hv P T f pk m bits dst =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k dst) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k) :
    ∀ y ∈ chainOps readTop k (hd T (y0F P f pk m bits) k) dst, y.Rel f (hv P T f pk m bits) := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp hy
  exact honest_chainOp hT hC hlen hacc readTop hk hread ht hdstpos hdst

include hlen in
/-- An honest copy of a top from the revealed word (digit `0`). -/
theorem honest_copyW {k c : ℕ} (hk : k < 42) (h0 : hd T (y0F P f pk m bits) k = 0)
    (hc : hv P T f pk m bits c =
      cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k)) :
    (copy (wCell k) c).Rel f (hv P T f pk m bits) := by
  show hv P T f pk m bits c = hv P T f pk m bits (wCell k) * hv P T f pk m bits oneCell
  rw [hv_one, mul_oneV, hc, hv_w hlen hk]
  unfold topOf; rw [if_pos h0]

/-- The honest accumulator after group `u`. -/
theorem honest_acc {u : ℕ} (hu : u < 13) :
    hv P T f pk m bits (accCell u) =
      natV (ofDigitsW gb (fun w => XF P T f pk m bits (w + 1)) (u + 1)) := by
  by_cases h12 : u < 12
  · exact hv_accl h12
  · obtain rfl : u = 12 := by omega
    rw [show accCell 12 = idxCell from rfl, hv_idx]
    have hfun : (fun w => XF P T f pk m bits (w + 1)) = digitW gb (IF P f pk m bits).toNat := by
      funext w; show hxs T _ (w + 1) = _; rw [hxs_succ]; rfl
    rw [hfun, show 12 + 1 = 13 from rfl,
      ofDigitsW_digitW gb _ 13 (by rw [show posW gb 13 = 128 from POS_13]; exact BitVec.isLt _)]
    show cellOfBits _ = cellOfBits _
    rw [BitVec.ofNat_toNat]
    rfl

end
end OptimalOTS.AffineVM
