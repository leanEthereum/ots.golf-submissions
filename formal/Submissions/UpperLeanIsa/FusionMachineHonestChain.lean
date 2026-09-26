import Submissions.UpperLeanIsa.FusionMachineHonest

/-! Honest chain assertions, including the fused dependency packet at each binding endpoint. -/
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OptimalOTS.HLFusion
open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV ans inputWord_len_of)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
variable {P : Fusion.Params} {T : Tab} {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length=5503)
  (hacc : P.codec.Accepted (effective (IF P f pk m bits)))

include hT hC hacc in
theorem honest_topBits {k : ℕ} (hk : k<42) :
    cellBits (hv P T f pk m bits (topCell k)) = ctxF P f pk m bits k := by
  rw [(hv_top hk trivial).1,cellBits_cellOfBits]
  have hh := congrFun (topsOfV_eq hacc hT hC) k
  rw [topsOfV,if_pos hk] at hh
  exact hh

attribute [local irreducible] Fusion.tagWord LeanIsaFieldRescale.costFactor

include hC hlen hacc in
theorem honest_fusedMd (k : Fin 42) (hk : binds k.val) :
    cellBits (hv P T f pk m bits (fusedMdCell k.val)) = P.fusedMd k := by
  rw [hC.fusedMd]
  have hsmall : ∀ k : Fin 42, binds k.val → k.val≠5 → k.val≠6 →
      fusedMdCell k.val = cCell (Fusion.tagIndex k).val ∧ (Fusion.tagIndex k).val≤22 := by decide
  by_cases h5 : k.val=5
  · have he : k=5 := Fin.ext h5
    subst k
    change cellBits (hv P T f pk m bits 3) = Fusion.tagWord 45
    rw [hv_lt P T f pk m bits (by decide),inputWord_len_of pk m bits hlen,length_bits]
  · by_cases h6 : k.val=6
    · have he : k=6 := Fin.ext h6
      subst k
      change cellBits (hv P T f pk m bits (gpCell 13)) = Fusion.tagWord 46
      rw [honest_gp13 hC hacc,sentinel_bits]
    · obtain ⟨he,hi⟩ := hsmall k hk h5 h6
      rw [he,hv_cc hi,factor_bits _ (by omega)]

include hT hC hlen hacc in
theorem honest_fusion_query (k : Fin 42) (u : Fin 6) (hu : Fusion.owner k = some u) (x : E) :
    blake2sQuery ![x,hv P T f pk m bits (topCell (depTop k.val 2)),
      hv P T f pk m bits (topCell (depTop k.val 3)),hv P T f pk m bits (topCell (depTop k.val 4))]
      (hv P T f pk m bits (depCv k.val)) (hv P T f pk m bits (depCv k.val+1))
      (hv P T f pk m bits (fusedMdCell k.val)) =
      Fusion.packet (Fusion.fusionWords (ctxF P f pk m bits) u (cellBits x) (P.fusedMd k)) := by
  obtain ⟨hc0,hc1,hd⟩ := fusion_cells k u hu
  have hk : binds k.val := (binds_owner k).mpr (by rw [hu]; simp)
  rw [blake2sQuery_eq,hc1,hc0,honest_fusedMd hC hlen hacc k hk]
  unfold Fusion.packet Fusion.fusionWords
  simp only [Matrix.cons_val,Fin.isValue]
  rw [(hd 2 (by omega)).1,(hd 3 (by omega)).1,(hd 4 (by omega)).1]
  rw [honest_topBits hT hC hacc (hd 0 (by omega)).2.2,
    honest_topBits hT hC hacc (hd 1 (by omega)).2.2,
    honest_topBits hT hC hacc (hd 2 (by omega)).2.2,
    honest_topBits hT hC hacc (hd 3 (by omega)).2.2,
    honest_topBits hT hC hacc (hd 4 (by omega)).2.2]

include hT hC hlen hacc in
/-- The honest chain step `t` of chain `k` (the last writes `dst`). -/
theorem honest_chainOp {k : ℕ} (hk : k < 42) {t dst : ℕ}
    (ht : t < hd T (y0F P f pk m bits) k)
    (hdstpos : 1 ≤ dst)
    (hdst : hv P T f pk m bits dst =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k dst) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k) :
    (chainOp k (hd T (y0F P f pk m bits) k) t dst).Rel f (hv P T f pk m bits) := by
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
  have hp : tpos k d t / 81 ≤ 22 := by
    have := OFFT_bound k hk; unfold tpos; omega
  have hq : blake2sQuery ![hv P T f pk m bits (if t = 0 then wCell k else xcCell k (t - 1)),
      hv P T f pk m bits (cCell (tpos k d t % 9)), hv P T f pk m bits (cCell (tpos k d t / 9 % 9)),
      hv P T f pk m bits (cCell (tpos k d t / 81))] (hv P T f pk m bits oneCell)
      (hv P T f pk m bits (oneCell + 1)) (hv P T f pk m bits oneCell) =
      P.codec.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t)
        (P.chainValue f (ctxF P f pk m bits) ⟨k, hk⟩ (LEN k - 1 - d) t (sigW bits k)) := by
    have hj : LEN k - 1 - d + t + 1 < LEN k := by omega
    obtain ⟨h0, h1, h2⟩ := hC.tag ⟨k, hk⟩ _ hj
    rw [blake2sQuery_eq, hv_cc (c := tpos k d t % 9) (by omega),
      hv_cc (c := tpos k d t / 9 % 9) (by omega), hv_cc hp, show oneCell + 1 = gCell from rfl,
      hv_g, hv_one, hsrc.2]
    unfold Params.chainInput
    rw [h0, h1, h2, hC.chainMd, hC.cv]
    rfl
  unfold chainOp
  dsimp only
  by_cases hb : t+1=d ∧ binds k
  · rw [if_pos hb]
    obtain ⟨u,hu⟩ : ∃ u, Fusion.owner ⟨k,hk⟩ = some u :=
      Option.ne_none_iff_exists'.mp ((binds_owner ⟨k,hk⟩).mp hb.2)
    have ha : P.active ⟨k,hk⟩ (LEN k-1-d+t) = some u := by
      unfold Fusion.Params.active
      rw [hC.len]
      change (if LEN k-1-d+t+2=LEN k then Fusion.owner ⟨k,hk⟩ else none) = some u
      rw [if_pos (by omega),hu]
    refine blake_rel (a:=AF P T f pk m bits k t)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) ?_ hout.1 hout.2
    rw [honest_fusion_query hT hC hlen hacc ⟨k,hk⟩ u hu,hsrc.2,
      AF_spec P T f pk m bits hk ht,Fusion.Params.chainInput,ha]
  · rw [if_neg hb]
    have ha : P.active ⟨k,hk⟩ (LEN k-1-d+t) = none := by
      unfold Fusion.Params.active
      rw [hC.len]
      change (if LEN k-1-d+t+2=LEN k then Fusion.owner ⟨k,hk⟩ else none) = none
      split_ifs with hh
      · have hl : t+1=d := by omega
        by_contra hn
        exact hb ⟨hl,(binds_owner ⟨k,hk⟩).mpr hn⟩
      · rfl
    refine blake_rel (a:=AF P T f pk m bits k t)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) (hv_canonical P T f pk m bits _)
      (hv_canonical P T f pk m bits _) ?_ hout.1 hout.2
    rw [hq,AF_spec P T f pk m bits hk ht,Fusion.Params.chainInput,ha]

include hT hC hlen hacc in
/-- The honest chain steps of chain `k` into `dst`. -/
theorem honest_chainOps {k dst : ℕ} (hk : k < 42)
    (hdstpos : 1 ≤ dst)
    (hdst : hv P T f pk m bits dst =
        cellOfBits (topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) k) ∧
      hv P T f pk m bits (junkCell k dst) = hiOf T (y0F P f pk m bits) (AF P T f pk m bits) k) :
    ∀ y ∈ chainOps k (hd T (y0F P f pk m bits) k) dst, y.Rel f (hv P T f pk m bits) := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp hy
  exact honest_chainOp hT hC hlen hacc hk ht hdstpos hdst

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
end OptimalOTS.HLFusion
