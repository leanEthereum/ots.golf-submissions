import Submissions.UpperLeanIsa.FreeLastPath
import Submissions.UpperLeanIsa.FreeLastCodec
import Submissions.UpperLeanIsa.SplitValues

namespace OptimalOTS.FreeLastVM
open OracleComp LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV hi_append_lo out_pair natV_add_disjoint)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {T : Tab} {P : FourFusion.Params}

def cV (T : Tab) (c : ℕ) : E := ofK (FreeLastBase.base ^ c)
def gV (T : Tab) : E := cV T 14

structure Compat (P : FourFusion.Params) (T : Tab) : Prop where
  len : ∀ k : Fin numChains, P.codec.len k = LEN k.val
  layer : P.codec.layer = 85
  digit_grp : ∀ (I : Word) (u i : ℕ) (hu : u < 13) (hi : i < gk u),
    P.codec.digit (effective I) ⟨chainOf u i, chainOf_lt u hu i hi⟩ = T u (field u I) i
  digit_free : ∀ I : Word, (∀ u < 13, field u I < VF u) →
    P.codec.digit (effective I) 0 = freeDigit (gcost T I)
  live : ∀ I : Word, P.codec.Accepted (effective I) → ∀ u < 13, field u I < VF u
  tag : ∀ (k : Fin numChains) (j : ℕ), j+1 < LEN k.val →
    P.codec.tag k j 0 = cellBits (cV T ((OFFT k.val+j)%9)) ∧
      P.codec.tag k j 1 = cellBits (cV T ((OFFT k.val+j)/9%9)) ∧
      P.codec.tag k j 2 = cellBits (cV T ((OFFT k.val+j)/81))
  hiTop : ∀ k : Fin numChains, P.codec.hiTop k = decide (k.val ∈ [1,19,25,34,12,16,23,33,8])
  cv : P.codec.cv = cellBits (cV T 2) ++ cellBits (cV T 1)
  chainMd : P.codec.chainMd = cellBits oneV
  idxMd : P.codec.idxMd = cellBits (cV T 11)
  fusedMd : ∀ k : Fin 42, P.fusedMd k = FreeLastCodec.domainWord (FourFusion.mdIndex k).val
  fusedTag : ∀ k : Fin 42, P.fusedTag k = FreeLastCodec.tagWord (FourFusion.tagIndex k).val
  rootMd : ∀ r : Fin 1, P.rootMd r = cellBits (cV T (FourFusion.rootIndex r).val)


theorem concrete_compat : Compat FreeLastCodec.params fusionTab where
  len k := lenN_eq k.val k.isLt
  layer := rfl
  digit_grp I u i hu hi := by
    have hk := chainOf_lt u hu i hi
    have hk1 := chainOf_pos u hu i hi
    obtain ⟨e1, e2⟩ := unitOf_eq _ hk hk1
    change FourChildCodec.digit (effective I) ⟨chainOf u i, hk⟩ = _
    rw [FourChildCodec.digit_group (effective I) ⟨chainOf u i, hk⟩
      (show chainOf u i ≠ 0 by omega)]
    simp only [e1, e2, unitOf_chainOf u hu i hi, coordOf_chainOf u hu i hi, field_eq hu]
    rfl
  digit_free I hl := by
    change FourChildCodec.digit (effective I) 0 = _
    rw [FourChildCodec.digit_free_live (fun u hu => by
        rw [field_eq hu]; exact (live_iff hu _ (digitW_lt _ _ _)).mpr (hl u hu)),
      fusion_freeDigit, fusion_gsum]
  live I hacc u hu := by
    change FourChildCodec.params.Accepted (effective I) at hacc
    have h := ((FourChildCodec.not_dummy_iff _).mp
      ((FourChildCodec.accepted_iff _).mp hacc).1) u hu
    rw [field_eq hu] at h
    exact (live_iff hu _ (digitW_lt _ _ _)).mp h
  tag k j _ := by
    refine ⟨?_,?_,?_⟩ <;>
    · change FreeLastCodec.word _ = _
      rw [off_eq k.val k.isLt]
      rfl
  hiTop _ := rfl
  cv := rfl
  chainMd := by
    change cellBits (ofK (FreeLastBase.base^0)) = cellBits oneV
    rw [pow_zero]
    rfl
  idxMd := rfl
  fusedMd _ := rfl
  fusedTag _ := rfl
  rootMd _ := rfl


structure ValueFacts (T : Tab) (B : BlakeRel) (v : Nat → E) (xs : Nat → Nat) : Prop where
  pro : ∀ ci ∈ prefixCode 15, ci.RelB B v
  seg_rel : ∀ {u i : Nat}, u < 13 → i < gk u →
    ∀ {ci : CInstr}, ci ∈ seg T u (xs (u+1)) i → ci.RelB B v
  free_chain : ∀ {t : Nat}, t < xs 0 → (chainOp topCell 0 (xs 0) t tfCell).RelB B v
  free_copy : (copy (if xs 0 = 0 then wCell 0 else tfCell) tfCell).RelB B v
  pk_copy : (copy (stCell 0) pkCell).RelB B v
  index : (CInstr.blake msgLo msgHi nonceCell pkCell (cCell 1) idxCell (cCell 11)).RelB B v
  root_rel : ∀ {u : Nat}, u < 13 → ∀ {ci : CInstr},
    ci ∈ rootIns T u (xs (u+1)) false → ci.RelB B v

def withFree (xs : Nat → Nat) (s : Nat) (f : Nat) : Nat := if f = 0 then s else xs (f-1)

theorem withFree_zero (xs : Nat → Nat) (s : Nat) : withFree xs s 0 = s := rfl
theorem withFree_succ (xs : Nat → Nat) (s u : Nat) : withFree xs s (u+1) = xs u := by
  simp only [withFree,show u+1 ≠ 0 by omega,if_false,Nat.add_sub_cancel]

theorem PathFacts.value_valid {B : BlakeRel} {v : Nat → E} {xs : Nat → Nat} {s : Nat} {z : Bool}
    (hp : PathFacts B v xs s z) : Valid (withFree xs s) := by
  intro f hf
  cases f with
  | zero => exact Nat.lt_succ_of_le hp.free_bound
  | succ u => rw [withFree_succ,Wf_succ (by omega)]; exact hp.valid u (by omega)

theorem PathFacts.values {B : BlakeRel} {v : Nat → E} {xs : Nat → Nat} {s : Nat} {z : Bool}
    (hp : PathFacts B v xs s z) : ValueFacts fusionTab B v (withFree xs s) where
  pro := hp.pro
  seg_rel hu hi ci hci := by
    simp only [withFree_succ] at hci
    apply hp.core_rel hu
    unfold FreeLastBlocks.core
    simp only [List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inr (mem_segs.mpr ⟨_,hi,hci⟩)))
  free_chain ht := hp.free _ (mem_chainOps.mpr ⟨_,ht,rfl⟩)
  free_copy := by
    rw [withFree_zero]
    by_cases hs : s = 0
    · have hz : z = true := by
        cases z with
        | false => have hh := hp.positive rfl; omega
        | true => rfl
      have h := hp.blk 1 (by decide) (copy (wCell 0) tfCell) (by
        simp only [hz,FreeLastBlocks.chosen,and_self,if_true,FreeLastBlocks.zero,List.mem_append,
          List.mem_cons,true_or,or_true])
      simpa only [if_pos hs] using h
    · simp only [if_neg hs,copy,CInstr.RelB,pro_one hp.pro,mul_oneV]
  pk_copy := hp.pro _ (prefixCode_mem (i:=12) (by decide : 12 < 15))
  index := hp.pro _ (prefixCode_mem (i:=13) (by decide : 13 < 15))
  root_rel hu ci hci := by
    simp only [withFree_succ] at hci
    apply hp.core_rel hu
    unfold FreeLastBlocks.core
    simp only [List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inr hci)

section Path
variable {f : HashTable} {v : ℕ → E} {xs : ℕ → ℕ}
  (hV : Valid xs) (hP : ValueFacts T (oracleRel f) v xs)


include hP in
theorem v_one : v oneCell = oneV := pro_one hP.pro
include hP in
theorem v_len : v lenCell = natV 5504 := pro_length hP.pro

include hP in
theorem v_c {c : ℕ} (hc : c ≤ 11) : v (cCell c) = cV T c := pro_c hP.pro (by omega)

include hP in
theorem cb_cv (hC : Compat P T) : cellBits (v (cCell 1+1)) ++ cellBits (v (cCell 1)) = P.codec.cv := by
  rw [show cCell 1+1 = cCell 2 from rfl,v_c hP (by decide : 2 ≤ 11),
    v_c hP (by decide : 1 ≤ 11),hC.cv]

theorem factor_bits (T : Tab) (i : Fin 47) :
    cellBits (cV T i.val) = FreeLastCodec.word i.val := rfl

include hP in
theorem fusedMd_cell (hC : Compat P T) (k : Fin 42) (_hk : binds k.val) :
    cellBits (v (fusedMdCell k.val)) = P.fusedMd k := by
  rw [hC.fusedMd]
  have he : ∀ k : Fin 42, fusedMdCell k.val =
      if (FourFusion.mdIndex k).val = 17 then lenCell else cCell (FourFusion.mdIndex k).val := by decide
  rw [he]
  unfold FreeLastCodec.domainWord
  by_cases h17 : (FourFusion.mdIndex k).val = 17
  · rw [if_pos h17, if_pos h17, v_len hP]
    rfl
  · have hi : (FourFusion.mdIndex k).val ≤ 11 := by
      have hb : ∀ k : Fin 42, binds k.val → (FourFusion.mdIndex k).val ≤ 11 ∨
          (FourFusion.mdIndex k).val = 17 := by decide
      exact (hb k _hk).resolve_right h17
    rw [if_neg h17, if_neg h17, v_c hP hi, factor_bits T _]

include hP in
theorem fusedTag_cell (hC : Compat P T) (k : Fin 42) :
    cellBits (v (fusedTagCell k.val)) = P.fusedTag k := by
  rw [hC.fusedTag]
  have hsmall : ∀ k : Fin 42,
      fusedTagCell k.val = (if (FourFusion.tagIndex k).val = 12 then lenCell else
        cCell (FourFusion.tagIndex k).val) ∧ (FourFusion.tagIndex k).val ≤ 12 := by decide
  obtain ⟨he,hi⟩ := hsmall k
  rw [he]
  unfold FreeLastCodec.tagWord
  by_cases h12 : (FourFusion.tagIndex k).val = 12
  · rw [if_pos h12,if_pos h12,v_len hP]; rfl
  · rw [if_neg h12,if_neg h12,v_c hP (by omega),factor_bits T _]

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

theorem chainOp_plain_query (hP : ValueFacts T (oracleRel f) v xs) (hC : Compat P T) {k : ℕ}
    (hk : k < 42) {d t : ℕ} (hd : d < LEN k) (ht : t < d) (x : E) :
    blake2sQuery ![x, v (cCell (tpos k d t % 9)), v (cCell (tpos k d t / 9 % 9)),
        v (cCell (tpos k d t / 81))] (v (cCell 1)) (v (cCell 1 + 1)) (v oneCell) =
      P.codec.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t) (cellBits x) := by
  have hj : LEN k - 1 - d + t + 1 < LEN k := by omega
  obtain ⟨h0, h1, h2⟩ := hC.tag ⟨k, hk⟩ _ hj
  have hp : tpos k d t / 81 ≤ 11 := by
    have := OFFT_bound k hk; unfold tpos; omega
  rw [blake2sQuery_eq, v_c hP (c := tpos k d t % 9) (by omega),
    v_c hP (c := tpos k d t / 9 % 9) (by omega), v_c hP (by omega : tpos k d t / 81 ≤ 11), cb_cv hP hC, v_one hP]
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


end Path
end
end OptimalOTS.FreeLastVM
