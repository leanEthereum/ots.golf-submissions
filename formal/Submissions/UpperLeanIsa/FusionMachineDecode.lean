import Submissions.UpperLeanIsa.FusionMachineBlocks

/-! The complete decoder and frame guard for the fused bytecode. -/
namespace OptimalOTS.HLFusion
open LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV)

def gOf (f : ℕ) : ℕ := f - 1
def zOf (_f : ℕ) : Bool := false
def Wf (f : ℕ) : ℕ := if f = 0 then 64 else VF (gOf f)
def ent (f x : ℕ) : ℕ := if f = 0 then entF x else entryOf (f-1) x
def bodyF (T : Tab) (f x : ℕ) : List CInstr := if f = 0 then fbody x else body T (gOf f) x false
def xOf (f e : ℕ) : ℕ := if f = 0 then (e-baseF)/68 else (dec e).2.1
def IsEntry (f e : ℕ) : Prop := f < 14 ∧ ∃ x < Wf f, e = ent f x

theorem ent_zero (x : ℕ) : ent 0 x = entF x := rfl
theorem ent_succ {u : ℕ} (_hu : u < 13) (x : ℕ) : ent (u+1) x = entryOf u x := by
  unfold ent; rw [if_neg (by omega), Nat.add_sub_cancel]
theorem bodyF_zero (T : Tab) (x : ℕ) : bodyF T 0 x = fbody x := rfl
theorem bodyF_succ (T : Tab) {u : ℕ} (_hu : u < 13) (x : ℕ) : bodyF T (u+1) x = body T u x false := by
  unfold bodyF gOf; rw [if_neg (by omega),Nat.add_sub_cancel]
theorem Wf_zero : Wf 0 = 64 := rfl
theorem Wf_succ {u : ℕ} (_hu : u < 13) : Wf (u+1) = VF u := by
  unfold Wf gOf; rw [if_neg (by omega),Nat.add_sub_cancel]

theorem xOf_ent {f x : ℕ} (hf : f < 14) (hx : x < Wf f) : xOf f (ent f x) = x := by
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · unfold xOf ent entF; rw [if_pos rfl,if_pos rfl]; omega
  · obtain ⟨u,rfl⟩ : ∃ u, f = u+1 := ⟨f-1,by omega⟩
    rw [Wf_succ (by omega)] at hx
    unfold xOf; rw [if_neg (by omega),ent_succ (by omega)]
    have hh := dec_entry (i:=0) (by omega) hx (by have := L_pos u (band u x); omega)
    rw [Nat.add_zero] at hh
    rw [hh]

theorem isEntry_eq {f e : ℕ} (h : IsEntry f e) : xOf f e < Wf f ∧ e = ent f (xOf f e) := by
  obtain ⟨hf, x, hx, rfl⟩ := h
  rw [xOf_ent hf hx]; exact ⟨hx, rfl⟩

theorem bodyF_straight (T : Tab) (f x : ℕ) : ∀ y ∈ bodyF T f x, y.straight = true := by
  unfold bodyF; split_ifs
  · exact fbody_straight x
  · exact body_straight T _ x _

/-- The unit cost of frame `f`: `4` for the free chain. -/
def gcuF (f : ℕ) : ℕ := if f = 0 then 5 else gcu (gOf f)

/-- Hashes of the block of `x` in frame `f` beyond the root call. -/
def cF (T : Tab) (f x : ℕ) : ℕ := if f = 0 then x else cost T (gOf f) x

/-- Root calls of frame `f`'s blocks. -/
def hmF (f : ℕ) : ℕ := if f = 0 then 0 else hm (gOf f)

theorem body_len_L {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    (body T u v z).length + 2 = L u (band u v) := by
  rw [body_len hT hu hv, hT.cost_eq u hu v hv]
  unfold L gcu; split_ifs <;> omega

theorem gcuF_zero : gcuF 0 = 5 := rfl
theorem cF_zero (T : Tab) (x : ℕ) : cF T 0 x = x := rfl
theorem hmF_zero : hmF 0 = 0 := rfl

theorem gOf_lt {f : ℕ} (hf0 : f ≠ 0) (hf : f < 14) : gOf f < 13 := by
  unfold gOf; omega

theorem bodyF_pos (T : Tab) {f : ℕ} (hf0 : f ≠ 0) (x : ℕ) :
    bodyF T f x = body T (gOf f) x (zOf f) := if_neg hf0

theorem Wf_pos {f : ℕ} (hf0 : f ≠ 0) : Wf f = VF (gOf f) := if_neg hf0

theorem bodyF_len {T : Tab} (hT : T.Hyp) {f x : ℕ} (hf : f < 14) (hx : x < Wf f) :
    (bodyF T f x).length = gcuF f - 2 + cF T f x + hmF f := by
  by_cases hf0 : f = 0
  · subst hf0; rw [bodyF_zero, fbody_len, gcuF_zero, cF_zero, hmF_zero]; omega
  · rw [Wf_pos hf0] at hx
    rw [bodyF_pos T hf0, body_len hT (gOf_lt hf0 hf) hx]
    unfold gcuF cF hmF; rw [if_neg hf0, if_neg hf0, if_neg hf0]

theorem bodyF_lcost {T : Tab} (hT : T.Hyp) {f x : ℕ} (hf : f < 14) (hx : x < Wf f) :
    lcost (bodyF T f x) = gcuF f - 2 + 10 * (cF T f x + hmF f) := by
  by_cases hf0 : f = 0
  · subst hf0; rw [bodyF_zero, fbody_lcost, gcuF_zero, cF_zero, hmF_zero]; omega
  · rw [Wf_pos hf0] at hx
    rw [bodyF_pos T hf0, body_lcost hT (gOf_lt hf0 hf) hx]
    unfold gcuF cF hmF; rw [if_neg hf0, if_neg hf0, if_neg hf0]


theorem topCell_lt {k : ℕ} (hk : k < 42) : topCell k + 1 < 346 := by
  have hh : ∀ k < 42, topCell k + 1 < 346 := by decide
  exact hh k hk

theorem xhCell_lt {k : ℕ} (hk : k < 42) : xhCell k + 1 < 346 := topCell_lt hk

theorem dep_bounds : ∀ k < 42, depCv k + 1 < 346 ∧ fusedMdCell k < 214 ∧
    ∀ i < 5, depTop k i < 42 := by decide

theorem chainOp_bounded {k d t dst : ℕ} (hk : k < 42) (ht : t < d) (hd : d ≤ 64)
    (hdst : dst + 1 < 2^16) : (chainOp k d t dst).Bounded := by
  have hx := xcBase_bound k hk
  have hL := LEN_le k hk
  have hdps := dep_bounds k hk
  have b2 := topCell_lt (hdps.2.2 2 (by decide))
  have b3 := topCell_lt (hdps.2.2 3 (by decide))
  have b4 := topCell_lt (hdps.2.2 4 (by decide))
  have hp : tpos k d t / 81 < 64 := by
    have := OFFT_bound k hk; unfold tpos; omega
  unfold chainOp
  split_ifs <;> simp only [CInstr.Bounded,cCell,oneCell] <;>
    (try split_ifs) <;> (simp only [wCell,xcCell]; omega)

theorem rtopCell_lt {k d : ℕ} (hk : k < 42) : rtopCell k d < 346 := by
  have := topCell_lt hk
  unfold rtopCell wCell; split_ifs <;> omega

theorem rt_lt (T : Tab) {u v : ℕ} {z : Bool} {j : ℕ} (_hu : u < 13) (hj : j < 4) : rt T u v z j < 346 := by
  unfold rt
  split_ifs
  · decide
  · exact rtopCell_lt (by omega)
  · exact rtopCell_lt (by omega)

theorem root_cells : ∀ u < 13, rootCv (hcall u)+1 < 346 ∧ stCell (hcall u)+1 < 346 ∧ rootMdCell (hcall u) < 73 := by decide

theorem rootIns_bounded (T : Tab) {u v : ℕ} {z : Bool} (hu : u < 13) :
    ∀ x ∈ rootIns T u v z, x.Bounded := by
  intro x hx
  unfold rootIns at hx
  split_ifs at hx
  · simp only [List.mem_singleton] at hx
    subst x
    have b0 := rt_lt T (v:=v) (z:=z) hu (j:=0) (by omega)
    have b1 := rt_lt T (v:=v) (z:=z) hu (j:=1) (by omega)
    have b2 := rt_lt T (v:=v) (z:=z) hu (j:=2) (by omega)
    have b3 := rt_lt T (v:=v) (z:=z) hu (j:=3) (by omega)
    have := root_cells u hu
    simp only [CInstr.Bounded]; omega
  · simp at hx

theorem body_bounded {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    ∀ x ∈ body T u v z, x.Bounded := by
  intro x hx
  unfold body at hx
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hx
  rcases hx with ((((h | h) | h) | h) | h) | h
  · unfold tie at h
    split_ifs at h <;> simp at h <;> (try rcases h with rfl | rfl) <;>
      simp only [CInstr.Bounded, accCell, tCell, copy, oneCell, idxCell] <;> (try split_ifs) <;> omega
  · subst h
    have := band_lt_17 hu hv
    rw [← hT.cost_eq u hu v hv] at this
    simp only [prodOp, CInstr.Bounded, gpCell, cCell]
    split_ifs <;> omega
  · obtain ⟨i, hi, hx⟩ := mem_segs.mp h
    have hk := chainOf_lt u hu i hi
    have hd := hT.coord_lt u hu v (lt_of_lt_of_le hv (VF_le u hu)) i hi
    have hL := LEN_le _ hk
    unfold seg at hx
    split_ifs at hx
    · simp at hx; subst hx
      have := topCell_lt hk
      simp only [copy, CInstr.Bounded, wCell, oneCell]; omega
    · obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp hx
      exact chainOp_bounded hk ht (by omega) (by have := topCell_lt hk; omega)
    · obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp hx
      exact chainOp_bounded hk ht (by omega) (by have := xhCell_lt hk; omega)
  · exact rootIns_bounded T hu x h
  · rw [h.2]; simp only [NOP, CInstr.Bounded, oneCell]; omega
  · subst h; unfold nextOp; split_ifs <;> simp only [CInstr.Bounded, copy, hCell, gCell, h1Cell,
      show stCell 2 = 344 from rfl, oneCell, pkCell] <;> (try split_ifs) <;> omega

theorem fbody_bounded (s : ℕ) (hs : s < 64) : ∀ x ∈ fbody s, x.Bounded := by
  intro x hx
  unfold fbody at hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with (rfl | h) | rfl | rfl
  · change 200 < 2^16; decide
  · obtain ⟨t,ht,rfl⟩ := mem_chainOps.mp h
    exact chainOp_bounded (by omega) ht (by omega) (by unfold tfCell; omega)
  · simp only [copy,CInstr.Bounded,wCell,tfCell,oneCell]; split_ifs <;> omega
  · simp only [CInstr.Bounded,hCell,gCell,h1Cell]; omega

theorem proList_straight : ∀ x ∈ proList, x.straight = true := by
  intro x hx
  unfold proList at hx
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hx
  rcases hx with (((rfl | rfl) | ⟨c, -, rfl⟩) | ⟨c,hc,rfl⟩) | rfl | rfl <;> rfl

theorem proList_bounded : ∀ x ∈ proList, x.Bounded := by
  intro x hx
  unfold proList at hx
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hx
  rcases hx with (((rfl | rfl) | ⟨c,hc,rfl⟩) | ⟨c,hc,rfl⟩) | rfl | rfl <;>
    simp only [CInstr.Bounded, cCell, oneCell, lenCell, gCell, msgLo, msgHi,
      nonceCell, pkCell, idxCell, hCell, h1Cell] <;> (try split_ifs) <;> (try simp only [List.mem_cons,List.not_mem_nil,or_false] at hc) <;> omega

theorem getD_mem_or {l : List CInstr} {i : ℕ} : l.getD i .pad ∈ l ∨ l.getD i .pad = .pad := by
  by_cases h : i < l.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; rw [List.getD_eq_default _ _ (by omega)]

theorem prologue_bounded (s : ℕ) : (prologue s).Bounded := by
  unfold prologue
  split_ifs
  · rcases getD_mem_or (l := proList) (i := s) with h | h
    · exact proList_bounded _ h
    · rw [h]; trivial
  · show 0 < 15; omega
  · trivial

theorem ctlF_bounded {f : ℕ} (hf : f < 14) : (ctlF f).Bounded := by
  unfold ctlF; split_ifs
  · show f + 1 < 15; omega
  · trivial

theorem blockInstr_bounded {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} {i : ℕ} (hu : u < 13)
    (hv : v < VF u) : (blockInstr T u v z i).Bounded := by
  unfold blockInstr
  by_cases h0 : i = 0
  · rw [if_pos h0]; show u+1 < 15; omega
  rw [if_neg h0]
  split_ifs
  · rcases getD_mem_or (l := body T u v z) (i := i - 1) with h | h
    · exact body_bounded hT hu hv _ h
    · rw [h]; trivial
  · exact ctlF_bounded (by omega)
  · trivial

theorem fblockInstr_bounded {s i : ℕ} (hs : s < 64) : (fblockInstr s i).Bounded := by
  unfold fblockInstr
  split_ifs
  · show 0 < 15; omega
  · rcases getD_mem_or (l := fbody s) (i := i - 1) with h | h
    · exact fbody_bounded s hs _ h
    · rw [h]; trivial
  · show frG0 s < 15; unfold frG0; omega
  · trivial

theorem cinstrAt_cases (T : Tab) (s : ℕ) :
    (s < 27 ∧ cinstrAt T s = prologue s) ∨
    (27 ≤ s ∧ s < gEnd ∧ cinstrAt T s = blockInstr T (dec s).1 (dec s).2.1 false (dec s).2.2) ∨
    (baseF ≤ s ∧ s < baseF+4352 ∧ cinstrAt T s = fblockInstr ((s-baseF)/68) ((s-baseF)%68)) ∨
    cinstrAt T s = .pad := by
  unfold cinstrAt
  by_cases h1 : s < 27
  · left; exact ⟨h1,if_pos h1⟩
  rw [if_neg h1]
  by_cases h2 : s < gEnd
  · right; left; exact ⟨by omega,h2,if_pos h2⟩
  rw [if_neg h2]
  by_cases h3 : s < baseF
  · right; right; right; exact if_pos h3
  rw [if_neg h3]
  by_cases h4 : s < baseF+4352
  · right; right; left; exact ⟨by omega,h4,if_pos h4⟩
  · right; right; right; exact if_neg h4

theorem cinstrAt_bounded {T : Tab} (hT : T.Hyp) (s : ℕ) : (cinstrAt T s).Bounded := by
  rcases cinstrAt_cases T s with ⟨-,h⟩ | ⟨h1,h2,h⟩ | ⟨h1,h2,h⟩ | h <;> rw [h]
  · exact prologue_bounded s
  · obtain ⟨hu,hv,-,-⟩ := dec_spec h1 h2
    exact blockInstr_bounded hT hu hv
  · have hs : (s-baseF)/68 < 64 := by unfold baseF at *; omega
    exact fblockInstr_bounded hs
  · trivial

theorem cinstrAt_pro (T : Tab) {s : ℕ} (h : s < 27) : cinstrAt T s = prologue s := by
  unfold cinstrAt; rw [if_pos h]

theorem cinstrAt_grp (T : Tab) {u v i : ℕ} (hu : u < 13) (hv : v < VF u)
    (hi : i < L u (band u v)) : cinstrAt T (entryOf u v + i) = blockInstr T u v false i := by
  have h1 := entryOf_ge hu hv
  have h2 := block_lt_gEnd hu hv hi
  unfold cinstrAt
  rw [if_neg (by omega), if_pos h2, dec_entry hu hv hi]

theorem cinstrAt_free (T : Tab) {s i : ℕ} (hs : s < 64) (hi : i < 68) :
    cinstrAt T (entF s + i) = fblockInstr s i := by
  unfold cinstrAt entF
  rw [if_neg (by unfold baseF; omega), if_neg (by unfold baseF gEnd; omega),
    if_neg (by omega), if_pos (by omega),
    show (baseF + 68 * s + i - baseF) / 68 = s by omega,
    show (baseF + 68 * s + i - baseF) % 68 = i by omega]

theorem ent_lt {f x : ℕ} (hf : f < 14) (hx : x < Wf f) : ent f x+68 ≤ sentinel := by
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · rw [Wf_zero] at hx; unfold ent entF baseF sentinel; rw [if_pos rfl]; omega
  · obtain ⟨u,rfl⟩ : ∃ u, f = u+1 := ⟨f-1,by omega⟩
    rw [Wf_succ (by omega)] at hx
    rw [ent_succ (by omega)]
    have := block_lt_gEnd (i:=0) (by omega) hx (by have := L_pos u (band u x); omega)
    unfold gEnd sentinel at *; omega

def ctlOf (f x : ℕ) : CInstr := if f = 0 then .dispatch (frG0 x) else ctlF (gOf f + 1)

/-- **Block decode.** The block of index `x` of frame `f`: its entry, its straight part, its
control op, all below the sentinel. -/
theorem cinstrAt_blk {T : Tab} (hT : T.Hyp) {f x : ℕ} (hf : f < 14) (hx : x < Wf f) :
    cinstrAt T (ent f x) = .entry f ∧
      (∀ i (hi : i < (bodyF T f x).length), cinstrAt T (ent f x + 1 + i) = (bodyF T f x)[i]) ∧
      cinstrAt T (ent f x + 1 + (bodyF T f x).length) = ctlOf f x ∧
      ent f x + 1 + (bodyF T f x).length < sentinel := by
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · rw [Wf_zero] at hx
    have hl := fbody_len x
    rw [bodyF_zero]
    rw [ent_zero]
    refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
    · have := cinstrAt_free T hx (i := 0) (by omega)
      rw [Nat.add_zero] at this
      rw [this]; unfold fblockInstr; rw [if_pos rfl]
    · rw [Nat.add_assoc, cinstrAt_free T hx (by omega)]
      unfold fblockInstr
      rw [if_neg (by omega), if_pos (by omega), show 1 + i - 1 = i by omega,
        List.getD_eq_getElem _ _ hi]
    · rw [Nat.add_assoc, cinstrAt_free T hx (by omega)]
      unfold fblockInstr ctlOf
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos rfl]
    · unfold entF baseF sentinel; omega
  · obtain ⟨u, rfl⟩ : ∃ u, f = u + 1 := ⟨f - 1, by omega⟩
    have hu : u < 13 := by omega
    rw [Wf_succ hu] at hx
    have hl := body_len_L (z := false) hT hu hx
    rw [bodyF_succ T hu, ent_succ hu]
    refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
    · have := cinstrAt_grp T (i := 0) hu hx (by omega)
      rw [Nat.add_zero] at this
      rw [this]; unfold blockInstr; rw [if_pos rfl]
    · rw [Nat.add_assoc, cinstrAt_grp T hu hx (by omega)]
      unfold blockInstr
      rw [if_neg (by omega), if_pos (by omega), show 1 + i - 1 = i by omega,
        List.getD_eq_getElem _ _ hi]
    · rw [Nat.add_assoc, cinstrAt_grp T hu hx (by omega)]
      unfold blockInstr ctlOf gOf
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
        Nat.add_sub_cancel]
    · have := block_lt_gEnd (i := (body T u x false).length + 1) hu hx (by omega)
      unfold gEnd sentinel at *; omega

theorem cinstrAt_of_entry {T : Tab} (hT : T.Hyp) {f e : ℕ} (h : IsEntry f e) :
    cinstrAt T e = .entry f := by
  obtain ⟨hf, x, hx, rfl⟩ := h
  exact (cinstrAt_blk hT hf hx).1

theorem isEntry_lt {f e : ℕ} (h : IsEntry f e) : e + 68 ≤ sentinel := by
  obtain ⟨hf, x, hx, rfl⟩ := h
  exact ent_lt hf hx

theorem prologue_ne_entry (s j : ℕ) : prologue s ≠ .entry j := by
  unfold prologue
  split_ifs
  · rcases getD_mem_or (l := proList) (i := s) with h | h
    · exact CInstr.ne_entry_of_straight (proList_straight _ h) j
    · rw [h]; simp
  · simp
  · simp

theorem ctlF_ne_entry (f j : ℕ) : ctlF f ≠ .entry j := by
  unfold ctlF; split_ifs <;> simp

theorem blockInstr_eq_entry {T : Tab} {u v : ℕ} {z : Bool} {i j : ℕ}
    (h : blockInstr T u v z i = .entry j) : i = 0 ∧ j = u + 1 := by
  unfold blockInstr at h
  by_cases h0 : i = 0
  · rw [if_pos h0] at h; exact ⟨h0, (CInstr.entry.inj h).symm⟩
  rw [if_neg h0] at h
  split_ifs at h
  · rcases getD_mem_or (l := body T u v z) (i := i - 1) with hm | hm
    · exact absurd h (CInstr.ne_entry_of_straight (body_straight T u v z _ hm) j)
    · rw [hm] at h; cases h
  · exact absurd h (ctlF_ne_entry _ _)

theorem fblockInstr_eq_entry {s i j : ℕ} (h : fblockInstr s i = .entry j) : i = 0 ∧ j = 0 := by
  unfold fblockInstr at h
  split_ifs at h with h0
  · exact ⟨h0, (CInstr.entry.inj h).symm⟩
  · rcases getD_mem_or (l := fbody s) (i := i - 1) with hm | hm
    · exact absurd h (CInstr.ne_entry_of_straight (fbody_straight s _ hm) j)
    · rw [hm] at h; cases h

theorem cinstrAt_eq_entry {T : Tab} {s f : ℕ} (h : cinstrAt T s = .entry f) : IsEntry f s := by
  rcases cinstrAt_cases T s with ⟨-,h'⟩ | ⟨h1,h2,h'⟩ | ⟨h1,h2,h'⟩ | h' <;> rw [h'] at h
  · exact absurd h (prologue_ne_entry _ _)
  · obtain ⟨hi,rfl⟩ := blockInstr_eq_entry h
    obtain ⟨hu,hv,-,hs⟩ := dec_spec h1 h2
    rw [hi,Nat.add_zero] at hs
    refine ⟨by omega,(dec s).2.1,?_,?_⟩
    · rw [Wf_succ hu]; exact hv
    · rw [ent_succ hu]; exact hs
  · obtain ⟨hi,rfl⟩ := fblockInstr_eq_entry h
    have hs : (s-baseF)/68 < 64 := by unfold baseF at *; omega
    refine ⟨by omega,(s-baseF)/68,by rw [Wf_zero]; exact hs,?_⟩
    rw [ent_zero]; unfold entF; omega
  · cases h

theorem frame_fail {T : Tab} (hT : T.Hyp) {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K)
    {f s : ℕ} (hf : f < 15) (hs : ¬ IsEntry f s) :
    LeanIsa.execute L ⟨pc, frame f⟩ (instrAt T s) = pure none :=
  exec_frame_fail hκ L pc hf (cinstrAt_bounded hT s) fun h => hs (cinstrAt_eq_entry h)

/-- In frame `1`, every entry slot fails: `I0` is reachable only through a frame jump. -/
theorem entry_fail_frame_one {T : Tab} (hT : T.Hyp) {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ)
    (pc : K) {f s : ℕ} (hs : IsEntry f s) :
    LeanIsa.execute L ⟨pc, 1⟩ (instrAt T s) = pure none := by
  show LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt T s).toInstr = pure none
  rw [cinstrAt_of_entry hT hs]
  exact exec_entry_frame_one hκ L pc (by have := hs.1; omega)

/-! ## Program facts -/

theorem finalPc_eq (T : Tab) : (program T).finalPc = gpow sentinel := by
  show gpow (2 ^ 18 - 1) = gpow 262143; norm_num

theorem gpow_ne_finalPc (T : Tab) {e : ℕ} (he : e < sentinel) : gpow e ≠ (program T).finalPc := by
  intro h
  have := gpow_inj (show e < 2 ^ 64 - 1 by unfold sentinel at he; omega)
    (show (262143 : ℕ) < 2 ^ 64 - 1 by norm_num) (h.trans (finalPc_eq T))
  unfold sentinel at he; omega

theorem fetch_eq (T : Tab) {s : ℕ} (hs : s < 2 ^ 18) :
    (program T).fetch (gpow s) = some (cinstrAt T s).toInstr :=
  (program T).fetch_gpow ⟨s, hs⟩

end OptimalOTS.HLFusion
