import Submissions.UpperLeanIsa.FusionMachineValues
import Submissions.UpperLeanIsa.FusionTranscript

/-! Any completing committed image certifies acceptance by the fused verifier. -/
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 0
namespace OptimalOTS.HLFusion
open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV ans cellBits_natV inputWord_pk inputWord_nonce inputWord_one inputWord_two
  inputWord_word length_of_inputWord_len probTrue_zero_of_fixed)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
variable {T : Tab} {P : Fusion.Params}

abbrev idxValue (f : HashTable) (P : Fusion.Params) (m : Message) (η : Nonce) (pk : PublicKey) :=
  P.codec.idxValue f m η pk
abbrev topsOf (f : HashTable) (P : Fusion.Params) (I : Index) (bits : List Bool) :=
  P.reconFromValue f I bits Fusion.chainOrder (fun _ => 0)
abbrev rootValue (f : HashTable) (P : Fusion.Params) := P.rootValue f

section Path
variable {f : HashTable} {v : ℕ → E} {xs : ℕ → ℕ}
  (hP : PathFacts T (oracleRel f) v xs)

def stVal (v : ℕ → E) (r : ℕ) : BitVec 256 := cellBits (v (stCell r + 1)) ++ cellBits (v (stCell r))

theorem stVal_lo (v : ℕ → E) (r : ℕ) : (stVal v r).extractLsb' 0 128 = cellBits (v (stCell r)) :=
  BitVec.extractLsb'_append_eq_right

theorem cellBits_oneV : cellBits oneV = (1 : Word) := by
  simp [oneV, ofK_eq_ofLimbs, cellBits]

def rootSeq (v : ℕ → E) (i : ℕ) : BitVec 256 := if i=0 then 0 else stVal v (i-1)
def homeU (r : ℕ) : ℕ := if r=0 then 5 else if r=1 then 6 else 0

theorem homeU_home {r : ℕ} (_hr : r<3) : homeU r=0 ∨ homeU r=5 ∨ homeU r=6 := by
  unfold homeU; split_ifs <;> omega

theorem homeU_lt {r : ℕ} (_hr : r<3) : homeU r<13 := by unfold homeU; split_ifs <;> omega

theorem hcall_homeU {r : ℕ} (hr : r<3) : hcall (homeU r)=r := by interval_cases r <;> rfl

def rootMsg (T : Tab) (xs : ℕ → ℕ) (r j : ℕ) : ℕ :=
  rt T (homeU r) (xs (homeU r+1)) false j

include hP in
theorem rootMd_cell (hC : Compat P T) (r : Fin 3) : cellBits (v (rootMdCell r.val)) = P.rootMd r := by
  have he : rootMdCell r.val = cCell (Fusion.rootIndex r).val := by fin_cases r <;> rfl
  have hi : (Fusion.rootIndex r).val ≤ 22 := by fin_cases r <;> decide
  rw [he,v_c hP hi,hC.rootMd]

theorem root_query_of (hone : v oneCell = oneV)
    (hmd : ∀ r : Fin 3, cellBits (v (rootMdCell r.val)) = P.rootMd r) (r : Fin 3) :
    blake2sQuery ![v (rootMsg T xs r.val 0),v (rootMsg T xs r.val 1),
      v (rootMsg T xs r.val 2),v (rootMsg T xs r.val 3)]
      (v (rootCv r.val)) (v (rootCv r.val+1)) (v (rootMdCell r.val)) =
      P.rootInput (topsV T v xs) r (rootSeq v r.val) := by
  rw [blake2sQuery_eq,hmd r]
  fin_cases r <;>
    simp [rootMsg,homeU,rt,rootCv,Fusion.Params.rootInput,rootSeq,topsV,rtopCell,
      exported,dg,unitOf,coordOf,topCell,stVal_lo,stCell,hone,cellBits_oneV]

include hP in
theorem root_query (hC : Compat P T) (r : Fin 3) :
    blake2sQuery ![v (rootMsg T xs r.val 0),v (rootMsg T xs r.val 1),
      v (rootMsg T xs r.val 2),v (rootMsg T xs r.val 3)]
      (v (rootCv r.val)) (v (rootCv r.val+1)) (v (rootMdCell r.val)) =
      P.rootInput (topsV T v xs) r (rootSeq v r.val) :=
  root_query_of (v_one hP) (rootMd_cell hP hC) r

include hP in
theorem root_step (hC : Compat P T) (r : Fin 3) :
    rootSeq v (r.val+1) = f ⟨896,P.rootInput (topsV T v xs) r (rootSeq v r.val)⟩ := by
  have hmem : CInstr.blake (rootMsg T xs r.val 0) (rootMsg T xs r.val 1)
      (rootMsg T xs r.val 2) (rootMsg T xs r.val 3) (rootCv r.val) (stCell r.val) (rootMdCell r.val) ∈
      bodyF T (frU (xs 0) (homeU r.val+1)) (xs (homeU r.val+1)) := by
    rw [bodyF_frU_succ T _ (homeU_lt r.isLt)]
    unfold body
    simp only [List.mem_append]
    left; left; right
    unfold rootIns
    rw [if_pos (homeU_home r.isLt),hcall_homeU r.isLt]
    exact List.mem_singleton_self _
  have hrel := hP.blk (homeU r.val+1) (by have := homeU_lt r.isLt; omega) _ hmem
  have hp := oracle_pair hrel
  rw [root_query hP hC r] at hp
  unfold rootSeq
  rw [if_neg (by omega),Nat.add_sub_cancel]
  exact hp

include hP in
theorem rootValue_topsV (hC : Compat P T) : rootValue f P (topsV T v xs) = cellBits (v (stCell 2)) := by
  have h0 : stVal v 0 = f ⟨896,P.rootInput (topsV T v xs) 0 0⟩ := root_step hP hC 0
  have h1 : stVal v 1 = f ⟨896,P.rootInput (topsV T v xs) 1 (stVal v 0)⟩ := root_step hP hC 1
  have h2 : stVal v 2 = f ⟨896,P.rootInput (topsV T v xs) 2 (stVal v 1)⟩ := root_step hP hC 2
  unfold rootValue Fusion.Params.rootValue
  simp only [Fusion.Params.rootFromValue]
  rw [← h0,← h1,← h2,stVal_lo]

end Path

open Fusion in
theorem reconFromValue_of_tops (f : HashTable) (I : Index) (bits : List Bool) (ctx : Tops)
    (hchain : ∀ k : Fin 42, P.chainValue f ctx k (P.codec.len k-1-P.codec.digit I k)
      (P.codec.digit I k) (decodeWord bits k) = ctx k.val)
    (l : List (Fin 42)) (hl : l.Pairwise (fun k k' => evaluationRank k.val < evaluationRank k'.val))
    (t : Tops) (ht : ∀ d, d ∉ l.map Fin.val → t d = ctx d) : P.reconFromValue f I bits l t = ctx := by
  induction l generalizing t with
  | nil => exact funext fun d => ht d (by simp)
  | cons k l ih =>
    obtain ⟨hbefore,hl⟩ := List.pairwise_cons.mp hl
    have hdep : ∀ u : Fin 6, owner k = some u → ∀ d ∈ children u, t d = ctx d := by
      intro u hu d hd
      apply ht d
      intro hmem
      have hr := dependency_precedes u u.isLt k.val ((owner_mem k u).mp hu) d hd
      obtain ⟨k',hk',he⟩ := List.mem_map.mp hmem
      rcases List.mem_cons.mp hk' with he' | hk'
      · have heq : d = k.val := he.symm.trans (congrArg Fin.val he')
        rw [heq] at hr
        omega
      · have hh := hbefore k' hk'
        rw [he] at hh
        omega
    rw [Fusion.Params.reconFromValue,P.chainValue_context f t ctx k _ _ _ hdep,hchain]
    apply ih hl
    intro d hd
    by_cases he : d=k.val
    · subst d; rw [Function.update_self]
    · rw [Function.update_of_ne he]
      exact ht d (by simpa only [List.map_cons,List.mem_cons,not_or] using ⟨he,hd⟩)

section Accept

variable {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool} {v : ℕ → E}

/-- **Fixed-table acceptance.** Cell values satisfying the relations along the path of `xs`, with
its landings, and agreeing with the loader on the pinned cells, certify a signature the verifier
accepts under the table. -/
theorem accept_of_path (hT : T.Hyp) (hC : Compat P T) (hpin : ∀ c < 47, v c = inputWord pk m bits c)
    {xs : ℕ → ℕ} (hV : Valid xs) (hP : PathFacts T (oracleRel f) v xs) (hL : Landing v xs) :
    bits.length = sigBits ∧ P.codec.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk := by
  -- the length
  have hlen : bits.length = 5503 :=
    length_of_inputWord_len pk m bits ((hpin 3 (by omega)).symm.trans (v_len hP))
  -- the index
  have hidx : (ans f (P.codec.idxInput m (decodeNonce bits) pk)).extractLsb' 0 128 = cellBits (v idxCell) := by
    have h : (CInstr.blake msgLo msgHi nonceCell pkCell oneCell idxCell gCell).Rel f v :=
      hP.pro _ pro_mem_idx
    have hlo := oracle_lo h
    have hpk : cellBits (v pkCell) = pk := by
      rw [show pkCell = 0 from rfl, hpin 0 (by omega), inputWord_pk]
      exact cellBits_cellOfBits pk
    have hq : blake2sQuery ![v msgLo, v msgHi, v nonceCell, v pkCell] (v oneCell)
        (v (oneCell + 1)) (v gCell) = P.codec.idxInput m (decodeNonce bits) pk := by
      rw [blake2sQuery_eq, cb_cv hP hC, v_g hP,
        show nonceCell = 46 from rfl, show msgHi = 2 from rfl,
        show msgLo = 1 from rfl, hpin 46 (by omega), hpin 2 (by omega),
        hpin 1 (by omega), inputWord_nonce pk m bits hlen, inputWord_two,
        inputWord_one, cellBits_cellOfBits (nonceWord (decodeNonce bits)),
        cellBits_cellOfBits (m.extractLsb' 128 128), cellBits_cellOfBits (m.extractLsb' 0 128),
        msg_split, hpk]
      unfold Params.idxInput
      rw [hC.idxMd]
    rw [hq] at hlo
    exact hlo.symm
  set I := (ans f (P.codec.idxInput m (decodeNonce bits) pk)).extractLsb' 0 128 with hIdef
  have heff : idxValue f P m (decodeNonce bits) pk = effective I := by
    exact indexSlice_effective _
  -- the tie
  have hacc := acc_eq hV hP 12 (by omega)
  rw [show accCell 12 = idxCell from rfl] at hacc
  have hlt : ∀ w, (fun w => if w < 13 then xs (w + 1) else 0) w < 2 ^ gb w := by
    intro w
    by_cases hw : w < 13
    · simp only [if_pos hw]; have := hV (w + 1) (by omega); rw [Wf_succ hw] at this
      exact lt_of_lt_of_le this (VF_le w hw)
    · simp only [if_neg hw]; positivity
  have hofd : ofDigitsW gb (fun w => xs (w + 1)) 13 =
      ofDigitsW gb (fun w => if w < 13 then xs (w + 1) else 0) 13 := by
    unfold ofDigitsW
    exact Finset.sum_congr rfl fun w hw => by simp only [if_pos (Finset.mem_range.mp hw)]
  have hI : I.toNat = ofDigitsW gb (fun w => if w < 13 then xs (w + 1) else 0) 13 := by
    rw [hidx, hacc, cellBits_natV, BitVec.toNat_ofNat, hofd, Nat.mod_eq_of_lt]
    have := ofDigitsW_lt gb _ hlt 13
    rwa [show posW gb 13 = 128 from POS_13] at this
  have hfield : ∀ u < 13, field u I = xs (u + 1) := by
    intro u hu
    unfold field
    rw [hI, digitW_ofDigitsW gb _ hlt 13 u hu, if_pos hu]
  -- the layer
  have hsum := layer_of_facts hT hV hP hL
  have hx0 : xs 0 < 64 := by have := hV 0 (by omega); rwa [Wf_zero] at this
  have hgc : gcost T I = gsum T xs := by
    unfold gcost gsum
    rw [list_sum_range]
    exact Finset.sum_congr rfl fun u hu => by rw [hfield u (Finset.mem_range.mp hu)]
  have hdig : ∀ k : Fin numChains, P.codec.digit (effective I) k = dg T xs k.val := by
    intro k
    by_cases hk0 : k.val = 0
    · have hk : k = 0 := Fin.ext hk0
      have hlive : ∀ u < 13, field u I < VF u := fun u hu => by
        rw [hfield u hu]; have := hV (u + 1) (by omega); rwa [Wf_succ hu] at this
      rw [hk, hC.digit_free I hlive, hgc,
        show dg T xs (0 : Fin numChains).val = xs 0 from if_pos rfl]
      unfold freeDigit
      rw [if_pos ⟨by omega, by omega⟩]
      omega
    · obtain ⟨hu, hi, hc⟩ := chainOf_unitOf k.val k.isLt (by omega)
      have hk : k = ⟨chainOf (unitOf k.val) (coordOf k.val), chainOf_lt _ hu _ hi⟩ :=
        Fin.ext hc.symm
      rw [hk, hC.digit_grp I _ _ hu hi, hfield _ hu, dg_chainOf T xs hu hi]
  rw [heff]
  refine ⟨hlen, ?_, ?_⟩
  · show ∑ k : Fin numChains, P.codec.digit (effective I) k = P.codec.layer
    rw [hC.layer, Finset.sum_congr rfl (fun k _ => hdig k),
      Fin.sum_univ_eq_sum_range (fun k => dg T xs k) 42, dg_sum]
    unfold gsum at hsum
    exact hsum
  · -- the tops
    have htops : topsOf f P (effective I) bits = topsV T v xs := by
      refine reconFromValue_of_tops f (effective I) bits (topsV T v xs) ?_ Fusion.chainOrder
        Fusion.Params.chainOrder_ranked (fun _ => 0) ?_
      · intro k
        have hw : cellBits (v (wCell k.val)) = decodeWord bits k := by
          have hk := k.isLt
          rw [hpin (wCell k.val) (by unfold wCell numChains at *; omega),
            show wCell k.val=4+k.val from rfl,inputWord_word pk m bits hlen k,cellBits_cellOfBits]
        rw [hdig k,hC.len k,← hw]
        exact (top_eq hV hP hT hC k.isLt).symm.trans (topsV_at T v xs k.isLt).symm
      · intro d hd
        have hn : ¬ d<42 := by
          intro hh
          exact hd (List.mem_map.mpr ⟨⟨d,hh⟩,Fusion.chainOrder_permutation.mem_iff.mpr
            (List.mem_finRange ⟨d,hh⟩),rfl⟩)
        simp only [topsV,if_neg hn]
    rw [htops, rootValue_topsV hP hC]
    -- the public key
    have hb := hP.blk 13 (by omega)
    rw [show (13 : ℕ) = 12 + 1 from rfl, bodyF_frU_succ T _ (by omega)] at hb
    have h : v pkCell = v (stCell 2) * v oneCell := hb (copy (stCell 2) pkCell) (by
      unfold body nextOp copy; simp)
    rw [v_one hP, mul_oneV] at h
    rw [← h, show pkCell = 0 from rfl, hpin 0 (by omega), inputWord_pk]
    exact cellBits_cellOfBits pk

end Accept

theorem inputCells_eq : LeanIsa.inputCells = 47 := rfl

theorem Lx_loadInput {κ : ℕ} (pk : PublicKey) (m : Message) (bits : List Bool) (L : MemImage κ)
    {c : ℕ} (h : c < 2 ^ κ) :
    Lx (LeanIsa.loadInput pk m bits L) c = if c < 47 then inputWord pk m bits c else Lx L c := by
  unfold Lx
  rw [dif_pos h, dif_pos h]
  show (if c < LeanIsa.inputCells then inputWord pk m bits c else L ⟨c, h⟩) = _
  rw [inputCells_eq]

theorem Lx_loadInput_pin {κ : ℕ} (hκ : 16 ≤ κ) (pk : PublicKey) (m : Message)
    (bits : List Bool) (L : MemImage κ) {c : ℕ} (hc : c < 47) :
    Lx (LeanIsa.loadInput pk m bits L) c = inputWord pk m bits c := by
  have h16 : (2 : ℕ) ^ 16 ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
  have h2 : c < 2 ^ κ := Nat.lt_of_lt_of_le hc (le_trans (by norm_num) h16)
  rw [Lx_loadInput pk m bits L h2, if_pos hc]

/-- **Fixed-table soundness.** If the run on the loaded image completes under the table `f`,
the verifier's fixed-table decision is `true`. -/
theorem fixed_sound (hT : T.Hyp) (hC : Compat P T) {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) (L : MemImage κ) {n c : ℕ}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits L) n Regs.initial))) :
    bits.length = sigBits ∧ P.codec.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk := by
  rw [initial_eq] at h
  have hpin := pinned_of_sem (simSem f) (oracleRel f) (sim_straight hT h16 hκ (lengthDomain_load h16 pk m bits L) f) h
  have hw := walk_of_sim hT h16 hκ (lengthDomain_load h16 pk m bits L) f hpin (by norm_num) h
  obtain ⟨hV, hP, hL, -, -⟩ := walk_full hT hw
  exact accept_of_path hT hC (fun c hc => Lx_loadInput_pin h16 pk m bits L hc) hV hP hL

theorem decision_true {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
    (h : bits.length = sigBits ∧ P.codec.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk) :
    P.verifyValue f pk m bits = true := by
  simp only [Fusion.Params.verifyValue,ne_eq,h.1,not_true_eq_false,if_false,h.2.1]
  rw [show P.rootValue f (P.reconFromValue f (P.codec.idxValue f m (decodeNonce bits) pk)
    bits Fusion.chainOrder (fun _ => 0)) = pk from h.2.2]
  simp

theorem sound (hT : T.Hyp) (hC : Compat P T) (S : LeanIsa.Submission) (hs : S.scheme = P.scheme)
    (hp : S.program = program T) : S.Sound := by
  intro pk m bits κ h16 h32 L n
  apply probTrue_zero_of_fixed
  intro f
  have hexec : S.exec L n pk m bits =
      LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits L) n Regs.initial := by
    unfold LeanIsa.Submission.exec
    rw [hp]
  have hver : S.scheme.verify pk m bits = P.verify pk m bits := by
    rw [hs]
    rfl
  rw [hexec, hver]
  simp only [simulateQ_bind, simulateQ_pure, Fusion.Params.fixed_verify, pure_bind]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨o, ho, hmem⟩ := hmem
  rw [mem_support_pure_iff] at hmem
  cases o with
  | none => simp at hmem
  | some c =>
    have hd := decision_true (fixed_sound hT hC h16 h32 f pk m bits L ho)
    rw [hd] at hmem
    simp at hmem

end
end OptimalOTS.HLFusion
