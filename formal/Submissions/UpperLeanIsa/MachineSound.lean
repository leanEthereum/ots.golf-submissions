import Submissions.UpperLeanIsa.MachineCycles

/-!
# Soundness of the HL-FLAT-A machine under a fixed oracle table

`accept_of_path`: cell values satisfying the fixed-table relations along the path of a digit
vector `s`, with the landings of `s`, and agreeing with the loader on the pinned cells, certify
a signature that `Flat.params.verify` accepts under the table.

1. The prologue pins `Z, ONE, LEN, TIDX, g, K0` and the symbols; the length cell pins
   `|σ| = 5504`, so the loader's cells are the 42 words and the nonce.
2. The index `BLAKE2S` is the scheme's index query; its low half `I` is the index cell.
3. The tie accumulates the tie patterns into the index cell (`acc_eq`), so `digit I k = s k`;
   the exponent identity (`layer_of_facts`, hash-free) gives `Σ s = 106`, so `I` is accepted.
4. The inline `BLAKE2S` compute the verifier's chain tops (`chain_top`), the ten root calls
   compute its root (`root_state`), and the pk `XOR` compares it with the public key.
-/

namespace OptimalOTS.HLFlat

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

/-- The scheme's parameters. -/
abbrev FP : Params := Flat.params

/-! ## Cell values and queries -/

theorem blake2sQuery_eq (a b c d cv0 cv1 md : E) :
    blake2sQuery ![a, b, c, d] cv0 cv1 md =
      hashInput (cellBits cv1 ++ cellBits cv0) (cellBits d ++ cellBits c ++ cellBits b ++ cellBits a)
        (cellBits md) := rfl

theorem cellBits_oneV : cellBits oneV = 1 := by rw [oneV, cellBits_ofK]; decide

theorem cellBits_gV : cellBits gV = BitVec.ofNat 128 2 := by rw [gV, cellBits_ofK]; decide

theorem cv_const : (1 : BitVec 128) ++ (0 : BitVec 128) = Flat.cv := by unfold Flat.cv; decide

theorem msg_split (a b : BitVec 128) (m : Message) :
    a ++ b ++ m.extractLsb' 128 128 ++ m.extractLsb' 0 128 = a ++ b ++ m := by
  have h := hi_append_lo m
  conv_rhs => rw [← h]
  rw [BitVec.append_assoc (x₁ := a ++ b)]
  exact BitVec.cast_eq _ _

theorem fpat_zero (k : ℕ) : fpat k 0 = 0 := by unfold fpat; rw [Nat.zero_mul]; exact natV_zero

/-- The oracle relation of a `BLAKE2S` gives its low output half. -/
theorem oracle_lo {f : HashTable} {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}
    (h : oracleRel f m cv0 cv1 o0 o1 md) :
    cellBits o0 = (f ⟨896, blake2sQuery m cv0 cv1 md⟩).extractLsb' 0 128 := h.2.2.2.2.2.2.1

/-- The oracle relation of a `BLAKE2S` gives its whole output pair. -/
theorem oracle_pair {f : HashTable} {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}
    (h : oracleRel f m cv0 cv1 o0 o1 md) :
    cellBits o1 ++ cellBits o0 = f ⟨896, blake2sQuery m cv0 cv1 md⟩ :=
  out_pair _ _ _ h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-! ## Chains under the table -/

/-- A sequence obeying the chain recursion is the fixed-table chain. -/
theorem chainValue_of_seq (f : HashTable) (P : Params) (k : Fin numChains) :
    ∀ (n j0 : ℕ) (X : ℕ → Word),
      (∀ t < n, X (t + 1) = (f ⟨896, P.chainInput k (j0 + t) (X t)⟩).extractLsb' 0 128) →
        X n = chainValue f P k j0 n (X 0) := by
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

/-- A sequence obeying the root recursion is the fixed-table root state. -/
theorem rootState_of_seq (f : HashTable) (P : Params) (t : Fin numChains → Word) :
    ∀ (n r : ℕ) (Y : ℕ → BitVec 256),
      (∀ i < n, Y (i + 1) = f ⟨896, P.rootInput t (r + i) (Y i)⟩) →
        rootState f P t r n (Y 0) = Y n := by
  intro n
  induction n with
  | zero => intro r Y _; rfl
  | succ n ih =>
    intro r Y h
    have h0 : Y 1 = f ⟨896, P.rootInput t r (Y 0)⟩ := by simpa using h 0 (by omega)
    calc rootState f P t r (n + 1) (Y 0) = rootState f P t (r + 1) n (Y 1) := by rw [h0]; rfl
      _ = Y (n + 1) := ih (r + 1) (fun i => Y (i + 1)) (fun i hi => by
        rw [h (i + 1) (by omega), show r + (i + 1) = r + 1 + i by ring])

/-! ## The chain sequence of a block -/

/-- The chain values a block walks through: the revealed word, the intermediate pairs, and the
chain's output cell after the last step. -/
def chainSeq (v : ℕ → E) (k n : ℕ) (t : ℕ) : Word :=
  cellBits (v (if t = 0 then wCell k else if t = n then chainOut k else xCell k (t - 1)))

theorem chainSeq_zero (v : ℕ → E) (k n : ℕ) : chainSeq v k n 0 = cellBits (v (wCell k)) := by
  unfold chainSeq; rw [if_pos rfl]

theorem chainSeq_last {v : ℕ → E} {k n : ℕ} (hn : n ≠ 0) :
    chainSeq v k n n = cellBits (v (chainOut k)) := by
  unfold chainSeq; rw [if_neg hn, if_pos rfl]

/-- Step `t` writes the pair of `chainSeq (t + 1)`. -/
theorem chainSeq_succ (v : ℕ → E) (k n t : ℕ) :
    chainSeq v k n (t + 1) = cellBits (v (if t + 1 = n then chainOut k else xCell k t)) := by
  unfold chainSeq; rw [if_neg (by omega)]
  by_cases h : t + 1 = n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Nat.add_sub_cancel]

/-- Step `t < n` reads `chainSeq t`. -/
theorem chainSeq_eq_src (v : ℕ → E) {k n t : ℕ} (ht : t < n) :
    cellBits (v (if t = 0 then wCell k else xCell k (t - 1))) = chainSeq v k n t := by
  unfold chainSeq
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, if_neg (by omega)]

/-! ## The path -/

section Path

variable {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool} {v : ℕ → E}
  {s : ℕ → ℕ} (hV : Valid s) (hP : PathFacts (fun t => (cinstrAt t).Rel f v) s)

include hP in
theorem pro_rel {t : ℕ} {ci : CInstr} (ht : t < 58) (hc : cinstrAt t = ci) : ci.Rel f v := by
  have := hP.pro t ht; rwa [hc] at this

include hV hP in
theorem blk_rel {k i : ℕ} (hk : k < 42) (hi0 : 0 < i) (hi : i ≤ 1 + pre k + s k + post k) :
    (blockOp k (s k) i).Rel f v := by
  have := hP.blk k hk i hi0 hi; rwa [cinstrAt_blk hk (hV k hk) hi0 hi] at this

include hP in
theorem root_rel {t : ℕ} (ht : t < 11) : (rootOp t).Rel f v := by
  have := hP.root t ht; rwa [cinstrAt_root ht] at this

section Consts

include hP

theorem v_z : v zCell = 0 := pro_rel hP (by omega) cinstrAt_set0
theorem v_one : v oneCell = oneV := pro_rel hP (by omega) cinstrAt_set1
theorem v_len : v lenCell = natV 5504 := pro_rel hP (by omega) cinstrAt_set2
theorem v_tidx : v tidxCell = natV 10 := pro_rel hP (by omega) cinstrAt_set3
theorem v_g : v gCell = gV := pro_rel hP (by omega) cinstrAt_set4
theorem v_sym {i : ℕ} (hi : i < 7) : v (symCell i) = natV (i + 3) :=
  pro_rel hP (by omega) (cinstrAt_sym hi)

theorem cb_z : cellBits (v zCell) = 0 := by rw [v_z hP]; exact cellBits_zero_E

theorem cb_cv : cellBits (v (zCell + 1)) ++ cellBits (v zCell) = Flat.cv := by
  rw [show zCell + 1 = oneCell from rfl, v_one hP, cb_z hP, cellBits_oneV, cv_const]

end Consts

/-- The chain-step query of a chain op. -/
theorem chainOp_query (hP : PathFacts (fun t => (cinstrAt t).Rel f v) s) {k : ℕ} (hk : k < 42)
    {j : ℕ} (hj : j < W k) (x : E) :
    blake2sQuery ![x, v (symCell (tagPos k j % 7)), v (symCell (tagPos k j / 7 % 7)),
        v (symCell (tagPos k j / 49))] (v zCell) (v (zCell + 1)) (v oneCell) =
      FP.chainInput ⟨k, hk⟩ j (cellBits x) := by
  have hp : tagPos k j < 343 := by
    have := @W_le k; unfold tagPos Flat.off; split_ifs <;> omega
  rw [blake2sQuery_eq, v_sym hP (Nat.mod_lt _ (by norm_num)), v_sym hP (Nat.mod_lt _ (by norm_num)),
    v_sym hP (by omega), cellBits_natV, cellBits_natV, cellBits_natV, cb_cv hP, v_one hP,
    cellBits_oneV]
  rfl

include hV in
/-- **Chain tops.** The root reads the verifier's chain top of chain `k`. -/
theorem chain_top (hP : PathFacts (fun t => (cinstrAt t).Rel f v) s) {k : ℕ} (hk : k < 42) :
    cellBits (v (rootTop k)) =
      chainValue f FP ⟨k, hk⟩ (W k - 1 - s k) (s k) (cellBits (v (wCell k))) := by
  have hs := hV k hk
  have hz := v_z hP
  by_cases h0 : s k = 0
  · rw [h0]
    show cellBits (v (rootTop k)) = cellBits (v (wCell k))
    by_cases hk0 : k = 0
    · subst hk0
      have h := blk_rel hV hP (k := 0) (i := s 0 + 2) hk (by omega)
        (by rw [pre_zero, post_zero]; omega)
      unfold blockOp at h
      rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_pos rfl, if_pos h0] at h
      have h' : v cvCell = v (wCell 0) + v zCell := h
      rw [show rootTop 0 = cvCell from rfl, h', hz, add_zero]
    · have h := blk_rel hV hP (k := k) (i := 1) hk (by omega) (by omega)
      unfold blockOp at h
      rw [if_neg hk0, if_pos rfl, if_pos h0] at h
      have h' : v (rootTop k) = v (wCell k) + v zCell := h
      rw [h', hz, add_zero]
  · -- the inline steps
    have hstep : ∀ t < s k, chainSeq v k (s k) (t + 1) =
        (f ⟨896, FP.chainInput ⟨k, hk⟩ (W k - 1 - s k + t) (chainSeq v k (s k) t)⟩).extractLsb' 0 128 := by
      intro t ht
      have h := blk_rel hV hP (k := k) (i := 1 + pre k + t) hk (by omega) (by omega)
      rw [blockOp_chain ht] at h
      unfold chainOp at h
      have hlo := oracle_lo h
      rw [chainOp_query hP hk (by omega)] at hlo
      rw [chainSeq_eq_src v ht] at hlo
      rw [chainSeq_succ]
      exact hlo
    have hend := chainValue_of_seq f FP ⟨k, hk⟩ (s k) (W k - 1 - s k) (chainSeq v k (s k)) hstep
    rw [chainSeq_last h0, chainSeq_zero] at hend
    by_cases hk0 : k = 0
    · subst hk0
      have h := blk_rel hV hP (k := 0) (i := s 0 + 2) hk (by omega)
        (by rw [pre_zero, post_zero]; omega)
      unfold blockOp at h
      rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg h0] at h
      have h' : v cvCell = v (topCell 0) + v zCell := h
      rw [show rootTop 0 = cvCell from rfl, h', hz, add_zero, ← hend]; rfl
    · rw [show rootTop k = chainOut k by unfold rootTop chainOut; rw [if_neg hk0],
        hend]

/-! ### The tie -/

/-- The digit vector, zero past the chains. -/
def sz (s : ℕ → ℕ) (k : ℕ) : ℕ := if k < 42 then s k else 0

omit hP in
theorem sz_lt (hV : Valid s) (k : ℕ) : sz s k < 2 ^ Flat.wid k := by
  unfold sz Flat.wid
  by_cases hk : k < 42
  · rw [if_pos hk]
    have := hV k hk
    unfold W at this
    split_ifs at * <;> omega
  · rw [if_neg hk, if_neg (by omega), if_neg hk]; norm_num

omit hV hP in
theorem posW_le_42 {k : ℕ} (hk : k ≤ 42) : posW Flat.wid k ≤ 128 := by
  rw [← Flat.pos_42]; exact posW_mono Flat.wid hk

include hV hP in
/-- **The tie.** The accumulator after chain `k` holds the digits `s 0, …, s k`. -/
theorem acc_eq : ∀ k < 42, v (accCell k) = natV (ofDigitsW Flat.wid (sz s) (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h := blk_rel hV hP (k := 0) (i := 1) hk (by omega) (by rw [pre_zero]; omega)
    unfold blockOp at h
    rw [if_pos rfl, if_pos rfl] at h
    have h' : v (accCell 0) = fpat 0 (s 0) := h
    rw [h', ofDigitsW_succ, ofDigitsW_zero, Nat.zero_add]
    unfold fpat sz; rw [if_pos hk]
  | succ k ih =>
    intro hk
    have hop : v (if s (k + 1) = 0 then zCell else tCell (k + 1)) = fpat (k + 1) (s (k + 1)) := by
      by_cases h0 : s (k + 1) = 0
      · rw [if_pos h0, v_z hP, h0, fpat_zero]
      · rw [if_neg h0]
        have h := blk_rel hV hP (k := k + 1) (i := 1) hk (by omega) (by omega)
        unfold blockOp at h
        rw [if_neg (by omega), if_pos rfl, if_neg h0] at h
        exact h
    have h := blk_rel hV hP (k := k + 1) (i := 2) hk (by omega)
      (by rw [pre_pos (by omega)]; omega)
    unfold blockOp at h
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl, Nat.add_sub_cancel] at h
    have h' : v (accCell (k + 1)) = v (accCell k) + v (if s (k + 1) = 0 then zCell else tCell (k + 1)) := h
    have hlt := ofDigitsW_lt Flat.wid (sz s) (sz_lt hV) (k + 1)
    have hlt2 := ofDigitsW_lt Flat.wid (sz s) (sz_lt hV) (k + 1 + 1)
    have h42 := posW_le_42 (k := k + 1 + 1) (by omega)
    have hpow : 2 ^ posW Flat.wid (k + 1 + 1) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) h42
    rw [h', hop, ih (by omega)]
    unfold fpat
    rw [show s (k + 1) = sz s (k + 1) by unfold sz; rw [if_pos hk],
      natV_add_disjoint hlt (by rw [← ofDigitsW_succ]; omega), ← ofDigitsW_succ]

/-! ### The root -/

/-- The root state after call `r`. -/
def stVal (v : ℕ → E) (r : ℕ) : BitVec 256 := cellBits (v (stCell r + 1)) ++ cellBits (v (stCell r))

/-- The tops the root reads. -/
def topsV (v : ℕ → E) (k : Fin numChains) : Word := cellBits (v (rootTop k.val))

theorem topAt_topsV (v : ℕ → E) {i : ℕ} (hi : i < 42) :
    Params.topAt (topsV v) i = cellBits (v (rootTop i)) := by
  unfold Params.topAt; rw [dif_pos hi]; rfl

theorem rhoCell_eq {r : ℕ} (h2 : 2 ≤ r) (h9 : r < 9) : rhoCell r = symCell (r - 2) := by
  unfold rhoCell; rw [if_neg (by omega), if_neg (by omega), if_pos h9]

theorem rootMd_eq {r : ℕ} (h2 : 2 ≤ r) (h9 : r < 9) : FP.rootMd r = BitVec.ofNat 128 (r + 1) := by
  show Flat.rootMd r = _
  unfold Flat.rootMd; rw [if_neg (by omega), if_neg (by omega), if_pos h9]

include hP in
theorem rho_md {r : ℕ} (hr : r < 10) : cellBits (v (rhoCell r)) = FP.rootMd r := by
  by_cases h0 : r = 0
  · subst h0; rw [show rhoCell 0 = zCell from rfl, cb_z hP]; rfl
  by_cases h1 : r = 1
  · subst h1; rw [show rhoCell 1 = gCell from rfl, v_g hP, cellBits_gV]; rfl
  by_cases h9 : r < 9
  · rw [rhoCell_eq (by omega) h9, rootMd_eq (by omega) h9, v_sym hP (by omega), cellBits_natV,
      show r - 2 + 3 = r + 1 by omega]
  · obtain rfl : r = 9 := by omega
    rw [show rhoCell 9 = lenCell from rfl, v_len hP, cellBits_natV]; rfl

/-- The root state sequence: the initial cv pair, then the states. -/
def rootSeq (v : ℕ → E) (i : ℕ) : BitVec 256 :=
  if i = 0 then Params.rootInit (topsV v) else stVal v (i - 1)

theorem rootCv_pair (v : ℕ → E) (i : ℕ) :
    cellBits (v (rootCv i + 1)) ++ cellBits (v (rootCv i)) = rootSeq v i := by
  unfold rootCv rootSeq
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos h0]
    unfold Params.rootInit
    rw [topAt_topsV v (by omega), topAt_topsV v (by omega)]
    rfl
  · rw [if_neg h0, if_neg h0]; rfl

include hP in
theorem root_step {i : ℕ} (hi : i < 10) :
    rootSeq v (i + 1) = f ⟨896, FP.rootInput (topsV v) i (rootSeq v i)⟩ := by
  have hrel := root_rel hP (t := i) (by omega)
  unfold rootOp at hrel
  rw [if_pos hi] at hrel
  have hp := oracle_pair hrel
  have hq : blake2sQuery ![v (rootTop (4 * i + 2)), v (rootTop (4 * i + 3)),
      v (rootTop (4 * i + 4)), v (rootTop (4 * i + 5))] (v (rootCv i)) (v (rootCv i + 1))
      (v (rhoCell i)) = FP.rootInput (topsV v) i (rootSeq v i) := by
    rw [blake2sQuery_eq, rootCv_pair, rho_md hP hi]
    unfold Params.rootInput
    rw [topAt_topsV v (by omega), topAt_topsV v (by omega), topAt_topsV v (by omega),
      topAt_topsV v (by omega)]
  rw [hq] at hp
  unfold rootSeq
  rw [if_neg (by omega), Nat.add_sub_cancel]
  exact hp

include hP in
/-- **The root.** The ten root calls compute the fixed-table root of the tops. -/
theorem root_state : rootState f FP (topsV v) 0 10 (Params.rootInit (topsV v)) = stVal v 9 := by
  have h := rootState_of_seq f FP (topsV v) 10 0 (rootSeq v) (fun i hi => by
    rw [Nat.zero_add]; exact root_step hP hi)
  unfold rootSeq at h
  rw [if_pos rfl, if_neg (by omega)] at h
  exact h

include hP in
theorem rootValue_topsV : rootValue f FP (topsV v) = cellBits (v (stCell 9)) := by
  unfold rootValue
  rw [root_state hP]
  exact BitVec.extractLsb'_append_eq_right

end Path

section Accept

variable {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool} {v : ℕ → E}

/-- **Fixed-table acceptance.** Cell values satisfying the relations along the path of `s`, with
its landings, and agreeing with the loader on the pinned cells, certify a signature the verifier
accepts under the table. -/
theorem accept_of_path (hpin : ∀ c < 47, v c = inputWord pk m bits c) {s : ℕ → ℕ} (hV : Valid s)
    (hP : PathFacts (fun t => (cinstrAt t).Rel f v) s) (hL : Landing v s) :
    bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk) ∧
      rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) = pk := by
  -- the length
  have hlen : bits.length = 5504 :=
    length_of_inputWord_len pk m bits ((hpin 3 (by omega)).symm.trans (v_len hP))
  -- the index
  have hidx : idxValue f FP m (decodeNonce bits) pk = cellBits (v idxCell) := by
    have h := pro_rel hP (by omega) cinstrAt_55
    have hlo := oracle_lo h
    have hpk : cellBits (v pkCell) = pk := by
      rw [show pkCell = 0 from rfl, hpin 0 (by omega), inputWord_pk]
      exact cellBits_cellOfBits pk
    have hq : blake2sQuery ![v msgLo, v msgHi, v nonceCell, v pkCell] (v zCell) (v (zCell + 1))
        (v tidxCell) = FP.idxInput m (decodeNonce bits) pk := by
      rw [blake2sQuery_eq, cb_cv hP, v_tidx hP, cellBits_natV,
        show nonceCell = 46 from rfl, show msgHi = 2 from rfl,
        show msgLo = 1 from rfl, hpin 46 (by omega), hpin 2 (by omega),
        hpin 1 (by omega), inputWord_nonce pk m bits hlen, inputWord_two,
        inputWord_one, cellBits_cellOfBits (decodeNonce bits),
        cellBits_cellOfBits (m.extractLsb' 128 128), cellBits_cellOfBits (m.extractLsb' 0 128),
        msg_split, hpk]
      rfl
    rw [hq] at hlo
    exact hlo.symm
  -- the tie
  have hacc := acc_eq hV hP 41 (by omega)
  rw [show accCell 41 = idxCell from rfl] at hacc
  have hI : (idxValue f FP m (decodeNonce bits) pk).toNat = ofDigitsW Flat.wid (sz s) 42 := by
    rw [hidx, hacc, cellBits_natV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := ofDigitsW_lt Flat.wid (sz s) (sz_lt hV) 42
    rwa [Flat.pos_42] at this
  have hdig : ∀ k : Fin numChains, FP.digit (idxValue f FP m (decodeNonce bits) pk) k = s k := by
    intro k
    show digitW Flat.wid _ k = _
    rw [hI, digitW_ofDigitsW Flat.wid (sz s) (sz_lt hV) 42 k k.isLt]
    unfold sz; rw [if_pos k.isLt]
  -- the layer
  have hsum := layer_of_facts (fun t h => CInstr.relNH_of_relB h) hV hP hL
  refine ⟨hlen, ?_, ?_⟩
  · show ∑ k : Fin numChains, FP.digit _ k = 106
    rw [Finset.sum_congr rfl (fun k _ => hdig k)]
    rw [Fin.sum_univ_eq_sum_range (fun k => s k) 42]
    exact hsum
  · -- the tops
    have htops : topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits = topsV v := by
      funext k
      have hw : cellBits (v (wCell k.val)) = decodeWord bits k := by
        have hk := k.isLt
        rw [hpin (wCell k.val) (by unfold wCell numChains at *; omega),
          show wCell k.val = 4 + k.val from rfl, inputWord_word pk m bits hlen k,
          cellBits_cellOfBits]
      unfold topsOf topsV
      rw [chain_top hV hP k.isLt, hdig k, show FP.len k = W k.val from (W_eq_len k).symm, hw]
    rw [htops, rootValue_topsV hP]
    -- the public key
    have h := root_rel hP (t := 10) (by omega)
    unfold rootOp at h
    rw [if_neg (by omega)] at h
    have h' : v pkCell = v (stCell 9) + v zCell := h
    rw [v_z hP, add_zero] at h'
    rw [← h', show pkCell = 0 from rfl, hpin 0 (by omega), inputWord_pk]
    exact cellBits_cellOfBits pk

end Accept


/-! ## Fixed-table soundness and the `Sound` clause -/

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
theorem fixed_sound {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (f : HashTable)
    (pk : PublicKey) (m : Message) (bits : List Bool) (L : MemImage κ) {n c : ℕ}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program (LeanIsa.loadInput pk m bits L) n Regs.initial))) :
    bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk) ∧
      rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) = pk := by
  rw [initial_eq] at h
  have hpin := pinned_of_sem (simSem f) (oracleRel f) (sim_straight h16 hκ f) h
  have hw := walk_of_sim h16 hκ f hpin (by norm_num) h
  obtain ⟨hV, hP, hL, -, -⟩ := walk_full (fun t h => CInstr.relNH_of_relB h) hw
  exact accept_of_path (fun c hc => Lx_loadInput_pin h16 pk m bits L hc) hV hP hL

open scoped Classical in
/-- The fixed-table verifier accepts when `fixed_sound`'s conclusion holds. -/
theorem decision_true {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
    (h : bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk) ∧
      rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) = pk) :
    (if bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk) then
        rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) == pk
      else false) = true := by
  rw [if_pos ⟨h.1, h.2.1⟩, h.2.2]; simp

/-- **Sound**: any submission running this bytecode for the HL-FLAT-A scheme is sound. -/
theorem sound (S : LeanIsa.Submission) (hs : S.scheme = Flat.scheme) (hp : S.program = program) :
    S.Sound := by
  intro pk m bits κ h16 h32 L n
  apply probTrue_zero_of_fixed
  intro f
  have hexec : S.exec L n pk m bits =
      LeanIsa.runCost program (LeanIsa.loadInput pk m bits L) n Regs.initial := by
    unfold LeanIsa.Submission.exec
    rw [hp]
  have hver : S.scheme.verify pk m bits = FP.verify pk m bits := by
    rw [hs]
    rfl
  rw [hexec, hver]
  simp only [simulateQ_bind, simulateQ_pure, fixed_verify, pure_bind]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨o, ho, hmem⟩ := hmem
  rw [mem_support_pure_iff] at hmem
  cases o with
  | none => simp at hmem
  | some c =>
    have hd := decision_true (fixed_sound h16 h32 f pk m bits L ho)
    rw [hd] at hmem
    simp at hmem

end

end OptimalOTS.HLFlat
