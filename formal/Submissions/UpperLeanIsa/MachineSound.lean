import Submissions.UpperLeanIsa.MachineCycles

/-!
# Soundness of the HL-GROUP-3 machine under a fixed oracle table

`accept_of_path`: cell values satisfying the fixed-table relations along the path of an index
vector `xs`, with its landings, and agreeing with the loader on the pinned cells, certify a
signature that the scheme `P` (any parameters with `Compat P T`) accepts under the table.

1. The prologue pins `ONE, LEN, g`, the cost constants and the frames; the length cell pins
   `|σ| = 5503`, so the loader's cells are the 42 words and the nonce.
2. The index `BLAKE2S` is the scheme's index query; its low half `I` is the index cell.
3. The tie accumulates the field values into the index cell (`acc_eq`), so the group fields of
   `I` are `xs (u + 1)` and the digits are the table coordinates; the exponent identity
   (`layer_of_facts`, hash-free) gives `xs 0 + Σ costs = 87`, so the free digit is `xs 0` and `I`
   is accepted.
4. The inline `BLAKE2S` compute the verifier's chain tops (`top_eq`), the nine root calls in the
   home blocks compute its root (`root_state`), and the last copy compares it with the public key.
-/

namespace OptimalOTS.HLG3

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

variable {T : Tab} {P : Params}

/-! ## Cell values and queries -/

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

/-- A sequence obeying the chain recursion is the fixed-table chain. -/
theorem chainValue_of_seq (f : HashTable) (P : Params) (k : Fin numChains) :
    ∀ (n j0 : ℕ) (X : ℕ → Word),
      (∀ t < n, X (t + 1) = P.slice k (j0 + t) (f ⟨896, P.chainInput k (j0 + t) (X t)⟩)) →
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

theorem list_sum_range (F : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-! ## Digits of an index vector -/

/-- The digit of chain `k` on the path of `xs`. -/
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

theorem rtopCell_exported {k d : ℕ} (hk : k ≠ 0) (he : exported k) : rtopCell k d = topCell k := by
  unfold rtopCell; rw [if_neg hk, if_pos he]

/-! ## The path -/

section Path

variable {f : HashTable} {v : ℕ → E} {xs : ℕ → ℕ}
  (hV : Valid xs) (hP : PathFacts T (oracleRel f) v xs)

section Consts

include hP

theorem v_one : v oneCell = oneV := (hP.pro _ pro_mem_init).1
theorem v_len : v lenCell = natV 5503 := (hP.pro _ pro_mem_init).2
theorem v_g : v gCell = gV := hP.pro _ pro_mem_g
theorem v_c {c : ℕ} (hc : c ≤ 16) : v (cCell c) = cV c := cCell_val hP.pro hc
theorem v_frame {r : ℕ} (hr : r < 13) : v (fCell r) = frameV r := hP.pro _ (pro_mem_frame (by omega))

theorem cb_cv (hC : Compat P T) : cellBits (v (oneCell + 1)) ++ cellBits (v oneCell) = P.cv := by
  rw [show oneCell + 1 = gCell from rfl, v_g hP, v_one hP, hC.cv]

end Consts

/-- The chain-step query of a chain op. -/
theorem chainOp_query (hP : PathFacts T (oracleRel f) v xs) (hC : Compat P T) {k : ℕ}
    (hk : k < 42) {d t : ℕ} (hd : d < LEN k) (ht : t < d) (x : E) :
    blake2sQuery ![x, v (cCell (tpos k d t % 9)), v (cCell (tpos k d t / 9 % 9)),
        v (cCell (tpos k d t / 81))] (v oneCell) (v (oneCell + 1)) (v oneCell) =
      P.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t) (cellBits x) := by
  have hj : LEN k - 1 - d + t + 1 < LEN k := by omega
  obtain ⟨h0, h1, h2⟩ := hC.tag ⟨k, hk⟩ _ hj
  have hp : tpos k d t / 81 ≤ 16 := by
    have := OFFT_bound k hk; unfold tpos; omega
  rw [blake2sQuery_eq, v_c hP (c := tpos k d t % 9) (by omega),
    v_c hP (c := tpos k d t / 9 % 9) (by omega), v_c hP hp, cb_cv hP hC, v_one hP]
  unfold Params.chainInput
  rw [h0, h1, h2, hC.chainMd]
  rfl

/-- The chain values a chain's steps walk through. -/
def chainSeq (v : ℕ → E) (k d dst : ℕ) (t : ℕ) : Word :=
  cellBits (v (if t = 0 then wCell k else if t = d then dst else xcCell k (t - 1)))

theorem stepOff_eq (hC : Compat P T) {k d t : ℕ} (hk : k < 42) (hd : d < LEN k)
    (ht : t < d) : P.stepOff ⟨k, hk⟩ (LEN k - 1 - d + t) =
      if t + 1 = d then 128 * topOff k else 0 := by
  unfold Params.stepOff
  rw [hC.hiTop, hC.len]
  have he : LEN k - 1 - d + t + 2 = LEN k ↔ t + 1 = d := by omega
  simp only [Fin.val_mk, decide_eq_true_eq, he]
  unfold topOff
  split_ifs <;> simp_all

theorem topCell_pos {k : ℕ} (hk : k < 42) : 1 ≤ topCell k := by
  unfold topCell; split_ifs <;> omega

theorem xhCell_pos {k : ℕ} (hk : k < 42) (hk0 : k ≠ 0) (he : ¬ exported k) : 1 ≤ xhCell k := by
  have h : ∀ k < 42, k ≠ 0 → ¬ exported k → 1 ≤ xhCell k := by decide
  exact h k hk hk0 he

include hP in
/-- **Chain value.** The `d` steps of chain `k` compute the verifier's chain from the revealed
word into `dst`. -/
theorem chain_val (hC : Compat P T) {k d dst : ℕ} (hk : k < 42) (hd : d < LEN k) (hd0 : d ≠ 0) (hdst : 1 ≤ dst)
    (hs : ∀ t < d, (chainOp k d t dst).Rel f v) :
    cellBits (v dst) = chainValue f P ⟨k, hk⟩ (LEN k - 1 - d) d (cellBits (v (wCell k))) := by
  have hstep : ∀ t < d, chainSeq v k d dst (t + 1) =
      P.slice ⟨k, hk⟩ (LEN k - 1 - d + t)
        (f ⟨896, P.chainInput ⟨k, hk⟩ (LEN k - 1 - d + t) (chainSeq v k d dst t)⟩) := by
    intro t ht
    have h := hs t ht
    unfold chainOp at h
    have hlo := oracle_lo h
    have hhi := h.2.2.2.2.2.2.2
    rw [chainOp_query hP hC hk hd ht] at hlo hhi
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
      · simpa only [hz, Nat.sub_zero, Nat.mul_zero, if_pos hlast] using hlo
      · have ho : topOff k = 1 := by omega
        simpa only [ho, Nat.mul_one, Nat.sub_add_cancel hdst, if_pos hlast] using hhi
    · rw [if_neg hlast] at hlo ⊢
      simpa only [if_neg hlast] using hlo
  have hend := chainValue_of_seq f P ⟨k, hk⟩ d (LEN k - 1 - d) (chainSeq v k d dst) hstep
  have hl : chainSeq v k d dst d = cellBits (v dst) := by
    unfold chainSeq; rw [if_neg hd0, if_pos rfl]
  have h0 : chainSeq v k d dst 0 = cellBits (v (wCell k)) := by unfold chainSeq; rw [if_pos rfl]
  rw [hl, h0] at hend
  exact hend

/-- The tops the root reads. -/
def topsV (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) (k : Fin numChains) : Word :=
  cellBits (v (rtopCell k.val (dg T xs k.val)))

include hV hP in
/-- **Chain tops.** The root reads the verifier's chain top of chain `k`. -/
theorem top_eq (hT : T.Hyp) (hC : Compat P T) {k : ℕ} (hk : k < 42) :
    cellBits (v (rtopCell k (dg T xs k))) =
      chainValue f P ⟨k, hk⟩ (LEN k - 1 - dg T xs k) (dg T xs k) (cellBits (v (wCell k))) := by
  have hd := dg_lt hT hV hk
  by_cases hk0 : k = 0
  · subst hk0
    have hx0 : xs 0 < 64 := by have := hV 0 (by omega); rwa [Wf_zero] at this
    have hb := hP.blk 0 (by omega)
    rw [bodyF_frU_zero] at hb
    rw [show dg T xs 0 = xs 0 from if_pos rfl]
    have hb' : ∀ y ∈ fbody (xs 0), y.Rel f v := hb
    unfold fbody at hb'
    by_cases hs0 : xs 0 = 0
    · rw [show rtopCell 0 (xs 0) = wCell 0 by unfold rtopCell; rw [if_pos rfl, if_pos hs0], hs0]
      rfl
    · rw [if_neg hs0] at hb'
      rw [show rtopCell 0 (xs 0) = tfCell by unfold rtopCell; rw [if_pos rfl, if_neg hs0]]
      refine chain_val hP hC (by omega) hd hs0 (by decide) (fun t ht => hb' _ ?_)
      simp only [List.mem_append, List.mem_singleton]
      left; right; exact mem_chainOps.mpr ⟨t, ht, rfl⟩
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
      rw [rtopCell_exported hk0 he]
      by_cases hd0 : T u (xs (u + 1)) i = 0
      · rw [if_pos hd0] at hb
        have h : v (topCell k) = v (wCell k) * v oneCell := hb (copy (wCell k) (topCell k)) (by simp)
        rw [h, v_one hP, mul_oneV, hd0]; rfl
      · rw [if_neg hd0] at hb
        exact chain_val hP hC hk hd hd0 (topCell_pos hk) (fun t ht => hb _ (mem_chainOps.mpr ⟨t, ht, rfl⟩))
    · rw [if_neg hx] at hb
      have he : ¬ exported k := by rw [← hc]; exact fun h => hx ((exported_iff u hu i hi).mp h)
      unfold rtopCell
      rw [if_neg hk0, if_neg he]
      by_cases hd0 : T u (xs (u + 1)) i = 0
      · rw [if_pos hd0, hd0]; rfl
      · rw [if_neg hd0]
        exact chain_val hP hC hk hd hd0 (xhCell_pos hk hk0 he) (fun t ht => hb _ (mem_chainOps.mpr ⟨t, ht, rfl⟩))

/-! ### The tie -/

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

/-! ### The root -/

/-- The root state after call `r`. -/
def stVal (v : ℕ → E) (r : ℕ) : BitVec 256 := cellBits (v (stCell r + 1)) ++ cellBits (v (stCell r))

theorem stVal_lo (v : ℕ → E) (r : ℕ) : (stVal v r).extractLsb' 0 128 = cellBits (v (stCell r)) :=
  BitVec.extractLsb'_append_eq_right

theorem cellBits_oneV : cellBits oneV = (1 : Word) := by
  simp [oneV, ofK_eq_ofLimbs, cellBits]

theorem topAt_topsV (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) {i : ℕ} (hi : i < 42) :
    Params.topAt (topsV T v xs) i = cellBits (v (rtopCell i (dg T xs i))) := by
  unfold Params.topAt; rw [dif_pos hi]; rfl

/-- The root state sequence: the initial cv pair, then the states. -/
def rootSeq (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) (i : ℕ) : BitVec 256 :=
  if i = 0 then Params.rootInit (topsV T v xs) else stVal v (i - 1)

theorem cellBits_gV : cellBits gV = (2 : Word) := by
  simp [gV, ofK_eq_ofLimbs, cellBits, g]

theorem rootCv_pair (T : Tab) (v : ℕ → E) (xs : ℕ → ℕ) {i : ℕ} (hi : i < 9) :
    cellBits (v (rootCv i + 1)) ++ cellBits (v (rootCv i)) =
      Params.rootCv (topsV T v xs) i (rootSeq T v xs i) := by
  interval_cases i <;>
    simp [rootCv, Params.rootCv, rootSeq, Params.rootInit, Params.topAt, stVal,
      numChains, topsV, rtopCell, exported, topCell, cvCell, stCell]

/-- The group that executes root call `r`: group 0 for call 1, groups 5 and 6 for calls 0 and 7,
group 12 for call 8, group `r + 5` otherwise. -/
def homeU (r : ℕ) : ℕ :=
  if r = 0 then 5 else if r = 1 then 0 else if r = 7 then 6 else if r = 8 then 12 else r + 5

theorem homeU_home {r : ℕ} (hr : r < 9) : homeU r = 0 ∨ 5 ≤ homeU r := by
  unfold homeU; split_ifs <;> omega

theorem homeU_lt {r : ℕ} (hr : r < 9) : homeU r < 13 := by
  unfold homeU; split_ifs <;> omega

theorem hcall_homeU {r : ℕ} (hr : r < 9) : hcall (homeU r) = r := by
  interval_cases r <;> rfl

/-- The four physical message operands of root call r. -/
def rootMsg (T : Tab) (xs : ℕ → ℕ) (r j : ℕ) : ℕ :=
  rt T (homeU r) (xs (homeU r + 1)) (zU (xs 0) (homeU r)) j

theorem rootMsg_block {i : ℕ} (hi : i < 9) :
    cellBits (v (rootMsg T xs i 3)) ++ cellBits (v (rootMsg T xs i 2)) ++
      cellBits (v (rootMsg T xs i 1)) ++ cellBits (v (rootMsg T xs i 0)) =
      Params.rootBlock (topsV T v xs) i (rootSeq T v xs i) := by
  interval_cases i <;>
    simp [rootMsg, homeU, rt, hcall, Params.rootBlock, rootSeq, stVal_lo, Params.topAt, numChains,
      topsV, rtopCell, exported, dg, unitOf, coordOf, chainOf, zU]

/-- The metadata operand of root call `i` is its frame constant, the scheme's metadata. -/
theorem rootMd_cell_of (hC : Compat P T) (hfr : ∀ r < 9, v (fCell r) = frameV r) {i : ℕ}
    (hi : i < 9) : cellBits (v (fCell i)) = P.rootMd i := by
  rw [hC.rootMd i hi, hfr i hi]

include hP in
theorem rootMd_cell (hC : Compat P T) {i : ℕ} (hi : i < 9) : cellBits (v (fCell i)) = P.rootMd i :=
  rootMd_cell_of hC (fun r hr => v_frame hP (by omega)) hi

include hP in
theorem root_step (hC : Compat P T) {i : ℕ} (hi : i < 9) :
    rootSeq T v xs (i + 1) = f ⟨896, P.rootInput (topsV T v xs) i (rootSeq T v xs i)⟩ := by
  have hmem : CInstr.blake (rootMsg T xs i 0) (rootMsg T xs i 1)
      (rootMsg T xs i 2) (rootMsg T xs i 3) (rootCv i) (stCell i) (fCell i) ∈
      bodyF T (frU (xs 0) (homeU i + 1)) (xs (homeU i + 1)) := by
    rw [bodyF_frU_succ T _ (homeU_lt hi)]
    unfold body
    simp only [List.mem_append]
    left; left; right
    unfold rootIns
    rw [if_pos (homeU_home hi), hcall_homeU hi]
    exact List.mem_singleton_self _
  have hrel := hP.blk (homeU i + 1) (by have := homeU_lt hi; omega) _ hmem
  have hp := oracle_pair hrel
  have hq : blake2sQuery ![v (rootMsg T xs i 0), v (rootMsg T xs i 1),
      v (rootMsg T xs i 2), v (rootMsg T xs i 3)] (v (rootCv i)) (v (rootCv i + 1))
      (v (fCell i)) = P.rootInput (topsV T v xs) i (rootSeq T v xs i) := by
    rw [blake2sQuery_eq, rootCv_pair T v xs hi, rootMsg_block hi, rootMd_cell hP hC hi]
    rfl
  rw [hq] at hp
  unfold rootSeq
  rw [if_neg (by omega), Nat.add_sub_cancel]
  exact hp

include hP in
/-- **The root.** The nine root calls compute the fixed-table root of the tops. -/
theorem root_state (hC : Compat P T) :
    rootState f P (topsV T v xs) 0 9 (Params.rootInit (topsV T v xs)) = stVal v 8 := by
  have h := rootState_of_seq f P (topsV T v xs) 9 0 (rootSeq T v xs) (fun i hi => by
    rw [Nat.zero_add]; exact root_step hP hC hi)
  unfold rootSeq at h
  rw [if_pos rfl, if_neg (by omega)] at h
  exact h

include hP in
theorem rootValue_topsV (hC : Compat P T) :
    rootValue f P (topsV T v xs) = cellBits (v (stCell 8)) := by
  unfold rootValue
  rw [root_state hP hC]
  exact BitVec.extractLsb'_append_eq_right

end Path

section Accept

variable {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool} {v : ℕ → E}

/-- **Fixed-table acceptance.** Cell values satisfying the relations along the path of `xs`, with
its landings, and agreeing with the loader on the pinned cells, certify a signature the verifier
accepts under the table. -/
theorem accept_of_path (hT : T.Hyp) (hC : Compat P T) (hpin : ∀ c < 47, v c = inputWord pk m bits c)
    {xs : ℕ → ℕ} (hV : Valid xs) (hP : PathFacts T (oracleRel f) v xs) (hL : Landing v xs) :
    bits.length = sigBits ∧ P.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk := by
  -- the length
  have hlen : bits.length = 5503 :=
    length_of_inputWord_len pk m bits ((hpin 3 (by omega)).symm.trans (v_len hP))
  -- the index
  have hidx : (ans f (P.idxInput m (decodeNonce bits) pk)).extractLsb' 0 128 = cellBits (v idxCell) := by
    have h : (CInstr.blake msgLo msgHi nonceCell pkCell oneCell idxCell gCell).Rel f v :=
      hP.pro _ pro_mem_idx
    have hlo := oracle_lo h
    have hpk : cellBits (v pkCell) = pk := by
      rw [show pkCell = 0 from rfl, hpin 0 (by omega), inputWord_pk]
      exact cellBits_cellOfBits pk
    have hq : blake2sQuery ![v msgLo, v msgHi, v nonceCell, v pkCell] (v oneCell)
        (v (oneCell + 1)) (v gCell) = P.idxInput m (decodeNonce bits) pk := by
      rw [blake2sQuery_eq, cb_cv hP hC, v_g hP,
        show nonceCell = 46 from rfl, show msgHi = 2 from rfl,
        show msgLo = 1 from rfl, hpin 46 (by omega), hpin 2 (by omega),
        hpin 1 (by omega), inputWord_nonce pk m bits hlen, inputWord_two,
        inputWord_one, cellBits_cellOfBits (nonceWord (decodeNonce bits)),
        cellBits_cellOfBits (m.extractLsb' 128 128), cellBits_cellOfBits (m.extractLsb' 0 128),
        msg_split, hpk]
      unfold Params.idxInput
      rw [hC.idxMd]
      rfl
    rw [hq] at hlo
    exact hlo.symm
  set I := (ans f (P.idxInput m (decodeNonce bits) pk)).extractLsb' 0 128 with hIdef
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
  have hdig : ∀ k : Fin numChains, P.digit (effective I) k = dg T xs k.val := by
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
  · show ∑ k : Fin numChains, P.digit (effective I) k = P.layer
    rw [hC.layer, Finset.sum_congr rfl (fun k _ => hdig k),
      Fin.sum_univ_eq_sum_range (fun k => dg T xs k) 42, dg_sum]
    unfold gsum at hsum
    exact hsum
  · -- the tops
    have htops : topsOf f P (effective I) bits = topsV T v xs := by
      funext k
      have hw : cellBits (v (wCell k.val)) = decodeWord bits k := by
        have hk := k.isLt
        rw [hpin (wCell k.val) (by unfold wCell numChains at *; omega),
          show wCell k.val = 4 + k.val from rfl, inputWord_word pk m bits hlen k,
          cellBits_cellOfBits]
      unfold topsOf topsV
      rw [top_eq hV hP hT hC k.isLt, hdig k, hC.len k, hw]
    rw [htops, rootValue_topsV hP hC]
    -- the public key
    have hb := hP.blk 13 (by omega)
    rw [show (13 : ℕ) = 12 + 1 from rfl, bodyF_frU_succ T _ (by omega)] at hb
    have h : v pkCell = v (stCell 8) * v oneCell := hb (copy (stCell 8) pkCell) (by
      unfold body nextOp copy; simp)
    rw [v_one hP, mul_oneV] at h
    rw [← h, show pkCell = 0 from rfl, hpin 0 (by omega), inputWord_pk]
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
theorem fixed_sound (hT : T.Hyp) (hC : Compat P T) {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) (L : MemImage κ) {n c : ℕ}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits L) n Regs.initial))) :
    bits.length = sigBits ∧ P.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk := by
  rw [initial_eq] at h
  have hpin := pinned_of_sem (simSem f) (oracleRel f) (sim_straight hT h16 hκ (lengthDomain_load h16 pk m bits L) f) h
  have hw := walk_of_sim hT h16 hκ (lengthDomain_load h16 pk m bits L) f hpin (by norm_num) h
  obtain ⟨hV, hP, hL, -, -⟩ := walk_full hT hw
  exact accept_of_path hT hC (fun c hc => Lx_loadInput_pin h16 pk m bits L hc) hV hP hL

open scoped Classical in
/-- The fixed-table verifier accepts when `fixed_sound`'s conclusion holds. -/
theorem decision_true {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
    (h : bits.length = sigBits ∧ P.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk) :
    (if bits.length = sigBits ∧ P.Accepted (idxValue f P m (decodeNonce bits) pk) then
        rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) == pk
      else false) = true := by
  rw [if_pos ⟨h.1, h.2.1⟩, h.2.2]; simp

/-- **Sound**: any submission running this bytecode for a scheme compatible with it is sound. -/
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
  simp only [simulateQ_bind, simulateQ_pure, fixed_verify, pure_bind]
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

end OptimalOTS.HLG3
