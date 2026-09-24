import Submissions.UpperLeanIsa.MachineCycles
import Submissions.UpperLeanIsa.ConstraintMath

/-!
# Soundness of the leanISA machine under a fixed oracle table

`CRel f v ci` is the relation the cell-level instruction `ci` asserts on the cell values `v`,
with `BLAKE2S` answered by the table `f`; `CRelNH v ci` is its hash-free part. `accept_of_path`
(design `NOTES.md` §6): cell values satisfying the relations along a path with leaf
vector `D` (`PathFacts`), and agreeing with the loader on the pinned cells, certify a signature
that the verifier accepts under `f`.

1. The constants pin the position cells, the checksum target and the length; the length pins
   the zero cells (`constFacts_of`, `inputWord_pad_zero`).
2. The tie ops accumulate the leaf digits into the message cells (`tie_facts`, `tie_chain`), so
   the message leaves are the message digits (`tie_iff`).
3. The checksum products give `Σ_{k<37} D k + 128 · D 37 + D 38 = 4699` (`checksum_of_path`,
   hash-free), so the checksum leaves are the checksum digits.
4. The leaf and body `BLAKE2S` compute the chain ends (`chain_from`), the absorptions fold them
   to the root (`root_sound`), and the pk `XOR` compares it with the public key.
-/

namespace OptimalOTS.LeanIsaBaseline.Honest

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery
  hashInput inputWord statementBits OracleCompressCells)
open OptimalOTS.LeanIsaBaseline.Machine

noncomputable section

/-! ## The relation of one instruction -/

/-- The relation the cell-level instruction asserts on the cell values `v` under table `f`:
`CInstr.Rel` of `MachineRun` without the range conditions. The trap `.pad` never holds. -/
def CRel (f : HashTable) (v : ℕ → E) : CInstr → Prop
  | .xor a b c => v c = v a + v b
  | .mul a b c => v c = v a * v b
  | .setc a k => v a = k
  | .blake m0 m1 m2 m3 cv out md =>
      OracleCompressCells ![v m0, v m1, v m2, v m3] (v cv) (v (cv + 1)) (v out) (v (out + 1))
        (v md) (f ⟨896, blake2sQuery ![v m0, v m1, v m2, v m3] (v cv) (v (cv + 1)) (v md)⟩)
  | .jump a b c => IsInK (v a) ∧ IsInK (v b) ∧ IsInK (v c)
  | .pad => False

/-- The hash-free relation on the cell values: `XOR`, `MUL` and `SET` equations only. -/
def CRelNH (v : ℕ → E) : CInstr → Prop
  | .xor a b c => v c = v a + v b
  | .mul a b c => v c = v a * v b
  | .setc a k => v a = k
  | .blake .. => True
  | .jump .. => True
  | .pad => False

theorem crelNH_of_crel {f : HashTable} {v : ℕ → E} {ci : CInstr} (h : CRel f v ci) :
    CRelNH v ci := by
  cases ci
  all_goals first | exact h | trivial

theorem crelNH_of_relNH {κ : ℕ} {L : MemImage κ} {ci : CInstr} (h : ci.RelNH L) :
    CRelNH (Lx L) ci := by
  cases ci
  all_goals first | trivial | exact h.2.2.2 | exact h.2

section Access

variable {v : ℕ → E}

theorem nh_setc {ci : CInstr} {a : ℕ} {k : E} (h : CRelNH v ci) (hs : ci = .setc a k) :
    v a = k := by
  subst hs; exact h

theorem nh_xor {ci : CInstr} {a b c : ℕ} (h : CRelNH v ci) (hs : ci = .xor a b c) :
    v c = v a + v b := by
  subst hs; exact h

theorem nh_mul {ci : CInstr} {a b c : ℕ} (h : CRelNH v ci) (hs : ci = .mul a b c) :
    v c = v a * v b := by
  subst hs; exact h

/-! ## Reading a path's slots

`Q` is any instruction predicate that the slot predicate `R` implies. -/

variable {R : ℕ → Prop} {Q : CInstr → Prop} (hQ : ∀ s, R s → Q (cinstrAt s)) {D : ℕ → ℕ}
include hQ

theorem leaf_at (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 37 ∨ k = 38) {i : ℕ}
    (hi : i < leafLen k (D k)) : Q (leafOp k (D k) i) := by
  have h := hQ _ (hP.leaf k hk i hi)
  rwa [cinstrAt_leaf hk (hD.1 k hk) (by have := leafLen_le k (D k); omega)] at h

theorem core_at (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 37 ∨ k = 38) {j : ℕ}
    (hj : tieLen k + j < leafLen k (D k)) : Q (coreOp k (D k) j) := by
  have h := leaf_at hQ hP hD hk hj
  rwa [leafOp_core] at h

theorem leafHi_at (hP : PathFacts R D) (hD : Valid D) {i : ℕ} (hi : i < 5) :
    Q (hiLeafOp (D 37) i) := by
  have h := hQ _ (hP.leafHi i hi)
  rwa [cinstrAt_hileaf hD.2 hi] at h

theorem body_at (hP : PathFacts R D) {k j : ℕ} (hk : k < 39) (hj : D k < j) (hj2 : j ≤ 126) :
    Q (bodyInstr k j) := by
  have h := hQ _ (hP.body k hk j hj hj2)
  rwa [cinstrAt_body hk (by omega) hj2] at h

theorem root_at (hP : PathFacts R D) {t : ℕ} (ht : t < 39) : Q (rootInstr t) := by
  have h := hQ _ (hP.root t ht)
  rwa [cinstrAt_root ht] at h

theorem pk_at (hP : PathFacts R D) : Q pkInstr := by
  have h := hQ _ hP.pk
  rwa [cinstrAt_pk] at h

end Access

theorem leafLen_of_lt {k e : ℕ} (he : e < 127) : leafLen k e = tieLen k + 4 := by
  unfold leafLen; rw [if_pos he]

theorem leafLen_of_ge {k e : ℕ} (he : ¬ e < 127) : leafLen k e = tieLen k + 5 := by
  unfold leafLen; rw [if_neg he]

/-! ## The constants -/

/-- What the constant slots `0 … 128` pin. -/
structure ConstFacts (v : ℕ → E) : Prop where
  pos : ∀ j, 1 ≤ j → j ≤ 127 → v (posCell j) = posV j
  k0 : v k0Cell = tgtV K0
  len : v lenCell = lenV

theorem constFacts_of {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    (hc : ∀ s < 129, R s) : ConstFacts v where
  pos j hj1 hj2 := by
    have h := nh_setc (hR _ (hc (j - 1) (by omega))) (cinstrAt_const (s := j - 1) (by omega))
    rwa [show j - 1 + 1 = j by omega] at h
  k0 := nh_setc (hR _ (hc 127 (by norm_num))) cinstrAt_k0
  len := nh_setc (hR _ (hc 128 (by norm_num))) cinstrAt_len

theorem oneCell_val {v : ℕ → E} (hc : ConstFacts v) : v oneCell = oneV := by
  rw [← posCell_one, hc.pos 1 le_rfl (by norm_num), posV_one]

/-! ## The checksum (hash-free) -/

/-- The checksum cells of a Rice leaf: `T_k = g ^ (s0 k + e + 1)` and `G_k = G_{k-1} · T_k`. -/
theorem leaf_checksum {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 37 ∨ k = 38) :
    v (tCell k) = tgtV (s0 k + D k + 1) ∧ v (gOut k) = v (gPrev k) * v (tCell k) := by
  by_cases he : D k < 127
  · have hL := leafLen_of_lt (k := k) he
    exact ⟨nh_setc (core_at hR hP hD hk (j := 2) (by omega)) (coreOp_set he),
      nh_mul (core_at hR hP hD hk (j := 1) (by omega)) (coreOp_mul he)⟩
  · have hL := leafLen_of_ge (k := k) he
    have h127 : D k = 127 := by have := hD.lt_128 hk; omega
    refine ⟨?_, nh_mul (core_at hR hP hD hk (j := 2) (by omega)) (coreOp127_mul (by omega))⟩
    rw [nh_setc (core_at hR hP hD hk (j := 1) (by omega)) (coreOp127_setT (by omega)), h127]

theorem s0_lt_of_lt {i : ℕ} (hi : i < 37) : s0 i < 50000 := by
  rcases Nat.eq_zero_or_pos i with rfl | h
  · rw [s0_zero]; omega
  · rw [s0_of_mid h hi]; omega

/-- The checksum identity, from the hash-free relations of any path: the leaf landing constants
multiply to `g ^ K0`. -/
theorem checksum_of_path {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D) :
    ∑ k ∈ Finset.range 37, D k + 128 * D 37 + D 38 = 4699 := by
  have hc := constFacts_of hR hP.const
  have hprod : ∀ k < 37, v (gCell k) = tgtV (∑ i ∈ Finset.range (k + 1), (s0 i + D i + 1)) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨hT, hG⟩ := leaf_checksum hR hP hD (k := 0) (Or.inl (by norm_num))
      rw [gOut_of (by norm_num), gPrev_zero, oneCell_val hc, hT, ← tgtV_zero, tgtV_mul,
        Nat.zero_add] at hG
      rw [hG, Finset.sum_range_one]
    | succ k ih =>
      intro hk
      obtain ⟨hT, hG⟩ := leaf_checksum hR hP hD (k := k + 1) (Or.inl hk)
      rw [gOut_of (by omega), gPrev_of (by omega), Nat.add_sub_cancel,
        ih (by omega), hT, tgtV_mul] at hG
      rw [hG, Finset.sum_range_succ _ (k + 1)]
  have hU := nh_setc (leafHi_at hR hP hD (i := 1) (by norm_num)) (hiLeafOp_setU _)
  have hG37 := nh_mul (leafHi_at hR hP hD (i := 2) (by norm_num)) (hiLeafOp_mul _)
  obtain ⟨hT38, hG38⟩ := leaf_checksum hR hP hD (k := 38) (Or.inr rfl)
  have h36 : v (gCell 36) = tgtV (∑ i ∈ Finset.range 37, (s0 i + D i + 1)) := hprod 36 (by norm_num)
  rw [h36, hU, tgtV_mul] at hG37
  rw [gOut_38, gPrev_38, hG37, hT38, tgtV_mul, hc.k0] at hG38
  have hbound : ∑ i ∈ Finset.range 37, (s0 i + D i + 1) ≤ ∑ _i ∈ Finset.range 37, 50128 :=
    Finset.sum_le_sum fun i hi => by
      have hi' := Finset.mem_range.mp hi
      have := hD.lt_128 (Or.inl hi')
      have := s0_lt_of_lt hi'
      omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hbound
  have hsplit : ∑ i ∈ Finset.range 37, (s0 i + D i + 1) =
      ∑ i ∈ Finset.range 37, (s0 i + 1) + ∑ i ∈ Finset.range 37, D i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  have hK0 : K0 = ∑ i ∈ Finset.range 37, (s0 i + 1) + (s0 38 + 1) + 4699 := rfl
  have h37 := hD.2
  have h38 := hD.lt_128 (Or.inr rfl)
  have hs38 : s0 38 = 65368 := s0_38
  have hbig : (2000000 + 128 * 36 + 65500 : ℕ) < 2 ^ 64 - 1 := by norm_num
  have heq := tgtV_inj (lt_of_le_of_lt (le_of_eq K0_eq) (by norm_num))
    (lt_of_le_of_lt (by omega) hbig) hG38
  have hK := K0_eq
  omega

/-! ## The tie (hash-free) -/

/-- The tie ops of the leaves `D 0 … D 36` close message cells 2 and 1 on the tie sums. -/
theorem tie_facts {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D)
    (hpos : ∀ j ≤ 127, v (posCell j) = posV j) : v 2 = tieHi D ∧ v 1 = tieLo D := by
  have hL : ∀ k, 4 ≤ leafLen k (D k) := fun k => leafLen_ge k (D k)
  have hmid : ∀ k, 1 ≤ k → k ≤ 35 → k ≠ 18 →
      v (accCell k) = v (accCell (k - 1)) + vV (tieShift k) (D k) := by
    intro k h1 h35 h18
    have hk : k < 37 ∨ k = 38 := Or.inl (by omega)
    have hf := nh_setc (leaf_at hR hP hD hk (i := 0) (by have := hL k; omega))
      (leafOp_mid0 h1 h35 h18)
    have h := nh_xor (leaf_at hR hP hD hk (i := 1) (by have := hL k; omega))
      (leafOp_mid1 h1 h35 h18)
    rw [h, hf]
  refine tie_chain D (fun k => v (accCell k)) (v 1) (v 2) ?_ ?_ ?_ ?_ ?_ ?_
  · have h := nh_setc (leaf_at hR hP hD (k := 0) (Or.inl (by norm_num)) (i := 0)
      (by have := hL 0; omega)) (leafOp_tie0 _)
    rw [h, tieShift_zero]
    rfl
  · intro k h1 h17
    show v (accCell k) = v (accCell (k - 1)) + _
    rw [hmid k h1 (by omega) (by omega), tieShift_of_lt (by omega),
      show 7 * (36 - k) - 128 = 124 - 7 * k by omega]
    rfl
  · have h := nh_xor (leaf_at hR hP hD (k := 18) (Or.inl (by norm_num)) (i := 0)
      (by have := hL 18; omega)) (leafOp_tie18a _)
    rw [h, hpos _ (by have := hD.lt_128 (k := 18) (Or.inl (by norm_num)); omega)]
    rfl
  · exact nh_setc (leaf_at hR hP hD (k := 18) (Or.inl (by norm_num)) (i := 1)
      (by have := hL 18; omega)) (leafOp_tie18b _)
  · intro k h19 h35
    show v (accCell k) = v (accCell (k - 1)) + _
    rw [hmid k (by omega) h35 (by omega), tieShift_of_ge (by omega)]
    rfl
  · have h := nh_xor (leaf_at hR hP hD (k := 36) (Or.inl (by norm_num)) (i := 0)
      (by have := hL 36; omega)) (leafOp_tie36 _)
    rw [h, hpos _ (by have := hD.lt_128 (k := 36) (Or.inl (by norm_num)); omega)]
    rfl

/-! ## Chains -/

/-- A chain-step `BLAKE2S` with pinned position cells computes the scheme's chain step. -/
theorem blake_chain_out {f : HashTable} {v : ℕ → E}
    (hpos : ∀ j ≤ 127, cellBits (v (posCell j)) = BitVec.ofNat 128 j)
    (hz0 : v zCell = 0) (hz1 : v (zCell + 1) = 0) {a k j out : ℕ} (hk : k ≤ 127) (hj : j ≤ 127)
    (h : CRel f v (.blake a (posCell k) (posCell j) zCell zCell out oneCell)) :
    cellBits (v out) = (f ⟨896, chainInput k j (cellBits (v a))⟩).extractLsb' 0 128 := by
  have hq : blake2sQuery ![v a, v (posCell k), v (posCell j), v zCell] (v zCell) (v (zCell + 1))
      (v oneCell) = chainInput k j (cellBits (v a)) :=
    blake2sQuery_chain k j _ _ _ _ _ _ _ (hpos k hk) (hpos j hj)
      (by rw [hz0]; exact cellBits_zero_E) (by rw [hz0]; exact cellBits_zero_E)
      (by rw [hz1]; exact cellBits_zero_E) (by rw [← posCell_one]; exact hpos 1 (by norm_num))
  obtain ⟨-, -, -, -, -, -, h2, -⟩ := h
  rw [hq] at h2
  exact h2

/-- The end of chain `k`: `x_{k,127} = chainValue f k (D k) (127 - D k) σ_k`. -/
theorem chain_end {f : HashTable} {v : ℕ → E} {D : ℕ → ℕ}
    (hP : PathFacts (CRel f v ∘ cinstrAt) D) (hD : Valid D)
    (hpos : ∀ j ≤ 127, cellBits (v (posCell j)) = BitVec.ofNat 128 j)
    (hz0 : v zCell = 0) (hz1 : v (zCell + 1) = 0) {k : ℕ} (hk : k < 39) :
    cellBits (v (xCell k 127)) =
      chainValue f k (D k) (127 - D k) (cellBits (v (sigCell k))) := by
  have hQ : ∀ s, (CRel f v ∘ cinstrAt) s → CRel f v (cinstrAt s) := fun _ h => h
  have hDk : D k ≤ 127 := by
    by_cases h37 : k = 37
    · subst h37; have := hD.2; omega
    · have := hD.lt_128 (k := k) (by omega); omega
  refine chain_from f k (D k) hDk _ (fun j => cellBits (v (xCell k j))) ?_ ?_ ?_
  · intro he
    by_cases h37 : k = 37
    · subst h37
      exact blake_chain_out hpos hz0 hz1 (by norm_num) (by omega)
        ((hiLeafOp_blake _) ▸ leafHi_at hQ hP hD (i := 0) (by norm_num))
    · have hk' : k < 37 ∨ k = 38 := by omega
      have hL := leafLen_of_lt (k := k) he
      exact blake_chain_out hpos hz0 hz1 (by omega) (by omega)
        ((coreOp_blake he) ▸ core_at hQ hP hD hk' (j := 0) (by omega))
  · intro j hj1 hj2
    exact blake_chain_out hpos hz0 hz1 (by omega) (by omega) (body_at hQ hP hk hj1 hj2)
  · intro he
    have hk' : k < 37 ∨ k = 38 := by
      by_cases h37 : k = 37
      · subst h37; have := hD.2; omega
      · omega
    have hL := leafLen_of_ge (k := k) (show ¬ D k < 127 by omega)
    have h := nh_xor (crelNH_of_crel (core_at hQ hP hD hk' (j := 0) (by omega)))
      (coreOp127_xor (by omega))
    show cellBits (v (xCell k 127)) = cellBits (v (sigCell k))
    rw [h, hz0, add_zero]

/-! ## Fixed-table soundness -/

/-- Cell values satisfying the relations along a path with leaf vector `D`, and agreeing with
the loader on the pinned cells, certify a signature the verifier accepts under the table. -/
theorem accept_of_path (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)
    (v : ℕ → E) (hpin : ∀ c < 47, v c = inputWord pk m bits c) {D : ℕ → ℕ} (hD : Valid D)
    (h : PathFacts (CRel f v ∘ cinstrAt) D) :
    bits.length = 4992 ∧ rootValue f (reconstructedWords f m bits) = pk := by
  have hR : ∀ s, (CRel f v ∘ cinstrAt) s → CRelNH v (cinstrAt s) :=
    fun _ h => crelNH_of_crel h
  have hQ : ∀ s, (CRel f v ∘ cinstrAt) s → CRel f v (cinstrAt s) := fun _ h => h
  have hc := constFacts_of hR h.const
  -- the length and the zero cells
  have hlen : bits.length = 4992 :=
    length_of_inputWord_len pk m bits ((hpin 3 (by norm_num)).symm.trans hc.len)
  refine ⟨hlen, ?_⟩
  have hz0 : v zCell = 0 :=
    (hpin 43 (by norm_num)).trans (inputWord_pad_zero pk m bits hlen le_rfl (by norm_num))
  have hz1 : v (zCell + 1) = 0 :=
    (hpin 44 (by norm_num)).trans (inputWord_pad_zero pk m bits hlen (by norm_num) (by norm_num))
  have hzb : cellBits (v zCell) = 0 := by rw [hz0]; exact cellBits_zero_E
  have hpos : ∀ j ≤ 127, v (posCell j) = posV j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [posCell_zero, hz0]; exact cellOfBits_zero.symm
    · exact hc.pos j hj0 hj
  have hposb : ∀ j ≤ 127, cellBits (v (posCell j)) = BitVec.ofNat 128 j := by
    intro j hj; rw [hpos j hj]; exact cellBits_cellOfBits _
  -- the revealed words
  have hsig : ∀ i : Fin 39, cellBits (v (sigCell i.val)) = decode bits i := by
    intro i
    have h1 : v (sigCell i.val) = inputWord pk m bits (4 + i.val) :=
      hpin (4 + i.val) (by have := i.isLt; omega)
    rw [h1, inputWord_sigDecode pk m bits hlen i]
    exact cellBits_cellOfBits _
  -- the message digits
  obtain ⟨h2, h1⟩ := tie_facts hR h hD hpos
  have hdig : ∀ k (hk : k < 37), D k = digit m ⟨k, by omega⟩ := by
    refine (tie_iff m D (fun k hk => hD.lt_128 (Or.inl hk)) ?_).mp ⟨?_, ?_⟩
    · have := hD.1 0 (Or.inl (by norm_num))
      rwa [nLeaves_zero] at this
    · rw [← h2, hpin 2 (by norm_num), inputWord_two]
    · rw [← h1, hpin 1 (by norm_num), inputWord_one]
  -- the checksum digits
  have hck := checksum_digits m D hdig (by have := hD.lt_128 (k := 38) (Or.inr rfl); omega)
    (checksum_of_path hR h hD)
  have hall : ∀ i : Fin 39, D i.val = digit m i := by
    intro i
    by_cases hi : i.val < 37
    · exact hdig i.val hi
    · by_cases h37 : i.val = 37
      · rw [show i = ⟨37, by norm_num⟩ from Fin.ext h37]; exact hck.1
      · rw [show i = ⟨38, by norm_num⟩ from Fin.ext (show i.val = 38 by have := i.isLt; omega)]
        exact hck.2
  -- the endpoints
  have hend : ∀ i : Fin 39, reconstructedWords f m bits i = cellBits (v (xCell i.val 127)) := by
    intro i
    have h1 := chain_end h hD hposb hz0 hz1 i.isLt
    rw [hall i, hsig i] at h1
    exact h1.symm
  -- the root
  have hroot : cellBits (v (rootStateCell 39)) = rootValue f (reconstructedWords f m bits) := by
    have habs : ∀ k < 39, blake2sQuery ![v (xCell k 127), v zCell, v zCell, v zCell]
        (v (rootStateCell k)) (v (rootStateCell k + 1)) (v (posCell (40 - k))) =
        hashInput (cellBits (v (rootStateCell k + 1)) ++ cellBits (v (rootStateCell k)))
          ((cellBits (v (xCell k 127))).setWidth 512) (BitVec.ofNat 128 (2 + (38 - k))) :=
      fun k hk => blake2sQuery_absorb (38 - k) _ _ _ _ _ _ _ hzb hzb hzb
        (by rw [hposb _ (by omega), show 2 + (38 - k) = 40 - k by omega])
    refine root_sound f _ (fun k => v (xCell k 127)) (fun k => v (rootStateCell k))
      (fun k => v (rootStateCell k + 1)) hend (by rw [rootStateCell_zero]; exact hzb)
      (by rw [rootStateCell_zero, hz1]; exact cellBits_zero_E) (fun k hk => ?_) (fun k hk => ?_)
    · obtain ⟨-, -, -, -, -, -, h2, -⟩ := root_at hQ h hk
      rw [habs k hk] at h2
      exact h2
    · obtain ⟨-, -, -, -, -, -, -, h2⟩ := root_at hQ h hk
      rw [habs k hk] at h2
      exact h2
  -- the public key
  have hpk := nh_xor (crelNH_of_crel (pk_at hQ h)) rfl
  rw [hz0, add_zero] at hpk
  have h0 : v pkCell = cellOfBits pk := (hpin 0 (by norm_num)).trans (inputWord_pk pk m bits)
  rw [← hroot, ← hpk, h0]
  exact cellBits_cellOfBits pk

end

end OptimalOTS.LeanIsaBaseline.Honest
