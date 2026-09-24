import Submissions.UpperLeanIsa.MachineCycles
import Submissions.UpperLeanIsa.MachineProver

/-!
# Soundness of the leanISA machine under a fixed oracle table

`CRel f v ci` is the relation the cell-level instruction `ci` asserts on the cell values `v`,
with `BLAKE2S` answered by the table `f`; `CRelNH v ci` is its hash-free part. `accept_of_path`
(design `NOTES.md` §6): cell values satisfying the relations along a path with leaf
vector `D` (`PathFacts`), and agreeing with the loader on the pinned cells, certify a signature
that the verifier accepts under `f`.

1. The constants pin the position cells, the zero pair, the checksum target and the length
   (`constFacts_of`).
2. The tie ops accumulate the leaf indices `D k − off k` into the message cells (`tie_facts`,
   `tie_chain`), so the message leaves are the message digits (`tie_iff`).
3. The checksum products give `Σ_{k<41} D k + 64 · (D 41 − 64) + D 42 = 5271`
   (`checksum_of_path`, hash-free), so the checksum leaves are the checksum digits.
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

theorem Valid.off_le {D : ℕ → ℕ} (hD : Valid D) {k : ℕ} (hk : k < 43) : off k ≤ D k := by
  by_cases h41 : k = 41
  · subst h41
    rw [off_41]
    exact hD.2.1
  · exact (hD.1 k (by omega)).1

variable {R : ℕ → Prop} {Q : CInstr → Prop} (hQ : ∀ s, R s → Q (cinstrAt s)) {D : ℕ → ℕ}
include hQ

theorem leaf_at (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 41 ∨ k = 42) {i : ℕ}
    (hi : i < leafLen k (D k)) : Q (leafOp k (D k) i) := by
  have h := hQ _ (hP.leaf k hk i hi)
  rwa [cinstrAt_leaf hk (hD.1 k hk).1 (hD.1 k hk).2
    (by have := leafLen_le k (D k); omega)] at h

theorem core_at (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 41 ∨ k = 42) {j : ℕ}
    (hj : tieLen k + j < leafLen k (D k)) : Q (coreOp k (D k) j) := by
  have h := leaf_at hQ hP hD hk hj
  rwa [leafOp_core] at h

theorem leafHi_at (hP : PathFacts R D) (hD : Valid D) {i : ℕ} (hi : i < 5) :
    Q (hiLeafOp (D 41 - 64) i) := by
  have h := hQ _ (hP.leafHi i hi)
  rwa [cinstrAt_hileaf (by have := hD.2.2; omega) hi] at h

theorem body_at (hP : PathFacts R D) (hD : Valid D) {k j : ℕ} (hk : k < 43) (hj : D k < j)
    (hj2 : j ≤ 126) : Q (bodyInstr k j) := by
  have h := hQ _ (hP.body k hk j hj hj2)
  have := Valid.off_le hD hk
  rwa [cinstrAt_body hk (by unfold bodyFirst; omega) hj2] at h

theorem root_at (hP : PathFacts R D) {t : ℕ} (ht : t < 43) : Q (rootInstr t) := by
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

/-- What the constant slots `0 … 130` pin. -/
structure ConstFacts (v : ℕ → E) : Prop where
  pos : ∀ j, 1 ≤ j → j ≤ 127 → v (posCell j) = posV j
  k0 : v k0Cell = tgtV K0
  len : v lenCell = lenV
  z0 : v zCell = 0
  z1 : v (zCell + 1) = 0

theorem constFacts_of {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    (hc : ∀ s < 131, R s) : ConstFacts v where
  pos j hj1 hj2 := by
    have h := nh_setc (hR _ (hc (j - 1) (by omega))) (cinstrAt_const (s := j - 1) (by omega))
    rwa [show j - 1 + 1 = j by omega] at h
  k0 := nh_setc (hR _ (hc 127 (by norm_num))) cinstrAt_k0
  len := nh_setc (hR _ (hc 128 (by norm_num))) cinstrAt_len
  z0 := nh_setc (hR _ (hc 129 (by norm_num))) cinstrAt_z0
  z1 := nh_setc (hR _ (hc 130 (by norm_num))) cinstrAt_z1

theorem oneCell_val {v : ℕ → E} (hc : ConstFacts v) : v oneCell = oneV := by
  rw [← posCell_one, hc.pos 1 le_rfl (by norm_num), posV_one]

theorem ConstFacts.pos_all {v : ℕ → E} (hc : ConstFacts v) {j : ℕ} (hj : j ≤ 127) :
    v (posCell j) = posV j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [posCell_zero, hc.z0, posV_zero]
  · exact hc.pos j hj0 hj

/-! ## The checksum (hash-free) -/

/-- The checksum cells of a Rice leaf: `T_k = g ^ (s0 k + e + 1)` and `G_k = G_{k-1} · T_k`. -/
theorem leaf_checksum {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 41 ∨ k = 42) :
    v (tCell k) = tgtV (s0 k + D k + 1) ∧ v (gOut k) = v (gPrev k) * v (tCell k) := by
  by_cases he : D k < 127
  · have hL := leafLen_of_lt (k := k) he
    exact ⟨nh_setc (core_at hR hP hD hk (j := 2) (by omega)) (coreOp_set he),
      nh_mul (core_at hR hP hD hk (j := 1) (by omega)) (coreOp_mul he)⟩
  · have hL := leafLen_of_ge (k := k) he
    have h127 : D k = 127 := by have := hD.lt_128 hk; omega
    refine ⟨?_, nh_mul (core_at hR hP hD hk (j := 2) (by omega)) (coreOp127_mul (by omega))⟩
    rw [nh_setc (core_at hR hP hD hk (j := 1) (by omega)) (coreOp127_setT (by omega)), h127]

theorem s0_lt_of_lt {i : ℕ} (hi : i < 41) : s0 i < 65491 := by
  have h := s0_le (k := i) (by omega)
  have : rootBase = 65491 := rfl
  omega

/-- The checksum identity, from the hash-free relations of any path: the leaf landing constants
multiply to `g ^ K0`. -/
theorem checksum_of_path {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D) :
    ∑ k ∈ Finset.range 41, D k + 64 * (D 41 - 64) + D 42 = 5271 := by
  have hc := constFacts_of hR hP.const
  have hprod : ∀ k < 41, v (gCell k) = tgtV (∑ i ∈ Finset.range (k + 1), (s0 i + D i + 1)) := by
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
  have hG41 := nh_mul (leafHi_at hR hP hD (i := 2) (by norm_num)) (hiLeafOp_mul _)
  obtain ⟨hT42, hG42⟩ := leaf_checksum hR hP hD (k := 42) (Or.inr rfl)
  have h40 : v (gCell 40) = tgtV (∑ i ∈ Finset.range 41, (s0 i + D i + 1)) := hprod 40 (by norm_num)
  rw [h40, hU, tgtV_mul] at hG41
  rw [gOut_42, gPrev_42, hG41, hT42, tgtV_mul, hc.k0] at hG42
  have hbound : ∑ i ∈ Finset.range 41, (s0 i + D i + 1) ≤ ∑ _i ∈ Finset.range 41, 65619 :=
    Finset.sum_le_sum fun i hi => by
      have hi' := Finset.mem_range.mp hi
      have := hD.lt_128 (Or.inl hi')
      have := s0_lt_of_lt hi'
      omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hbound
  have hsplit : ∑ i ∈ Finset.range 41, (s0 i + D i + 1) =
      ∑ i ∈ Finset.range 41, (s0 i + 1) + ∑ i ∈ Finset.range 41, D i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  have hK0 : K0 = ∑ i ∈ Finset.range 41, (s0 i + 1) + (s0 42 + 1) + 5271 := rfl
  have h41 := hD.2.2
  have h42 := hD.lt_128 (Or.inr rfl)
  have hs42 : s0 42 = 65364 := s0_42
  have hbig : (2700000 + 64 * 50 + 65500 : ℕ) < 2 ^ 64 - 1 := by norm_num
  have heq := tgtV_inj (lt_of_le_of_lt (le_of_eq K0_eq) (by norm_num))
    (lt_of_le_of_lt (by omega) hbig) hG42
  have hK := K0_eq
  omega

/-! ## The tie (hash-free) -/

/-- The tie ops of the leaves `D 0 … D 40` close message cells 2 and 1 on the tie sums of the
leaf indices `D k − off k`. -/
theorem tie_facts {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D)
    (hpos : ∀ j ≤ 127, v (posCell j) = posV j) :
    v 2 = tieHi (fun k => D k - off k) ∧ v 1 = tieLo (fun k => D k - off k) := by
  have hL : ∀ k, 4 ≤ leafLen k (D k) := fun k => leafLen_ge k (D k)
  have hw : ∀ k < 41, vV (tieShift k) (D k - off k) = tieWord (fun k => D k - off k) k :=
    fun k hk => vV_tieShift (fun k => D k - off k) hk
  have hlast : ∀ k, (k = 19 ∨ k = 40) →
      v (posCell (D k - off k)) = tieWord (fun k => D k - off k) k := by
    intro k hk
    rw [tieWord_last _ hk, hpos _ (by have := hD.lt_128 (k := k) (Or.inl (by omega)); omega)]
    rfl
  refine tie_chain _ (fun k => v (accCell k)) (v 1) (v 2) ?_ ?_ ?_ ?_ ?_
  · rw [← hw 0 (by norm_num)]
    exact nh_setc (leaf_at hR hP hD (k := 0) (Or.inl (by norm_num)) (i := 0)
      (by have := hL 0; omega)) (leafOp_tie0 _)
  · intro k h1 h39 h19 h20
    have hk : k < 41 ∨ k = 42 := Or.inl (by omega)
    have hf := nh_setc (leaf_at hR hP hD hk (i := 0) (by have := hL k; omega))
      (leafOp_mid0 h1 h39 h19 h20)
    have h := nh_xor (leaf_at hR hP hD hk (i := 1) (by have := hL k; omega))
      (leafOp_mid1 h1 h39 h19 h20)
    show v (accCell k) = v (accCell (k - 1)) + _
    rw [h, hf, hw k (by omega)]
  · have h := nh_xor (leaf_at hR hP hD (k := 19) (Or.inl (by norm_num)) (i := 0)
      (by have := hL 19; omega)) (leafOp_tie19 _)
    rw [h, hlast 19 (Or.inl rfl)]
  · rw [← hw 20 (by norm_num)]
    exact nh_setc (leaf_at hR hP hD (k := 20) (Or.inl (by norm_num)) (i := 0)
      (by have := hL 20; omega)) (leafOp_tie20 _)
  · have h := nh_xor (leaf_at hR hP hD (k := 40) (Or.inl (by norm_num)) (i := 0)
      (by have := hL 40; omega)) (leafOp_tie40 _)
    rw [h, hlast 40 (Or.inr rfl)]

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
    (hz0 : v zCell = 0) (hz1 : v (zCell + 1) = 0) {k : ℕ} (hk : k < 43) :
    cellBits (v (xCell k 127)) =
      chainValue f k (D k) (127 - D k) (cellBits (v (sigCell k))) := by
  have hQ : ∀ s, (CRel f v ∘ cinstrAt) s → CRel f v (cinstrAt s) := fun _ h => h
  have hDk : D k ≤ 127 := by
    by_cases h41 : k = 41
    · subst h41; have := hD.2.2; omega
    · have := hD.lt_128 (k := k) (by omega); omega
  refine chain_from f k (D k) hDk _ (fun j => cellBits (v (xCell k j))) ?_ ?_ ?_
  · intro he
    by_cases h41 : k = 41
    · subst h41
      have h := leafHi_at hQ hP hD (i := 0) (by norm_num)
      rw [hiLeafOp_blake, show 64 + (D 41 - 64) = D 41 by have := hD.2.1; omega] at h
      exact blake_chain_out hpos hz0 hz1 (by norm_num) (by omega) h
    · have hk' : k < 41 ∨ k = 42 := by omega
      have hL := leafLen_of_lt (k := k) he
      exact blake_chain_out hpos hz0 hz1 (by omega) (by omega)
        ((coreOp_blake he) ▸ core_at hQ hP hD hk' (j := 0) (by omega))
  · intro j hj1 hj2
    exact blake_chain_out hpos hz0 hz1 (by omega) (by omega) (body_at hQ hP hD hk hj1 hj2)
  · intro he
    have hk' : k < 41 ∨ k = 42 := by
      by_cases h41 : k = 41
      · subst h41; have := hD.2.2; omega
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
    bits.length = 5504 ∧ rootValue f (reconstructedWords f m bits) = pk := by
  have hR : ∀ s, (CRel f v ∘ cinstrAt) s → CRelNH v (cinstrAt s) :=
    fun _ h => crelNH_of_crel h
  have hQ : ∀ s, (CRel f v ∘ cinstrAt) s → CRel f v (cinstrAt s) := fun _ h => h
  have hc := constFacts_of hR h.const
  -- the length
  have hlen : bits.length = 5504 :=
    length_of_inputWord_len pk m bits ((hpin 3 (by norm_num)).symm.trans hc.len)
  refine ⟨hlen, ?_⟩
  have hz0 := hc.z0
  have hz1 := hc.z1
  have hzb : cellBits (v zCell) = 0 := by rw [hz0]; exact cellBits_zero_E
  have hpos : ∀ j ≤ 127, v (posCell j) = posV j := fun j hj => hc.pos_all hj
  have hposb : ∀ j ≤ 127, cellBits (v (posCell j)) = BitVec.ofNat 128 j := by
    intro j hj; rw [hpos j hj]; exact cellBits_cellOfBits _
  -- the revealed words
  have hsig : ∀ i : Fin 43, cellBits (v (sigCell i.val)) = decode bits i := by
    intro i
    have h1 : v (sigCell i.val) = inputWord pk m bits (4 + i.val) :=
      hpin (4 + i.val) (by have := i.isLt; omega)
    rw [h1, inputWord_sigDecode pk m bits hlen i]
    exact cellBits_cellOfBits _
  -- the message digits
  obtain ⟨h2, h1⟩ := tie_facts hR h hD hpos
  have hdig : ∀ k (hk : k < 41), D k = digit m ⟨k, by omega⟩ := by
    have ht := (tie_iff m (fun k => D k - off k) (fun k hk => by
      have := hD.1 k (Or.inl hk)
      rw [← nLeaves_eq_pow]
      show D k - off k < nLeaves k
      omega)).mp ⟨by rw [← h2, hpin 2 (by norm_num), inputWord_two],
        by rw [← h1, hpin 1 (by norm_num), inputWord_one]⟩
    intro k hk
    have e := ht k hk
    have := Valid.off_le hD (k := k) (by omega)
    rw [← off_eq_digitOff] at e
    omega
  -- the checksum digits
  have hck := checksum_digits m D hdig hD.2.1
    (by have := (hD.1 42 (Or.inr rfl)).1; rwa [off_42] at this)
    (hD.lt_128 (Or.inr rfl)) (checksum_of_path hR h hD)
  have hall : ∀ i : Fin 43, D i.val = digit m i := by
    intro i
    by_cases hi : i.val < 41
    · exact hdig i.val hi
    · by_cases h41 : i.val = 41
      · rw [show i = 41 from Fin.ext h41]; exact hck.1
      · rw [show i = 42 from Fin.ext (show i.val = 42 by have := i.isLt; omega)]
        exact hck.2
  -- the endpoints
  have hend : ∀ i : Fin 43, reconstructedWords f m bits i = cellBits (v (xCell i.val 127)) := by
    intro i
    have h1 := chain_end h hD hposb hz0 hz1 i.isLt
    rw [hall i, hsig i] at h1
    exact h1.symm
  -- the root
  have hroot : cellBits (v (rootStateCell 43)) = rootValue f (reconstructedWords f m bits) := by
    have habs : ∀ k < 43, blake2sQuery ![v (xCell k 127), v zCell, v zCell, v zCell]
        (v (rootStateCell k)) (v (rootStateCell k + 1)) (v (posCell (44 - k))) =
        hashInput (cellBits (v (rootStateCell k + 1)) ++ cellBits (v (rootStateCell k)))
          ((cellBits (v (xCell k 127))).setWidth 512) (BitVec.ofNat 128 (2 + (42 - k))) :=
      fun k hk => blake2sQuery_absorb (42 - k) _ _ _ _ _ _ _ hzb hzb hzb
        (by rw [hposb _ (by omega), show 2 + (42 - k) = 44 - k by omega])
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
