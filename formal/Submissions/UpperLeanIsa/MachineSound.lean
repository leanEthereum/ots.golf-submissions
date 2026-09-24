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
2. The tie ops accumulate the leaf digits into the message cells (`tie_rel`, `tie_run`), so the
   message leaves are the message digits.
3. The checksum products give `Σ_{k<32} D k + 256 · D 32 + D 33 = 8160` (`checksum_of_path`,
   hash-free, also used by the cycle bound), so the checksum leaves are the checksum digits.
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

theorem leaf_at (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 32 ∨ k = 33) {i : ℕ}
    (hi : i < leafLen k (D k)) : Q (leafOp k (D k) i) := by
  have h := hQ _ (hP.leaf k hk i hi)
  rwa [cinstrAt_leaf hk (hD.1 k hk) (by have := leafLen_le k (D k); omega)] at h

theorem core_at (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 32 ∨ k = 33) {j : ℕ}
    (hj : tieLen k + j < leafLen k (D k)) : Q (coreOp k (D k) j) := by
  have h := leaf_at hQ hP hD hk hj
  rwa [leafOp_core] at h

theorem leaf32_at (hP : PathFacts R D) (hD : Valid D) {i : ℕ} (hi : i < 5) :
    Q (leaf32Op (D 32) i) := by
  have h := hQ _ (hP.leaf32 i hi)
  rwa [cinstrAt_leaf32 hD.2 hi] at h

theorem body_at (hP : PathFacts R D) {k j : ℕ} (hk : k < 34) (hj : D k < j) (hj2 : j ≤ 254) :
    Q (bodyInstr k j) := by
  have h := hQ _ (hP.body k hk j hj hj2)
  rwa [cinstrAt_body hk (by omega) hj2] at h

theorem root_at (hP : PathFacts R D) {t : ℕ} (ht : t < 34) : Q (rootInstr t) := by
  have h := hQ _ (hP.root t ht)
  rwa [cinstrAt_root ht] at h

theorem pk_at (hP : PathFacts R D) : Q pkInstr := by
  have h := hQ _ hP.pk
  rwa [cinstrAt_pk] at h

end Access

theorem leafLen_of_lt {k e : ℕ} (he : e < 255) : leafLen k e = tieLen k + 4 := by
  unfold leafLen; rw [if_pos he]

theorem leafLen_of_ge {k e : ℕ} (he : ¬ e < 255) : leafLen k e = tieLen k + 5 := by
  unfold leafLen; rw [if_neg he]

/-! ## The constants -/

/-- What the constant slots `0 … 256` pin. -/
structure ConstFacts (v : ℕ → E) : Prop where
  pos : ∀ j, 1 ≤ j → j ≤ 255 → v (posCell j) = posV j
  k0 : v k0Cell = tgtV K0
  len : v lenCell = lenV

theorem constFacts_of {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    (hc : ∀ s < 257, R s) : ConstFacts v where
  pos j hj1 hj2 := by
    have h := nh_setc (hR _ (hc (j - 1) (by omega))) (cinstrAt_const (s := j - 1) (by omega))
    rwa [show j - 1 + 1 = j by omega] at h
  k0 := nh_setc (hR _ (hc 255 (by norm_num))) cinstrAt_k0
  len := nh_setc (hR _ (hc 256 (by norm_num))) cinstrAt_len

theorem oneCell_val {v : ℕ → E} (hc : ConstFacts v) : v oneCell = oneV := by
  rw [← posCell_one, hc.pos 1 le_rfl (by norm_num), posV_one]

/-! ## The checksum (hash-free) -/

/-- The checksum cells of a Rice leaf: `T_k = g ^ (s0 k + e + 1)` and `G_k = G_{k-1} · T_k`. -/
theorem leaf_checksum {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D) {k : ℕ} (hk : k < 32 ∨ k = 33) :
    v (tCell k) = tgtV (s0 k + D k + 1) ∧ v (gOut k) = v (gPrev k) * v (tCell k) := by
  by_cases he : D k < 255
  · have hL := leafLen_of_lt (k := k) he
    exact ⟨nh_setc (core_at hR hP hD hk (j := 2) (by omega)) (coreOp_set he),
      nh_mul (core_at hR hP hD hk (j := 1) (by omega)) (coreOp_mul he)⟩
  · have hL := leafLen_of_ge (k := k) he
    have h255 : D k = 255 := by have := hD.1 k hk; omega
    refine ⟨?_, nh_mul (core_at hR hP hD hk (j := 2) (by omega)) (coreOp255_mul (by omega))⟩
    rw [nh_setc (core_at hR hP hD hk (j := 1) (by omega)) (coreOp255_setT (by omega)), h255]

/-- The checksum identity, from the hash-free relations of any path: the leaf landing constants
multiply to `g ^ K0`. -/
theorem checksum_of_path {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D) :
    ∑ k ∈ Finset.range 32, D k + 256 * D 32 + D 33 = 8160 := by
  have hc := constFacts_of hR hP.const
  have hprod : ∀ k < 32, v (gCell k) = tgtV (∑ i ∈ Finset.range (k + 1), (s0 i + D i + 1)) := by
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
      rw [gOut_of (by omega), gPrev_of (by omega) (by omega), Nat.add_sub_cancel,
        ih (by omega), hT, tgtV_mul] at hG
      rw [hG, Finset.sum_range_succ _ (k + 1)]
  have hU := nh_setc (leaf32_at hR hP hD (i := 1) (by norm_num)) (leaf32Op_setU _)
  have hG32 := nh_mul (leaf32_at hR hP hD (i := 2) (by norm_num)) (leaf32Op_mul _)
  obtain ⟨hT33, hG33⟩ := leaf_checksum hR hP hD (k := 33) (Or.inr rfl)
  have h31 : v (gCell 31) = tgtV (∑ i ∈ Finset.range 32, (s0 i + D i + 1)) := hprod 31 (by norm_num)
  rw [h31, hU, tgtV_mul] at hG32
  rw [gOut_33, gPrev_33, hG32, hT33, tgtV_mul, hc.k0] at hG33
  have hbound : ∑ i ∈ Finset.range 32, (s0 i + D i + 1) ≤ ∑ _i ∈ Finset.range 32, 200000 :=
    Finset.sum_le_sum fun i hi => by
      have hi' := Finset.mem_range.mp hi
      have := hD.1 i (Or.inl hi')
      rw [s0_of_lt hi']
      omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hbound
  have hsplit : ∑ i ∈ Finset.range 32, (s0 i + D i + 1) =
      ∑ i ∈ Finset.range 32, (s0 i + 1) + ∑ i ∈ Finset.range 32, D i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  have hK0 : K0 = ∑ i ∈ Finset.range 32, (s0 i + 1) + (s0 33 + 1) + 8160 := rfl
  have h32 := hD.2
  have h33 := hD.1 33 (Or.inr rfl)
  have hs33 : s0 33 = 130781 := s0_33
  have hbig : (6400000 + 256 * 32 + 131100 : ℕ) < 2 ^ 64 - 1 := by norm_num
  have heq := tgtV_inj (lt_of_le_of_lt (le_of_eq K0_eq) (by norm_num))
    (lt_of_le_of_lt (by omega) hbig) hG33
  omega

/-- `checksum_of_path` for a walk's hash-free relations (the cycle bound). -/
theorem checksum_of_holdsNH {κ : ℕ} {L : MemImage κ} {R : ℕ → Prop}
    (hR : ∀ s, R s → HoldsNH L s) {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D) :
    ∑ k ∈ Finset.range 32, D k + 256 * D 32 + D 33 = 8160 :=
  checksum_of_path (fun s h => crelNH_of_relNH (hR s h)) hP hD

/-! ## The tie (hash-free) -/

theorem bytePos_half {h' i : ℕ} (hh : h' < 2) (hi : i < 16) : bytePos (16 * h' + i) = 15 - i := by
  unfold bytePos; omega

/-- The tie ops of leaf `D k`: `acc_k = [k % 16 ≠ 0] · acc_{k-1} + vV (bytePos k) (D k)`. -/
theorem tie_rel {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D)
    (hpos : ∀ j ≤ 255, v (posCell j) = posV j) {k : ℕ} (hk : k < 32) :
    v (accCell k) = (if k % 16 = 0 then 0 else v (accCell (k - 1))) + vV (bytePos k) (D k) := by
  have hL : 4 ≤ leafLen k (D k) := leafLen_ge k (D k)
  by_cases h0 : k % 16 = 0
  · rw [if_pos h0, zero_add]
    exact nh_setc (leaf_at hR hP hD (Or.inl hk) (i := 0) (by omega)) (leafOp_tie0 hk h0)
  · rw [if_neg h0]
    by_cases h15 : k % 16 = 15
    · have h := nh_xor (leaf_at hR hP hD (Or.inl hk) (i := 0) (by omega)) (leafOp_tie15 hk h15)
      rw [h, hpos _ (by have := hD.1 k (Or.inl hk); omega), show bytePos k = 0 by
        unfold bytePos; omega, vV_zero]
    · have hf := nh_setc (leaf_at hR hP hD (Or.inl hk) (i := 0) (by omega))
        (leafOp_mid0 hk h0 h15)
      have h := nh_xor (leaf_at hR hP hD (Or.inl hk) (i := 1) (by omega))
        (leafOp_mid1 hk h0 h15)
      rw [h, hf]

/-- The tie of half `h'` (chains `16h' … 16h' + 15`) accumulates its tie words. -/
theorem tie_run {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ s, R s → CRelNH v (cinstrAt s))
    {D : ℕ → ℕ} (hP : PathFacts R D) (hD : Valid D)
    (hpos : ∀ j ≤ 255, v (posCell j) = posV j) {h' : ℕ} (hh : h' < 2) :
    ∀ s < 16, v (accCell (16 * h' + s)) =
      ∑ i ∈ Finset.range (s + 1), vV (15 - i) (D (16 * h' + i)) := by
  intro s
  induction s with
  | zero =>
    intro _
    rw [tie_rel hR hP hD hpos (by omega), if_pos (by omega), zero_add, Finset.sum_range_one,
      bytePos_half hh (by norm_num)]
  | succ s ih =>
    intro hs
    rw [tie_rel hR hP hD hpos (by omega), if_neg (by omega),
      show 16 * h' + (s + 1) - 1 = 16 * h' + s by omega, ih (by omega),
      Finset.sum_range_succ _ (s + 1), bytePos_half hh hs]

/-! ## Chains -/

/-- A chain-step `BLAKE2S` with pinned position cells computes the scheme's chain step. -/
theorem blake_chain_out {f : HashTable} {v : ℕ → E}
    (hpos : ∀ j ≤ 255, cellBits (v (posCell j)) = BitVec.ofNat 128 j)
    (hz0 : v zCell = 0) (hz1 : v (zCell + 1) = 0) {a k j out : ℕ} (hk : k ≤ 255) (hj : j ≤ 255)
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

/-- The end of chain `k`: `x_{k,255} = chainValue f k (D k) (255 - D k) σ_k`. -/
theorem chain_end {f : HashTable} {v : ℕ → E} {D : ℕ → ℕ}
    (hP : PathFacts (CRel f v ∘ cinstrAt) D) (hD : Valid D)
    (hpos : ∀ j ≤ 255, cellBits (v (posCell j)) = BitVec.ofNat 128 j)
    (hz0 : v zCell = 0) (hz1 : v (zCell + 1) = 0) {k : ℕ} (hk : k < 34) :
    cellBits (v (xCell k 255)) =
      chainValue f k (D k) (255 - D k) (cellBits (v (sigCell k))) := by
  have hQ : ∀ s, (CRel f v ∘ cinstrAt) s → CRel f v (cinstrAt s) := fun _ h => h
  have hDk : D k ≤ 255 := by
    rcases Nat.lt_or_ge k 32 with h | h
    · have := hD.1 k (Or.inl h); omega
    · rcases (show k = 32 ∨ k = 33 by omega) with rfl | rfl
      · have := hD.2; omega
      · have := hD.1 33 (Or.inr rfl); omega
  refine chain_from f k (D k) hDk _ (fun j => cellBits (v (xCell k j))) ?_ ?_ ?_
  · intro he
    by_cases h32 : k = 32
    · subst h32
      exact blake_chain_out hpos hz0 hz1 (by norm_num) (by omega)
        ((leaf32Op_blake _) ▸ leaf32_at hQ hP hD (i := 0) (by norm_num))
    · have hk' : k < 32 ∨ k = 33 := by omega
      have hL := leafLen_of_lt (k := k) he
      exact blake_chain_out hpos hz0 hz1 (by omega) (by omega)
        ((coreOp_blake he) ▸ core_at hQ hP hD hk' (j := 0) (by omega))
  · intro j hj1 hj2
    exact blake_chain_out hpos hz0 hz1 (by omega) (by omega) (body_at hQ hP hk hj1 hj2)
  · intro he
    have hk' : k < 32 ∨ k = 33 := by
      rcases Nat.lt_or_ge k 32 with h | h
      · exact Or.inl h
      · rcases (show k = 32 ∨ k = 33 by omega) with rfl | rfl
        · have := hD.2; omega
        · exact Or.inr rfl
    have hL := leafLen_of_ge (k := k) (show ¬ D k < 255 by omega)
    have h := nh_xor (crelNH_of_crel (core_at hQ hP hD hk' (j := 0) (by omega)))
      (coreOp255_xor (by omega))
    show cellBits (v (xCell k 255)) = cellBits (v (sigCell k))
    rw [h, hz0, add_zero]

/-! ## Fixed-table soundness -/

/-- Cell values satisfying the relations along a path with leaf vector `D`, and agreeing with
the loader on the pinned cells, certify a signature the verifier accepts under the table. -/
theorem accept_of_path (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)
    (v : ℕ → E) (hpin : ∀ c < 47, v c = inputWord pk m bits c) {D : ℕ → ℕ} (hD : Valid D)
    (h : PathFacts (CRel f v ∘ cinstrAt) D) :
    bits.length = 4352 ∧ rootValue f (reconstructedWords f m bits) = pk := by
  have hR : ∀ s, (CRel f v ∘ cinstrAt) s → CRelNH v (cinstrAt s) :=
    fun _ h => crelNH_of_crel h
  have hQ : ∀ s, (CRel f v ∘ cinstrAt) s → CRel f v (cinstrAt s) := fun _ h => h
  have hc := constFacts_of hR h.const
  -- the length and the zero cells
  have hlen : bits.length = 4352 :=
    length_of_inputWord_len pk m bits ((hpin 3 (by norm_num)).symm.trans hc.len)
  refine ⟨hlen, ?_⟩
  have hz0 : v zCell = 0 :=
    (hpin 38 (by norm_num)).trans (inputWord_pad_zero pk m bits hlen le_rfl (by norm_num))
  have hz1 : v (zCell + 1) = 0 :=
    (hpin 39 (by norm_num)).trans (inputWord_pad_zero pk m bits hlen (by norm_num) (by norm_num))
  have hzb : cellBits (v zCell) = 0 := by rw [hz0]; exact cellBits_zero_E
  have hpos : ∀ j ≤ 255, v (posCell j) = posV j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [posCell_zero, hz0]; exact cellOfBits_zero.symm
    · exact hc.pos j hj0 hj
  have hposb : ∀ j ≤ 255, cellBits (v (posCell j)) = BitVec.ofNat 128 j := by
    intro j hj; rw [hpos j hj]; exact cellBits_cellOfBits _
  -- the revealed words
  have hsig : ∀ i : Fin 34, cellBits (v (sigCell i.val)) = decode bits i := by
    intro i
    have h1 : v (sigCell i.val) = inputWord pk m bits (4 + i.val) :=
      hpin (4 + i.val) (by have := i.isLt; omega)
    rw [h1, inputWord_sigDecode pk m bits hlen i]
    exact cellBits_cellOfBits _
  -- the message digits
  have hbyte : ∀ h' < 2, ∀ i < 16, D (16 * h' + i) < 256 := fun h' hh i hi =>
    hD.1 _ (Or.inl (by omega))
  have hhalf : ∀ h' < 2, v (accCell (16 * h' + 15)) = cellOfBits (BitVec.ofNat 128
      (∑ b ∈ Finset.range 16, 256 ^ b * D (16 * h' + 15 - b))) := fun h' hh =>
    (tie_run hR h hD hpos hh 15 (by norm_num)).trans (tie_sum_half D _ (hbyte h' hh))
  have hdig : ∀ k (hk : k < 32), D k = digit m ⟨k, by omega⟩ := by
    intro k hk
    by_cases h16 : 16 ≤ k
    · have hcell := (hhalf 1 (by norm_num)).symm.trans (hpin 1 (by norm_num))
      rw [inputWord_one] at hcell
      have hb := byte_of_pack _ (fun b hb => hD.1 _ (Or.inl (by omega)))
        _ hcell (31 - k) (by omega)
      rw [show 16 * 1 + 15 - (31 - k) = k by omega] at hb
      rw [hb, digit_cell1 m ⟨k, by omega⟩ h16 hk]
    · have hcell := (hhalf 0 (by norm_num)).symm.trans (hpin 2 (by norm_num))
      rw [inputWord_two] at hcell
      have hb := byte_of_pack _ (fun b hb => hD.1 _ (Or.inl (by omega)))
        _ hcell (15 - k) (by omega)
      rw [show 16 * 0 + 15 - (15 - k) = k by omega] at hb
      rw [hb, digit_cell2 m ⟨k, by omega⟩ (show k < 16 by omega)]
  -- the checksum digits
  have hck := checksum_digits m D hdig (by have := hD.1 33 (Or.inr rfl); omega)
    (checksum_of_path hR h hD)
  have hall : ∀ i : Fin 34, D i.val = digit m i := by
    intro i
    by_cases hi : i.val < 32
    · exact hdig i.val hi
    · by_cases h32 : i.val = 32
      · rw [show i = ⟨32, by norm_num⟩ from Fin.ext h32]; exact hck.1
      · rw [show i = ⟨33, by norm_num⟩ from Fin.ext (show i.val = 33 by have := i.isLt; omega)]; exact hck.2
  -- the endpoints
  have hend : ∀ i : Fin 34, reconstructedWords f m bits i = cellBits (v (xCell i.val 255)) := by
    intro i
    have h1 := chain_end h hD hposb hz0 hz1 i.isLt
    rw [hall i, hsig i] at h1
    exact h1.symm
  -- the root
  have hroot : cellBits (v (rootStateCell 34)) = rootValue f (reconstructedWords f m bits) := by
    have habs : ∀ k < 34, blake2sQuery ![v (xCell k 255), v zCell, v zCell, v zCell]
        (v (rootStateCell k)) (v (rootStateCell k + 1)) (v (posCell (35 - k))) =
        hashInput (cellBits (v (rootStateCell k + 1)) ++ cellBits (v (rootStateCell k)))
          ((cellBits (v (xCell k 255))).setWidth 512) (BitVec.ofNat 128 (2 + (33 - k))) :=
      fun k hk => blake2sQuery_absorb (33 - k) _ _ _ _ _ _ _ hzb hzb hzb
        (by rw [hposb _ (by omega), show 2 + (33 - k) = 35 - k by omega])
    refine root_sound f _ (fun k => v (xCell k 255)) (fun k => v (rootStateCell k))
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
