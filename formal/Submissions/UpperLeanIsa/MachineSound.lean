import Submissions.UpperLeanIsa.MachineProver
import Mathlib.Tactic.Choose

/-!
# Soundness of the leanISA machine under a fixed oracle table

`CRel f v ci` is the relation the cell-level instruction `ci` asserts on the cell values `v`,
with `BLAKE2S` answered by the table `f`. `accept_of_rel`: cell values that satisfy all `N`
relations, and agree with the loader on the pinned cells, certify a signature that the verifier
accepts under `f`. The argument is per segment: the thermometer and the multiplexer read each
chain's endpoint off the cells (`chain_sound_255`), the links pin the digits to the message and
the checksum (`byte_of_pack`, `checksum_link_digit`), and the root states fold to the public key
(`root_sound`).
-/

namespace OptimalOTS.LeanIsaBaseline.Honest

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits eq_of_cellBits_eq blake2sQuery
  hashInput inputWord statementBits OracleCompressCells)
open OptimalOTS.LeanIsaBaseline.Machine

noncomputable section

/-! ## The relation of one instruction -/

/-- The relation the cell-level instruction asserts on the cell values `v` under table `f`:
`CInstr.Rel` of `MachineRun` without the range conditions. -/
def CRel (f : HashTable) (v : ℕ → E) : CInstr → Prop
  | .xor a b c => v c = v a + v b
  | .mul a b c => v c = v a * v b
  | .setc a k => v a = k
  | .blake m0 m1 m2 m3 cv out md =>
      OracleCompressCells ![v m0, v m1, v m2, v m3] (v cv) (v (cv + 1)) (v out) (v (out + 1))
        (v md) (f ⟨896, blake2sQuery ![v m0, v m1, v m2, v m3] (v cv) (v (cv + 1)) (v md)⟩)
  | .jump a b c => IsInK (v a) ∧ IsInK (v b) ∧ IsInK (v c)

/-- All `N` relations. -/
def AllRel (f : HashTable) (v : ℕ → E) : Prop := ∀ k < N, CRel f v (cinstrAt k)

/-! ## Segment accessors -/

section Access

variable {f : HashTable} {v : ℕ → E}

theorem rel_const (h : AllRel f v) {a : ℕ} (ha : a < A_len) : CRel f v (constInstr a) := by
  have hA : A_len = 5191 := rfl
  have hN : N = 92093 := rfl
  have h1 := h a (by omega)
  rwa [cinstrAt_const ha] at h1

theorem rel_step (h : AllRel f v) {i j r : ℕ} (hi : i < 34) (hj : j < 255) (hr : r < 10) :
    CRel f v (stepInstr i j r) := by
  have hA : A_len = 5191 := rfl
  have hN : N = 92093 := rfl
  have h1 := h (A_len + 2553 * i + 10 * j + r) (by omega)
  rwa [cinstrAt_step hi hj hr] at h1

theorem rel_end (h : AllRel f v) {i e : ℕ} (hi : i < 34) (he : e < 3) :
    CRel f v (endInstr i e) := by
  have hA : A_len = 5191 := rfl
  have hN : N = 92093 := rfl
  have h1 := h (A_len + 2553 * i + 2550 + e) (by omega)
  rwa [cinstrAt_end hi he] at h1

theorem rel_link (h : AllRel f v) {h' s : ℕ} (hh : h' < 2) (hs : s < 15) :
    CRel f v (linkInstr h' s) := by
  have hC : C_start = 91993 := rfl
  have hN : N = 92093 := rfl
  have h1 := h (C_start + 15 * h' + s) (by omega)
  rwa [cinstrAt_link hh hs] at h1

theorem rel_prod (h : AllRel f v) {s : ℕ} (hs : s < 32) : CRel f v (prodInstr s) := by
  have hD : D_start = 92023 := rfl
  have hN : N = 92093 := rfl
  have h1 := h (D_start + s) (by omega)
  rwa [cinstrAt_prod hs] at h1

theorem rel_root (h : AllRel f v) {t : ℕ} (ht : t < 35) : CRel f v (rootInstr t) := by
  have hE : E_start = 92055 := rfl
  have hN : N = 92093 := rfl
  have h1 := h (E_start + t) (by omega)
  rwa [cinstrAt_root ht] at h1

end Access

/-! ## Unfolding the chain slots -/

theorem stepInstr_0 (i j : ℕ) : stepInstr i j 0 = .mul (tCell i j) (tCell i j) (tCell i j) := by
  unfold stepInstr
  rw [if_pos rfl]

theorem stepInstr_1 (i j : ℕ) :
    stepInstr i j 1 = .mul (tPrevCell i j) (tCell i j) (tPrevCell i j) := by
  unfold stepInstr
  rw [if_neg (by decide), if_pos rfl]

theorem stepInstr_2 (i j : ℕ) : stepInstr i j 2 = .xor (xCell i j) (sigCell i) (sCell i j) := by
  unfold stepInstr
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem stepInstr_3 (i j : ℕ) :
    stepInstr i j 3 = .mul (tPrevCell i j) (sCell i j) (uCell i j) := by
  unfold stepInstr
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem stepInstr_4 (i j : ℕ) : stepInstr i j 4 = .xor (sigCell i) (uCell i j) (inCell i j) := by
  unfold stepInstr
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem stepInstr_5 (i j : ℕ) :
    stepInstr i j 5 =
      .blake (inCell i j) (chainIdCell i) (posCell j) zCell zCell (xCell i (j + 1)) oneCell := by
  unfold stepInstr
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]

theorem stepInstr_6 (i j : ℕ) :
    stepInstr i j 6 = .mul (tCell i j) (wvCell (bytePos i) j) (pVCell i j) := by
  unfold stepInstr
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem stepInstr_7 (i j : ℕ) :
    stepInstr i j 7 = .xor (aVCell i j) (pVCell i j) (aVCell i (j + 1)) := by
  unfold stepInstr
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem stepInstr_8 (i j : ℕ) :
    stepInstr i j 8 = .mul (tCell i j) (wuSelCell i j) (pUCell i j) := by
  unfold stepInstr
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem stepInstr_9 (i j : ℕ) :
    stepInstr i j 9 = .xor (aUCell i j) (pUCell i j) (aUCell i (j + 1)) := by
  unfold stepInstr
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide)]

theorem endInstr_0 (i : ℕ) : endInstr i 0 = .xor (xCell i 255) (sigCell i) (e0Cell i) := by
  unfold endInstr
  rw [if_pos rfl]

theorem endInstr_1 (i : ℕ) : endInstr i 1 = .mul (tCell i 254) (e0Cell i) (e1Cell i) := by
  unfold endInstr
  rw [if_neg (by decide), if_pos rfl]

theorem endInstr_2 (i : ℕ) : endInstr i 2 = .xor (sigCell i) (e1Cell i) (endCell i) := by
  unfold endInstr
  rw [if_neg (by decide), if_neg (by decide)]

theorem prodInstr_lt {s : ℕ} (hs : s < 31) :
    prodInstr s = .mul (prodAccCell s) (pCell (s + 1)) (prodAccCell (s + 1)) := by
  unfold prodInstr
  rw [if_pos hs]

theorem prodInstr_31 : prodInstr 31 = .mul (pCell 32) (pCell 33) (prodAccCell 31) := by
  unfold prodInstr
  rw [if_neg (by decide)]

theorem rootInstr_lt {t : ℕ} (ht : t < 34) :
    rootInstr t = .blake (endCell t) zCell zCell zCell (rootStateCell t)
      (rootStateCell (t + 1)) (rootMdCell (33 - t)) := by
  unfold rootInstr
  rw [if_pos ht]

theorem rootInstr_34 : rootInstr 34 = .xor (rootStateCell 34) zCell pkCell := by
  unfold rootInstr
  rw [if_neg (by decide)]

theorem linkAccCell_zero (h' : ℕ) : linkAccCell h' 0 = dCell (linkChain h' 0) := by
  unfold linkAccCell
  rw [if_pos rfl]

theorem linkAccCell_15 (h' : ℕ) : linkAccCell h' 15 = 1 + h' := by
  unfold linkAccCell
  rw [if_neg (by decide), if_pos rfl]

theorem prodAccCell_zero : prodAccCell 0 = pCell 0 := by
  unfold prodAccCell
  rw [if_pos rfl]

theorem bytePos_linkChain {h' b : ℕ} (hh : h' < 2) (hb : b < 16) :
    bytePos (linkChain h' b) = b := by
  unfold bytePos linkChain
  rw [if_pos (by omega)]
  omega

/-! ## Runs of relations -/

/-- A run of link `XOR`s sums the `D` cells of its half. -/
theorem link_run (v : ℕ → E) (h' : ℕ)
    (hs : ∀ s < 15, v (linkAccCell h' (s + 1)) =
      v (linkAccCell h' s) + v (dCell (linkChain h' (s + 1)))) :
    ∀ s ≤ 15, v (linkAccCell h' s) = ∑ b ∈ Finset.range (s + 1), v (dCell (linkChain h' b)) := by
  intro s
  induction s with
  | zero =>
    intro _
    show v (linkAccCell h' 0) = ∑ b ∈ Finset.range 1, v (dCell (linkChain h' b))
    rw [Finset.sum_range_one, linkAccCell_zero]
  | succ s ih =>
    intro hs1
    rw [Finset.sum_range_succ, hs s (by omega), ih (by omega)]

/-- The checksum product run multiplies the `P` cells. -/
theorem prod_run (v : ℕ → E)
    (hs : ∀ s < 31, v (prodAccCell (s + 1)) = v (prodAccCell s) * v (pCell (s + 1))) :
    ∀ s ≤ 31, v (prodAccCell s) = ∏ b ∈ Finset.range (s + 1), v (pCell b) := by
  intro s
  induction s with
  | zero =>
    intro _
    show v (prodAccCell 0) = ∏ b ∈ Finset.range 1, v (pCell b)
    rw [Finset.prod_range_one, prodAccCell_zero]
  | succ s ih =>
    intro hs1
    rw [Finset.prod_range_succ, hs s (by omega), ih (by omega)]

/-! ## One chain -/

/-- What the constants of segment A pin, as used by the chains and the root. -/
structure ConstFacts (v : ℕ → E) : Prop where
  z0 : v zCell = 0
  z1 : v (zCell + 1) = 0
  one : v oneCell = oneV
  chainId : ∀ i < 34, v (chainIdCell i) = chainIdV i
  rootMd : ∀ r < 34, v (rootMdCell r) = rootMdV r
  pos : ∀ j < 255, v (posCell j) = posV j
  wv : ∀ p < 16, ∀ j < 255, v (wvCell p j) = wvV p j
  wu : ∀ i < 34, ∀ j < 255, v (wuSelCell i j) = auW i j
  vb : ∀ p < 16, v (vbCell p) = vbV p
  ub : ∀ i < 34, v (aUBaseCell i) = auBase i
  len : v lenCell = lenV

theorem constFacts_of (f : HashTable) (v : ℕ → E) (h : AllRel f v) : ConstFacts v := by
  have hA : A_len = 5191 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := rel_const h (a := 0) (by omega)
    rw [constInstr_zero] at h1
    exact h1
  · have h1 := rel_const h (a := 1) (by omega)
    rw [constInstr_one] at h1
    exact h1
  · have h1 := rel_const h (a := 2) (by omega)
    rw [constInstr_two] at h1
    exact h1
  · intro i hi
    have h1 := rel_const h (a := 4 + i) (by omega)
    rw [constInstr_chainId hi] at h1
    exact h1
  · intro r hr
    have h1 := rel_const h (a := 38 + r) (by omega)
    rw [constInstr_rootMd hr] at h1
    exact h1
  · intro j hj
    have h1 := rel_const h (a := 72 + j) (by omega)
    rw [constInstr_pos hj] at h1
    exact h1
  · intro p hp j hj
    have h1 := rel_const h (a := 327 + 255 * p + j) (by omega)
    rw [constInstr_wv hp hj] at h1
    exact h1
  · intro i hi j hj
    unfold wuSelCell auW
    by_cases h32 : i < 32
    · rw [if_pos h32, if_pos h32]
      have h1 := rel_const h (a := 4407 + j) (by omega)
      rw [constInstr_wu hj] at h1
      exact h1
    · by_cases h33 : i = 32
      · rw [if_neg h32, if_neg h32, if_pos h33, if_pos h33]
        have h1 := rel_const h (a := 4662 + j) (by omega)
        rw [constInstr_wuHi hj] at h1
        exact h1
      · rw [if_neg h32, if_neg h32, if_neg h33, if_neg h33]
        have h1 := rel_const h (a := 4917 + j) (by omega)
        rw [constInstr_wuLo hj] at h1
        exact h1
  · intro p hp
    have h1 := rel_const h (a := 5174 + p) (by omega)
    rw [constInstr_vb hp] at h1
    exact h1
  · intro i hi
    unfold aUBaseCell auBase
    by_cases h32 : i < 32
    · rw [if_pos h32, if_pos h32]
      have h1 := rel_const h (a := 2) (by omega)
      rw [constInstr_two] at h1
      exact h1
    · by_cases h33 : i = 32
      · rw [if_neg h32, if_neg h32, if_pos h33, if_pos h33]
        have h1 := rel_const h (a := 5172) (by omega)
        rw [constInstr_ubHi] at h1
        exact h1
      · rw [if_neg h32, if_neg h32, if_neg h33, if_neg h33]
        have h1 := rel_const h (a := 5173) (by omega)
        rw [constInstr_ubLo] at h1
        exact h1
  · have h1 := rel_const h (a := 5190) (by omega)
    rw [constInstr_len] at h1
    exact h1

/-- What one chain's relations force: a digit `d ≤ 255`, the endpoint's chain value, and the
two link values `D = V_d`, `P = U_d`. -/
theorem chain_facts (f : HashTable) (v : ℕ → E) (h : AllRel f v) (hc : ConstFacts v)
    {i : ℕ} (hi : i < 34) :
    ∃ d ≤ 255, cellBits (v (endCell i)) = chainValue f i d (255 - d) (cellBits (v (sigCell i))) ∧
      v (dCell i) = vV (bytePos i) d ∧ v (pCell i) = uV i d := by
  -- the thermometer
  have hb : ∀ j < 255, v (tCell i j) = v (tCell i j) * v (tCell i j) := by
    intro j hj
    have h1 := rel_step h hi hj (r := 0) (by norm_num)
    rw [stepInstr_0] at h1
    exact h1
  have hm : ∀ j, j + 1 < 255 → v (tCell i j) = v (tCell i j) * v (tCell i (j + 1)) := by
    intro j hj
    have h1 := rel_step h hi hj (r := 1) (by norm_num)
    rw [stepInstr_1, tPrevCell_succ] at h1
    exact h1
  obtain ⟨d, hd, ht⟩ := exists_thermo (fun j => v (tCell i j)) 255 hb hm
  refine ⟨d, hd, ?_, ?_, ?_⟩
  · -- the chain
    have hs : ∀ j < 255, v (sCell i j) = v (xCell i j) + v (sigCell i) := by
      intro j hj
      have h1 := rel_step h hi hj (r := 2) (by norm_num)
      rw [stepInstr_2] at h1
      exact h1
    have hu : ∀ j < 255, v (uCell i j) = v (tPrevCell i j) * v (sCell i j) := by
      intro j hj
      have h1 := rel_step h hi hj (r := 3) (by norm_num)
      rw [stepInstr_3] at h1
      exact h1
    have hin : ∀ j < 255, v (inCell i j) = v (sigCell i) + v (uCell i j) := by
      intro j hj
      have h1 := rel_step h hi hj (r := 4) (by norm_num)
      rw [stepInstr_4] at h1
      exact h1
    have hin0 : v (inCell i 0) = v (sigCell i) := by
      rw [hin 0 (by norm_num), hu 0 (by norm_num), tPrevCell_zero, hc.z0, zero_mul, add_zero]
    have hin' : ∀ j < 254, v (inCell i (j + 1)) =
        v (sigCell i) + v (tCell i j) * (v (xCell i (j + 1)) + v (sigCell i)) := by
      intro j hj
      rw [hin (j + 1) (by omega), hu (j + 1) (by omega), hs (j + 1) (by omega), tPrevCell_succ]
    have hx : ∀ j < 255, cellBits (v (xCell i (j + 1))) =
        (f ⟨896, chainInput i j (cellBits (v (inCell i j)))⟩).extractLsb' 0 128 := by
      intro j hj
      have h1 := rel_step h hi hj (r := 5) (by norm_num)
      rw [stepInstr_5] at h1
      have hq : blake2sQuery ![v (inCell i j), v (chainIdCell i), v (posCell j), v zCell]
          (v zCell) (v (zCell + 1)) (v oneCell) = chainInput i j (cellBits (v (inCell i j))) := by
        apply blake2sQuery_chain
        · rw [hc.chainId i hi]
          exact cellBits_cellOfBits _
        · rw [hc.pos j hj]
          exact cellBits_cellOfBits _
        · rw [hc.z0]
          exact cellBits_zero
        · rw [hc.z0]
          exact cellBits_zero
        · rw [hc.z1]
          exact cellBits_zero
        · rw [hc.one]
          exact cellBits_oneV
      obtain ⟨-, -, -, -, -, -, h2, -⟩ := h1
      rw [hq] at h2
      exact h2
    have he : v (endCell i) =
        v (sigCell i) + v (tCell i 254) * (v (xCell i 255) + v (sigCell i)) := by
      have h0 := rel_end h hi (e := 0) (by norm_num)
      have h1 := rel_end h hi (e := 1) (by norm_num)
      have h2 := rel_end h hi (e := 2) (by norm_num)
      rw [endInstr_0] at h0
      rw [endInstr_1] at h1
      rw [endInstr_2] at h2
      have h0' : v (e0Cell i) = v (xCell i 255) + v (sigCell i) := h0
      have h1' : v (e1Cell i) = v (tCell i 254) * v (e0Cell i) := h1
      have h2' : v (endCell i) = v (sigCell i) + v (e1Cell i) := h2
      rw [h2', h1', h0']
    exact chain_sound_255 f i d hd (v (sigCell i)) (v (endCell i)) (fun j => v (tCell i j))
      (fun j => v (xCell i j)) (fun j => v (inCell i j)) ht hin0 hin' hx he
  · -- the V link
    have hp : bytePos i < 16 := by
      unfold bytePos
      split
      · omega
      · omega
    have h0 : v (aVCell i 0) = vV (bytePos i) 255 := by
      rw [aVCell_zero, hc.vb _ hp, vbV_eq]
    have hs : ∀ j < 255, v (aVCell i (j + 1)) = v (aVCell i j) +
        v (tCell i j) * (vV (bytePos i) j + vV (bytePos i) (j + 1)) := by
      intro j hj
      have h6 := rel_step h hi hj (r := 6) (by norm_num)
      have h7 := rel_step h hi hj (r := 7) (by norm_num)
      rw [stepInstr_6] at h6
      rw [stepInstr_7] at h7
      have h6' : v (pVCell i j) = v (tCell i j) * v (wvCell (bytePos i) j) := h6
      have h7' : v (aVCell i (j + 1)) = v (aVCell i j) + v (pVCell i j) := h7
      rw [h7', h6', hc.wv _ hp j hj, wvV_eq]
    rw [dCell_eq]
    exact telescope add_self_E (vV (bytePos i)) (fun j => v (aVCell i j))
      (fun j => v (tCell i j)) d 255 hd ht h0 hs
  · -- the U link
    have h0 : v (aUCell i 0) = uV i 255 := by
      rw [aUCell_zero, hc.ub i hi, auBase_eq]
    have hs : ∀ j < 255, v (aUCell i (j + 1)) = v (aUCell i j) +
        v (tCell i j) * (uV i j + uV i (j + 1)) := by
      intro j hj
      have h8 := rel_step h hi hj (r := 8) (by norm_num)
      have h9 := rel_step h hi hj (r := 9) (by norm_num)
      rw [stepInstr_8] at h8
      rw [stepInstr_9] at h9
      have h8' : v (pUCell i j) = v (tCell i j) * v (wuSelCell i j) := h8
      have h9' : v (aUCell i (j + 1)) = v (aUCell i j) + v (pUCell i j) := h9
      rw [h9', h8', hc.wu i hi j hj, auW_eq]
    rw [pCell_eq]
    exact telescope add_self_E (uV i) (fun j => v (aUCell i j)) (fun j => v (tCell i j)) d 255
      hd ht h0 hs

/-! ## Fixed-table soundness -/

/-- Cell values satisfying all `N` relations, and agreeing with the loader on the pinned cells,
certify a signature the verifier accepts under the table. -/
theorem accept_of_rel (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)
    (v : ℕ → E) (hpin : ∀ c < 47, v c = inputWord pk m bits c) (h : AllRel f v) :
    bits.length = 4352 ∧ rootValue f (reconstructedWords f m bits) = pk := by
  have hc := constFacts_of f v h
  -- the length
  have hlen : bits.length = 4352 := by
    have h3 : v lenCell = inputWord pk m bits 3 := hpin 3 (by norm_num)
    rw [hc.len] at h3
    exact length_of_inputWord_three pk m bits h3.symm
  refine ⟨hlen, ?_⟩
  -- the revealed words
  have hsig : ∀ i : Fin 34, cellBits (v (sigCell i.val)) = decode bits i := by
    intro i
    have h1 : v (sigCell i.val) = inputWord pk m bits (4 + i.val) :=
      hpin (4 + i.val) (by have := i.isLt; omega)
    rw [h1, inputWord_decode pk m bits hlen i]
    exact cellBits_cellOfBits _
  -- the chains
  have hch : ∀ i, ∃ d, i < 34 → d ≤ 255 ∧
      cellBits (v (endCell i)) = chainValue f i d (255 - d) (cellBits (v (sigCell i))) ∧
      v (dCell i) = vV (bytePos i) d ∧ v (pCell i) = uV i d := by
    intro i
    by_cases hi : i < 34
    · obtain ⟨d, hd, h1, h2, h3⟩ := chain_facts f v h hc hi
      exact ⟨d, fun _ => ⟨hd, h1, h2, h3⟩⟩
    · exact ⟨0, fun h' => absurd h' hi⟩
  choose dd hdd using hch
  -- the message digits
  have hhalf : ∀ h' < 2, v (1 + h') = cellOfBits (BitVec.ofNat 128
      (∑ b ∈ Finset.range 16, 256 ^ b * dd (linkChain h' b))) := by
    intro h' hh
    have hrun : v (linkAccCell h' 15) =
        ∑ b ∈ Finset.range 16, v (dCell (linkChain h' b)) :=
      link_run v h' (fun s hs => rel_link h hh hs) 15 (le_refl 15)
    rw [linkAccCell_15] at hrun
    rw [hrun, ← pack_sum_eq (fun b => dd (linkChain h' b)) 16 (fun b hb => by
      have := (hdd (linkChain h' b) (by unfold linkChain; omega)).1
      show dd (linkChain h' b) < 256
      omega)]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' : b < 16 := Finset.mem_range.mp hb
    rw [(hdd (linkChain h' b) (by unfold linkChain; omega)).2.2.1, bytePos_linkChain hh hb']
    all_goals rfl
  have hdig : ∀ i (hi : i < 32), dd i = digit m ⟨i, by omega⟩ := by
    intro i hi
    by_cases h16 : 16 ≤ i
    · -- message cell 1, in-cell byte 31 - i
      have hcell : v (1 + 0) = inputWord pk m bits 1 := hpin 1 (by norm_num)
      rw [hhalf 0 (by norm_num), inputWord_one] at hcell
      have hbyte : dd (linkChain 0 (31 - i)) =
          (m.extractLsb' 0 128).toNat / 256 ^ (31 - i) % 256 :=
        byte_of_pack (fun b => dd (linkChain 0 b)) (fun b hb => by
          have := (hdd (linkChain 0 b) (by unfold linkChain; omega)).1
          show dd (linkChain 0 b) < 256
          omega) (m.extractLsb' 0 128) hcell (31 - i) (by omega)
      have hl : linkChain 0 (31 - i) = i := by
        unfold linkChain
        omega
      rw [digit_cell1 m ⟨i, by omega⟩ (show 16 ≤ i from h16) (show i < 32 from hi)]
      rw [hl] at hbyte
      exact hbyte
    · -- message cell 2, in-cell byte 15 - i
      have hcell : v (1 + 1) = inputWord pk m bits 2 := hpin 2 (by norm_num)
      rw [hhalf 1 (by norm_num), inputWord_two] at hcell
      have hbyte : dd (linkChain 1 (15 - i)) =
          (m.extractLsb' 128 128).toNat / 256 ^ (15 - i) % 256 :=
        byte_of_pack (fun b => dd (linkChain 1 b)) (fun b hb => by
          have := (hdd (linkChain 1 b) (by unfold linkChain; omega)).1
          show dd (linkChain 1 b) < 256
          omega) (m.extractLsb' 128 128) hcell (15 - i) (by omega)
      have hl : linkChain 1 (15 - i) = i := by
        unfold linkChain
        omega
      rw [digit_cell2 m ⟨i, by omega⟩ (show i < 16 by omega)]
      rw [hl] at hbyte
      exact hbyte
  -- the checksum digits
  have hprod : ∏ b ∈ Finset.range 32, v (pCell b) = v (pCell 32) * v (pCell 33) := by
    have hrun : v (prodAccCell 31) = ∏ b ∈ Finset.range 32, v (pCell b) :=
      prod_run v (fun s hs => by
        have h1 := rel_prod h (s := s) (by omega)
        rw [prodInstr_lt hs] at h1
        exact h1) 31 (le_refl 31)
    have h31 := rel_prod h (s := 31) (by norm_num)
    rw [prodInstr_31] at h31
    have h31' : v (prodAccCell 31) = v (pCell 32) * v (pCell 33) := h31
    rw [← hrun, h31']
  have hck : dd 32 = digit m ⟨32, by norm_num⟩ ∧ dd 33 = digit m ⟨33, by norm_num⟩ := by
    have hP : ∀ b < 32, v (pCell b) = ofK (gpow (255 - dd b)) := by
      intro b hb
      rw [(hdd b (by omega)).2.2.2]
      unfold uV uExp
      rw [if_pos hb]
    have hl : ∏ b ∈ Finset.range 32, v (pCell b) =
        ofK (gpow (∑ b ∈ Finset.range 32, (255 - dd b))) :=
      (Finset.prod_congr rfl (fun b hb => hP b (Finset.mem_range.mp hb))).trans
        (ofK_gpow_prod (fun b => 255 - dd b) 32)
    have h32 : v (pCell 32) = ofK (gpow (256 * dd 32)) := by
      rw [(hdd 32 (by norm_num)).2.2.2]
      unfold uV uExp
      rw [if_neg (by norm_num), if_pos rfl]
    have h33 : v (pCell 33) = ofK (gpow (dd 33)) := by
      rw [(hdd 33 (by norm_num)).2.2.2]
      unfold uV uExp
      rw [if_neg (by norm_num), if_neg (by norm_num)]
    rw [hl, h32, h33, ← ofK_mul] at hprod
    exact checksum_link_digit m dd hdig (dd 32) (dd 33) (hdd 32 (by norm_num)).1
      (hdd 33 (by norm_num)).1 (ofK_injective hprod) ⟨32, by norm_num⟩ ⟨33, by norm_num⟩ rfl rfl
  have hall : ∀ i : Fin 34, dd i.val = digit m i := by
    intro i
    by_cases hi : i.val < 32
    · exact hdig i.val hi
    · by_cases h32 : i.val = 32
      · have e : i = ⟨32, by norm_num⟩ := Fin.ext h32
        rw [e]
        exact hck.1
      · have hi33 : i.val = 33 := by have := i.isLt; omega
        have e : i = ⟨33, by norm_num⟩ := Fin.ext hi33
        rw [e]
        exact hck.2
  -- the endpoints
  have hend : ∀ i : Fin 34, reconstructedWords f m bits i = cellBits (v (endCell i.val)) := by
    intro i
    have h1 := (hdd i.val i.isLt).2.1
    rw [hall i, hsig i] at h1
    exact h1.symm
  -- the root
  have hlo0 : cellBits (v (rootStateCell 0)) = 0 := by
    rw [rootStateCell_zero, hc.z0]
    exact cellBits_zero
  have hhi0 : cellBits (v (rootStateCell 0 + 1)) = 0 := by
    rw [rootStateCell_zero, hc.z1]
    exact cellBits_zero
  have hroot : cellBits (v (rootStateCell 34)) = rootValue f (reconstructedWords f m bits) :=
    root_sound f (reconstructedWords f m bits) (fun k => v (endCell k))
    (fun k => v (rootStateCell k)) (fun k => v (rootStateCell k + 1)) hend hlo0 hhi0
    (fun k hk => by
      have h1 := rel_root h (t := k) (by omega)
      rw [rootInstr_lt hk] at h1
      have hq := blake2sQuery_absorb (33 - k) (v (endCell k)) (v zCell) (v zCell) (v zCell)
        (v (rootStateCell k)) (v (rootStateCell k + 1)) (v (rootMdCell (33 - k)))
        (by rw [hc.z0]; exact cellBits_zero) (by rw [hc.z0]; exact cellBits_zero)
        (by rw [hc.z0]; exact cellBits_zero)
        (by rw [hc.rootMd _ (by omega)]; exact cellBits_cellOfBits _)
      obtain ⟨-, -, -, -, -, -, h2, -⟩ := h1
      rw [hq] at h2
      exact h2)
    (fun k hk => by
      have h1 := rel_root h (t := k) (by omega)
      rw [rootInstr_lt hk] at h1
      have hq := blake2sQuery_absorb (33 - k) (v (endCell k)) (v zCell) (v zCell) (v zCell)
        (v (rootStateCell k)) (v (rootStateCell k + 1)) (v (rootMdCell (33 - k)))
        (by rw [hc.z0]; exact cellBits_zero) (by rw [hc.z0]; exact cellBits_zero)
        (by rw [hc.z0]; exact cellBits_zero)
        (by rw [hc.rootMd _ (by omega)]; exact cellBits_cellOfBits _)
      obtain ⟨-, -, -, -, -, -, -, h2⟩ := h1
      rw [hq] at h2
      exact h2)
  -- the public key
  have hpk := rel_root h (t := 34) (by norm_num)
  rw [rootInstr_34] at hpk
  have hpk' : v pkCell = v (rootStateCell 34) + v zCell := hpk
  rw [hc.z0, add_zero] at hpk'
  have h0 : v pkCell = inputWord pk m bits 0 := hpin 0 (by norm_num)
  rw [inputWord_zero] at h0
  rw [← hroot, ← hpk', h0]
  exact cellBits_cellOfBits pk

end

end OptimalOTS.LeanIsaBaseline.Honest
