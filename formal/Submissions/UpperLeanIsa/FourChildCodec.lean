import Submissions.UpperLeanIsa.GenOrderFast
import Submissions.UpperLeanIsa.LayerAvailability
import Submissions.UpperLeanIsa.LayerDigits
import Submissions.UpperLeanIsa.LayerProfile
import Submissions.UpperLeanIsa.SplitCodec
import Submissions.UpperLeanIsa.TierCodec

/-! Layer-85 codec for the mixed four/five-child candidate. The eight binding
units have nonzero visible prefixes; hidden coordinates remain part of the
injective digit tuple. Explicit tuple-specific alias intervals support the
exceptional 496- and 144-fold multiplicities. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace FourChildCodec

open LeanerVM.Parameters

/-! ## Units, chains and positions -/

/-- The table shape of unit `u`. -/
def ushape (u : ℕ) : ℕ := u % 13

/-- Width of group field `u` (zero past the 13 units). -/
def ubits (u : ℕ) : ℕ := if u < 13 then shB (ushape u) else 0

/-- The chains of unit `u`, by coordinate: the home of call 1, four exporters, the homes of calls
0 and 7, the homes of calls 2 … 6, and the fifth exporter. -/
def unitChains (u : ℕ) : List ℕ :=
  [[1, 2, 7], [12, 13, 17], [18, 22, 23], [27, 28, 32], [33, 37, 38], [3, 4, 5, 6], [8, 9, 10, 11], [14, 15, 16], [19, 20, 21], [24, 25, 26], [29, 30, 31], [34, 35, 36], [39, 40, 41]].getD u []

/-- Chain `i` of unit `u`. -/
def chainAt (u i : ℕ) : ℕ := (unitChains u).getD i 0

/-- The unit of group chain `k ≥ 1`. -/
def unitOf (k : ℕ) : ℕ :=
  [0, 0, 0, 5, 5, 5, 5, 0, 6, 6, 6, 6, 1, 1, 7, 7, 7, 1, 2, 8, 8, 8, 2, 2, 9, 9, 9, 3, 3, 10, 10, 10, 3, 4, 11, 11, 11, 4, 4, 12, 12, 12].getD k 0

/-- The coordinate of group chain `k ≥ 1` in its unit. -/
def coordOf (k : ℕ) : ℕ :=
  [0, 0, 1, 0, 1, 2, 3, 2, 0, 1, 2, 3, 0, 1, 0, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2].getD k 0

/-- Positions of chain `k`: 64 for the free chain, else its coordinate's digit bound. -/
def lenN (k : ℕ) : ℕ := if k = 0 then 64 else shLen (ushape (unitOf k)) (coordOf k)

/-- First step position of chain `k` (`off (k + 1) = off k + len k - 1`; 719 steps). -/
def off (k : ℕ) : ℕ :=
  [0, 63, 79, 95, 111, 127, 143, 159, 175, 191, 207, 223, 239, 255, 271, 287, 303, 319, 335, 351, 367, 383, 399, 415, 431, 447, 463, 479, 495, 511, 527, 543, 559, 575, 591, 607, 623, 639, 655, 671, 687, 703].getD k 719

/-- The chain and step of position `p`. -/
def locAux (p : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, k => (k, p - off k)
  | fuel + 1, k => if p < off (k + 1) then (k, p - off k) else locAux p fuel (k + 1)

/-- The chain and step of position `p < 719`. -/
def locate (p : ℕ) : ℕ × ℕ := locAux p 42 0

theorem ushape_lt (u : ℕ) : ushape u < 13 := Nat.mod_lt _ (by decide)

theorem ubits_eq {u : ℕ} (hu : u < 13) : ubits u = shB (ushape u) := if_pos hu

/-- The chain maps are mutually inverse. -/
theorem chain_facts : ∀ k < 41, unitOf (k + 1) < 13 ∧ coordOf (k + 1) < shK (ushape (unitOf (k + 1)))
    ∧ chainAt (unitOf (k + 1)) (coordOf (k + 1)) = k + 1 := by decide

theorem unit_facts : ∀ u < 13, ∀ i < shK (ushape u), 1 ≤ chainAt u i ∧ chainAt u i < 42 ∧
    unitOf (chainAt u i) = u ∧ coordOf (chainAt u i) = i := by decide

/-- The offsets advance by the chain lengths (42 checks instead of 719 `locate` runs). -/
theorem off_succ : ∀ k < 42, off (k + 1) = off k + (lenN k - 1) := by decide +kernel

theorem off_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 42) : off a ≤ off b := by
  induction b with
  | zero => rw [Nat.le_zero.1 hab]
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]
    · rw [off_succ b (by omega)]
      exact (ih (by omega) (by omega)).trans (Nat.le_add_right _ _)

/-- `locAux` started at any earlier chain with enough fuel finds position `off k + j`. -/
theorem locAux_find {k j : ℕ} (hk : k < 42) (hj : j < lenN k - 1) :
    ∀ d k' fuel, k' + d = k → d ≤ fuel → locAux (off k + j) fuel k' = (k, j) := by
  intro d
  induction d with
  | zero =>
    intro k' fuel hk' _
    rw [Nat.add_zero] at hk'
    subst hk'
    cases fuel with
    | zero => simp [locAux]
    | succ fuel =>
      rw [locAux, if_pos (by rw [off_succ k' hk]; omega)]
      simp
  | succ d ih =>
    intro k' fuel hk' hf
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hle : off (k' + 1) ≤ off k := off_mono (by omega) hk.le
    rw [locAux, if_neg (by omega)]
    exact ih (k' + 1) fuel (by omega) (by omega)

/-- Step positions are below `9 ^ 3` and determine the chain and step. -/
theorem pos_facts : ∀ k < 42, ∀ j < lenN k - 1, off k + j < 729 ∧ locate (off k + j) = (k, j) := by
  intro k hk j hj
  have h42 : off 42 = 719 := rfl
  have hs := off_succ k hk
  have hm : off (k + 1) ≤ off 42 := off_mono (by omega) le_rfl
  refine ⟨by omega, locAux_find hk hj k 0 42 (by omega) (by omega)⟩

theorem posW_13 : posW ubits 13 = 127 := by decide

theorem steps_eq : ∑ k : Fin 42, (lenN k - 1) = 719 := by decide +kernel

/-! ## Digits -/

/-- Entry `v` of unit `u`. -/
def tup (u v : ℕ) : List ℕ := tupS (ushape u) v

/-- The cost of entry `v` of unit `u`: its digit sum (`tup_sum`). -/
def cost (u v : ℕ) : ℕ := costS (ushape u) v

/-- Group field `u` of the index. -/
def field (u : ℕ) (I : Index) : ℕ := digitW ubits I.toNat u

/-- The total cost of the 13 group fields. -/
def gsum (I : Index) : ℕ := ∑ u ∈ Finset.range 13, cost u (field u I)

/-- The free chain's digit: the layer minus the total cost, when that is in `[0, 63]`. -/
def freeDigit (c : ℕ) : ℕ := if 22 ≤ c ∧ c ≤ 85 then 85 - c else 0

/-- The live entries of unit `u`. -/
def cut (u : ℕ) : ℕ := cutS (ushape u)

/-- An index is a *dummy* when some field is a dummy entry. The machine has no blocks for these
entries, and the free digit keeps dummy indices off the layer. -/
def dummy (I : Index) : Prop := ∃ u < 13, cut u ≤ field u I

/-- The free digit of an index: `[gsum = 85]` for a dummy (so its digit sum is never `85`),
else `freeDigit (gsum I)`. -/
def freeD (I : Index) : ℕ :=
  if dummy I then (if gsum I = 85 then 1 else 0) else freeDigit (gsum I)

/-- Digit of chain `k` (on naturals). -/
def digitN (I : Index) (k : ℕ) : ℕ :=
  if k = 0 then freeD I else (tup (unitOf k) (field (unitOf k) I)).getD (coordOf k) 0

theorem field_lt (u : ℕ) (I : Index) : field u I < 2 ^ ubits u := digitW_lt ubits _ _

theorem field_lt' {u : ℕ} (hu : u < 13) (I : Index) : field u I < 2 ^ shB (ushape u) := by
  rw [← ubits_eq hu]; exact field_lt u I

theorem tup_length {u v : ℕ} (hv : v < 2 ^ shB (ushape u)) : (tup u v).length = shK (ushape u) :=
  tupS_length (ushape_lt u) hv

theorem tup_sum {u v : ℕ} (hv : v < 2 ^ shB (ushape u)) : (tup u v).sum = cost u v :=
  tupS_sum (ushape_lt u) hv

theorem sum_range_getD (l : List ℕ) :
    ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

/-- The digits of the 41 group chains sum to the total cost. -/
theorem sum_group_digits (I : Index) :
    ∑ k ∈ Finset.range 41, digitN I (k + 1) = gsum I := by
  have hu : ∀ u ∈ Finset.range 13, cost u (field u I) =
      ∑ i ∈ Finset.range (shK (ushape u)), (tup u (field u I)).getD i 0 := by
    intro u hu
    have hv := field_lt' (Finset.mem_range.mp hu) I
    rw [← tup_sum hv, ← sum_range_getD, tup_length hv]
  rw [gsum, Finset.sum_congr rfl hu, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun k => ⟨unitOf (k + 1), coordOf (k + 1)⟩)
    (fun x => chainAt x.1 x.2 - 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have := chain_facts k (Finset.mem_range.mp hk)
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨this.1, this.2.1⟩
  · rintro ⟨u, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have := unit_facts u hx.1 i hx.2
    simp only [Finset.mem_range]
    omega
  · intro k hk
    have := chain_facts k (Finset.mem_range.mp hk)
    simp only [this.2.2, Nat.add_sub_cancel]
  · rintro ⟨u, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have := unit_facts u hx.1 i hx.2
    simp only [Nat.sub_add_cancel this.1, this.2.2.1, this.2.2.2]
  · intro k _
    simp only [digitN, Nat.add_one_ne_zero, if_false]

/-! ## The parameters -/

/-- The 128-bit word of the field constant `g ^ e`: the cell `ofK (gpow e)` as `BLAKE2S` reads
it. -/
def gword (e : ℕ) : Word := LeanIsa.cellBits (ofK (gpow e))

/-- Tag symbol `d < 9`: the cost constant `C_d = g ^ (67 d)`. -/
def sym (d : ℕ) : Word := gword (1152921504606846976 * d)

/-- The frame exponent of root call `r` (the machine's frame constant `F_r`). -/
def rootExp (r : ℕ) : ℕ := (r + 1) * 1152921504606846976

/-- Positions of chain `k`. -/
def len (k : Fin numChains) : ℕ := lenN k

/-- The accepted layer. -/
def layer : ℕ := 85

/-- Digit of chain `k`. -/
def digit (I : Index) (k : Fin numChains) : ℕ := digitN I k

/-- Tag cells `A, B, C` of the step of chain `k` at position `j`: the base-9 digits of
`off k + j`. -/
def tag (k : Fin numChains) (j : ℕ) : Fin 3 → Word :=
  ![sym ((off k + j) % 9), sym ((off k + j) / 9 % 9), sym ((off k + j) / 81)]

/-- The constant cv pair `(cv₀, cv₁) = (1, g)` (the machine's adjacent `ONE, G` cells). -/
def cv : BitVec 256 := gword 1 ++ gword 0

/-- Metadata of chain steps: `ONE`. -/
def chainMd : Word := gword 0

/-- Metadata of the index query: `G`. -/
def idxMd : Word := gword 1

/-- Metadata of root call `r`: the frame constant `F_r`. -/
def rootMd (r : ℕ) : Word := gword (rootExp r)

/-- The GROUP-3 parameters. -/
def params : Params where
  len := len
  layer := layer
  digit := digit
  tag := tag
  cv := cv
  chainMd := chainMd
  idxMd := idxMd
  rootMd := rootMd
  hiTop := fun k => decide (k.val ∈ [1, 19, 25, 34, 12, 16, 23, 33, 8])

/-- The HL-GROUP-3 scheme. -/
def scheme : OracleAlgorithm.Scheme := params.scheme


/-! ## Field-constant words -/

theorem gword_eq (e : ℕ) : gword e = (0 : BitVec 64) ++ (gpow e : K) := by
  unfold gword LeanIsa.cellBits
  rw [limb_ofK, limb_ofK]
  simp

/-- Words of distinct `g`-powers below the group order are distinct. -/
theorem gword_inj {a b : ℕ} (ha : a < 18446744073709551615) (hb : b < 18446744073709551615)
    (h : gword a = gword b) : a = b := by
  rw [gword_eq, gword_eq] at h
  have h' : (gpow a : K) = gpow b := by
    simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (64 + 64) => z.extractLsb' 0 64) h
  exact OptimalOTS.GenFast.gpow_injOn (Set.mem_Iio.mpr (by norm_num; omega)) (Set.mem_Iio.mpr (by norm_num; omega)) h'

theorem sym_inj {a b : ℕ} (ha : a < 9) (hb : b < 9) (h : sym a = sym b) : a = b := by
  have := gword_inj (by omega) (by omega) h
  omega

theorem chainMd_ne : params.chainMd ≠ params.idxMd := by
  intro h
  have := gword_inj (a := 0) (b := 1) (by norm_num) (by norm_num) h
  omega

theorem rootMd_ne : ∀ r < 9, params.rootMd r ≠ params.idxMd := by
  intro r hr h
  have := gword_inj (a := rootExp r) (b := 1) (by unfold rootExp; omega) (by norm_num) h
  unfold rootExp at this
  omega

theorem chainMd_ne_root : ∀ r < 9, params.chainMd ≠ params.rootMd r := by
  intro r hr h
  have := gword_inj (a := 0) (b := rootExp r) (by norm_num) (by unfold rootExp; omega) h
  unfold rootExp at this
  omega

theorem rootMd_inj : ∀ r s, r < 9 → s < 9 → params.rootMd r = params.rootMd s → r = s := by
  intro r s hr hs h
  have := gword_inj (a := rootExp r) (b := rootExp s) (by unfold rootExp; omega)
    (by unfold rootExp; omega) h
  unfold rootExp at this
  omega

/-! ## Digits: bounds, injectivity, acceptance -/

theorem digit_lt (I : Index) (k : Fin numChains) : digit I k < len k := by
  unfold digit len digitN lenN
  by_cases hk : k.val = 0
  · rw [if_pos hk, if_pos hk]
    unfold freeD freeDigit
    split_ifs <;> omega
  · rw [if_neg hk, if_neg hk]
    have hf := chain_facts (k.val - 1) (by have : k.val < 42 := k.isLt; omega)
    rw [Nat.sub_add_cancel (by omega)] at hf
    exact tupS_lt (ushape_lt _) (field_lt' hf.1 I) hf.2.1

theorem tup_eq_of_getD {u : ℕ} {a b : ℕ} (ha : a < 2 ^ shB (ushape u))
    (hb : b < 2 ^ shB (ushape u))
    (h : ∀ i < shK (ushape u), (tup u a).getD i 0 = (tup u b).getD i 0) : tup u a = tup u b := by
  have la := tupS_length (ushape_lt u) ha
  have lb := tupS_length (ushape_lt u) hb
  apply List.ext_getElem (by unfold tup; rw [la, lb])
  intro i hi hi'
  have := h i (by unfold tup at hi; rwa [la] at hi)
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi', Option.getD_some, Option.getD_some] at this

/-- Equal digits give equal tuples in every unit. -/
theorem tup_eq_of_digit {I I' : Index} (h : digit I' = digit I) {u : ℕ} (hu : u < 13) :
    tup u (field u I') = tup u (field u I) := by
  refine tup_eq_of_getD (field_lt' hu I') (field_lt' hu I) fun i hi => ?_
  obtain ⟨h1, h2, h3, h4⟩ := unit_facts u hu i hi
  have := congrFun h ⟨chainAt u i, h2⟩
  simp only [digit, digitN, if_neg (show chainAt u i ≠ 0 by omega), h3, h4] at this
  exact this

theorem sum_digits (I : Index) :
    ∑ k : Fin numChains, digit I k = freeD I + gsum I := by
  change ∑ k : Fin 42, digitN I k.val = _
  rw [Fin.sum_univ_eq_sum_range (fun k => digitN I k) 42, Finset.sum_range_succ',
    sum_group_digits]
  simp only [digitN, ↓reduceIte]
  omega

/-- **Acceptance** is a window on the total cost. -/
theorem accepted_iff (I : Index) :
    params.Accepted I ↔ ¬ dummy I ∧ 22 ≤ gsum I ∧ gsum I < 86 := by
  change ∑ k : Fin numChains, digit I k = 85 ↔ _
  rw [sum_digits]
  unfold freeD freeDigit
  by_cases hd : dummy I
  · rw [if_pos hd]
    simp only [hd, not_true_eq_false, false_and, iff_false]
    split_ifs <;> omega
  · rw [if_neg hd]
    simp only [hd, not_false_eq_true, true_and]
    split_ifs <;> omega

/-! ## Field tuples -/

/-- The digit function of a field tuple, extended by zero. -/
def digitFun (c : (u : Fin 13) → Fin (2 ^ ubits u)) (u : ℕ) : ℕ :=
  if h : u < 13 then (c ⟨u, h⟩).val else 0

theorem digitFun_lt (c : (u : Fin 13) → Fin (2 ^ ubits u)) (u : ℕ) :
    digitFun c u < 2 ^ ubits u := by
  unfold digitFun
  split_ifs with h
  · exact (c ⟨u, h⟩).isLt
  · positivity

/-- The index with the given group fields. -/
def indexOf (c : (u : Fin 13) → Fin (2 ^ ubits u)) : Index :=
  BitVec.ofNat 127 (ofDigitsW ubits (digitFun c) 13)

theorem indexOf_toNat (c : (u : Fin 13) → Fin (2 ^ ubits u)) :
    (indexOf c).toNat = ofDigitsW ubits (digitFun c) 13 := by
  have h := ofDigitsW_lt ubits (digitFun c) (digitFun_lt c) 13
  rw [posW_13] at h
  rw [indexOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem field_indexOf (c : (u : Fin 13) → Fin (2 ^ ubits u)) (u : Fin 13) :
    field u (indexOf c) = (c u).val := by
  rw [field, indexOf_toNat, digitW_ofDigitsW ubits _ (digitFun_lt c) 13 u u.isLt, digitFun,
    dif_pos u.isLt]

/-- An index is the index of its fields. -/
theorem indexOf_fields (I : Index) : indexOf (fun u => ⟨field u I, field_lt u I⟩) = I := by
  apply BitVec.eq_of_toNat_eq
  rw [indexOf_toNat]
  have hI : I.toNat < 2 ^ posW ubits 13 := by rw [posW_13]; exact I.isLt
  conv_rhs => rw [← ofDigitsW_digitW ubits I.toNat 13 hI]
  unfold ofDigitsW
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [digitFun, dif_pos (Finset.mem_range.mp hu)]
  rfl

theorem gsum_eq (I : Index) : gsum I = ∑ u : Fin 13, cost u (field u I) :=
  (Fin.sum_univ_eq_sum_range (fun u => cost u (field u I)) 13).symm

theorem cut_le : ∀ u < 13, cut u ≤ 2 ^ ubits u := by decide

theorem cut_le' {u : ℕ} (hu : u < 13) : cut u ≤ 2 ^ shB (ushape u) := by
  rw [← ubits_eq hu]; exact cut_le u hu

theorem not_dummy_iff (I : Index) : ¬ dummy I ↔ ∀ u < 13, field u I < cut u := by
  simp only [dummy, not_exists, not_and, not_le]

/-! ## Classes and their weights

A class is the digit vector of an accepted index. Two accepted indices have the same digits
exactly when their fields are aliases, so the accepted indices of a class number the product of
the field multiplicities (`weight_eq`). -/

/-- The multiplicity of entry `v` of unit `u`: the number of its aliases. -/
def mult (u v : ℕ) : ℕ := multS (ushape u) v

/-- The product of the multiplicities of the fields of `I`. -/
def wprod (I : Index) : ℕ := ∏ u : Fin 13, mult u (field u I)

/-- The aliases of field `u` of `I`. -/
def aliases (I : Index) (u : Fin 13) : Finset (Fin (2 ^ ubits u)) :=
  Finset.univ.filter fun x => lead (ushape u) (field u I) ≤ x.val ∧
    x.val < lead (ushape u) (field u I) + mult u (field u I)

theorem cost_live {u v : ℕ} (_ : v < cut u) : cost u v = band (ushape u) v := rfl

theorem card_aliases {I : Index} {u : Fin 13} (hl : field u I < cut u) :
    (aliases I u).card = mult u (field u I) := by
  have hs := ushape_lt u
  have hle := lead_add_le hs hl
  have hcut := cut_le u u.isLt
  unfold mult at hle ⊢
  unfold cut at hl hcut
  have hI : (Finset.Ico (lead (ushape u) (field u I)) (lead (ushape u) (field u I) +
      multS (ushape u) (field u I))).card =
      multS (ushape u) (field u I) := by simp
  rw [← hI]
  refine Finset.card_bij' (fun x _ => x.val) (fun y hy => ⟨y, by
      rw [Finset.mem_Ico] at hy; omega⟩) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hx).2
  · intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_Ico.mp hy⟩
  · intro x _; rfl
  · intro y _; rfl

/-- Accepted indices with the same digits as an accepted `I` are exactly the indices whose fields
are aliases of `I`'s. -/
theorem same_digits_iff {I : Index} (hI : params.Accepted I) (I' : Index) :
    (params.Accepted I' ∧ params.digit I' = params.digit I) ↔ ∀ u : Fin 13,
      lead (ushape u) (field u I) ≤ field u I' ∧
        field u I' < lead (ushape u) (field u I) + mult u (field u I) := by
  have hlI := (not_dummy_iff I).mp ((accepted_iff I).mp hI).1
  constructor
  · rintro ⟨hI', hd⟩ u
    have hl' := (not_dummy_iff I').mp ((accepted_iff I').mp hI').1
    have ht := tup_eq_of_digit hd u.isLt
    have := (tupS_eq_iff (ushape_lt u) (hlI u u.isLt) (hl' u u.isLt)).mp ht
    exact this
  · intro h
    have hl' : ∀ u < 13, field u I' < cut u := by
      intro u hu
      have hh := h ⟨u, hu⟩
      simp only at hh
      have := lead_add_le (ushape_lt u) (hlI u hu)
      unfold mult at hh
      unfold cut; omega
    have ht : ∀ u < 13, tup u (field u I') = tup u (field u I) := by
      intro u hu
      have hh := h ⟨u, hu⟩
      simp only at hh
      unfold mult at hh
      exact (tupS_eq_iff (ushape_lt u) (hlI u hu) (hl' u hu)).mpr hh
    have hc : ∀ u < 13, cost u (field u I') = cost u (field u I) := by
      intro u hu
      rw [← tup_sum (field_lt' hu I'), ← tup_sum (field_lt' hu I), ht u hu]
    have hg : gsum I' = gsum I := by
      rw [gsum_eq, gsum_eq]
      exact Finset.sum_congr rfl fun u _ => hc u u.isLt
    have hacc := (accepted_iff I).mp hI
    have hnd' := (not_dummy_iff I').mpr hl'
    refine ⟨(accepted_iff I').mpr ⟨hnd', hg ▸ hacc.2⟩, ?_⟩
    funext k
    change digitN I' k = digitN I k
    unfold digitN
    split_ifs with hk
    · unfold freeD; rw [if_neg hnd', if_neg hacc.1, hg]
    · have hf := chain_facts (k.val - 1) (by have : k.val < 42 := k.isLt; omega)
      rw [Nat.sub_add_cancel (by omega)] at hf
      rw [ht _ hf.1]

/-- **The weight of an accepted index** is the product of its field multiplicities. -/
theorem weight_eq {I : Index} (hI : params.Accepted I) : params.weight I = wprod I := by
  have hlI := (not_dummy_iff I).mp ((accepted_iff I).mp hI).1
  unfold Params.weight wprod
  rw [← Finset.prod_congr rfl fun (u : Fin 13) _ => card_aliases (hlI u.val u.isLt),
    ← Fintype.card_piFinset]
  refine Finset.card_bij' (fun I' _ => fun u => ⟨field u I', field_lt u I'⟩)
    (fun c _ => indexOf c) ?_ ?_ ?_ ?_
  · intro I' hI'
    rw [Finset.mem_filter] at hI'
    have := (same_digits_iff hI I').mp hI'.2
    simp only [Fintype.mem_piFinset, aliases, Finset.mem_filter, Finset.mem_univ, true_and]
    exact this
  · intro c hc
    simp only [Fintype.mem_piFinset, aliases, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (same_digits_iff hI (indexOf c)).mpr fun u => ?_⟩
    rw [field_indexOf]; exact hc u
  · intro I' _; exact indexOf_fields I'
  · intro c _
    funext u
    exact Fin.ext (field_indexOf c u)

/-! ## Interface for the machine -/

/-- The bit positions of the group fields (`POS`), and `128` past the last one. -/
theorem posW_eq : ∀ u < 14, posW ubits u =
    [0, 9, 18, 27, 36, 45, 57, 68, 78, 88, 98, 108, 117, 127].getD u 0 := by decide

theorem digit_free (I : Index) : digit I 0 = freeD I := by
  simp only [digit, digitN]; rfl

/-- The free digit of an index without dummy fields. -/
theorem digit_free_live {I : Index} (h : ∀ u < 13, field u I < cut u) :
    digit I 0 = freeDigit (gsum I) := by
  rw [digit_free, freeD, if_neg ((not_dummy_iff I).mpr h)]

theorem digit_group (I : Index) (k : Fin numChains) (hk : k.val ≠ 0) :
    digit I k = (tup (unitOf k) (field (unitOf k) I)).getD (coordOf k) 0 := by
  simp only [digit, digitN, if_neg hk]

/-- A live entry lies in the band of its cost. -/
theorem cost_spec {u v : ℕ} (hv : v < cut u) :
    AS (ushape u) (cost u v) ≤ v ∧ v < AS (ushape u) (cost u v + 1) := by
  rw [cost_live hv]
  exact ⟨(band_spec (ushape_lt u) hv).1, (band_spec (ushape_lt u) hv).2.1⟩

theorem cost_lt {u v : ℕ} (hv : v < cut u) : cost u v < 18 :=
  (band_spec (ushape_lt u) hv).2.2

theorem gword_zero : gword 0 = LeanIsa.cellBits (ofK 1) := by
  show LeanIsa.cellBits (ofK (g ^ 0)) = _; rw [pow_zero]

theorem gword_one : gword 1 = LeanIsa.cellBits (ofK g) := by
  show LeanIsa.cellBits (ofK (g ^ 1)) = _; rw [pow_one]

end FourChildCodec


end OptimalOTS.LeanIsaBaseline.Layer
