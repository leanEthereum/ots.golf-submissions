import Submissions.UpperLeanIsa.LayerAvailability
import Submissions.UpperLeanIsa.LayerDigits
import Submissions.UpperLeanIsa.LayerCount

/-!
# FLAT-42: the HL-FLAT-A layer scheme

The instance of `LayerScheme` the HL-FLAT-A machine implements (model:
`leanisa-frontier/hlflat/hlflat_model.py`).

* **Chains.** 40 chains of 8 positions and 2 of 16 (310 steps); the digit of chain `k` is the
  bit field of the 128-bit index at `posW wid k` of width `wid k` (3 bits for `k < 40`, 4 for
  `k = 40, 41`): the 42 fields tile the index, so digits and index are in bijection.
* **Layer.** An index is accepted when its digits sum to `106`; there are exactly
  `N₁₀₆ = 69117521303608168194311003377855640` accepted indices (`numValid_eq`).
* **Tags.** Chain step `(k, j)` sits at position `p = off k + j < 310`; its tag cells are the
  symbols `sym (p % 7)`, `sym (p / 7 % 7)`, `sym (p / 49)` with `sym = 0, 1, 2, 4, 8, 16, 32`.
  The constant cv pair is `(0, 1)` (the machine's adjacent `Z, ONE` cells). Metadata: chain steps
  `1`, index `10`, root calls `0, 2, 4, …, 128, 5504, 3`. All tag symbols and metadata values are
  constants the machine already holds: `Z`, `ONE`, the powers `g ^ 1 … g ^ 7`, the checked length
  cell and one extra constant `3`.
* **Availability.** Signing fails with probability at most `2 ^ -128` for every message chosen
  from the public key (`signingFailure`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Flat

/-- Digit widths: 40 three-bit fields, then 2 four-bit fields. -/
def wid (k : ℕ) : ℕ := if k < 40 then 3 else if k < 42 then 4 else 0

/-- Positions of chain `k`: 8 or 16. -/
def len (k : Fin numChains) : ℕ := 2 ^ wid k

/-- The accepted layer. -/
def layer : ℕ := 106

/-- Digit `k` of the index: its bit field at `posW wid k`. -/
def digit (I : Word) (k : Fin numChains) : ℕ := digitW wid I.toNat k

/-- First step position of chain `k` (chains of 7 steps, then two of 15). -/
def off (k : ℕ) : ℕ := if k < 40 then 7 * k else 280 + 15 * (k - 40)

/-- The symbol `v < 7`: `0, 1, 2, 4, 8, 16, 32`. -/
def sym (v : ℕ) : Word := BitVec.ofNat 128 (if v = 0 then 0 else 2 ^ (v - 1))

/-- Tag cells `A, B, C` of the step of chain `k` at position `j`. -/
def tag (k : Fin numChains) (j : ℕ) : Fin 3 → Word :=
  ![sym ((off k + j) % 7), sym ((off k + j) / 7 % 7), sym ((off k + j) / 49)]

/-- The constant cv pair `(cv₀, cv₁) = (0, 1)`. -/
def cv : BitVec 256 := BitVec.ofNat 256 (2 ^ 128)

/-- Metadata of chain steps (`ONE`). -/
def chainMd : Word := 1

/-- Metadata of the index query. -/
def idxMd : Word := 10

/-- Metadata of root call `r`: `0, 2, 4, 8, 16, 32, 64, 128, 5504, 3`. -/
def rootMd (r : ℕ) : Word :=
  BitVec.ofNat 128 (if r = 0 then 0 else if r < 8 then 2 ^ r else if r = 8 then 5504 else 3)

/-- The FLAT-42 parameters. -/
def params : Params where
  len := len
  layer := layer
  digit := digit
  tag := tag
  cv := cv
  chainMd := chainMd
  idxMd := idxMd
  rootMd := rootMd

/-- The HL-FLAT-A scheme. -/
def scheme : OracleAlgorithm.Scheme := params.scheme

/-! ## Basic facts -/

theorem digit_lt (I : Word) (k : Fin numChains) : digit I k < len k := digitW_lt wid _ _

theorem pos_42 : posW wid 42 = 128 := by decide

theorem chainMd_ne : params.chainMd ≠ params.idxMd := by decide

theorem rootMd_ne : ∀ r < 10, params.rootMd r ≠ params.idxMd := by
  intro r hr
  interval_cases r <;> decide

/-! ## Counting the accepted indices -/

/-- Accepted digit tuples. -/
def tuples : Finset ((k : Fin numChains) → Fin (2 ^ wid k)) :=
  Finset.univ.filter fun c => ∑ k, (c k).val = layer

theorem tuples_card : tuples.card = compW wid 42 layer := card_compW wid 42 layer

/-- The digit function of a tuple, extended by zero. -/
def digitFun (c : (k : Fin numChains) → Fin (2 ^ wid k)) (k : ℕ) : ℕ :=
  if h : k < 42 then (c ⟨k, h⟩).val else 0

theorem digitFun_lt (c : (k : Fin numChains) → Fin (2 ^ wid k)) (k : ℕ) :
    digitFun c k < 2 ^ wid k := by
  unfold digitFun
  split_ifs with h
  · exact (c ⟨k, h⟩).isLt
  · positivity

/-- The index with the given digits. -/
def indexOf (c : (k : Fin numChains) → Fin (2 ^ wid k)) : Word :=
  BitVec.ofNat 128 (ofDigitsW wid (digitFun c) 42)

theorem indexOf_toNat (c : (k : Fin numChains) → Fin (2 ^ wid k)) :
    (indexOf c).toNat = ofDigitsW wid (digitFun c) 42 := by
  have h := ofDigitsW_lt wid (digitFun c) (digitFun_lt c) 42
  rw [pos_42] at h
  rw [indexOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem digit_indexOf (c : (k : Fin numChains) → Fin (2 ^ wid k)) (k : Fin numChains) :
    digit (indexOf c) k = (c k).val := by
  rw [digit, indexOf_toNat, digitW_ofDigitsW wid _ (digitFun_lt c) 42 k k.isLt, digitFun,
    dif_pos k.isLt]

attribute [local irreducible] tuples

theorem card_accepted : params.numValid = compW wid 42 layer := by
  rw [← tuples_card, Params.numValid]
  refine Finset.card_bij' (fun I _ => fun k => ⟨digit I k, digitW_lt wid _ _⟩)
    (fun c _ => indexOf c) ?_ ?_ ?_ ?_
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
    simp only [tuples, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hI
  · intro c hc
    simp only [tuples, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change ∑ k, digit (indexOf c) k = layer
    rw [← hc]
    exact Finset.sum_congr rfl fun k _ => digit_indexOf c k
  · intro I _
    apply BitVec.eq_of_toNat_eq
    rw [indexOf_toNat]
    have agree : ∀ k ∈ Finset.range 42,
        digitFun (fun k : Fin numChains => (⟨digit I k, digitW_lt wid _ _⟩ : Fin (2 ^ wid k))) k *
          2 ^ posW wid k = digitW wid I.toNat k * 2 ^ posW wid k := by
      intro k hk
      rw [digitFun, dif_pos (Finset.mem_range.mp hk)]
      rfl
    unfold ofDigitsW
    rw [Finset.sum_congr rfl agree]
    have hI : I.toNat < 2 ^ posW wid 42 := by rw [pos_42]; exact I.isLt
    exact ofDigitsW_digitW wid I.toNat 42 hI
  · intro c _
    funext k
    apply Fin.ext
    exact digit_indexOf c k

/-- `N₁₀₆`, by kernel evaluation of the partial-sum table. -/
theorem compW_layer : compW wid 42 layer = 69117521303608168194311003377855640 := by
  rw [← compTableW_getD wid layer 42 layer le_rfl]
  decide +kernel

/-- The exact number of accepted indices. -/
theorem numValid_eq : params.numValid = 69117521303608168194311003377855640 := by
  rw [card_accepted, compW_layer]

/-- Layer 105 is not enough: `N₁₀₅ < 200 · 2 ^ 108` (the availability threshold used here). -/
theorem compW_105 : compW wid 42 105 < 200 * 2 ^ 108 := by
  rw [← compTableW_getD wid 105 42 105 le_rfl]
  decide +kernel

/-! ## Availability -/

theorem numValid_ge : 200 * 2 ^ 108 ≤ params.numValid := by
  rw [numValid_eq]; norm_num

/-- **Signing availability of HL-FLAT-A.** -/
theorem signingFailure : scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) :=
  params.signingFailure chainMd_ne rootMd_ne numValid_ge

end Flat

end OptimalOTS.LeanIsaBaseline.Layer
