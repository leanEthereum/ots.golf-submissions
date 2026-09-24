import Submissions.UpperLeanIsa.SchemeFlat
import Submissions.UpperLeanIsa.BasicProperties

/-!
# FLAT-42 satisfies the standing hypotheses

`Flat.hyp : Flat.params.Hyp`: the digit fields tile the index (digits determine the index), the
tag symbols `3 + p % 7, 3 + p / 7 % 7, 3 + p / 49` determine the step position `p = off k + j`
and hence `(k, j)`, and the metadata values `1` (chains), `10` (index) and `0, 2, …, 9, 5504`
(root calls) are pairwise distinct. Hence `Flat.admissible`, with the concrete budgets
`keygen 640`, `sign 2 ^ 20` and `verify 234`.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Flat

theorem len_eq (k : Fin numChains) : len k = if k.val < 40 then 8 else 16 := by
  have hk := k.isLt
  unfold len wid
  by_cases h : k.val < 40
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_pos (show k.val < 42 by omega), if_neg h]; rfl

theorem digit_inj (I I' : Word) (h : ∀ k, digit I k = digit I' k) : I = I' := by
  apply BitVec.eq_of_toNat_eq
  have hI : I.toNat < 2 ^ posW wid 42 := by rw [pos_42]; exact I.isLt
  have hI' : I'.toNat < 2 ^ posW wid 42 := by rw [pos_42]; exact I'.isLt
  rw [← ofDigitsW_digitW wid I.toNat 42 hI, ← ofDigitsW_digitW wid I'.toNat 42 hI']
  unfold ofDigitsW
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have := h ⟨k, hk'⟩
  unfold digit at this
  rw [this]

theorem sym_inj {a b : ℕ} (ha : a < 7) (hb : b < 7) (h : sym a = sym b) : a = b := by
  have hn := congrArg BitVec.toNat h
  unfold sym at hn
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at hn
  omega

theorem tag_inj (k k' : Fin numChains) (j j' : ℕ) (hj : j + 1 < len k) (hj' : j' + 1 < len k')
    (h0 : tag k j 0 = tag k' j' 0) (h1 : tag k j 1 = tag k' j' 1)
    (h2 : tag k j 2 = tag k' j' 2) : k = k' ∧ j = j' := by
  rw [len_eq] at hj hj'
  have hk : k.val < 42 := k.isLt
  have hk' : k'.val < 42 := k'.isLt
  have hp : off k + j < 343 := by unfold off; split_ifs at hj ⊢ <;> omega
  have hp' : off k' + j' < 343 := by unfold off; split_ifs at hj' ⊢ <;> omega
  simp only [tag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have e0 := sym_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h0
  have e1 := sym_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
  have e2 := sym_inj (by omega) (by omega) h2
  have hpp : off k + j = off k' + j' := by omega
  unfold off at hpp
  have hkk : k.val = k'.val ∧ j = j' := by split_ifs at hpp hj hj' <;> omega
  exact ⟨Fin.ext hkk.1, hkk.2⟩

theorem rootMd_toNat (r : ℕ) (hr : r < 10) :
    (rootMd r).toNat = if r = 0 then 0 else if r = 1 then 2 else if r < 9 then r + 1 else 5504 := by
  unfold rootMd
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  split_ifs <;> omega

theorem hyp : params.Hyp where
  len_pos := fun k => Nat.one_le_two_pow
  digit_lt := digit_lt
  digit_inj := digit_inj
  layer_pos := by decide
  tag_inj := tag_inj
  chain_idx := chainMd_ne
  chain_root := by
    intro r hr h
    have hn := congrArg BitVec.toNat h
    change (chainMd).toNat = (rootMd r).toNat at hn
    rw [rootMd_toNat r hr] at hn
    have h1 : (chainMd).toNat = 1 := rfl
    rw [h1] at hn
    split_ifs at hn <;> omega
  root_idx := rootMd_ne
  root_inj := by
    intro r s hr hs h
    have hn := congrArg BitVec.toNat h
    change (rootMd r).toNat = (rootMd s).toNat at hn
    rw [rootMd_toNat r hr, rootMd_toNat s hs] at hn
    split_ifs at hn <;> omega
  numValid_ge := numValid_ge
  numValid_le := by rw [numValid_eq]; norm_num
  keygen_le := by
    have : (∑ k : Fin numChains, (params.len k - 1)) = 310 := by
      change (∑ k : Fin numChains, (len k - 1)) = 310
      simp only [len_eq]
      decide
    rw [this]; norm_num
  verify_le := by change 22 + 2 * 106 ≤ 2 ^ 20; norm_num
  len_zero := by change 2 ≤ len 0; rw [len_eq]; decide

/-- **Admissibility of HL-FLAT-A.** -/
theorem admissible : scheme.Admissible := params.admissible hyp

/-- Key generation of HL-FLAT-A costs 640 compressions on every path. -/
theorem keygen_cost : CostAtMost params.keygen 640 := by
  have h := params.cost_keygen
  have : (∑ k : Fin numChains, (params.len k - 1)) = 310 := by
    change (∑ k : Fin numChains, (len k - 1)) = 310
    simp only [len_eq]
    decide
  rwa [this] at h

/-- Verification of HL-FLAT-A costs at most 234 compressions on every path. -/
theorem verify_cost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (params.verify pk m bits) 234 :=
  params.cost_verify pk m bits

end Flat

end OptimalOTS.LeanIsaBaseline.Layer
