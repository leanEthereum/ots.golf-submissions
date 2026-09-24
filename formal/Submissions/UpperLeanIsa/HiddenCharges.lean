import Submissions.UpperLeanIsa.Exposure

/-! Guessing a hidden chain input. Position tags ensure that a query can address
only one chain position, so the bound does not pay a factor for all chain nodes. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleSpec ENNReal
open scoped Classical
noncomputable section

attribute [local irreducible] hashBits publicFiber finiteFiber queryLocation Record.query

local instance : DecidableEq Record := Classical.decEq Record

def wordGuessRate : ℝ≥0∞ := (2 ^ 128)⁻¹

theorem wordGuessRate_eq : wordGuessRate = secondPreimageRate * 2 := by
  unfold wordGuessRate secondPreimageRate
  rw [show (2 : ℝ≥0∞) ^ 129 = 2 ^ 128 * 2 by rw [← pow_succ],
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp)), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

theorem uniform_low_rate :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (2 ^ 128 : ℕ) = wordGuessRate := by
  rw [Fintype.card_bitVec, show hashBits = 256 by unfold hashBits; rfl]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  unfold wordGuessRate
  rw [show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add],
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

private theorem word_putSource_zero (ξ : Record) (i : Fin 39) (x : Word) :
    (ξ.putSource i x).word i 0 = x := by
  simp only [Record.word, Fin.val_zero, dite_true, Record.putSource, Function.update_self]

private theorem word_putAnswer_prev (ξ : Record) (i : Fin 39) (j : Fin 128)
    (hj : j.val ≠ 0) (x : BitVec hashBits) :
    (ξ.putAnswer (.inl (i, ⟨j.val - 1, by have := j.isLt; omega⟩)) x).word i j =
      x.setWidth 128 := by
  simp only [Record.word, dif_neg hj, Record.putAnswer, Function.update_self]
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.ushiftRight_zero]

/-- Every word strictly before the cut retains a uniform 128-bit marginal,
even after conditioning on the complete public data of that cut. -/
theorem hidden_word_charge (d : Cut) (v : PublicData) (i : Fin 39) (j : Fin 128)
    (hj : j.val < (d i).val) (x : Word) (w : ℝ≥0∞) :
    (∑ ξ ∈ publicFiber d v, if ξ.word i j = x then w else 0) ≤
      wordGuessRate * ∑ _ξ ∈ publicFiber d v, w := by
  rw [Finset.mul_sum]
  by_cases hz : j.val = 0
  · have he : j = 0 := Fin.ext hz
    subst j
    have hi : 0 < (d i).val := hj
    rw [sum_resample (fun ξ : Record => ξ.1 i) (fun ξ y => ξ.putSource i y)
      (fun ξ y => putSource_get ξ i y) (fun ξ y => putSource_restore ξ i y)
      (publicFiber d v) (fiber_closed_source d v i hi)]
    apply Finset.sum_le_sum
    intro ξ _
    simp only [word_putSource_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ x)]
    exact le_of_eq (by rw [Fintype.card_bitVec]; simp only [Nat.cast_pow, Nat.cast_ofNat]; rfl)
  · let p : Fin 127 := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hp : p.val + 1 < (d i).val := by dsimp [p]; omega
    rw [sum_resample (fun ξ : Record => ξ.2 (.inl (i, p)))
      (fun ξ y => ξ.putAnswer (.inl (i, p)) y)
      (fun ξ y => putAnswer_get ξ (.inl (i, p)) y)
      (fun ξ y => putAnswer_restore ξ (.inl (i, p)) y)
      (publicFiber d v) (fiber_closed_answer d v i p hp)]
    apply Finset.sum_le_sum
    intro ξ _
    have he (y : BitVec hashBits) :
        (ξ.putAnswer (.inl (i, p)) y).word i j = y.setWidth 128 :=
      word_putAnswer_prev ξ i j hz y
    simp only [he]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc := card_filter_low_le hashBits 128 (by unfold hashBits; omega) x
    rw [show hashBits - 128 = 128 by unfold hashBits; rfl] at hc
    calc
      _ ≤ (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) * w) :=
        mul_le_mul' le_rfl (mul_le_mul' (Nat.cast_le.mpr hc) le_rfl)
      _ = wordGuessRate * w := by rw [← mul_assoc, uniform_low_rate]

theorem record_chain_query_eq_iff (ξ ζ : Record) (i : Fin 39) (j : Fin 127) :
    ξ.query (.inl (i, j)) = ζ.query (.inl (i, j)) ↔
      ξ.word i j.castSucc = ζ.word i j.castSucc := by
  constructor
  · intro h
    unfold Record.query at h
    have hi : ξ.input (.inl (i, j)) = ζ.input (.inl (i, j)) :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact (chainInput_eq_iff i i j j _ _).mp hi |>.2.2
  · intro h
    unfold Record.query
    apply congrArg (fun x : BitVec 896 => (⟨896, x⟩ : Query))
    exact congrArg (chainInput i.val j.val) h

theorem hiddenCache_isSome_iff (d : Cut) (ξ : Record) (q : Query) :
    (hiddenCache d ξ q).isSome ↔ ∃ a, Hidden d a ∧ ξ.query a = q := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨a, ha, hq, _⟩ := (hiddenCache_some_iff d ξ q u).mp hu
    exact ⟨a, ha, hq⟩
  · rintro ⟨a, ha, hq⟩
    exact ⟨ξ.2 a, (hiddenCache_some_iff d ξ q _).mpr ⟨a, ha, hq, rfl⟩⟩

/-- Per-query guessing charge, including the two-compression price of a tagged input. -/
theorem hidden_input_charge (d : Cut) (v : PublicData) (q : Query) (w : ℝ≥0∞) :
    (∑ ξ ∈ publicFiber d v, if (hiddenCache d ξ q).isSome then w else 0) ≤
      secondPreimageRate * queryCost (.inr q) * ∑ _ξ ∈ publicFiber d v, w := by
  classical
  by_cases hex : ∃ ζ : Record, ∃ a, Hidden d a ∧ ζ.query a = q
  · obtain ⟨ζ, a, ha, rfl⟩ := hex
    cases a with
    | inr i => exact ha.elim
    | inl a =>
      rcases a with ⟨i, j⟩
      have he (ξ : Record) : (hiddenCache d ξ (ζ.query (.inl (i, j)))).isSome ↔
          ξ.word i j.castSucc = ζ.word i j.castSucc := by
        rw [hiddenCache_isSome_iff]
        constructor
        · rintro ⟨b, _, hb⟩
          have he := location_eq_of_query_eq ξ ζ b (.inl (i, j)) hb
          subst b
          exact (record_chain_query_eq_iff ξ ζ i j).mp hb
        · intro h
          exact ⟨.inl (i, j), ha, (record_chain_query_eq_iff ξ ζ i j).mpr h⟩
      have hc : queryCost (.inr (ζ.query (.inl (i, j)))) = 2 := by
        norm_num [Record.query, queryCost, blockCost, blockBits]
      simp only [he, hc, Nat.cast_ofNat, ← wordGuessRate_eq]
      exact hidden_word_charge d v i j.castSucc ha (ζ.word i j.castSucc) w
  · have hn (ξ : Record) : ¬ (hiddenCache d ξ q).isSome := by
      intro h
      obtain ⟨a, ha, hq⟩ := (hiddenCache_isSome_iff d ξ q).mp h
      exact hex ⟨ξ, a, ha, hq⟩
    simp only [if_neg (hn _), Finset.sum_const_zero]
    exact bot_le

end
end OptimalOTS.LeanIsaBaseline
