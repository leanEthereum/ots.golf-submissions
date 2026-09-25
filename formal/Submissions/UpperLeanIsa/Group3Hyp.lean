import Submissions.UpperLeanIsa.SchemeGroup3
import Submissions.UpperLeanIsa.BasicProperties

/-!
# Concrete admissibility hypotheses

The effective fields tile 127 bits and the tuples determine that index. Base-9 tags identify
all 655 chain steps. Chain, index, and seven root metadata values are distinct field powers.
The concrete budgets are 1326 key-generation compressions, at most 2^20 signing compressions,
and 210 verification compressions.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Group3

theorem tag_inj (k k' : Fin numChains) (j j' : ℕ) (hj : j + 1 < len k) (hj' : j' + 1 < len k')
    (h0 : tag k j 0 = tag k' j' 0) (h1 : tag k j 1 = tag k' j' 1)
    (h2 : tag k j 2 = tag k' j' 2) : k = k' ∧ j = j' := by
  unfold len at hj hj'
  obtain ⟨hp, hl⟩ := pos_facts k k.isLt j (by omega)
  obtain ⟨hp', hl'⟩ := pos_facts k' k'.isLt j' (by omega)
  simp only [tag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have e0 := sym_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h0
  have e1 := sym_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
  have e2 := sym_inj (by omega) (by omega) h2
  have hpp : off k + j = off k' + j' := by omega
  rw [hpp, hl'] at hl
  obtain ⟨hk, hjj⟩ := Prod.mk.inj hl
  exact ⟨Fin.ext hk.symm, hjj.symm⟩

theorem hyp : params.Hyp where
  len_pos := fun k => (Nat.zero_le _).trans_lt (digit_lt 0 k)
  digit_lt := digit_lt
  digit_inj := digit_inj
  layer_pos := by decide
  tag_inj := tag_inj
  chain_idx := chainMd_ne
  chain_root := chainMd_ne_root
  root_idx := rootMd_ne
  root_inj := rootMd_inj
  numValid_ge := numValid_ge
  numValid_le := by rw [numValid_eq]; norm_num
  keygen_le := by
    change 2 * (∑ k : Fin 42, (lenN k - 1)) + 16 ≤ 2 ^ 20
    rw [steps_eq]; norm_num
  verify_le := by change 18 + 2 * 96 ≤ 2 ^ 20; norm_num
  len_zero := by change 2 ≤ lenN 0; decide

/-- **Admissibility of HL-GROUP-3.** -/
theorem admissible : scheme.Admissible := params.admissible hyp

/-- Key generation of HL-GROUP-3 costs 1326 compressions on every path. -/
theorem keygen_cost : CostAtMost params.keygen 1326 := by
  have h := params.cost_keygen
  have e : (∑ k : Fin numChains, (params.len k - 1)) = 655 := steps_eq
  rwa [e] at h

/-- Verification of HL-GROUP-3 costs at most 210 compressions on every path. -/
theorem verify_cost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (params.verify pk m bits) 210 :=
  params.cost_verify pk m bits

end Group3

end OptimalOTS.LeanIsaBaseline.Layer
