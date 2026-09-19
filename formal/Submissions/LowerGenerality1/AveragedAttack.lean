import Submissions.LowerGenerality1.PatternAttack
import Submissions.LowerGenerality1.AveragedSearch

/-! Retain all reconstruction-pattern classes in the signature-conversion attack. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.AveragedAttack

open OptimalOTS.Dag

open PatternAttack

theorem forgeFrom_success_ge (S : Scheme) (i : Fin numCuts)
    (x : S.graph.Assignment) (c : Cache)
    (hc : S.graph.CacheConsistent x c)
    (D : Finset Query) (hD : BareLower.HasSupport c D) (hcardD : D.card ≤ 2 ^ 22)
    (m₁ : Message) :
    (99 / 100 : ℝ≥0∞) * AveragedSearch.hitRate (S.samePattern i).card ≤ E (run
      (forgeFrom S (2 ^ 122) i
        (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x))
        (Conversion.observed S i x) m₁ >>= check S (S.publicKey x) m₁) c) win := by
  unfold forgeFrom
  rw [bind_assoc, run_bind, E_bind, sampleBits, run_liftM, E_map]
  have hmass := BareLower.fresh_new_mass_paper_99 hD hcardD m₁
  refine le_trans ?_ (BareLower.expectedValue_ge_indicator ($ᵗ BitVec msgBits)
    (fun m₂ => BareLower.FreshMessage c m₂ ∧ m₂ ≠ m₁) _ (AveragedSearch.hitRate (S.samePattern i).card) ?_)
  · refine (mul_le_mul_left hmass (AveragedSearch.hitRate (S.samePattern i).card)).trans ?_
    apply mul_le_mul_left
    apply E_mono
    intro m
    split_ifs <;> simp_all
  · intro m₂ _ hm₂
    dsimp only
    rw [if_neg hm₂.2, bind_map_left, run_bind, E_bind]
    have hG : ∀ n ∈ targets S i, n < 2 ^ 128 := by
      intro n hn
      obtain ⟨j,rfl,_⟩ := mem_targets S i n hn
      have hj := j.isLt
      change j.val < 2 ^ 115 at hj
      exact hj.trans (by norm_num)
    have hh := AveragedSearch.paper_success_ge (targets S i) hG m₂ c hm₂.1
    rw [card_targets] at hh
    exact hh.trans (search_check_ge S _ i x m₁ m₂ hm₂.2 c hc)

theorem forge_success_ge (S : Scheme) (i : Fin numCuts)
    (x : S.graph.Assignment) (c : Cache)
    (hc : S.graph.CacheConsistent x c)
    (D : Finset Query) (hD : BareLower.HasSupport c D) (hcardD : D.card ≤ 2 ^ 22)
    (m₁ : Message) (η₁ : Nonce)
    (w : BitVec hashBits)
    (hw : c ⟨msgBits + nonceBits,m₁ ++ η₁⟩ = some w)
    (hidx : (w.setWidth idxBits).toNat = i.val) :
    (99 / 100 : ℝ≥0∞) * AveragedSearch.hitRate (S.samePattern i).card ≤ E (run
      (forge S (2 ^ 122) m₁ (some (η₁,S.graph.encode (S.sets i) x)) >>=
        check S (S.publicKey x) m₁) c) win := by
  unfold forge
  rw [bind_assoc, run_bind, Conversion.run_index_cached m₁ η₁ c w hw, E_bind, E_pure]
  dsimp only
  generalize (w.setWidth idxBits).toNat = n at hidx ⊢
  subst hidx
  rw [dif_pos i.isLt]
  simp only [Fin.eta, bind_assoc]
  rw [run_bind, Conversion.run_honest_reconstruct S i x c hc, E_bind, E_pure]
  exact forgeFrom_success_ge S i x c hc D hD hcardD m₁

end OptimalOTS.AveragedAttack
