import Submissions.UpperLeanIsa.StageA
import Submissions.UpperLeanIsa.CostPrefix

/-!
# Strong unforgeability of a layer scheme

For every adversary `A` whose experiment costs at most `B ≤ 2 ^ 127` compressions on every path,

```
probTrue (experiment P.scheme A) ≤ badW + κ (B - keygenCost) < B / 2 ^ 127,
```

where `badW ≤ (9 + |Loc|) / 2 ^ 128` is the weight of the records that are not good (the last
call's metadata is a constant tag, or some other keygen answer has the public key as its low
half), and the strict inequality uses `keygenCost = 2 |Loc|`; for larger budgets the bound is
trivial.

The proof: key generation is a uniform record up to the records that are not separated
(`E_run_keygen`); the good records are kept, the others pay their weight; the first attacker
stage is coupled to a run in which only the exposed part of the keygen cache is present (`iub`);
records are regrouped by their public data before signing (`regroup`); the good records of each
group are bounded by `stageA_master` (the first stage, signing as one disjoint case split, and
the second stage); the group weights sum to one (`sum_sumW_fiber₀`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.validSet Params.encQuery
  Params.V Params.validInputs publicFiber finiteFiber hiddenCache exposedCache
  queryLocation Record.query RowPot.idxBits RowPot.nonceBits

/-! ## Budgets -/

theorem costAtMost_bind_run_support {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) {b : ℕ} (h : CostAtMost (oa >>= k) b) :
    ∀ (c : Cache) (p : α × Cache), p ∈ support (run oa c) → CostAtMost (k p.1) b := by
  induction oa using OracleComp.inductionOn generalizing b with
  | pure x =>
    intro c p hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [pure_bind] at h
    exact h
  | query_bind t k' ih =>
    intro c p hp
    rw [bind_assoc, costAtMost_query_bind_iff] at h
    obtain ⟨-, h⟩ := h
    rw [run_query_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, -, hp⟩ := hp
    exact CostAtMost.mono (ih u (h u) c' p hp) (Nat.sub_le _ _)

theorem costAtMost_liftM_bind {α β : Type} (pc : ProbComp α)
    (k : α → OracleComp Spec β) {b : ℕ}
    (h : CostAtMost ((liftM pc : OracleComp Spec α) >>= k) b) :
    ∀ x ∈ support pc, CostAtMost (k x) b := by
  change CostAtMost (liftComp pc Spec >>= k) b at h
  induction pc using OracleComp.inductionOn generalizing b with
  | pure x =>
    intro x' hx'
    rw [support_pure, Set.mem_singleton_iff] at hx'
    subst hx'
    rwa [liftComp_pure, pure_bind] at h
  | query_bind t mx ih =>
    intro x hx
    rw [liftComp_bind] at h
    have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
        (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
      simp [liftComp]; rfl
    rw [hq, bind_assoc, costAtMost_query_bind_iff] at h
    obtain ⟨-, h⟩ := h
    rw [support_bind] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, -, hx⟩ := hx
    have := ih u (h u) x hx
    simpa [queryCost] using this

theorem costAtMost_tabulate_sample_bind {n m : ℕ} {β : Type}
    (k : (Fin n → BitVec m) → OracleComp Spec β) {b : ℕ}
    (h : CostAtMost (tabulate (fun _ : Fin n => sampleBits m) >>= k) b) :
    ∀ v, CostAtMost (k v) b := by
  induction n with
  | zero =>
    intro v
    rw [tabulate_zero', pure_bind] at h
    have hv : v = Fin.elim0 := funext fun i => Fin.elim0 i
    rw [hv]
    exact h
  | succ n ih =>
    intro v
    rw [tabulate_succ'] at h
    simp only [bind_assoc, pure_bind] at h
    have h1 := costAtMost_liftM_bind ($ᵗ BitVec m) _ h (v 0) (by simp)
    have h2 := ih _ h1 (fun i => v i.succ)
    have hv : (Fin.cases (v 0) (fun i => v i.succ) : Fin (n + 1) → BitVec m) = v := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hv] at h2
    exact h2

theorem mem_image_univ_gen {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (a : α) :
    f a ∈ Finset.univ.image f :=
  Finset.mem_image_of_mem f (Finset.mem_univ a)

theorem exists_of_mem_image_univ_gen {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    {b : β} (h : b ∈ Finset.univ.image f) : ∃ a, f a = b := by
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
  exact ⟨a, ha⟩

namespace Params

variable (P : Params) (A : OracleAlgorithm.Adversary)

/-- Every budget of the experiment pays for the first chain query of key generation. -/
theorem two_le_of_costAtMost_experiment (hP : P.Hyp) {B : ℕ}
    (h : CostAtMost (OracleAlgorithm.experiment P.scheme A) B) : 2 ≤ B := by
  rw [experiment_eq] at h
  unfold keygen at h
  simp only [bind_assoc] at h
  have h1 := costAtMost_tabulate_sample_bind _ h (fun _ => 0)
  rw [tabulate_succ'] at h1
  simp only [bind_assoc] at h1
  have hlen := hP.len_zero
  obtain ⟨n, hn⟩ : ∃ n, P.len 0 - 1 = n + 1 := ⟨P.len 0 - 2, by omega⟩
  rw [hn, chainList_succ', bind_assoc, chainStep, bind_map_left, hash,
    costAtMost_query_bind_iff] at h1
  exact le_trans (le_of_eq (queryCost_896 rfl).symm) h1.1

/-! ## Key generation and the first stage -/

theorem recW_ne_zero : recW P ≠ 0 := by
  unfold recW
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

theorem sum_recW : ∑ _ξ : Record P, recW P = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold recW
  have h : (Fintype.card (Record P) : ℝ≥0∞) ≠ 0 := by
    have : Fintype.card (Record P) ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast this
  exact ENNReal.mul_inv_cancel h (ENNReal.natCast_ne_top _)

/-- Every separated record is a possible outcome of key generation. -/
theorem mem_support_run_keygen (hP : P.Hyp) (ξ : Record P) (hξ : ξ.Sep) :
    ((ξ.pk, ξ.sk), ξ.cache) ∈ support (run P.keygen ∅) := by
  by_contra hns
  have h0 : E (run P.keygen ∅) (fun p => ind (p = ((ξ.pk, ξ.sk), ξ.cache))) = 0 := by
    refine le_antisymm (expectedValue_le_of_support fun p hp => ?_) bot_le
    have hne : p ≠ ((ξ.pk, ξ.sk), ξ.cache) := by
      intro he
      apply hns
      rw [← he]
      exact hp
    exact le_of_eq (ind_not hne)
  have hge := E_run_keygen_ge hP (fun p => ind (p = ((ξ.pk, ξ.sk), ξ.cache)))
    (fun p => ind_le_one _)
  rw [h0] at hge
  have hall := Iff.mp (Fintype.sum_eq_zero_iff_of_nonneg (fun _ => bot_le)) (le_antisymm hge bot_le)
  have h2 : recW P * (if ξ.Sep then ind (((ξ.pk, ξ.sk), ξ.cache) = ((ξ.pk, ξ.sk), ξ.cache))
      else 0) = 0 := congrFun hall ξ
  rw [if_pos hξ, ind_of rfl, mul_one] at h2
  exact P.recW_ne_zero h2

theorem costAtMost_rest (hP : P.Hyp) {B : ℕ}
    (h : CostAtMost (OracleAlgorithm.experiment P.scheme A) B) :
    ∀ ξ : Record P, ξ.Sep → CostAtMost (P.rest A (ξ.pk, ξ.sk)) (B - P.keygenCost) := by
  intro ξ hξ
  rw [experiment_eq] at h
  exact (P.spends_keygen.run_budget (P.rest A) ∅ _
    (P.mem_support_run_keygen hP ξ hξ) h).2

/-- The nine constant tags leave some word free. -/
theorem exists_not_tag : ∃ w : Word, ¬ P.IsTag w := by
  by_contra hall
  push_neg at hall
  let S : Finset Word := insert P.chainMd (insert P.idxMd ((Finset.range 7).image P.rootMd))
  have hsub : (Finset.univ : Finset Word) ⊆ S := by
    intro w _
    rcases hall w with h | h | ⟨r, hr, h⟩
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hr)))
  have hc := Finset.card_le_card hsub
  have hS : S.card ≤ 9 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_insert_le P.idxMd ((Finset.range 7).image P.rootMd)
    have := (Finset.card_image_le (s := Finset.range 7) (f := P.rootMd)).trans
      (le_of_eq (Finset.card_range 7))
    omega
  rw [Finset.card_univ, Fintype.card_bitVec] at hc
  have : (2 : ℕ) ^ 128 ≤ 9 := hc.trans hS
  norm_num at this

attribute [local semireducible] hashBits in
/-- A separated record. -/
theorem exists_sep : ∃ ξ : Record P, ξ.Sep := by
  obtain ⟨w, hw⟩ := P.exists_not_tag
  refine ⟨((fun _ => 0), (fun _ => (0 : Word) ++ w)), ?_⟩
  unfold Record.Sep Record.lastTag
  simpa only [BitVec.extractLsb'_append_eq_right] using hw

theorem keygenCost_le_of_experiment (hP : P.Hyp) {B : ℕ}
    (h : CostAtMost (OracleAlgorithm.experiment P.scheme A) B) : P.keygenCost ≤ B := by
  obtain ⟨ξ, hξ⟩ := P.exists_sep
  rw [experiment_eq] at h
  exact (P.spends_keygen.run_budget (P.rest A) ∅ _
    (P.mem_support_run_keygen hP ξ hξ) h).1

theorem E_run_experiment (hP : P.Hyp) :
    E (run (OracleAlgorithm.experiment P.scheme A) ∅) g ≤
      ∑ ξ : Record P, recW P *
        (if ξ.Sep then E (run (P.rest A (ξ.pk, ξ.sk)) ξ.cache) g else 1) := by
  rw [experiment_eq, run_bind, E_bind]
  exact E_run_keygen hP _ (fun _ => E_le_one _ g_le_one)

theorem stageA_iub (hP : P.Hyp) (ξ : Record P) :
    E (run (P.rest A (ξ.pk, ξ.sk)) ξ.cache) g ≤
      E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (fun p =>
        if Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ) then 1 else
          E (run (P.rest₂ A ξ.pk ξ.sk p.1)
            (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g) := by
  unfold rest
  rw [run_bind, E_bind, ← exposure_partition (beforeSigning P) ξ]
  exact iub (A.choose ξ.pk) (hiddenCache (beforeSigning P) ξ)
    (fun p => E (run (P.rest₂ A ξ.pk ξ.sk p.1) p.2) g) (fun _ => E_le_one _ g_le_one)
    (exposedCache (beforeSigning P) ξ) (exposure_disjoint (beforeSigning P) ξ)

/-! ## The weight of the records that are not good -/

/-- The weight of the records that are not good. -/
def badW : ℝ≥0∞ := ∑ ξ : Record P, recW P * ind (¬ ξ.Good)

/-- An event on one answer, `lo (answer) ∈ W`, where `W` does not depend on that answer. -/
theorem sum_low_event (b : Loc P) (W : Record P → Finset Word)
    (hW : ∀ ξ v, W (ξ.putAnswer b v) = W ξ) :
    ∑ ξ : Record P, recW P * ind ((ξ.2 b).extractLsb' 0 128 ∈ W ξ) ≤
      ∑ ξ : Record P, recW P * ((W ξ).card * ((2 : ℝ≥0∞) ^ 128)⁻¹) := by
  have key := sum_resample (R := Record P) (V := BitVec hashBits) (fun ξ : Record P => ξ.2 b)
    (fun ξ v => ξ.putAnswer b v)
    (fun ξ v => putAnswer_get ξ b v) (fun ξ v => putAnswer_restore ξ b v) Finset.univ
    (fun r _ v => by simp)
    (fun ξ => recW P * ind ((ξ.2 b).extractLsb' 0 128 ∈ W ξ))
  rw [key]
  refine Finset.sum_le_sum fun ξ _ => ?_
  simp only [putAnswer_get, hW]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm _ (recW P), mul_assoc]
  refine mul_le_mul' le_rfl ?_
  have hcount : (Finset.univ.filter fun v : BitVec hashBits =>
      v.extractLsb' 0 128 ∈ W ξ).card ≤ (W ξ).card * 2 ^ 128 := by
    have hsub : (Finset.univ.filter fun v : BitVec hashBits => v.extractLsb' 0 128 ∈ W ξ) ⊆
        (W ξ).biUnion fun w => Finset.univ.filter fun v : BitVec hashBits =>
          v.extractLsb' 0 128 = w := by
      intro v hv
      rw [Finset.mem_filter] at hv
      rw [Finset.mem_biUnion]
      exact ⟨_, hv.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ w ∈ W ξ, (Finset.univ.filter fun v : BitVec hashBits => v.extractLsb' 0 128 = w).card
        ≤ ∑ _w ∈ W ξ, 2 ^ 128 := Finset.sum_le_sum fun w _ => card_low_le w
      _ = (W ξ).card * 2 ^ 128 := by rw [Finset.sum_const, smul_eq_mul]
  have hs : ∑ v : BitVec hashBits, ind (v.extractLsb' 0 128 ∈ W ξ) =
      ((Finset.univ.filter fun v : BitVec hashBits => v.extractLsb' 0 128 ∈ W ξ).card : ℝ≥0∞) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold ind
    by_cases h : v.extractLsb' 0 128 ∈ W ξ <;> simp [h]
  rw [hs]
  calc (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun v : BitVec hashBits => v.extractLsb' 0 128 ∈ W ξ).card : ℝ≥0∞)
      ≤ (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (((W ξ).card * 2 ^ 128 : ℕ) : ℝ≥0∞) :=
        mul_le_mul' le_rfl (Nat.cast_le.mpr hcount)
    _ = (W ξ).card * ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (2 ^ 128 : ℕ)) := by
        push_cast; ring
    _ = (W ξ).card * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by rw [inv_card_mul_two_pow_128, rate_two]

/-- The tag words. -/
def tagSet : Finset Word := insert P.chainMd (insert P.idxMd ((Finset.range 7).image P.rootMd))

theorem mem_tagSet {w : Word} : P.IsTag w ↔ w ∈ P.tagSet := by
  unfold tagSet Params.IsTag
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (h | h | ⟨r, hr, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨r, hr, h.symm⟩)
  · rintro (h | h | ⟨r, hr, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨r, hr, h.symm⟩)

theorem tagSet_card : P.tagSet.card ≤ 9 := by
  unfold tagSet
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_insert_le P.idxMd ((Finset.range 7).image P.rootMd)
  have := (Finset.card_image_le (s := Finset.range 7) (f := P.rootMd)).trans
    (le_of_eq (Finset.card_range 7))
  omega

theorem sum_not_sep :
    ∑ ξ : Record P, recW P * ind (¬ ξ.Sep) ≤ 9 * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  have h := sum_low_event (P := P) (.inr 6) (fun _ => P.tagSet) (fun _ _ => rfl)
  have he : ∀ ξ : Record P, ind (¬ ξ.Sep) = ind ((ξ.2 (.inr 6)).extractLsb' 0 128 ∈ P.tagSet) := by
    intro ξ
    unfold Record.Sep Record.lastTag
    exact ind_congr (by rw [not_not, P.mem_tagSet])
  simp only [he]
  refine h.trans ?_
  rw [← Finset.sum_mul, P.sum_recW, one_mul]
  exact mul_le_mul' (by exact_mod_cast P.tagSet_card) le_rfl

theorem sum_not_pkFresh :
    ∑ ξ : Record P, recW P * ind (¬ ξ.PkFresh) ≤
      (Fintype.card (Loc P) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  have hpt : ∀ ξ : Record P, ind (¬ ξ.PkFresh) ≤
      ∑ a : Loc P, ind (a ≠ .inr 7 ∧ (ξ.2 (.inr 7)).extractLsb' 0 128 ∈
        ({(ξ.2 a).extractLsb' 0 128} : Finset Word)) := by
    intro ξ
    by_cases h : ξ.PkFresh
    · rw [ind_not (not_not.mpr h)]; exact bot_le
    · rw [ind_of h]
      unfold Record.PkFresh at h
      push_neg at h
      obtain ⟨a, ha, he⟩ := h
      calc (1 : ℝ≥0∞) = ind (a ≠ .inr 7 ∧ (ξ.2 (.inr 7)).extractLsb' 0 128 ∈
            ({(ξ.2 a).extractLsb' 0 128} : Finset Word)) := by
            rw [ind_of ⟨ha, Finset.mem_singleton.mpr (by rw [he]; rfl)⟩]
        _ ≤ _ := Finset.single_le_sum (f := fun a : Loc P => ind (a ≠ .inr 7 ∧
              (ξ.2 (.inr 7)).extractLsb' 0 128 ∈ ({(ξ.2 a).extractLsb' 0 128} : Finset Word)))
            (fun _ _ => bot_le) (Finset.mem_univ a)
  calc ∑ ξ : Record P, recW P * ind (¬ ξ.PkFresh)
      ≤ ∑ ξ : Record P, recW P * ∑ a : Loc P, ind (a ≠ .inr 7 ∧
          (ξ.2 (.inr 7)).extractLsb' 0 128 ∈ ({(ξ.2 a).extractLsb' 0 128} : Finset Word)) :=
        Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl (hpt ξ)
    _ = ∑ a : Loc P, ∑ ξ : Record P, recW P * ind (a ≠ .inr 7 ∧
          (ξ.2 (.inr 7)).extractLsb' 0 128 ∈ ({(ξ.2 a).extractLsb' 0 128} : Finset Word)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ _a : Loc P, ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases ha : a = .inr 7
        · simp only [ha, ne_eq, not_true_eq_false, false_and, ind_not not_false, mul_zero,
            Finset.sum_const_zero]
          exact bot_le
        · have h := sum_low_event (P := P) (.inr 7)
            (fun ξ => ({(ξ.2 a).extractLsb' 0 128} : Finset Word))
            (fun ξ v => by
              unfold Record.putAnswer
              dsimp only
              rw [Function.update_of_ne ha])
          have he : ∀ ξ : Record P, ind (a ≠ .inr 7 ∧ (ξ.2 (.inr 7)).extractLsb' 0 128 ∈
              ({(ξ.2 a).extractLsb' 0 128} : Finset Word)) =
              ind ((ξ.2 (.inr 7)).extractLsb' 0 128 ∈ ({(ξ.2 a).extractLsb' 0 128} : Finset Word)) :=
            fun ξ => ind_congr ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
          simp only [he]
          refine h.trans (le_of_eq ?_)
          simp only [Finset.card_singleton, Nat.cast_one, one_mul]
          rw [← Finset.sum_mul, P.sum_recW, one_mul]
    _ = (Fintype.card (Loc P) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem badW_le :
    P.badW ≤ (9 + (Fintype.card (Loc P) : ℝ≥0∞)) * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  unfold badW
  calc ∑ ξ : Record P, recW P * ind (¬ ξ.Good)
      ≤ ∑ ξ : Record P, (recW P * ind (¬ ξ.Sep) + recW P * ind (¬ ξ.PkFresh)) := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        rw [← mul_add]
        refine mul_le_mul' le_rfl ((ind_mono fun h => ?_).trans (ind_or_le _ _))
        unfold Record.Good at h
        by_contra h'
        push_neg at h'
        exact h ⟨h'.1, h'.2⟩
    _ = _ + _ := Finset.sum_add_distrib
    _ ≤ 9 * ((2 : ℝ≥0∞) ^ 128)⁻¹ + (Fintype.card (Loc P) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ :=
        add_le_add P.sum_not_sep P.sum_not_pkFresh
    _ = _ := by ring

theorem card_loc : Fintype.card (Loc P) = (∑ k, (P.len k - 1)) + 8 := by
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp only [Fintype.card_fin]

theorem keygenCost_eq : P.keygenCost = 2 * Fintype.card (Loc P) := by
  rw [card_loc]
  unfold keygenCost
  ring

/-- The records that are not good weigh less than the key-generation budget at rate `κ`. -/
theorem badW_lt : P.badW < κ * (P.keygenCost : ℝ≥0∞) := by
  have hL : 8 ≤ Fintype.card (Loc P) := by rw [card_loc]; omega
  refine P.badW_le.trans_lt ?_
  rw [keygenCost_eq, κ_eq]
  set n := Fintype.card (Loc P) with hn
  have h2 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
    rw [show (2 : ℝ≥0∞) ^ 128 = 2 * 2 ^ 127 by rw [← pow_succ']]
    rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  rw [h2, show (2 : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ * ((2 * n : ℕ) : ℝ≥0∞) =
    ((4 * n : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ by push_cast; ring]
  have hlt : (9 + (n : ℝ≥0∞)) < ((4 * n : ℕ) : ℝ≥0∞) := by
    have : 9 + n < 4 * n := by omega
    exact_mod_cast this
  rw [mul_comm _ ((2 : ℝ≥0∞) ^ 128)⁻¹, mul_comm _ ((2 : ℝ≥0∞) ^ 128)⁻¹]
  exact ENNReal.mul_lt_mul_right (by simp) (by simp) hlt

/-! ## Regrouping by public data before signing -/

local instance instDecEqPublicData : DecidableEq (PublicData P) := Classical.decEq _

local instance instDecEqRecord : DecidableEq (Record P) := Classical.decEq _

/-- The public data before signing of all records. -/
def dataSet₀ : Finset (PublicData P) := Finset.univ.image (publicData (beforeSigning P))

theorem mem_dataSet₀ (ξ : Record P) : publicData (beforeSigning P) ξ ∈ P.dataSet₀ := by
  unfold dataSet₀
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨ξ, rfl⟩

theorem exists_of_mem_dataSet₀ {v : PublicData P} (hv : v ∈ P.dataSet₀) :
    ∃ ξ, publicData (beforeSigning P) ξ = v := by
  unfold dataSet₀ at hv
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
  exact hv

theorem fiber₀_eq_filter (v : PublicData P) :
    (Finset.univ.filter fun ξ : Record P => publicData (beforeSigning P) ξ = v) = P.fiber₀ v := by
  ext ξ
  unfold fiber₀
  rw [mem_publicFiber]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] dataSet₀

theorem nonempty_record : Nonempty (Record P) := ⟨((fun _ => 0), (fun _ => 0))⟩

/-- A representative of the records with public data `v`. -/
def rep (v : PublicData P) : Record P :=
  @Classical.epsilon (Record P) P.nonempty_record (fun ξ => ξ ∈ P.fiber₀ v)

theorem rep_mem {v : PublicData P} (hv : v ∈ P.dataSet₀) : P.rep v ∈ P.fiber₀ v := by
  obtain ⟨ξ, hξ⟩ := P.exists_of_mem_dataSet₀ hv
  have hex : ∃ ζ, ζ ∈ P.fiber₀ v := ⟨ξ, (mem_publicFiber _ v ξ).2 hξ⟩
  unfold rep
  exact Classical.epsilon_spec hex

theorem regroup (hP : P.Hyp) (G : Record P → (Message × A.State) × Cache → ℝ≥0∞) :
    ∑ ξ : Record P, recW P * E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) =
      ∑ v ∈ P.dataSet₀,
        E (run (A.choose (P.rep v).pk) (exposedCache (beforeSigning P) (P.rep v)))
          (fun p => ∑ ξ ∈ P.fiber₀ v, recW P * G ξ p) := by
  symm
  calc ∑ v ∈ P.dataSet₀,
        E (run (A.choose (P.rep v).pk) (exposedCache (beforeSigning P) (P.rep v)))
          (fun p => ∑ ξ ∈ P.fiber₀ v, recW P * G ξ p)
      = ∑ v ∈ P.dataSet₀, ∑ ξ ∈ P.fiber₀ v,
          recW P * E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [E_weighted_sum]
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        have hd : publicData (beforeSigning P) ξ = publicData (beforeSigning P) (P.rep v) :=
          ((mem_publicFiber _ _ _).1 hξ).trans ((mem_publicFiber _ _ _).1 (P.rep_mem hv)).symm
        rw [data_pk_eq _ ξ (P.rep v) hd,
          exposedCache_data_eq hP beforeSigning_valid ξ (P.rep v) hd]
    _ = ∑ v ∈ P.dataSet₀, ∑ ξ ∈ Finset.univ.filter
          (fun ξ : Record P => publicData (beforeSigning P) ξ = v),
            recW P * E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [P.fiber₀_eq_filter]
    _ = ∑ ξ : Record P, recW P *
          E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) :=
        Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := P.dataSet₀)
          (g := publicData (beforeSigning P)) (fun ξ _ => P.mem_dataSet₀ ξ) _

theorem sum_sumW_fiber₀ : ∑ v ∈ P.dataSet₀, sumW P (P.fiber₀ v) = 1 := by
  calc ∑ v ∈ P.dataSet₀, sumW P (P.fiber₀ v)
      = ∑ v ∈ P.dataSet₀, ∑ _ξ ∈ Finset.univ.filter
          (fun ξ : Record P => publicData (beforeSigning P) ξ = v), recW P := by
        refine Finset.sum_congr rfl fun v _ => ?_
        unfold sumW
        rw [P.fiber₀_eq_filter]
    _ = ∑ _ξ : Record P, recW P :=
        Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := P.dataSet₀)
          (g := publicData (beforeSigning P)) (fun ξ _ => P.mem_dataSet₀ ξ) _
    _ = 1 := P.sum_recW

/-! ## The bound -/

attribute [local irreducible] CostAtMost OracleAlgorithm.experiment Params.rest Params.rest₂
  Params.stB Params.keygen Params.verify

theorem main_bound_rest (hP : P.Hyp) {B : ℕ} (hB' : B ≤ 2 ^ 127)
    (hrest : ∀ ξ : Record P, ξ.Good →
      CostAtMost (A.choose ξ.pk >>= P.rest₂ A ξ.pk ξ.sk) B) :
    probTrue (OracleAlgorithm.experiment P.scheme A) ≤ P.badW + κ * B := by
  rw [probTrue_eq_E_run, show (fun p : Bool × Cache => if p.1 = true then (1 : ℝ≥0∞) else 0) = g
    from rfl]
  set G : Record P → (Message × A.State) × Cache → ℝ≥0∞ := fun ξ p =>
    if ξ.Good then (if Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ) then 1 else
      E (run (P.rest₂ A ξ.pk ξ.sk p.1)
        (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g) else 0 with hG
  calc E (run (OracleAlgorithm.experiment P.scheme A) ∅) g
      ≤ ∑ ξ : Record P, recW P *
          (if ξ.Sep then E (run (P.rest A (ξ.pk, ξ.sk)) ξ.cache) g else 1) :=
        P.E_run_experiment A hP
    _ ≤ ∑ ξ : Record P, (recW P * ind (¬ ξ.Good) +
          recW P * E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ)) := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        rw [← mul_add]
        refine mul_le_mul' le_rfl ?_
        by_cases hg : ξ.Good
        · rw [if_pos hg.1, ind_not (not_not.mpr hg), zero_add]
          refine (P.stageA_iub A hP ξ).trans (le_of_eq ?_)
          refine congrArg _ (funext fun p => ?_)
          rw [hG]
          dsimp only
          rw [if_pos hg]
        · rw [ind_of hg]
          refine le_trans ?_ le_self_add
          split_ifs
          · exact E_le_one _ g_le_one
          · exact le_rfl
    _ = P.badW + ∑ ξ : Record P, recW P *
          E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) := by
        rw [Finset.sum_add_distrib]
        rfl
    _ = P.badW + ∑ v ∈ P.dataSet₀,
          E (run (A.choose (P.rep v).pk) (exposedCache (beforeSigning P) (P.rep v)))
            (fun p => ∑ ξ ∈ P.fiber₀ v, recW P * G ξ p) := by
        rw [P.regroup A hP G]
    _ = P.badW + ∑ v ∈ P.dataSet₀,
          E (run (A.choose (P.rep v).pk) (exposedCache (beforeSigning P) (P.rep v)))
            (fun p => P.FA A (P.rep v).pk ((P.fiber₀ v).filter Record.Good) p.1 p.2) := by
        refine congrArg _ (Finset.sum_congr rfl fun v hv => ?_)
        refine congrArg _ (funext fun p => ?_)
        unfold FA
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        have hd : publicData (beforeSigning P) ξ = publicData (beforeSigning P) (P.rep v) :=
          ((mem_publicFiber _ _ _).1 hξ).trans ((mem_publicFiber _ _ _).1 (P.rep_mem hv)).symm
        rw [hG]
        dsimp only
        by_cases hg : ξ.Good
        · rw [if_pos hg, if_pos hg, data_pk_eq _ ξ (P.rep v) hd]
        · rw [if_neg hg, if_neg hg, mul_zero]
    _ ≤ P.badW + ∑ v ∈ P.dataSet₀, κ * sumW P (P.fiber₀ v) * B := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun v hv => ?_)
        exact P.stageA_master A hP v ((P.fiber₀ v).filter Record.Good) (Finset.filter_subset _ _)
          (fun ξ hξ => (Finset.mem_filter.1 hξ).2) (P.rep v) (P.rep_mem hv) B hB'
          fun ξ hξ => by
            have hξF := (Finset.mem_filter.1 hξ).1
            have hd : publicData (beforeSigning P) ξ = publicData (beforeSigning P) (P.rep v) :=
              ((mem_publicFiber _ _ _).1 hξF).trans
                ((mem_publicFiber _ _ _).1 (P.rep_mem hv)).symm
            have h := hrest ξ (Finset.mem_filter.1 hξ).2
            rw [data_pk_eq _ ξ (P.rep v) hd] at h
            exact h
    _ = P.badW + κ * B := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, P.sum_sumW_fiber₀, mul_one]

theorem main_bound (hP : P.Hyp) {B : ℕ}
    (hB : CostAtMost (OracleAlgorithm.experiment P.scheme A) B) (hB' : B ≤ 2 ^ 127) :
    probTrue (OracleAlgorithm.experiment P.scheme A) ≤
      P.badW + κ * (B - P.keygenCost : ℕ) := by
  apply P.main_bound_rest A hP ((Nat.sub_le B P.keygenCost).trans hB')
  intro ξ hξ
  simpa only [rest] using P.costAtMost_rest A hP hB ξ hξ.1

/-- Honest key-generation cost supplies the strictness at the 127-bit rate, absorbing the
weight of the records that are not good. -/
theorem badW_add_lt {B : ℕ} (hKB : P.keygenCost ≤ B) :
    P.badW + κ * (B - P.keygenCost : ℕ) < (B : ℝ≥0∞) / 2 ^ securityBits := by
  have hsec : securityBits = 127 := rfl
  have hsplit : (B : ℝ≥0∞) / 2 ^ securityBits =
      κ * (P.keygenCost : ℝ≥0∞) + κ * (B - P.keygenCost : ℕ) := by
    rw [hsec, ENNReal.div_eq_inv_mul, ← κ_eq, ← mul_add]
    congr 1
    rw [← Nat.cast_add, Nat.add_sub_cancel' hKB]
  rw [hsplit]
  have hfin : κ * ((B - P.keygenCost : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (by rw [κ_eq]; simp) (ENNReal.natCast_ne_top _)
  exact ENNReal.add_lt_add_right hfin P.badW_lt

theorem one_lt_div {B : ℕ} (h : 2 ^ 127 < B) :
    (1 : ℝ≥0∞) < (B : ℝ≥0∞) / 2 ^ securityBits := by
  have hsec : securityBits = 127 := rfl
  rw [hsec, ENNReal.lt_div_iff_mul_lt (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
  exact_mod_cast h

/-- **Strong unforgeability** of a layer scheme. -/
theorem secure (hP : P.Hyp) : P.scheme.Secure := by
  intro A B hB
  by_cases hle : B ≤ 2 ^ 127
  · exact (P.main_bound A hP hB hle).trans_lt
      (P.badW_add_lt (P.keygenCost_le_of_experiment A hP hB))
  · exact (probOutput_le_one).trans_lt (one_lt_div (not_le.1 hle))

end Params

end OptimalOTS.LeanIsaBaseline.Layer
