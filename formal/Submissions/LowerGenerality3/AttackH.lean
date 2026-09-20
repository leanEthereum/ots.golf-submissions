import Submissions.LowerGenerality3.Attack0

/-!
# Attacker H: query the promising points

The attacker draws a uniform message `m`, queries the first `K + 1` promising short queries for
`m` (all of them if there are fewer), asks for a signature on `m + 1`, and forges on `m` with a
candidate accepting one of the answers it saw, when there is one. Its success is at least
`hTerm`, which dominates the honest signer's chance of reading a fresh promising point up to the
factor `1 / τ` (`dec_le_hTerm`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits securityBits maxSignatureBits keygenBudget signBudget

variable (S : OracleAlgorithm.Scheme) (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic)

/-- The first `n` members of a finite set, in some order. -/
def listOf (Q : Finset Query) (n : ℕ) : List Query := Q.toList.take n

theorem mem_of_mem_listOf {Q : Finset Query} {n : ℕ} {q : Query} (h : q ∈ listOf Q n) : q ∈ Q :=
  Finset.mem_toList.mp (List.mem_of_mem_take h)

theorem length_listOf_le (Q : Finset Query) (n : ℕ) : (listOf Q n).length ≤ n := by
  unfold listOf
  exact (List.length_take ..).trans_le (min_le_left _ _)

theorem listOf_nodup (Q : Finset Query) (n : ℕ) : (listOf Q n).Nodup :=
  (Finset.nodup_toList Q).sublist (List.take_sublist _ _)

theorem length_listOf (Q : Finset Query) (n : ℕ) : (listOf Q n).length = min n Q.card := by
  unfold listOf
  rw [List.length_take, Finset.length_toList]

theorem listOf_eq_of_card_le {Q : Finset Query} {n : ℕ} (h : Q.card ≤ n) :
    (listOf Q n).toFinset = Q := by
  unfold listOf
  rw [List.take_of_length_le (by rw [Finset.length_toList]; exact h), Finset.toList_toFinset]

/-- Some returned pair is useful for `m`. -/
def HasUseful (pk : PublicKey) (m : Message) (r : List (Query × BitVec hashBits)) : Prop :=
  ∃ e ∈ r, Useful S hv hd pk m e.1 e.2

/-- A candidate accepting one of the returned pairs, if any. -/
def selH (pk : PublicKey) (m : Message) (r : List (Query × BitVec hashBits)) :
    OracleAlgorithm.Signature :=
  if h : HasUseful S hv hd pk m r then h.choose_spec.2.choose else []

theorem selH_spec {pk : PublicKey} {m : Message} {r : List (Query × BitVec hashBits)}
    (h : HasUseful S hv hd pk m r) :
    ∃ e ∈ r, ∃ f, shape S hv hd pk m (selH S hv hd pk m r) = .one e.1 f ∧ f e.2 = true := by
  simp only [selH, dif_pos h]
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.choose_spec⟩

/-- The list the attacker queries. -/
def queriesH (K : ℕ) (pk : PublicKey) (m : Message) : List Query :=
  listOf (promising S hv hd pk m) (K + 1)

theorem queriesH_short (K : ℕ) (pk : PublicKey) (m : Message) :
    ∀ q ∈ queriesH S hv hd K pk m, q.1 ≤ 512 :=
  fun q hq => ((mem_promising S hv hd).mp (mem_of_mem_listOf hq)).1

def advH (K : ℕ) : OracleAlgorithm.Adversary where
  State := PublicKey × Message × List (Query × BitVec hashBits)
  choose pk := do
    let m ← uniformMsg
    let r ← answers (queriesH S hv hd K pk m)
    pure (m + 1, (pk, m, r))
  forge st _ := pure (st.2.1, selH S hv hd st.1 st.2.1 st.2.2)

theorem experimentH_eq (K : ℕ) :
    S.weakExperiment (advH S hv hd K) = (do
      let k ← S.keygen
      let m ← uniformMsg
      let r ← answers (queriesH S hv hd K k.1 m)
      let _ ← S.sign k.2 (m + 1)
      S.verify k.1 m (selH S hv hd k.1 m r)) := by
  unfold OracleAlgorithm.Scheme.weakExperiment advH
  simp only [bind_assoc, pure_bind]
  congr 1
  funext k
  congr 1
  funext m
  congr 1
  funext r
  congr 1
  funext σ
  have hdec : decide (m ≠ m + 1) = true := decide_eq_true (Ne.symm (succ_ne m))
  simp only [hdec, Bool.or_true, Bool.and_true, bind_pure]

theorem costH {K T : ℕ} (hk : S.KeygenCostAtMost K) (hs : S.SignCostAtMost T) :
    CostAtMost (S.weakExperiment (advH S hv hd K)) (2 * K + T + 2) := by
  rw [experimentH_eq]
  refine Costs.CostAtMost.bind_le hk (b₂ := K + T + 2) (fun k => ?_) (by omega)
  refine Costs.CostAtMost.bind_le cost_uniformMsg (b₂ := K + T + 2) (fun m => ?_) (by omega)
  refine Costs.CostAtMost.bind_le (Costs.CostAtMost.mono
    (cost_answers _ (queriesH_short S hv hd K k.1 m)) (length_listOf_le _ _)) (b₂ := T + 1)
    (fun r => ?_) (by omega)
  exact Costs.CostAtMost.bind (hs k.2 (m + 1)) fun _ => hv _ _ _

/-- The attacker's term for a key-generation outcome and a message. -/
def hTerm (K : ℕ) (k : (PublicKey × S.SecretKey) × Cache) (m : Message) : ℝ≥0∞ :=
  1 - Sm k.2 (Useful S hv hd k.1.1 m) (queriesH S hv hd K k.1.1 m).toFinset k.2

/-- After `answers`, a decided fresh point is a returned useful pair. -/
theorem hasUseful_of_dec (K : ℕ) (k : (PublicKey × S.SecretKey) × Cache) (m : Message)
    (p : List (Query × BitVec hashBits) × Cache)
    (hp : p ∈ support (run (answers (queriesH S hv hd K k.1.1 m)) k.2))
    (h : Dec k.2 (Useful S hv hd k.1.1 m) (queriesH S hv hd K k.1.1 m).toFinset p.2) :
    HasUseful S hv hd k.1.1 m p.1 := by
  obtain ⟨q, hq, -, y, hy, hu⟩ := h
  obtain ⟨h1, h2⟩ := answers_spec _ k.2 p hp
  obtain ⟨y', hy'⟩ := h2 q (List.mem_toFinset.mp hq)
  have := h1 (q, y') hy'
  simp only at this
  rw [this] at hy
  have hyy : y' = y := Option.some.inj hy
  subst hyy
  exact ⟨(q, _), hy', hu⟩

/-- The success of attacker H is at least the mass of `hTerm`. -/
theorem successH (K : ℕ) :
    E (run S.keygen ∅) (fun k => E ($ᵗ BitVec msgBits) (fun m => hTerm S hv hd K k m)) ≤
      probTrue (S.weakExperiment (advH S hv hd K)) := by
  rw [experimentH_eq, probTrue_eq_win, win_bind]
  apply E_mono
  intro k
  rw [win_bind, run_uniformMsg, E_map]
  apply E_mono
  intro m
  rw [win_bind, hTerm, ← E_dec_answers k.2 (Useful S hv hd k.1.1 m) _ (queriesH S hv hd K k.1.1 m)
    (fun q hq => List.mem_toFinset.mp hq)]
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hdec : Dec k.2 (Useful S hv hd k.1.1 m) (queriesH S hv hd K k.1.1 m).toFinset p.2
  · rw [if_pos hdec]
    have hu := hasUseful_of_dec S hv hd K k m p hp hdec
    obtain ⟨e, he, f, hs, hf⟩ := selH_spec S hv hd hu
    have hcached : p.2 e.1 = some e.2 := (answers_spec _ k.2 p hp).1 e he
    rw [win_bind]
    calc (1 : ℝ≥0∞) = E (run (S.sign k.1.2 (m + 1)) p.2) (fun _ => (1 : ℝ≥0∞)) := (E_const _ _).symm
      _ ≤ _ := by
        apply expectedValue_mono_of_support
        intro s hs'
        have hsub : Cache.Sub p.2 s.2 := sub_of_mem_support_run _ _ _ hs'
        rw [verify_eq_shape S hv hd, hs, win_one_some (hsub _ _ hcached), if_pos hf]
  · rw [if_neg hdec]
    exact zero_le

/-! ## The honest side is dominated -/

theorem pr_useful_eq (pk : PublicKey) (m : Message) (q : Query) :
    pr (Useful S hv hd pk m) q = pm S hv hd pk m q := rfl

/-- The honest chance of reading a fresh promising point is at most `hTerm / τ`. -/
theorem dec_le_hTerm {K : ℕ} (hk : S.KeygenCostAtMost K) (k : (PublicKey × S.SecretKey) × Cache)
    (hkm : k ∈ support (run S.keygen ∅)) (m : Message) :
    1 - Sm k.2 (Useful S hv hd k.1.1 m) (promising S hv hd k.1.1 m) k.2 ≤ τ⁻¹ * hTerm S hv hd K k m := by
  by_cases hcard : (promising S hv hd k.1.1 m).card ≤ K + 1
  · -- every promising query is asked
    have he : (queriesH S hv hd K k.1.1 m).toFinset = promising S hv hd k.1.1 m :=
      listOf_eq_of_card_le hcard
    rw [hTerm, he]
    have h1 : (1 : ℝ≥0∞) ≤ τ⁻¹ := by
      rw [τ, one_div, inv_inv]
      exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2 ^ 25)
    calc _ = 1 * _ := (one_mul _).symm
      _ ≤ τ⁻¹ * _ := mul_le_mul' h1 le_rfl
  · -- `K + 1` promising queries are asked, one of them fresh for the key-generation cache
    push_neg at hcard
    obtain ⟨D, hD, hDcard⟩ := exists_support_run_empty hk k hkm
    have hlen : (queriesH S hv hd K k.1.1 m).length = K + 1 := by
      rw [queriesH, length_listOf]
      exact min_eq_left hcard.le
    have hnodup := listOf_nodup (promising S hv hd k.1.1 m) (K + 1)
    have hcardl : (queriesH S hv hd K k.1.1 m).toFinset.card = K + 1 := by
      rw [queriesH, List.toFinset_card_of_nodup hnodup]
      exact hlen
    have hfresh : ∃ q ∈ (queriesH S hv hd K k.1.1 m).toFinset, k.2 q = none := by
      by_contra hall
      push_neg at hall
      have hsub : (queriesH S hv hd K k.1.1 m).toFinset ⊆ D := fun q hq => by
        have := hall q hq
        exact hD q (by rw [Option.isSome_iff_ne_none]; exact this)
      have := Finset.card_le_card hsub
      omega
    obtain ⟨q₀, hq₀, hfresh₀⟩ := hfresh
    have hprom : q₀ ∈ promising S hv hd k.1.1 m := mem_of_mem_listOf (List.mem_toFinset.mp hq₀)
    have hτ : τ ≤ pr (Useful S hv hd k.1.1 m) q₀ := by
      rw [pr_useful_eq]; exact ((mem_promising S hv hd).mp hprom).2
    have hS : Sm k.2 (Useful S hv hd k.1.1 m) (queriesH S hv hd K k.1.1 m).toFinset k.2 ≤ 1 - τ := by
      unfold Sm
      split_ifs
      · exact zero_le
      · have hopen : q₀ ∈ open_ k.2 (queriesH S hv hd K k.1.1 m).toFinset k.2 :=
          Finset.mem_filter.mpr ⟨hq₀, hfresh₀, hfresh₀⟩
        calc ∏ q ∈ open_ k.2 (queriesH S hv hd K k.1.1 m).toFinset k.2, (1 - pr (Useful S hv hd k.1.1 m) q)
            = (1 - pr (Useful S hv hd k.1.1 m) q₀) *
              ∏ q ∈ (open_ k.2 (queriesH S hv hd K k.1.1 m).toFinset k.2).erase q₀,
                (1 - pr (Useful S hv hd k.1.1 m) q) := (Finset.mul_prod_erase _ _ hopen).symm
          _ ≤ (1 - pr (Useful S hv hd k.1.1 m) q₀) * 1 :=
              mul_le_mul' le_rfl (Finset.prod_le_one (fun _ _ => zero_le) (fun _ _ => tsub_le_self))
          _ ≤ 1 - τ := by rw [mul_one]; exact tsub_le_tsub_left hτ 1
    have hτ1 : τ ≤ 1 := by
      rw [τ]
      exact ENNReal.div_le_of_le_mul (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 1 * 2 ^ 25))
    have hterm : τ ≤ hTerm S hv hd K k m := by
      rw [hTerm]
      calc τ = 1 - (1 - τ) := (ENNReal.sub_sub_cancel ENNReal.one_ne_top hτ1).symm
        _ ≤ _ := tsub_le_tsub_left hS 1
    calc 1 - Sm k.2 (Useful S hv hd k.1.1 m) (promising S hv hd k.1.1 m) k.2 ≤ 1 := tsub_le_self
      _ = τ⁻¹ * τ := (ENNReal.inv_mul_cancel (by rw [τ]; exact (ENNReal.div_pos one_ne_zero (by simp)).ne')
            (by rw [τ]; exact ENNReal.div_ne_top one_ne_top (by simp))).symm
      _ ≤ τ⁻¹ * hTerm S hv hd K k m := mul_le_mul' le_rfl hterm

end OptimalOTS.LowerGenerality3
