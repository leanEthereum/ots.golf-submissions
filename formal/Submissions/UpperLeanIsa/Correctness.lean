import Submissions.UpperLeanIsa.LayerAvailability
import Submissions.UpperLeanIsa.Records
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Fixed-table semantics and perfect correctness

For a fixed oracle table `f` every program of the layer scheme has an explicit value:
`chainValue`, `chainListValue`, `idxValue`, `rootFromValue`, `rootValue`, and the exact verifier
decision `verifyValue` on arbitrary raw inputs (`fixed_verify`). Signing under a fixed table only
returns encodings of the revealed words at an accepted index (`fixed_signLoop_support`): its
best trial is always an accepted index of its nonce (`FixedBest`).
Correctness under the shared cached random oracle follows from VCVio's cached-oracle support
characterization (`probTrue_zero_of_fixed`), for every public-key-dependent message choice.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

attribute [local irreducible] trials sigBits

/-- A fixed oracle table. -/
abbrev HashTable := QueryImpl hashSpec Id

namespace Params

variable (P : Params)

/-- The index under a fixed table. -/
def idxValue (f : HashTable) (m : Message) (η : Nonce) (pk : PublicKey) : Index :=
  indexSlice (f ⟨896, P.idxInput m η pk⟩)

/-! ## Fixed-table simulation -/

theorem fixed_hash (f : HashTable) {n : ℕ} (x : BitVec n) :
    simulateQ (unifFwdAnswerImpl f) (hash x) = pure (f ⟨n, x⟩) := by
  rw [hash, simulateQ_spec_query]
  rfl

theorem fixed_index (f : HashTable) (m : Message) (η : Nonce) (pk : PublicKey) :
    simulateQ (unifFwdAnswerImpl f) (P.index m η pk) = pure (P.idxValue f m η pk) := by
  simp only [index, simulateQ_map, fixed_hash, map_pure]
  rfl

/-- The best trial under a fixed table is an accepted index of its nonce. -/
def FixedBest (f : HashTable) (m : Message) (pk : PublicKey) (β : Option (Nonce × Index)) :
    Prop :=
  ∀ b, β = some b → P.Accepted (P.idxValue f m b.1 pk) ∧ b.2 = P.idxValue f m b.1 pk

theorem fixedBest_upd (f : HashTable) (m : Message) (pk : PublicKey)
    {β : Option (Nonce × Index)} (h : P.FixedBest f m pk β) (η : Nonce) :
    P.FixedBest f m pk (P.upd β η (P.idxValue f m η pk)) := by
  intro b hb
  unfold upd at hb
  split_ifs at hb with hbt
  · obtain rfl := (Option.some.inj hb).symm
    refine ⟨?_, rfl⟩
    cases β with
    | none => simpa [better] using hbt
    | some b' =>
      simp only [better, Bool.and_eq_true, decide_eq_true_eq] at hbt
      exact hbt.1
  · exact h b hb

/-- Under a fixed table, signing only returns encodings of the revealed words at an accepted
index of the nonce. -/
theorem fixed_signLoop_support (f : HashTable) (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (β : Option (Nonce × Index)),
      P.FixedBest f m sk.pk β → ∀ σ : Option (List Bool),
      σ ∈ support (simulateQ (unifFwdAnswerImpl f) (P.signLoop sk m k tried β)) →
      ∀ s, σ = some s → ∃ η : Nonce, P.Accepted (P.idxValue f m η sk.pk) ∧
        s = encode (P.revealed sk (P.idxValue f m η sk.pk)) η := by
  have hbase : ∀ β : Option (Nonce × Index), P.FixedBest f m sk.pk β → ∀ s,
      P.sigOf sk β = some s → ∃ η : Nonce, P.Accepted (P.idxValue f m η sk.pk) ∧
        s = encode (P.revealed sk (P.idxValue f m η sk.pk)) η := by
    intro β hβ s hs
    cases β with
    | none => cases hs
    | some b =>
      obtain ⟨h1, h2⟩ := hβ b rfl
      refine ⟨b.1, h1, ?_⟩
      simp only [sigOf, Option.map_some, Option.some.injEq] at hs
      rw [← hs, ← h2]
  intro k
  induction k with
  | zero =>
    intro tried β hβ σ hσ s hs
    simp only [signLoop, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hσ
    rw [hσ] at hs
    exact hbase β hβ s hs
  | succ k ih =>
    intro tried β hβ σ hσ s hs
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signLoop_succ sk m k tried β hc, simulateQ_bind, support_bind] at hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨j, -, hσ⟩ := hσ
      unfold loopBody at hσ
      have hq : (liftM (Spec.query (.inr ⟨896, P.idxInput m (nonceOf tried hc j) sk.pk⟩)) :
          OracleComp Spec (BitVec hashBits)) = hash (P.idxInput m (nonceOf tried hc j) sk.pk) :=
        rfl
      rw [hq, simulateQ_bind, fixed_hash, pure_bind] at hσ
      unfold afterHash at hσ
      exact ih _ _ (P.fixedBest_upd f m sk.pk hβ (nonceOf tried hc j)) σ hσ s hs
    · rw [signLoop, dif_neg hc, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hσ
      rw [hσ] at hs
      exact hbase β hβ s hs

theorem fixed_sign_support (f : HashTable) (sk : SecretKey) (m : Message) (s : List Bool)
    (hs : some s ∈ support (simulateQ (unifFwdAnswerImpl f) (P.sign sk m))) :
    ∃ η : Nonce, P.Accepted (P.idxValue f m η sk.pk) ∧
      s = encode (P.revealed sk (P.idxValue f m η sk.pk)) η := by
  rw [P.sign_eq] at hs
  exact P.fixed_signLoop_support f sk m trials ∅ none (fun b h => by cases h) _ hs s rfl

/-- A zero-probability lemma that keeps all repeated hash answers consistent. -/
theorem probTrue_zero_of_fixed (oa : OracleComp Spec Bool)
    (h : ∀ f : HashTable, true ∉ support (simulateQ (unifFwdAnswerImpl f) oa)) :
    probTrue oa = 0 := by
  rw [probTrue, probOutput_eq_zero_iff]
  intro hs
  change true ∈ support (Prod.fst <$> (simulateQ oracleImpl oa).run ∅) at hs
  rw [support_map] at hs
  obtain ⟨⟨b, cache⟩, hs, hb⟩ := hs
  change b = true at hb
  subst b
  obtain ⟨f, _, hf⟩ :=
    (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff oa ∅ true).mpr ⟨cache, hs⟩
  exact h f hf

end Params

end OptimalOTS.LeanIsaBaseline.Layer
