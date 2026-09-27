import Submissions.UpperCompressions.LongChain91AuthActual
import Submissions.UpperCompressions.ProofBundle08

/-!
# Conditional signed game for the cost-91 long-chain scheme

This is the actual completed-table signer law.  It retains the returned nonce
and class, the original-cache replay event, and a single shared continuation
budget for fresh-index and graph authentication loss.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter

abbrev signedDecode : BitVec hashBits → Option (Fin M) :=
  LongChain91Empirical.decode
abbrev signedTier : Fin M → ℕ := LongChain91Empirical.rank
abbrev IndexTable := BitVec (msgBits + 86) → BitVec hashBits

/-! ## Concrete decoder posterior rate -/

theorem concrete_weak_mass_pos (i : Fin M) :
    0 < fraction (weakRank signedTier i ∘ signedDecode) := by
  rw [LongChain91Empirical.weakRank_probability]
  unfold Chain18Compact.survival
  have h := Chain18Compact.prefix_lt_R (LongChain91Schedule.tier i)
  have hR : (0 : ℝ) < Chain18Compact.R := by norm_num [Chain18Compact.R]
  have hc : ((Chain18Compact.prefixMass (LongChain91Schedule.tier i) : ℕ) : ℝ) <
      (Chain18Compact.R : ℝ) := by exact_mod_cast h
  exact sub_pos.mpr ((div_lt_one hR).2 hc)

theorem concrete_class_fraction (i : Fin M) :
    fraction (fun y => signedDecode y = some i) =
      LongChain91Security.classProbability i := by
  unfold fraction
  convert LongChain91Empirical.uniform_decode_probability i using 1
  congr 1
  funext y
  split_ifs <;> rfl

theorem survival_ge_rejection (i : Fin M) :
    1 - (∑ j : Fin M, LongChain91Security.classProbability j) ≤
      Chain18Compact.survival
        (Chain18Compact.prefixMass (LongChain91Schedule.tier i)) := by
  rw [LongChain91Security.classProbability_sum]
  unfold Chain18Compact.survival
  have hmass := Chain18Compact.prefix_add_mass_le
    (LongChain91Schedule.tier i)
  have hpfx : Chain18Compact.prefixMass (LongChain91Schedule.tier i) ≤
      Chain18Compact.acceptedAliases := by omega
  have hR : (0 : ℝ) < Chain18Compact.R := by norm_num [Chain18Compact.R]
  have hpfx' :
      ((Chain18Compact.prefixMass (LongChain91Schedule.tier i) : ℕ) : ℝ) ≤
        (Chain18Compact.acceptedAliases : ℝ) := by exact_mod_cast hpfx
  exact sub_le_sub_left (div_le_div_of_nonneg_right hpfx' hR.le) 1

theorem concrete_posterior_rate_le (i : Fin M) :
    fraction (fun y => signedDecode y = some i) /
        fraction (weakRank signedTier i ∘ signedDecode) ≤
      LongChain91Security.classProbability i /
        (1 - ∑ j : Fin M, LongChain91Security.classProbability j) := by
  rw [concrete_class_fraction, LongChain91Empirical.weakRank_probability]
  exact div_le_div_of_nonneg_left
    (LongChain91Security.classProbability_pos i).le
    (by
      have h := LongChain91Security.classProbability_sum_lt_one
      linarith)
    (survival_ge_rejection i)

theorem concrete_rate_eq_base_excess (i : Fin M) :
    LongChain91Security.classProbability i /
        (1 - ∑ j : Fin M, LongChain91Security.classProbability j) =
      Chain18Compact.kappa / 2 + LongChain91Security.excess i := by
  have hraw := LongChain91Security.excess_raw_eq i
  have heq := LongChain91Security.excess_eq i
  linarith

theorem concrete_posterior_rate_ennreal_base_excess (i : Fin M) :
    ENNReal.ofReal (fraction (fun y => signedDecode y = some i) /
      fraction (weakRank signedTier i ∘ signedDecode)) ≤
      ENNReal.ofReal (Chain18Compact.kappa / 2) +
        ENNReal.ofReal (LongChain91Security.excess i) := by
  have he : 0 ≤ LongChain91Security.excess i := by
    unfold LongChain91Security.excess
    exact le_max_right _ _
  rw [← ENNReal.ofReal_add
    (show 0 ≤ Chain18Compact.kappa / 2 by
      unfold Chain18Compact.kappa
      positivity) he]
  apply ENNReal.ofReal_le_ofReal
  exact (concrete_posterior_rate_le i).trans_eq
    (concrete_rate_eq_base_excess i)

def verifyForgery (pk : PublicKey) (m₁ : Message) (σ : Option WeightedScheme.Signature)
    (z : Message × WeightedScheme.Signature) : OracleComp Spec ForgeryResult := do
  let ok ← scheme.verify pk z.1 z.2
  return (z.1,z.2,ok && decide (σ.map (fun s => (m₁,s)) ≠ some z))

theorem stBWithForgery_bind (A : scheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option WeightedScheme.Signature) :
    stBWithForgery A pk m₁ st σ = A.forge st σ >>= verifyForgery pk m₁ σ := by
  unfold stBWithForgery verifyForgery
  congr 1
  funext z
  cases z
  dsimp only [WeightedScheme.Scheme.toAlgorithm]
  congr 1
  funext ok
  congr 3
  congr 1
  exact decide_eq_decide.mpr Iff.rfl

theorem verifyForgery_queries_chosen (pk : PublicKey) (m₁ : Message)
    (σ : Option WeightedScheme.Signature) (z : Message × WeightedScheme.Signature) (c : Cache) :
    publicHit (encQuery (z.1,z.2.1)) (verifyForgery pk m₁ σ z) c = 1 := by
  unfold verifyForgery WeightedScheme.Scheme.verify
  rw [bind_assoc]
  exact publicHit_hash_target (z.1++z.2.1) _ c

def forgedInput (z : Message × WeightedScheme.Signature) : EncInput := (z.1,z.2.1)

theorem fExp_indexLength_none (A? : Option (Finset Name)) (ξ : Rec)
    (q : Query) (hq : q.1 = msgBits+86) : fExp A? ξ q = none := by
  have hk : kc ξ q = none := by
    cases hc : kc ξ q with
    | none => rfl
    | some u =>
      obtain ⟨h,p,hp,he,_⟩ := (kc_apply_iff ξ q u).mp hc
      exact False.elim (len_hashParent_ne_enc hp ((congrArg Sigma.fst he).symm.trans hq))
  unfold fExp
  split_ifs
  · exact hk
  · rfl

/-- This adapter supplies the concrete forge/verify/strong-check continuation
to FreshOverlay. The actual query-prefix, graph exposure, and positive weak-rank
mass premises are all discharged. -/
theorem concrete_fresh_overlay (A : scheme.toAlgorithm.Adversary)
    (ξ : Rec) (m : Message) (st : A.State) (c : Cache) (k : ℕ)
    (v : Nonce 86) (i : Fin M) :
    E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
      signedChosen (exposeCache (run (loop 86 signedDecode signedTier m k)
        ((lengthSlice (msgBits+86)).preload c g)) (fExp (some (setsName i)) ξ))
        (fun s => A.forge st (signatureFromWinner ξ s)) forgedInput (some (v,i))
        (freshAlternative 86 c (m,v))
        (fun d => signedDecode (g (d.1++d.2)) = some i)) ≤
      ENNReal.ofReal (fraction (fun y => signedDecode y = some i) /
        fraction (weakRank signedTier i ∘ signedDecode)) *
        E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
          signedCharge (exposeCache (run (loop 86 signedDecode signedTier m k)
            ((lengthSlice (msgBits+86)).preload c g)) (fExp (some (setsName i)) ξ))
            (fun s => stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ s))
            (some (v,i)) (indexPaid (isIndexLength (msgBits+86)))) := by
  have h := eager_fresh_chosen_overlay_bound 86 signedDecode signedTier m k
    c (fExp (some (setsName i)) ξ) (fExp_indexLength_none _ ξ)
    (fun s => A.forge st (signatureFromWinner ξ s))
    (fun s => verifyForgery (pkOf ξ) m (signatureFromWinner ξ s))
    forgedInput v i (concrete_weak_mass_pos i)
    (fun s z d => verifyForgery_queries_chosen (pkOf ξ) m (signatureFromWinner ξ s) z d)
  have he : (fun s => A.forge st (signatureFromWinner ξ s) >>=
      verifyForgery (pkOf ξ) m (signatureFromWinner ξ s)) =
      (fun s => stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ s)) :=
    funext fun s => (stBWithForgery_bind A (pkOf ξ) m st (signatureFromWinner ξ s)).symm
  rw [he] at h
  exact h

/-- A completed table is stable under the actual public execution. An accepted
different-input forgery therefore uses either the original public cache or a
fresh coordinate of this same completed table. -/
theorem forgery_replay_or_fresh (A : scheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d)
    (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A (pkOf ξ) m st
      (some (η,revealed (setsName i) ξ))) d)) (hok : p.1.2.2 = true) :
    Cache.Hits p.2 (fHid (some (setsName i)) ξ) ∨ Spr p.2 ξ ∨
      AlternateClass c (m,η) i ∨
      (freshAlternative 86 c (m,η) (p.1.1,p.1.2.1.1) ∧
        signedDecode (g (p.1.1++p.1.2.1.1)) = some i) := by
  obtain ⟨u,hu,hs | hh | hi⟩ := stBWithForgery_index_witness A ξ i η m st d p hp hok
  · exact Or.inr (Or.inl hs)
  · exact Or.inl hh
  · have hmono := sub_of_mem_support_run _ d p hp
    let q : Query := encQuery (p.1.1,p.1.2.1.1)
    cases hc : c q with
    | some y =>
      have hpq := hmono q y (hsub q y ((lengthSlice (msgBits+86)).preload_some c g q y hc))
      have hy : y = u := Option.some.inj (hpq.symm.trans hu)
      exact Or.inr (Or.inr (Or.inl ⟨_,hi.2,y,hc,hy ▸ hi.1⟩))
    | none =>
      have hpre : (lengthSlice (msgBits+86)).preload c g q =
          some (g (p.1.1++p.1.2.1.1)) := by
        unfold QuerySlice.preload
        rw [Cache.extend_apply, hc, Option.none_or]
        exact lengthSlice_inside _ g _
      have hpq := hmono q _ (hsub q _ hpre)
      have hu' : g (p.1.1++p.1.2.1.1) = u := Option.some.inj (hpq.symm.trans hu)
      exact Or.inr (Or.inr (Or.inr ⟨⟨hc,hi.2⟩,hu' ▸ hi.1⟩))
theorem graph_iub_forgery (oa : OracleComp Spec ForgeryResult) (ξ : Rec)
    (A? : Option (Finset Name)) (d d' : Cache)
    (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run oa (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run oa (Cache.extend d' (fExp A? ξ)))
        (fun p => if Cache.Hits p.2 (fHid A? ξ) then 1 else forgerySuccess p) := by
  have hkc : Cache.extend d' (kc ξ) =
      Cache.extend (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    rw [Cache.extend_assoc, extend_fExp_fHid]
  have hdisj : Cache.Disjoint (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    intro q hq
    have hkq : (kc ξ q).isSome := by
      obtain ⟨h,p,hp,_,hqp⟩ := (fHid_isSome_iff _ ξ q).mp hq
      exact (kc_isSome_iff ξ q).mpr ⟨h,p,hp,hqp⟩
    rw [Cache.extend_apply, indexExtension_kc_none hd' hξ hkq, Option.none_or]
    exact disjoint_fExp_fHid _ ξ q hq
  rw [hkc]
  exact iub oa (fHid A? ξ) forgerySuccess
    (fun p => by unfold forgerySuccess; split_ifs <;> simp) _ hdisj

/-- Concrete game-to-events bound. Replay is measured in the original public
cache; private signer entries are part of the fresh-table term, not replay. -/
theorem signed_success_replay_fresh (A : scheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d' : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hd' : IndexExtension c d') (hξ : ¬ Cache.Hits c (kc ξ))
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d') :
    E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
      (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
          ind (AlternateClass c (m,η) i) +
          ind (freshAlternative 86 c (m,η) (p.1.1,p.1.2.1.1) ∧
            signedDecode (g (p.1.1++p.1.2.1.1)) = some i)) := by
  refine (graph_iub_forgery _ ξ (some (setsName i)) c d' hd' hξ).trans ?_
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hh : Cache.Hits p.2 (fHid (some (setsName i)) ξ)
  · rw [if_pos hh, ind_of hh]
    exact le_add_right (le_add_right le_self_add)
  · rw [if_neg hh]
    by_cases hok : p.1.2.2 = true
    · rw [forgerySuccess, if_pos hok]
      have hsub' : Cache.Sub ((lengthSlice (msgBits+86)).preload c g)
          (Cache.extend d' (fExp (some (setsName i)) ξ)) :=
        fun q u h => Cache.extend_apply_of_some (hsub q u h)
      rcases forgery_replay_or_fresh A ξ i η m st c _ g hsub' p hp hok with hh' | hs | ho | hf
      · exact absurd hh' hh
      · rw [ind_of hs]
        exact le_add_right (le_add_right le_add_self)
      · rw [ind_of ho]
        exact le_add_right le_add_self
      · rw [ind_of hf]
        exact le_add_self
    · rw [forgerySuccess, if_neg hok]
      exact zero_le

theorem indexExtension_trans {c d e : Cache} (hcd : IndexExtension c d)
    (hde : IndexExtension d e) : IndexExtension c e := by
  refine ⟨fun q u h => hde.1 q u (hcd.1 q u h), ?_⟩
  intro q u hc he
  cases hd : d q with
  | none => exact hde.2 q u hd he
  | some v => exact hcd.2 q v hc hd

theorem indexExtension_preload (c : Cache) (g : BitVec (msgBits+86) → BitVec hashBits) :
    IndexExtension c ((lengthSlice (msgBits+86)).preload c g) := by
  refine ⟨fun q u h => (lengthSlice (msgBits+86)).preload_some c g q u h, ?_⟩
  intro q u hc he
  by_cases hq : q.1 = msgBits+86
  · exact exists_encQuery_of_length q hq
  · unfold QuerySlice.preload at he
    rw [Cache.extend_apply, hc, Option.none_or, lengthSlice_outside _ g q hq] at he
    cases he

theorem loop_indexExtension {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (p : Option (Winner 86 M) × Cache)
    (hp : p ∈ support (run (loop 86 decode tier m k) c)) : IndexExtension c p.2 := by
  refine ⟨sub_of_mem_support_run _ c p hp, ?_⟩
  intro q u hc he
  obtain ⟨η,hη⟩ := ReplacementLocality.loop_new_cache_row 86 decode tier m k c p hp q u hc he
  exact ⟨(m,η),hη⟩

theorem preloaded_loop_indexExtension {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (p : Option (Winner 86 M) × Cache)
    (hp : p ∈ support (run (loop 86 decode tier m k) ((lengthSlice (msgBits+86)).preload c g))) :
    IndexExtension c p.2 :=
  indexExtension_trans (indexExtension_preload c g) (loop_indexExtension decode tier m k _ p hp)

theorem auth_E_add {α : Type} (p : ProbComp α) (f g : α → ℝ≥0∞) :
    E p (fun x => f x+g x) = E p f+E p g := by
  simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]

/-- Verifying a forged pair keeps its chosen input unchanged. Dropping the
verification outcome converts the terminal fresh event to the exact forge
expectation used in FreshOverlay's `signedChosen`. -/
theorem terminal_chosen_le_forge (A : scheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (c : Cache) (P : EncInput → Prop) :
    E (run (stBWithForgery A pk m st σ) c) (fun p => ind (P (p.1.1,p.1.2.1.1))) ≤
      E (run (A.forge st σ) c) (fun p => ind (P (forgedInput p.1))) := by
  rw [stBWithForgery_bind]
  dsimp only [WeightedScheme.Scheme.toAlgorithm] at A ⊢
  rw [run_bind, E_bind]
  apply E_mono
  intro p
  unfold verifyForgery
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  exact E_const_le _ _

/-- Pointwise actual signed-game master. Its replay and fresh payoffs are
measured before signing and before final verification respectively, and graph
costs use exactly the same reduced continuation/cache as the fresh-index cost. -/
theorem signed_game_leaf (A : scheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d' : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hd' : IndexExtension c d') (hξ : ¬ Cache.Hits c (kc ξ))
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d') :
    E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
      (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ))+ind (Spr p.2 ξ)) +
      ind (AlternateClass c (m,η) i) +
      E (run (A.forge st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (freshAlternative 86 c (m,η) (forgedInput p.1) ∧
          signedDecode (g (p.1.1++p.1.2.1)) = some i)) := by
  have h := signed_success_replay_fresh A ξ i η m st c d' g hd' hξ hsub
  rw [auth_E_add, auth_E_add] at h
  refine h.trans (add_le_add (add_le_add le_rfl (E_const_le _ _)) ?_)
  exact terminal_chosen_le_forge A (pkOf ξ) m st _ _
    (fun u => freshAlternative 86 c (m,η) u ∧ signedDecode (g (u.1++u.2)) = some i)

theorem retained_success_eq (A : scheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (c : Cache) :
    E (run (stBWithForgery A pk m st σ) c) forgerySuccess =
      E (run (stB A pk m st σ) c) successValue := by
  rw [← stBWithForgery_map A pk m st σ, run_map, E_map]
  rfl
def signedAverage (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F : IndexTable → Cache → ℝ≥0∞) : ℝ≥0∞ :=
  E ($ᵗ IndexTable) (fun g =>
    E (run (loop 86 signedDecode signedTier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p => if p.1=b then F g p.2 else 0))

theorem signedAverage_mono_support (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F G : IndexTable → Cache → ℝ≥0∞)
    (h : ∀ g p, p ∈ support (run (loop 86 signedDecode signedTier m k)
      ((lengthSlice (msgBits+86)).preload c g)) → p.1=b → F g p.2 ≤ G g p.2) :
    signedAverage m c k b F ≤ signedAverage m c k b G := by
  apply E_mono
  intro g
  apply expectedValue_mono_of_support
  intro p hp
  split_ifs with hb
  · exact h g p hp hb
  · exact le_rfl

theorem signedAverage_add (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F G : IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => F g d+G g d) =
      signedAverage m c k b F+signedAverage m c k b G := by
  let trial (g : IndexTable) := run (loop 86 signedDecode signedTier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2+G g p.2 else 0)) =
    E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2 else 0)) +
    E latent (fun g => E (trial g) (fun p => if p.1=b then G g p.2 else 0))
  have hh (P : Prop) [Decidable P] (a b : ℝ≥0∞) : (if P then a+b else 0) =
      (if P then a else 0)+(if P then b else 0) := by split_ifs <;> simp
  simp_rw [hh,auth_E_add]

theorem signedAverage_const_mul (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (a : ℝ≥0∞) (F : IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => a*F g d) = a*signedAverage m c k b F := by
  let trial (g : IndexTable) := run (loop 86 signedDecode signedTier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then a*F g p.2 else 0)) =
    a*E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2 else 0))
  have hh (P : Prop) [Decidable P] (x : ℝ≥0∞) : (if P then a*x else 0) = a*(if P then x else 0) := by
    split_ifs <;> simp
  simp_rw [hh,← E_const_mul]

theorem signedAverage_sum {ι : Type} (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (T : Finset ι) (F : ι → IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => ∑ ξ ∈ T, F ξ g d) =
      ∑ ξ ∈ T, signedAverage m c k b (F ξ) := by
  let trial (g : IndexTable) := run (loop 86 signedDecode signedTier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then ∑ ξ∈T, F ξ g p.2 else 0)) =
    ∑ ξ∈T, E latent (fun g => E (trial g) (fun p => if p.1=b then F ξ g p.2 else 0))
  have hh (P : Prop) [Decidable P] (f : ι → ℝ≥0∞) : (if P then ∑ ξ ∈ T, f ξ else 0) =
      ∑ ξ ∈ T, if P then f ξ else 0 := by split_ifs <;> simp
  simp_rw [hh,E_finsetSum]

theorem signedAverage_weighted_sum (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (T : Finset Rec) (F : Rec → IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => ∑ ξ ∈ T, w*F ξ g d) =
      ∑ ξ ∈ T, w*signedAverage m c k b (F ξ) := by
  rw [signedAverage_sum]
  simp_rw [signedAverage_const_mul]

def fixedPost (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin M) :=
  stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ))

def graphLoss (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin M) (d : Cache) : ℝ≥0∞ :=
  E (run (fixedPost A ξ m st η i) (Cache.extend d (fExp (some (setsName i)) ξ)))
    (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ))+ind (Spr p.2 ξ))

def freshLoss (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin M)
    (c : Cache) (g : IndexTable) (d : Cache) : ℝ≥0∞ :=
  E (run (A.forge st (some (η,revealed (setsName i) ξ)))
    (Cache.extend d (fExp (some (setsName i)) ξ)))
    (fun p => ind (freshAlternative 86 c (m,η) (forgedInput p.1) ∧
      signedDecode (g (p.1.1++p.1.2.1))=some i))

def postCost (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin M)
    (charge : Spec.Domain → ℝ≥0∞) (d : Cache) : ℝ≥0∞ :=
  expectedCharge charge (fixedPost A ξ m st η i) (Cache.extend d (fExp (some (setsName i)) ξ))

def posteriorRate (i : Fin M) : ℝ≥0∞ :=
  ENNReal.ofReal (fraction (fun y => signedDecode y=some i) /
    fraction (weakRank signedTier i ∘ signedDecode))

private def jointInd (P Q : Prop) : ℝ≥0∞ := if P ∧ Q then 1 else 0

theorem signedAverage_fresh_bound (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin M) :
    signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c) ≤
      posteriorRate i * signedAverage m c k (some (η,i))
        (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d) := by
  have h := concrete_fresh_overlay A ξ m st c k η i
  unfold signedChosen signedCharge exposeCache at h
  simp only [E_map] at h
  dsimp only [WeightedScheme.Scheme.toAlgorithm] at A
  have hl : (fun g => E (run (loop 86 signedDecode signedTier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then E (run (A.forge st (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (fExp (some (setsName i)) ξ)))
          (fun s => jointInd (freshAlternative 86 c (m,η) (forgedInput s.1))
            (signedDecode (g ((forgedInput s.1).1++(forgedInput s.1).2))=some i))
        else 0)) =
      (fun g => E (run (loop 86 signedDecode signedTier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then freshLoss A ξ m st η i c g p.2 else 0)) := by
    funext g
    congr 1
    funext p
    split_ifs with hp
    · rw [hp]
      simp only [freshLoss, signatureFromWinner, Option.map_some, forgedInput, ind, jointInd]
      congr 1
      funext s
      split_ifs <;> rfl
    · rfl
  have hr : (fun g => E (run (loop 86 signedDecode signedTier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then expectedCharge (indexPaid (isIndexLength (msgBits+86)))
          (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (fExp (some (setsName i)) ξ)) else 0)) =
      (fun g => E (run (loop 86 signedDecode signedTier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) p.2 else 0)) := by
    funext g
    congr 1
    funext p
    split_ifs with hp
    · rw [hp]
      rfl
    · rfl
  have hlE := congrArg (E ($ᵗ IndexTable)) hl
  have hrE := congrArg (E ($ᵗ IndexTable)) hr
  exact hlE.symm.le.trans (h.trans_eq (congrArg (posteriorRate i * ·) hrE))

theorem signedAverage_graph_bound (A : scheme.toAlgorithm.Adversary)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin M) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ)) :
    signedAverage m c k (some (η,i)) (fun _ d => ∑ ξ∈T, w*graphLoss A ξ m st η i d) ≤
      signedAverage m c k (some (η,i)) (fun _ d => (∑ ξ∈T, w*ind (Spr c ξ)) +
        authRate * ∑ ξ∈fiberA pk, w*postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d) := by
  apply signedAverage_mono_support
  intro g p hp _
  have hext := preloaded_loop_indexExtension signedDecode signedTier m k c g p hp
  have h := postsign_auth_expected (isCut_setsName i) pk T hT c p.2 hext hTc
    (isIndexLength (msgBits+86)) (fun q hq => exists_encQuery_of_length q hq)
    (fun dt => stBWithForgery A dt.1 m st (some (η,dt.2.1)))
  exact h

/-! The graph and index rates use the same actual continuation clock. -/

theorem record_shared_paid_budget {alpha : Type} (Ac : Finset Name)
    (pk : BitVec 128) (d' : Cache) (isIndex : Spec.Domain → Prop)
    (a b : ℝ≥0∞) (K : Data → OracleComp Spec alpha) (B : ℕ)
    (hB : ∀ xi ∈ fiberA pk, CostAtMost (K (dataOf Ac xi)) B) :
    a * (∑ xi ∈ fiberA pk, w * expectedCharge (indexPaid isIndex)
      (K (dataOf Ac xi)) (Cache.extend d' (fExp (some Ac) xi))) +
    b * (∑ xi ∈ fiberA pk, w * expectedCharge (otherPaid isIndex)
      (K (dataOf Ac xi)) (Cache.extend d' (fExp (some Ac) xi))) ≤
      max a b * sumW (fiberA pk) * B := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ xi ∈ fiberA pk, w *
        (a * expectedCharge (indexPaid isIndex)
          (K (dataOf Ac xi)) (Cache.extend d' (fExp (some Ac) xi)) +
         b * expectedCharge (otherPaid isIndex)
          (K (dataOf Ac xi)) (Cache.extend d' (fExp (some Ac) xi))) := by
      apply Finset.sum_congr rfl
      intro xi _
      ring
    _ ≤ ∑ xi ∈ fiberA pk, w * (max a b * B) :=
      Finset.sum_le_sum fun xi hxi => mul_le_mul_right
        (paid_shared_budget isIndex a b (K (dataOf Ac xi))
          (Cache.extend d' (fExp (some Ac) xi)) B (hB xi hxi)) w
    _ = _ := by rw [← Finset.sum_mul, ← sumW]; ring

def signedMass (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner) : ℝ≥0∞ :=
  signedAverage m c k b (fun _ _ => 1)

theorem signedAverage_const (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (a : ℝ≥0∞) : signedAverage m c k b (fun _ _ => a) = a*signedMass m c k b := by
  simpa only [mul_one,signedMass] using signedAverage_const_mul m c k b a (fun _ _ => 1)

def SupportedPostBudget (A : scheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) : Prop :=
  ∀ ξ∈fiberA pk, ∀ g p,
    p ∈ support (run (loop 86 signedDecode signedTier m k)
      ((lengthSlice (msgBits+86)).preload c g)) →
    CostAtMost (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ p.1)) B

def successLoss (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin M) (d : Cache) : ℝ≥0∞ :=
  E (run (fixedPost A ξ m st η i) (Cache.extend d (kc ξ))) forgerySuccess

theorem signed_leaf_average (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin M) (hξ : ¬ Cache.Hits c (kc ξ)) :
    signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d) ≤
      signedAverage m c k (some (η,i)) (fun _ d => graphLoss A ξ m st η i d) +
      signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i)) +
      signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c) := by
  rw [← signedAverage_add, ← signedAverage_add]
  apply signedAverage_mono_support
  intro g p hp _
  exact signed_game_leaf A ξ i η m st c p.2 g
    (preloaded_loop_indexExtension signedDecode signedTier m k c g p hp)
    hξ (sub_of_mem_support_run _ _ p hp)

theorem signed_cost_budget (A : scheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) (η : Nonce 86)
    (i : Fin M) (hB : SupportedPostBudget A pk m st c k B) :
    posteriorRate i * (∑ ξ∈fiberA pk, w*signedAverage m c k (some (η,i))
      (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d)) +
    authRate * (∑ ξ∈fiberA pk, w*signedAverage m c k (some (η,i))
      (fun _ d => postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d)) ≤
      (max (posteriorRate i) authRate * sumW (fiberA pk) * B) * signedMass m c k (some (η,i)) := by
  rw [← signedAverage_weighted_sum, ← signedAverage_weighted_sum,
    ← signedAverage_const_mul, ← signedAverage_const_mul, ← signedAverage_add,
    ← signedAverage_const]
  apply signedAverage_mono_support
  intro g p hp hb
  have hcont : ∀ ξ∈fiberA pk,
      CostAtMost (fixedPost A ξ m st η i) B := by
    intro ξ hξ
    have h := hB ξ hξ g p hp
    simpa only [hb,signatureFromWinner,Option.map_some,fixedPost] using h
  have h := record_shared_paid_budget (setsName i) pk p.2 (isIndexLength (msgBits+86))
    (posteriorRate i) authRate
    (fun dt => stBWithForgery A dt.1 m st (some (η,dt.2.1))) B hcont
  exact h

/-- Conditional successful-signature master for a fixed returned nonce/class.
It contains the actual strong-success event, concrete posterior law, graph
resampling, and one supported continuation clock. Only the pre-sign record
filter and the actual residual budget are premises. -/
theorem signed_winner_master (A : scheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) (η : Nonce 86)
    (i : Fin M) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    (∑ ξ∈T, w*signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d)) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
      sumW T * signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i)) +
      (max (posteriorRate i) authRate * sumW (fiberA pk) * B)*signedMass m c k (some (η,i)) := by
  let G (ξ : Rec) := signedAverage m c k (some (η,i)) (fun _ d => graphLoss A ξ m st η i d)
  let F (ξ : Rec) := signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c)
  let CI (ξ : Rec) := signedAverage m c k (some (η,i))
    (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d)
  let CO (ξ : Rec) := signedAverage m c k (some (η,i))
    (fun _ d => postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d)
  let R := signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i))
  have hG : (∑ ξ∈T, w*G ξ) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
        authRate*(∑ ξ∈fiberA pk, w*CO ξ) := by
    have h := signedAverage_graph_bound A pk T hT m st c k η i hTc
    rw [signedAverage_weighted_sum, signedAverage_add, signedAverage_const,
      signedAverage_const_mul, signedAverage_weighted_sum] at h
    exact h
  have hF : (∑ ξ∈T, w*F ξ) ≤ posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ) := by
    calc
      _ ≤ ∑ ξ∈T, w*(posteriorRate i*CI ξ) :=
        Finset.sum_le_sum fun ξ _ => mul_le_mul_right (signedAverage_fresh_bound A ξ m st c k η i) w
      _ = posteriorRate i*(∑ ξ∈T, w*CI ξ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := mul_le_mul_right (Finset.sum_le_sum_of_subset hT) (posteriorRate i)
  calc
    _ ≤ ∑ ξ∈T, w*(G ξ+R+F ξ) := Finset.sum_le_sum fun ξ hξ =>
      mul_le_mul_right (signed_leaf_average A ξ m st c k η i (hTc ξ hξ)) w
    _ = (∑ ξ∈T, w*G ξ)+sumW T*R+(∑ ξ∈T, w*F ξ) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_mul,sumW]
    _ ≤ ((∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
        authRate*(∑ ξ∈fiberA pk, w*CO ξ))+sumW T*R+
        posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ) := add_le_add (add_le_add hG le_rfl) hF
    _ = (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) + sumW T*R +
        (posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ)+authRate*(∑ ξ∈fiberA pk, w*CO ξ)) := by ring
    _ ≤ _ := add_le_add le_rfl (signed_cost_budget A pk m st c k B η i hB)

def nonePost (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) := stBWithForgery A (pkOf ξ) m st none

def noneSuccessLoss (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (d : Cache) : ℝ≥0∞ :=
  E (run (nonePost A ξ m st) (Cache.extend d (kc ξ))) forgerySuccess

def noneOtherCost (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (d : Cache) : ℝ≥0∞ :=
  expectedCharge (otherPaid (isIndexLength (msgBits+86))) (nonePost A ξ m st) d

theorem retained_charge_eq (A : scheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (charge : Spec.Domain → ℝ≥0∞) (c : Cache) :
    expectedCharge charge (stBWithForgery A pk m st σ) c =
      expectedCharge charge (stB A pk m st σ) c := by
  have h := expectedCharge_map charge (stBWithForgery A pk m st σ)
    (fun r : ForgeryResult => r.2.2) c
  rw [stBWithForgery_map] at h
  exact h.symm

theorem none_fiber_leaf (A : scheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c d' : Cache) (hd' : IndexExtension c d') (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ)) :
    (∑ ξ∈T, w*noneSuccessLoss A ξ m st d') ≤
      (∑ ξ∈T, w*ind (Spr c ξ)) + authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d') := by
  have hsum : (∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d') =
      sumW (fiberA pk)*expectedCharge (otherPaid (isIndexLength (msgBits+86)))
        (stB A pk m st none) d' := by
    calc
      _ = ∑ ξ∈fiberA pk, w*expectedCharge (otherPaid (isIndexLength (msgBits+86)))
          (stB A pk m st none) d' := by
        apply Finset.sum_congr rfl
        intro ξ hξ
        unfold noneOtherCost nonePost
        rw [retained_charge_eq, (Finset.mem_filter.mp hξ).2]
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ = ∑ ξ∈T, w*E (run (stB A (pkOf ξ) m st none) (Cache.extend d' (kc ξ))) successValue := by
      apply Finset.sum_congr rfl
      intro ξ _
      exact congrArg (w*·) (retained_success_eq A (pkOf ξ) m st none _)
    _ ≤ (∑ ξ∈T, w*ind (Spr c ξ)) + (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid (isIndexLength (msgBits+86))) (stB A pk m st none) d' :=
      failed_sign_success_expected A pk T hT m st c d' hd' hTc
        (isIndexLength (msgBits+86)) (fun q hq => exists_encQuery_of_length q hq)
    _ = _ := by rw [hsum]; ring

theorem none_cost_budget (A : scheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ)
    (hB : SupportedPostBudget A pk m st c k B) :
    signedAverage m c k none (fun _ d => authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) ≤
      (authRate*sumW (fiberA pk)*B)*signedMass m c k none := by
  rw [← signedAverage_const]
  apply signedAverage_mono_support
  intro g p hp hb
  have hcont : ∀ ξ∈fiberA pk, noneOtherCost A ξ m st p.2 ≤ B := by
    intro ξ hξ
    have h := hB ξ hξ g p hp
    have hc : CostAtMost (nonePost A ξ m st) B := by
      simpa only [hb,signatureFromWinner,Option.map_none,nonePost] using h
    have hq := expectedCharge_budget (otherPaid (isIndexLength (msgBits+86))) 1
      (fun t => by simpa only [one_mul] using otherPaid_le_queryCost (isIndexLength (msgBits+86)) t)
      (nonePost A ξ m st) B hc p.2
    simpa only [one_mul,noneOtherCost] using hq
  calc
    _ ≤ authRate*(∑ ξ∈fiberA pk, w*B) := mul_le_mul_right
      (Finset.sum_le_sum fun ξ hξ => mul_le_mul_right (hcont ξ hξ) w) authRate
    _ = _ := by rw [← Finset.sum_mul]; simp only [sumW,mul_assoc]

/-- Joint actual failed-signature success, with no posterior/index premise and
no budget obligation for unsupported signer outputs. -/
theorem signed_none_master (A : scheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ)
    (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    (∑ ξ∈T, w*signedAverage m c k none (fun _ d => noneSuccessLoss A ξ m st d)) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k none +
      (authRate*sumW (fiberA pk)*B)*signedMass m c k none := by
  rw [← signedAverage_weighted_sum]
  calc
    _ ≤ signedAverage m c k none (fun _ d => (∑ ξ∈T, w*ind (Spr c ξ)) +
        authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) := by
      apply signedAverage_mono_support
      intro g p hp _
      exact none_fiber_leaf A pk T hT m st c p.2
        (preloaded_loop_indexExtension signedDecode signedTier m k c g p hp) hTc
    _ = (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k none +
        signedAverage m c k none (fun _ d => authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) := by
      rw [signedAverage_add,signedAverage_const]
    _ ≤ _ := add_le_add le_rfl (none_cost_budget A pk m st c k B hB)

def winnerReplay (c : Cache) (m : Message) : SignedWinner → ℝ≥0∞
  | none => 0
  | some (η,i) => ind (AlternateClass c (m,η) i)

def winnerExcess : SignedWinner → ℝ≥0∞
  | none => 0
  | some (_,i) => ENNReal.ofReal (LongChain91Security.excess i)

def signerAverage (m : Message) (c : Cache) (k : ℕ) (F : SignedWinner → ℝ≥0∞) : ℝ≥0∞ :=
  E ($ᵗ IndexTable) (fun g => E (run (loop 86 signedDecode signedTier m k)
    ((lengthSlice (msgBits+86)).preload c g)) (fun p => F p.1))

def outcomeSuccessLoss (A : scheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (b : SignedWinner) (d : Cache) : ℝ≥0∞ :=
  E (run (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ b))
    (Cache.extend d (kc ξ))) forgerySuccess

def conditionalGame (A : scheme.toAlgorithm.Adversary) (T : Finset Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) : ℝ≥0∞ :=
  ∑ ξ∈T, w*E ($ᵗ IndexTable) (fun g =>
    E (run (loop 86 signedDecode signedTier m k)
      ((lengthSlice (msgBits+86)).preload c g))
      (fun p => outcomeSuccessLoss A ξ m st p.1 p.2))

theorem signedAverage_partition (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → IndexTable → Cache → ℝ≥0∞) :
    (∑ b : SignedWinner, signedAverage m c k b (F b)) =
      E ($ᵗ IndexTable) (fun g => E (run (loop 86 signedDecode signedTier m k)
        ((lengthSlice (msgBits+86)).preload c g)) (fun p => F p.1 g p.2)) := by
  let trial (g : IndexTable) := run (loop 86 signedDecode signedTier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change (∑ b : SignedWinner, E latent (fun g => E (trial g)
    (fun p => if p.1=b then F b g p.2 else 0))) =
      E latent (fun g => E (trial g) (fun p => F p.1 g p.2))
  rw [← E_finsetSum]
  congr 1
  funext g
  rw [← E_finsetSum]
  congr 1
  funext p
  simp

theorem signedMass_weighted_sum (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → ℝ≥0∞) :
    (∑ b : SignedWinner, F b*signedMass m c k b) = signerAverage m c k F := by
  simp_rw [← signedAverage_const]
  exact signedAverage_partition m c k (fun b _ _ => F b)

theorem signedMass_sum_le (m : Message) (c : Cache) (k : ℕ) :
    (∑ b : SignedWinner, signedMass m c k b) ≤ 1 := by
  have h := signedMass_weighted_sum m c k (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  exact (E_mono _ (fun _ => E_const_le _ 1)).trans (E_const_le _ 1)

theorem conditionalGame_partition (A : scheme.toAlgorithm.Adversary)
    (T : Finset Rec) (m : Message) (st : A.State) (c : Cache) (k : ℕ) :
    conditionalGame A T m st c k =
      ∑ b : SignedWinner, ∑ ξ∈T, w*signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d) := by
  unfold conditionalGame
  calc
    _ = ∑ ξ∈T, w*(∑ b : SignedWinner,
        signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d)) := by
      apply Finset.sum_congr rfl
      intro ξ _
      exact congrArg (w*·) (signedAverage_partition m c k (fun b _ d => outcomeSuccessLoss A ξ m st b d)).symm
    _ = _ := by simp only [Finset.mul_sum]; rw [Finset.sum_comm]

theorem authRate_ofReal : authRate = ENNReal.ofReal (Chain18Compact.kappa/2) := by
  unfold authRate Chain18Compact.kappa
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
    ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ)<2^127)]
  norm_num

theorem max_posterior_auth_le (i : Fin M) :
    max (posteriorRate i) authRate ≤ authRate+ENNReal.ofReal (LongChain91Security.excess i) := by
  apply max_le
  · rw [authRate_ofReal]
    exact concrete_posterior_rate_ennreal_base_excess i
  · exact le_self_add

theorem signed_outcome_master (A : scheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c : Cache) (k B : ℕ) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) (b : SignedWinner) :
    (∑ ξ∈T, w*signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d)) ≤
      ((∑ ξ∈T, w*ind (Spr c ξ)) + sumW T*winnerReplay c m b +
        (sumW (fiberA pk)*B)*(authRate+winnerExcess b))*signedMass m c k b := by
  cases b with
  | none =>
    have h := signed_none_master A pk T hT m st c k B hTc hB
    change (∑ ξ∈T, w*signedAverage m c k none (fun _ d => noneSuccessLoss A ξ m st d)) ≤ _
    refine h.trans_eq ?_
    simp only [winnerReplay,winnerExcess,mul_zero,add_zero]
    ring
  | some b =>
    rcases b with ⟨η,i⟩
    have h := signed_winner_master A pk T hT m st c k B η i hTc hB
    change (∑ ξ∈T, w*signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d)) ≤ _
    refine h.trans ?_
    rw [signedAverage_const]
    calc
      _ ≤ (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
          sumW T*(ind (AlternateClass c (m,η) i)*signedMass m c k (some (η,i))) +
          ((authRate+ENNReal.ofReal (LongChain91Security.excess i))*sumW (fiberA pk)*B)*
            signedMass m c k (some (η,i)) := by
        gcongr
        exact max_posterior_auth_le i
      _ = _ := by simp only [winnerReplay,winnerExcess]; ring

/-- The actual conditional sign/forge/verify game, including signing failure,
is bounded by surviving pre-sign spurious mass plus replay and expected class
excess of the same all-L signer. The base graph/index cost is spent once.
Only supported remaining budgets and the pre-sign no-hit record filter remain. -/
theorem conditional_game_master (A : scheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c : Cache) (k B : ℕ) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    conditionalGame A T m st c k ≤
      (∑ ξ∈T, w*ind (Spr c ξ)) + sumW (fiberA pk) *
        (signerAverage m c k (winnerReplay c m) +
          B*(authRate+signerAverage m c k winnerExcess)) := by
  rw [conditionalGame_partition]
  let P := ∑ ξ∈T, w*ind (Spr c ξ)
  let Z := sumW (fiberA pk)*(B:ℝ≥0∞)
  calc
    _ ≤ ∑ b : SignedWinner, (P+sumW T*winnerReplay c m b+Z*(authRate+winnerExcess b))*
        signedMass m c k b := Finset.sum_le_sum fun b _ =>
      signed_outcome_master A pk T hT m st c k B hTc hB b
    _ = P*(∑ b : SignedWinner, signedMass m c k b) +
        sumW T*(∑ b : SignedWinner, winnerReplay c m b*signedMass m c k b) +
        Z*(authRate*(∑ b : SignedWinner, signedMass m c k b) +
          ∑ b : SignedWinner, winnerExcess b*signedMass m c k b) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib]
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ P*1 + sumW T*(∑ b : SignedWinner, winnerReplay c m b*signedMass m c k b) +
        Z*(authRate*1+∑ b : SignedWinner, winnerExcess b*signedMass m c k b) := by
      gcongr <;> exact signedMass_sum_le m c k
    _ = P+sumW T*signerAverage m c k (winnerReplay c m)+Z*(authRate+signerAverage m c k winnerExcess) := by
      rw [mul_one,mul_one,signedMass_weighted_sum,signedMass_weighted_sum]
    _ ≤ P+sumW (fiberA pk)*signerAverage m c k (winnerReplay c m)+
        Z*(authRate+signerAverage m c k winnerExcess) := by
      gcongr
      exact sumW_mono hT
    _ = _ := by dsimp only [P,Z]; ring

end OptimalOTS.WeightedConstruction.LongChain91
