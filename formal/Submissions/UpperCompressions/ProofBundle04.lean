import Submissions.UpperCompressions.ProofBundle02
import Submissions.UpperCompressions.ProofBundle00
import Submissions.UpperCompressions.ProofBundle03
import OptimalOTS.Dag

section

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling.Availability

attribute [local irreducible] Finset.univ Finset.filter

theorem card_option_none {n : ℕ} {α : Type} (decode : BitVec n → Option α) (a : ℕ)
    (ha : (Finset.univ.filter fun w => (decode w).isSome).card = a) :
    (Finset.univ.filter fun w => (decode w).isNone).card = 2^n-a := by
  have hp (w : BitVec n) : (decode w).isNone = true ↔ ¬ (decode w).isSome = true := by
    cases decode w <;> simp
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BitVec n))) (p := fun w => (decode w).isSome = true)
  simp only [← hp,ha,Finset.card_univ,Fintype.card_bitVec] at h
  omega

theorem uniform_option_miss {n : ℕ} {α : Type} (decode : BitVec n → Option α) (a : ℕ)
    (ha : (Finset.univ.filter fun w => (decode w).isSome).card = a) (c : ℝ≥0∞) :
    E ($ᵗ BitVec n) (fun w => if (decode w).isNone then c else 0) =
      ((2^n-a : ℕ) : ℝ≥0∞)/(2:ℝ≥0∞)^n*c := by
  rw [E_uniform]
  simp only [mul_ite,mul_zero]
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,
    card_option_none decode a ha,Fintype.card_bitVec]
  simp only [Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,mul_assoc]

end OptimalOTS.WeightedSampling.Availability
end
end

section

/-! Graph-only cache freshness, independent of any nonce or index sampler. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedFreshness

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits
  maxSignatureBits keygenBudget signBudget Dag.nonceBits Dag.idxBits Dag.numCuts Dag.trials

/-- Every supported lazy-oracle run leaves cache entries of length `L` unchanged. -/
def PreservesLength {α : Type} (L : ℕ) (oa : OracleComp Spec α) : Prop :=
  ∀ (c : Cache) (p : α × Cache), p ∈ support (run oa c) →
    ∀ q : Query, q.1 = L → p.2 q = c q

namespace PreservesLength

variable {L : ℕ} {α β : Type}

theorem of_pure (x : α) : PreservesLength L (pure x : OracleComp Spec α) := by
  intro c p hp q hq
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rfl

theorem bind {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    (h₁ : PreservesLength L oa) (h₂ : ∀ x, PreservesLength L (ob x)) :
    PreservesLength L (oa >>= ob) := by
  intro c p hp q hq
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨x, d⟩, hx, hp⟩ := hp
  exact (h₂ x d p hp q hq).trans (h₁ c (x, d) hx q hq)

theorem map {oa : OracleComp Spec α} (h : PreservesLength L oa) (f : α → β) :
    PreservesLength L (f <$> oa) := by
  intro c p hp q hq
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  exact h c p' hp' q hq

theorem of_liftM (pc : ProbComp α) :
    PreservesLength L (liftM pc : OracleComp Spec α) := by
  intro c p hp q hq
  rw [run_liftM, support_map, Set.mem_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  rfl

theorem hash {k : ℕ} (u : BitVec k) (hk : k ≠ L) : PreservesLength L (OptimalOTS.hash u) := by
  intro c p hp q hq
  have hne : q ≠ (⟨k, u⟩ : Query) := by
    intro heq
    exact hk ((congrArg Sigma.fst heq).symm.trans hq)
  unfold OptimalOTS.hash run at hp
  rw [simulateQ_spec_query] at hp
  rcases hc : c ⟨k, u⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨w, _, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact QueryCache.cacheQuery_of_ne _ _ hne
  · rw [oracleImpl_run_inr_some hc, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl

theorem foldlM {γ δ : Type} (f : γ → δ → OracleComp Spec γ)
    (hf : ∀ x a, PreservesLength L (f x a)) :
    ∀ (l : List δ) (init : γ), PreservesLength L (l.foldlM f init)
  | [], _ => of_pure _
  | a :: l, init => by
      rw [List.foldlM_cons]
      exact bind (hf init a) fun y => foldlM f hf l y

end PreservesLength

/-- Every hash node has an input length distinct from `L`. -/
def HashInputsAvoid (G : Dag.Graph) (L : ℕ) : Prop :=
  ∀ v, match G.kind v with
    | .hash p _ _ => G.len p ≠ L
    | _ => True

theorem evalNode_preservesLength (G : Dag.Graph) {L : ℕ} (hG : HashInputsAvoid G L)
    (x : G.Assignment) (v : Fin G.size) (s : OracleComp Spec (BitVec (G.len v)))
    (hs : PreservesLength L s) : PreservesLength L (G.evalNode x v s) := by
  have hv := hG v
  unfold Dag.Graph.evalNode
  cases hk : G.kind v with
  | source => exact hs
  | det => exact PreservesLength.of_pure _
  | hash p _ h =>
    exact PreservesLength.map (PreservesLength.hash _ (by simpa only [hk] using hv)) _

theorem sampleAssignment_preservesLength (G : Dag.Graph) (L : ℕ) :
    PreservesLength L G.sampleAssignment := by
  unfold Dag.Graph.sampleAssignment
  refine PreservesLength.foldlM _ (fun z v => ?_) (List.finRange G.size) (fun _ => 0)
  exact PreservesLength.map (PreservesLength.of_liftM _) _

theorem evaluate_preservesLength (G : Dag.Graph) {L : ℕ} (hG : HashInputsAvoid G L)
    (z : G.Assignment) : PreservesLength L (G.evaluate z) := by
  unfold Dag.Graph.evaluate
  refine PreservesLength.foldlM _ (fun x v => ?_) (List.finRange G.size) (fun _ => 0)
  exact PreservesLength.map
    (evalNode_preservesLength G hG x v _ (PreservesLength.of_pure _)) _

theorem graph_keygen_preservesLength (G : Dag.Graph) {L : ℕ} (hG : HashInputsAvoid G L) :
    PreservesLength L G.keygen :=
  PreservesLength.bind (sampleAssignment_preservesLength G L)
    (fun z => evaluate_preservesLength G hG z)

/-- Probability as an indicator expectation under the actual lazy oracle. -/
theorem probTrue_eq_E_run (oa : OracleComp Spec Bool) :
    probTrue oa = E (run oa ∅) (fun p => if p.1 = true then 1 else 0) := by
  unfold probTrue
  rw [run'_eq, probOutput_map_eq_tsum_ite, E, expectedValue_def]
  refine tsum_congr fun x => ?_
  rcases x with ⟨b, c⟩
  cases b <;> simp

end OptimalOTS.WeightedFreshness

end
end

section

/-! Bridge from the executable first-minimum selector to the exact iid finite
sampling law. Ranks may tie across arbitrary output labels; only ranks determine
priority, and nonce identity determines the target event. -/

namespace WeightedReplacement

open OptimalOTS.WeightedSampling
attribute [local instance] Classical.propDecidable

def weakRank {β : Type} (rank : β → ℕ) (v : β) : Option β → Prop
  | none => True
  | some a => rank v ≤ rank a

def strictRank {β : Type} (rank : β → ℕ) (v : β) : Option β → Prop
  | none => True
  | some a => rank v < rank a

theorem select_weakRank_iff {β : Type} (rank : β → ℕ) (v : β)
    (xs : List (Option β)) :
    weakRank rank v (select rank xs) ↔ ∀ a ∈ xs, weakRank rank v a := by
  cases hs : select rank xs with
  | none =>
    have hh := (select_none_iff rank xs).mp hs
    simp only [weakRank, true_iff]
    intro a ha
    rw [hh a ha]
    trivial
  | some w =>
    constructor
    · intro hv a ha
      cases a with
      | none => trivial
      | some a => exact hv.trans (select_rank_le rank xs w hs a ha)
    · intro hall
      exact hall (some w) (select_source rank xs w hs)

theorem best_eq_target_iff {β : Type} (rank : β → ℕ) (v : β) (a b : Option β) :
    best rank a b = some v ↔
      (a = some v ∧ weakRank rank v b) ∨ (strictRank rank v a ∧ b = some v) := by
  cases a with
  | none => simp [best, strictRank]
  | some a =>
    cases b with
    | none => simp [best, weakRank]
    | some b =>
      by_cases h : rank a ≤ rank b
      · simp only [best, if_pos h, Option.some.injEq, weakRank, strictRank]
        constructor
        · rintro rfl
          exact Or.inl ⟨rfl, h⟩
        · rintro (⟨rfl, _⟩ | ⟨hv, rfl⟩)
          · rfl
          · omega
      · simp only [best, if_neg h, Option.some.injEq, weakRank, strictRank]
        constructor
        · rintro rfl
          exact Or.inr ⟨by omega, rfl⟩
        · rintro (⟨rfl, hv⟩ | ⟨_, rfl⟩)
          · omega
          · rfl

theorem select_eq_firstMinimumEvent {β : Type} (rank : β → ℕ) (v : β)
    (xs : List (Option β)) :
    select rank xs = some v ↔
      FirstMinimumEvent (some v) (weakRank rank v) (strictRank rank v) xs := by
  induction xs with
  | nil => simp [select, firstMinimumEvent_nil]
  | cons a xs ih =>
    rw [select, best_eq_target_iff, firstMinimumEvent_cons, select_weakRank_iff, ih]

theorem firstMinimumEvent_map_iff {α β : Type*} (f : α → β) (v : α) (w : β)
    (weak strict : β → Prop) (hf : ∀ a, f a = w ↔ a = v) (xs : List α) :
    FirstMinimumEvent w weak strict (xs.map f) ↔
      FirstMinimumEvent v (weak ∘ f) (strict ∘ f) xs := by
  induction xs with
  | nil => simp [firstMinimumEvent_nil]
  | cons a xs ih =>
    simp only [List.map_cons, firstMinimumEvent_cons, hf, ih,
      List.forall_mem_map, Function.comp_apply]

/-- Exact iid probability of the executable selector returning one labeled
target. The target output must identify precisely its nonce; other outputs may
have the same tier without any restriction. -/
theorem iid_select_probability {α β : Type} [Fintype α]
    (rank : β → ℕ) (candidate : α → Option β) (v : α) (w : β)
    (hc : ∀ a, candidate a = some w ↔ a = v) (n : ℕ) :
    iidMean n (fun xs => if select rank (xs.map candidate) = some w then (1 : ℝ) else 0) =
      kernel n (fraction (weakRank rank w ∘ candidate))
        (fraction (strictRank rank w ∘ candidate)) / Fintype.card α := by
  classical
  have hev (xs : List α) : select rank (xs.map candidate) = some w ↔
      FirstMinimumEvent v (weakRank rank w ∘ candidate) (strictRank rank w ∘ candidate) xs := by
    rw [select_eq_firstMinimumEvent]
    exact firstMinimumEvent_map_iff candidate v (some w) _ _ hc xs
  have hv : ¬ (strictRank rank w ∘ candidate) v := by
    simp [Function.comp_def, (hc v).mpr rfl, strictRank]
  simp_rw [hev]
  exact iid_first_minimum_event_probability v _ _ hv n

/-- Attaching the nonce to its decoded class gives the exact label-injectivity
premise, without assuming classes or tiers distinguish nonce positions. -/
theorem tagged_candidate_target_iff {α γ : Type} (table : α → Option γ)
    (v : α) (i : γ) (hv : table v = some i) (a : α) :
    (fun j => (a,j)) <$> table a = some (v,i) ↔ a = v := by
  cases ha : table a with
  | none =>
    have hav : a ≠ v := by
      intro he
      subst a
      rw [hv] at ha
      cases ha
    simp [ha, hav]
  | some j =>
    change (some (a,j) = some (v,i)) ↔ a = v
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · exact fun h => h.1
    · intro he
      subst a
      exact ⟨rfl, Option.some.inj (ha.symm.trans hv)⟩

/-- Complete finite-table theorem: a nonce has the common tier kernel divided by
the number of nonces. Tiers may have any number of classes and aliases. -/
theorem iid_tagged_table_probability {α γ : Type} [Fintype α]
    (table : α → Option γ) (tier : γ → ℕ) (v : α) (i : γ)
    (hv : table v = some i) (n : ℕ) :
    iidMean n (fun xs =>
      if select (fun p : α × γ => tier p.2)
          (xs.map fun a => (fun j => (a,j)) <$> table a) = some (v,i)
      then (1 : ℝ) else 0) =
      kernel n (fraction (weakRank tier i ∘ table))
        (fraction (strictRank tier i ∘ table)) / Fintype.card α := by
  let cand : α → Option (α × γ) := fun a => (fun j => (a,j)) <$> table a
  have hw : weakRank (fun p : α × γ => tier p.2) (v,i) ∘ cand =
      weakRank tier i ∘ table := by
    funext a
    cases ht : table a <;> simp [cand, ht, weakRank]
  have hs : strictRank (fun p : α × γ => tier p.2) (v,i) ∘ cand =
      strictRank tier i ∘ table := by
    funext a
    cases ht : table a <;> simp [cand, ht, strictRank]
  have h := iid_select_probability (fun p : α × γ => tier p.2) cand v (v,i)
    (tagged_candidate_target_iff table v i hv) n
  rw [hw, hs] at h
  convert h using 1
  congr 1
  funext xs
  dsimp only [cand]
  split_ifs <;> rfl

end WeightedReplacement
end

section

/-! The exact finite-table law for the actual probabilistic oracle program.
This closes the conversion between finite iid expectations and `ProbComp`.
Full-table versus lazy-table reasoning and adaptive security are separate. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling

namespace WeightedReplacement

open scoped Classical

theorem iidMean_nonneg {α : Type*} [Fintype α] (n : ℕ) (g : List α → ℝ)
    (hg : ∀ xs, 0 ≤ g xs) : 0 ≤ iidMean n g := by
  induction n generalizing g with
  | zero => exact hg []
  | succ n ih =>
    change 0 ≤ (∑ a, iidMean n (fun xs => g (a :: xs))) / (Fintype.card α : ℝ)
    exact div_nonneg (Finset.sum_nonneg fun a _ => ih _ (fun xs => hg (a :: xs)))
      (Nat.cast_nonneg _)

theorem ofReal_uniformMean {α : Type*} [Fintype α] [Nonempty α]
    (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ENNReal.ofReal (uniformMean g) =
      ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g a) := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [uniformMean, ENNReal.ofReal_div_of_pos hcard,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => hg a), ENNReal.ofReal_natCast,
    div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- Every nonnegative real payoff has the same expectation in the executable
private draw program and the explicitly normalized finite iid sample space. -/
theorem E_drawList_ofReal (n k : ℕ) (g : List (Nonce n) → ℝ)
    (hg : ∀ xs, 0 ≤ g xs) :
    E (drawList n k) (fun xs => ENNReal.ofReal (g xs)) =
      ENNReal.ofReal (iidMean k g) := by
  induction k generalizing g with
  | zero => simp [drawList, E_pure, iidMean]
  | succ k ih =>
    rw [drawList, E_bind]
    simp only [E_bind, E_pure]
    rw [E_uniform, iidMean,
      ofReal_uniformMean _ (fun a => iidMean_nonneg k _ (fun xs => hg (a :: xs)))]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ih _ (fun xs => hg (a :: xs))]

/-- The actual all-L oracle loop, conditioned only by fixing its complete table,
returns each accepted nonce with exactly the common tier kernel divided by N. -/
theorem E_loop_fixed_row_target (n M k : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (v : Nonce n) (i : Fin M) (hv : decode (table v) = some i) :
    E (run (loop n decode tier m k) c)
      (fun p => if p.1 = some (v,i) then 1 else 0) =
      ENNReal.ofReal (kernel k
        (fraction (weakRank tier i ∘ decode ∘ table))
        (fraction (strictRank tier i ∘ decode ∘ table)) / Fintype.card (Nonce n)) := by
  rw [run_loop_fixed_row n decode tier m table c hc, E_map]
  have hprob := iid_tagged_table_probability (decode ∘ table) tier v i hv k
  have he := E_drawList_ofReal n k
    (fun xs => if select (fun p : Nonce n × Fin M => tier p.2)
      (xs.map fun a => (fun j => (a,j)) <$> decode (table a)) = some (v,i)
      then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num)
  have hp : (iidMean k fun xs => if select (fun p : Nonce n × Fin M => tier p.2)
      (xs.map fun a => (fun j => (a,j)) <$> decode (table a)) = some (v,i)
      then (1 : ℝ) else 0) =
      kernel k (fraction (weakRank tier i ∘ decode ∘ table))
        (fraction (strictRank tier i ∘ decode ∘ table)) / Fintype.card (Nonce n) := by
    convert hprob using 1
    congr 1
    funext xs
    simp only [Function.comp_apply]
    split_ifs <;> rfl
  rw [hp] at he
  simp only [candidate, Function.comp_apply, apply_ite,
    ENNReal.ofReal_one, ENNReal.ofReal_zero] at he ⊢
  convert he using 1
  congr 1

end WeightedReplacement
end

section

/-! Adaptive public-prefix invariance for actual `OracleComp Spec` programs.
The interpreter records uniform draws and answered hash queries, and stops before
answering the distinguished query. Its whole distribution is invariant under any
change to that table coordinate. This uses a complete-table view; hidden signer
queries never become independent fresh public answers. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical

abbrev PublicStep := Σ t : Spec.Domain, Spec.Range t
abbrev PublicTrace := List PublicStep

end
end WeightedReplacement
end

section

/-! Stopped public prefixes under the actual mixed lazy oracle. Only the
distinguished request is intercepted; every answered query uses oracleImpl.
The final implementation cache is hidden, while all public answers and coins
are retained. Privately cached answers therefore need no fresh-draw fiction. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical

def overwrite (c : Cache) (u : Query) (y : BitVec hashBits) : Cache :=
  Function.update c u (some y)

theorem overwrite_cacheQuery (c : Cache) (u q : Query) (y w : BitVec hashBits)
    (hqu : q ≠ u) :
    (overwrite c u y).cacheQuery q w = overwrite (c.cacheQuery q w) u y := by
  funext r
  by_cases hrq : r = q
  · subst r
    simp [overwrite, Function.update_of_ne hqu]
  · by_cases hru : r = u
    · subst r
      simp [overwrite, QueryCache.cacheQuery_of_ne _ _ hrq]
    · simp [overwrite, QueryCache.cacheQuery_of_ne _ _ hrq, Function.update_of_ne hru]

theorem oracleImpl_overwrite (u q : Query) (hqu : q ≠ u)
    (c : Cache) (y : BitVec hashBits) :
    (oracleImpl (.inr q)).run (overwrite c u y) =
      (fun p => (p.1, overwrite p.2 u y)) <$> (oracleImpl (.inr q)).run c := by
  have hlookup : overwrite c u y q = c q := Function.update_of_ne hqu _ _
  cases hc : c q with
  | none =>
    have ho : overwrite c u y q = none := hlookup.trans hc
    rw [oracleImpl_run_inr_none hc, oracleImpl_run_inr_none ho]
    simp only [map_bind, map_pure]
    apply bind_congr
    intro w
    rw [overwrite_cacheQuery c u q y w hqu]
  | some w =>
    have ho : overwrite c u y q = some w := hlookup.trans hc
    rw [oracleImpl_run_inr_some hc, oracleImpl_run_inr_some ho, map_pure]

/-- All actual oracle responses before the first public request to u. Returning
none means u was requested, and its answer has not been exposed. -/
def hybridPrefix {α : Type} (u : Query) (oa : OracleComp Spec α) :
    Cache → PublicTrace → ProbComp (Option α × PublicTrace) :=
  OracleComp.construct (fun a _ tr => pure (some a, tr))
    (fun t _ rec c tr => match t with
      | .inl n => do
          let a ← HasQuery.query (spec := unifSpec) (m := ProbComp) n
          rec a c (⟨.inl n, a⟩ :: tr)
      | .inr q => if q = u then pure (none, tr) else do
          let p ← (oracleImpl (.inr q)).run c
          rec p.1 p.2 (⟨.inr q, p.1⟩ :: tr)) oa

theorem hybridPrefix_pure {α : Type} (u : Query) (a : α) (c : Cache) (tr : PublicTrace) :
    hybridPrefix u (pure a) c tr = pure (some a, tr) := by simp [hybridPrefix]

theorem hybridPrefix_unif {α : Type} (u : Query) (n : ℕ)
    (k : Spec.Range (.inl n) → OracleComp Spec α) (c : Cache) (tr : PublicTrace) :
    hybridPrefix u (liftM (Spec.query (.inl n)) >>= k) c tr =
      (HasQuery.query (spec := unifSpec) (m := ProbComp) n) >>= fun a =>
        hybridPrefix u (k a) c (⟨.inl n,a⟩ :: tr) := by simp [hybridPrefix]

theorem hybridPrefix_target {α : Type} (u : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (tr : PublicTrace) :
    hybridPrefix u (liftM (Spec.query (.inr u)) >>= k) c tr = pure (none,tr) := by
  simp [hybridPrefix]

theorem hybridPrefix_hash {α : Type} (u q : Query) (hqu : q ≠ u)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (tr : PublicTrace) :
    hybridPrefix u (liftM (Spec.query (.inr q)) >>= k) c tr =
      (oracleImpl (.inr q)).run c >>= fun p =>
        hybridPrefix u (k p.1) p.2 (⟨.inr q,p.1⟩ :: tr) := by
  simp [hybridPrefix, hqu]

/-- The entire stopped public-prefix distribution is unchanged by overwriting
the distinguished cache cell, whether originally absent or privately cached. -/
theorem hybridPrefix_overwrite {α : Type} (u : Query) (oa : OracleComp Spec α)
    (c : Cache) (tr : PublicTrace) (y : BitVec hashBits) :
    hybridPrefix u oa (overwrite c u y) tr = hybridPrefix u oa c tr := by
  induction oa using OracleComp.inductionOn generalizing c tr with
  | pure a => rw [hybridPrefix_pure, hybridPrefix_pure]
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [hybridPrefix_unif, hybridPrefix_unif]
      exact bind_congr fun a => ih a c _
    | inr q =>
      by_cases hqu : q = u
      · subst q
        rw [hybridPrefix_target, hybridPrefix_target]
      · rw [hybridPrefix_hash u q hqu, hybridPrefix_hash u q hqu,
          oracleImpl_overwrite u q hqu]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        apply bind_congr
        intro p
        exact ih p.1 p.2 _

theorem hybridPrefix_event_overwrite {α : Type} (u : Query) (oa : OracleComp Spec α)
    (c : Cache) (tr : PublicTrace) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) :
    E (hybridPrefix u oa (overwrite c u y) tr) (fun p => if event p then 1 else 0) =
      E (hybridPrefix u oa c tr) (fun p => if event p then 1 else 0) := by
  rw [hybridPrefix_overwrite]

end
end WeightedReplacement
end

section

/-! Public query accounting in the original shared-cache execution. Queries
are charged even when the implementation cache already contains their answers. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementPublicCost_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits blockBits msgBits signBudget

def expectedCharge {α : Type} (charge : Spec.Domain → ℝ≥0∞) (oa : OracleComp Spec α) : Cache → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ => 0)
    (fun t _ rec c => charge t + E ((oracleImpl t).run c) (fun p => rec p.1 p.2)) oa

@[simp] theorem expectedCharge_pure {α : Type} (charge : Spec.Domain → ℝ≥0∞) (a : α) (c : Cache) :
    expectedCharge charge (pure a) c = 0 := by simp [expectedCharge]

theorem expectedCharge_query {α : Type} (charge : Spec.Domain → ℝ≥0∞) (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) :
    expectedCharge charge (liftM (Spec.query t) >>= k) c =
      charge t + E ((oracleImpl t).run c) (fun p => expectedCharge charge (k p.1) p.2) := by
  simp [expectedCharge]

theorem expectedCharge_add {α : Type} (a b : Spec.Domain → ℝ≥0∞) (oa : OracleComp Spec α) (c : Cache) :
    expectedCharge (fun t => a t+b t) oa c = expectedCharge a oa c + expectedCharge b oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    simp only [expectedCharge_query]
    simp_rw [ih]
    simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]
    ring

theorem expectedCharge_mono {α : Type} (a b : Spec.Domain → ℝ≥0∞)
    (hab : ∀ t, a t ≤ b t) (oa : OracleComp Spec α) (c : Cache) :
    expectedCharge a oa c ≤ expectedCharge b oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    rw [expectedCharge_query, expectedCharge_query]
    exact add_le_add (hab t) (E_mono _ (fun p => ih p.1 p.2))

theorem expectedCharge_budget {α : Type} (charge : Spec.Domain → ℝ≥0∞) (rate : ℝ≥0∞)
    (hc : ∀ t, charge t ≤ rate * queryCost t) (oa : OracleComp Spec α)
    (b : ℕ) (hB : CostAtMost oa b) (c : Cache) : expectedCharge charge oa c ≤ rate*b := by
  induction oa using OracleComp.inductionOn generalizing b c with
  | pure x => simp
  | query_bind t k ih =>
    unfold CostAtMost at hB
    rw [isQueryBound_query_bind_iff] at hB
    rw [expectedCharge_query]
    calc
      _ ≤ rate*queryCost t + E ((oracleImpl t).run c) (fun _ => rate*((b-queryCost t:ℕ):ℝ≥0∞)) :=
        add_le_add (hc t) (E_mono _ (fun p => ih p.1 _ (hB.2 p.1) p.2))
      _ ≤ rate*queryCost t + rate*((b-queryCost t:ℕ):ℝ≥0∞) := add_le_add le_rfl (E_const_le _ _)
      _ = rate*b := by rw [← mul_add, ← Nat.cast_add, Nat.add_sub_of_le hB.1]

def publicHit {α : Type} (u : Query) (oa : OracleComp Spec α) : Cache → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ => 0)
    (fun t _ rec c => match t with
      | .inl n => E ((oracleImpl (.inl n)).run c) (fun p => rec p.1 p.2)
      | .inr q => if q = u then 1 else E ((oracleImpl (.inr q)).run c) (fun p => rec p.1 p.2)) oa

@[simp] theorem publicHit_pure {α : Type} (u : Query) (a : α) (c : Cache) :
    publicHit u (pure a) c = 0 := by simp [publicHit]

theorem publicHit_query {α : Type} (u : Query) (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) :
    publicHit u (liftM (Spec.query t) >>= k) c =
      if t = .inr u then 1 else E ((oracleImpl t).run c) (fun p => publicHit u (k p.1) p.2) := by
  cases t <;> simp [publicHit]

theorem publicHit_query_le {α : Type} (u : Query) (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) :
    publicHit u (liftM (Spec.query t) >>= k) c ≤
      (if t = .inr u then 1 else 0) + E ((oracleImpl t).run c) (fun p => publicHit u (k p.1) p.2) := by
  cases t with
  | inl n => simp [publicHit]
  | inr q =>
    by_cases hqu : q = u
    · simp [publicHit, hqu]
    · simp [publicHit, hqu]

/-- publicHit is exactly the probability that the actual mixed-oracle prefix
stops before answering u. Trace initialization does not affect this event. -/
theorem publicHit_eq_prefix {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache) (tr : PublicTrace) :
    publicHit u oa c = E (hybridPrefix u oa c tr) (fun p => if p.1 = none then 1 else 0) := by
  induction oa using OracleComp.inductionOn generalizing c tr with
  | pure a => simp [publicHit, hybridPrefix_pure, E_pure]
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [hybridPrefix_unif, publicHit_query]
      simp only [reduceCtorEq, if_false, oracleImpl_run_inl, E_bind, E_pure]
      apply congrArg
      funext a
      exact ih a c _
    | inr q =>
      by_cases hqu : q = u
      · subst q
        rw [publicHit_query u (.inr u) k c, hybridPrefix_target]
        simp [E_pure]
      · rw [hybridPrefix_hash u q hqu, E_bind]
        simp only [publicHit_query, Sum.inr.injEq, if_neg hqu]
        apply congrArg
        funext p
        exact ih p.1 p.2 _

def exposureCharge {D : Type} [Fintype D] (e : D → Query) (t : Spec.Domain) : ℝ≥0∞ :=
  ∑ d, if t = .inr (e d) then 1 else 0

/-- Sum of first-public-hit probabilities is bounded by the expected number of
paid queries to those inputs. Repeated queries only increase the upper bound. -/
theorem publicHit_sum_le {D α : Type} [Fintype D] (e : D → Query)
    (oa : OracleComp Spec α) (c : Cache) :
    (∑ d, publicHit (e d) oa c) ≤ expectedCharge (exposureCharge e) oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    rw [expectedCharge_query]
    calc
      _ ≤ ∑ d, ((if t = .inr (e d) then 1 else 0) +
          E ((oracleImpl t).run c) (fun p => publicHit (e d) (k p.1) p.2)) :=
        Finset.sum_le_sum (fun d _ => publicHit_query_le (e d) t k c)
      _ = exposureCharge e t + E ((oracleImpl t).run c) (fun p => ∑ d, publicHit (e d) (k p.1) p.2) := by
        rw [Finset.sum_add_distrib]
        apply congrArg (exposureCharge e t + ·)
        exact (expectedValue_finsetSum ((oracleImpl t).run c) Finset.univ
          (fun d p => publicHit (e d) (k p.1) p.2)).symm
      _ ≤ _ := add_le_add le_rfl (E_mono _ (fun p : Spec.Range t × Cache => ih p.1 p.2))

theorem exposureCharge_eq {D : Type} [Fintype D] (e : D → Query) (he : Function.Injective e)
    (t : Spec.Domain) : exposureCharge e t = if ∃ d, t = .inr (e d) then 1 else 0 := by
  by_cases ht : ∃ d, t = .inr (e d)
  · obtain ⟨d, hd⟩ := ht
    have hh (d' : D) : t = .inr (e d') ↔ d' = d := by
      constructor
      · intro h
        exact (he (Sum.inr.inj (hd.symm.trans h))).symm
      · rintro rfl
        exact hd
    simp [exposureCharge, hh]
  · have hh : ∀ d, t ≠ .inr (e d) := by simpa using ht
    simp [exposureCharge, hh]

def indexPaid (isIndex : Spec.Domain → Prop) (t : Spec.Domain) : ℝ≥0∞ :=
  if isIndex t then queryCost t else 0

def otherPaid (isIndex : Spec.Domain → Prop) (t : Spec.Domain) : ℝ≥0∞ :=
  if isIndex t then 0 else queryCost t

theorem exposureCharge_le_indexPaid {D : Type} [Fintype D] (e : D → Query)
    (he : Function.Injective e) (isIndex : Spec.Domain → Prop)
    (hi : ∀ d, isIndex (.inr (e d))) (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d))) :
    ∀ t, exposureCharge e t ≤ indexPaid isIndex t := by
  intro t
  rw [exposureCharge_eq e he]
  split_ifs with ht
  · obtain ⟨d,rfl⟩ := ht
    rw [indexPaid, if_pos (hi d)]
    exact_mod_cast hpaid d
  · exact bot_le

theorem publicHit_sum_le_indexPaid {D α : Type} [Fintype D] (e : D → Query)
    (he : Function.Injective e) (isIndex : Spec.Domain → Prop)
    (hi : ∀ d, isIndex (.inr (e d))) (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d)))
    (oa : OracleComp Spec α) (c : Cache) :
    (∑ d, publicHit (e d) oa c) ≤ expectedCharge (indexPaid isIndex) oa c :=
  (publicHit_sum_le e oa c).trans (expectedCharge_mono _ _
    (exposureCharge_le_indexPaid e he isIndex hi hpaid) oa c)

theorem paid_split {α : Type} (isIndex : Spec.Domain → Prop) (oa : OracleComp Spec α) (c : Cache) :
    expectedCharge (indexPaid isIndex) oa c + expectedCharge (otherPaid isIndex) oa c =
      expectedCharge (fun t => queryCost t) oa c := by
  rw [← expectedCharge_add]
  congr 1
  funext t
  simp [indexPaid, otherPaid]
  split_ifs <;> simp

/-- Index and graph exposure costs share one pathwise budget. Neither term
receives a separate copy of the full budget. -/
theorem paid_shared_budget {α : Type} (isIndex : Spec.Domain → Prop) (a b : ℝ≥0∞)
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ) (hB : CostAtMost oa B) :
    a*expectedCharge (indexPaid isIndex) oa c + b*expectedCharge (otherPaid isIndex) oa c ≤
      max a b * B := by
  calc
    _ ≤ max a b * expectedCharge (indexPaid isIndex) oa c +
        max a b * expectedCharge (otherPaid isIndex) oa c :=
      add_le_add (mul_le_mul' (le_max_left _ _) le_rfl) (mul_le_mul' (le_max_right _ _) le_rfl)
    _ = max a b * expectedCharge (fun t => queryCost t) oa c := by rw [← mul_add, paid_split]
    _ ≤ _ := mul_le_mul' le_rfl (by
      simpa using expectedCharge_budget (fun t => queryCost t) 1 (fun _ => by simp) oa B hB c)

end
end WeightedReplacement
end

section

namespace OptimalOTS.WeightedConstruction.WideForest

abbrev EncInput := Message × BitVec 86

def encQuery (u : EncInput) : Query := ⟨msgBits + 86, u.1 ++ u.2⟩

end OptimalOTS.WeightedConstruction.WideForest
end

section

/-!
# Values of the concrete scheme

For a record `ξ : Rec` (sources and hash outputs), `val ξ n` is the value of node `n` in the
honest evaluation `graph.evalRec ξ`.  This file gives the explicit formulas (`val_src`, …,
`val_rh`), describes the keygen cache (`kc ξ`) through the keygen points `pointOf ξ h p` of the
hash nodes, splits it into the exposed and hidden parts relative to a disclosure set
(`fExp`, `fHid`), defines the event `Spr` (a cached answer at a non-keygen point that begins with
an honest value), and records which record coordinates each value depends on (`deps`), with the
two coordinate updates `updSrc` and `updHash`.

The oracle has no labels.  A keygen point is the bare input `⟨p.len, val ξ p⟩` of a hash node; the
hash node is read back from the tweak in its 16 high bits (`tagNat_pointOf`, `tagging`), and a
keygen point never has the length of an index query (`pointOf_ne_encQuery`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace WeightedConstruction.WideForest

/-! ### Auxiliary cast lemmas -/

/-! ## Hash nodes and keygen points -/

/-! ## The tagging of the concrete graph -/

/-! ## Exposed and hidden points -/

/-! ## The event `Spr` -/

/- Some cached answer, at a string carrying the tweak of a hash node but different from the
honest input of that node, begins with the honest output of that node.  The tweak condition makes
a query count for one hash node only: without labels, a string of length `p.len` could otherwise
be a spurious preimage for every hash node with that input length. -/

/-- Exact low129 fibers leave127 unconstrained oracle output bits. -/
theorem card_filter_lowWord_le (a : BitVec 129) :
    (Finset.univ.filter fun w : BitVec 256 => lowWord w = a).card ≤ 2 ^ 127 :=
  le_of_eq (TruncFiber.card_256_129 a)

/-! ## Coordinates -/

/-! ## The coordinate that randomizes the input of a hash node -/

end WeightedConstruction.WideForest

end OptimalOTS

end
end
