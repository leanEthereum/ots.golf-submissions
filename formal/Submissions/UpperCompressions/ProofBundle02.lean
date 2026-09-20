import OptimalOTS.OracleAlgorithm
import OptimalOTS.Dag
import VCVio.EvalDist.Expectation

/- Original module: Submissions.UpperCompressions.TypedScheme; SHA256 357bc9974021aa4bf36108aa172edd0cec0c8dc55d158a327e6f52ec83fbdc35. -/
section

/-!
# Oracle algorithms with a typed signature and an injective encoding

An internal proof device of this root, not part of the contract. The contract's
`OracleAlgorithm.Scheme` transmits bit strings; here signatures have any type with an injective
bit encoding, as for DAG signatures (nonce, disclosed values). `WireAdapter` transfers every
requirement to the scheme on the encoded bit strings.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS

/-- Key generation, signing and verification with an injective signature encoding. -/
structure TypedScheme where
  SecretKey : Type
  Signature : Type
  encodeSignature : Signature → List Bool
  encodeSignature_injective : Function.Injective encodeSignature
  keygen : OracleComp Spec (PublicKey × SecretKey)
  sign : SecretKey → Message → OracleComp Spec (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp Spec Bool

namespace TypedScheme

/-- A one-signature attacker. -/
structure Adversary (S : TypedScheme) where
  State : Type
  choose : PublicKey → OracleComp Spec (Message × State)
  forge : State → Option S.Signature → OracleComp Spec (Message × S.Signature)

/-- The strong-forgery experiment. -/
def experiment (S : TypedScheme) (A : S.Adversary) : OracleComp Spec Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

def Secure (S : TypedScheme) : Prop :=
  ∀ (A : S.Adversary) (B : ℕ), CostAtMost (S.experiment A) B →
    probTrue (S.experiment A) < (B : ℝ≥0∞) / 2 ^ securityBits

def VerifyCostAtMost (S : TypedScheme) (c : ℕ) : Prop :=
  ∀ pk m σ, CostAtMost (S.verify pk m σ) c

def VerifyDeterministic (S : TypedScheme) : Prop :=
  ∀ pk m σ, Deterministic (S.verify pk m σ)

def KeygenCostAtMost (S : TypedScheme) (b : ℕ) : Prop := CostAtMost S.keygen b

def SignCostAtMost (S : TypedScheme) (b : ℕ) : Prop :=
  ∀ sk m, CostAtMost (S.sign sk m) b

def SignatureSizeAtMost (S : TypedScheme) (n : ℕ) : Prop :=
  ∀ sk m σ, some σ ∈ support (S.sign sk m) → (S.encodeSignature σ).length ≤ n

def RejectsOversized (S : TypedScheme) (n : ℕ) : Prop :=
  ∀ pk m σ, n < (S.encodeSignature σ).length → true ∉ support (S.verify pk m σ)

def Correct (S : TypedScheme) : Prop := ∀ message : PublicKey → Message,
  probTrue (do
    let (pk, sk) ← S.keygen
    let m := message pk
    let σ ← S.sign sk m
    match σ with
    | none => return false
    | some s => return !(← S.verify pk m s)) = 0

def SigningFailureAtMost (S : TypedScheme) (ε : ℝ≥0∞) : Prop :=
  ∀ message : PublicKey → Message,
  probTrue (do
    let (pk, sk) ← S.keygen
    return (← S.sign sk (message pk)).isNone) ≤ ε

/-- Every requirement except security, with signing failure at most `ε`. -/
structure Admissible (S : TypedScheme) (ε : ℝ≥0∞) : Prop where
  failure_lt_one : ε < 1
  correct : S.Correct
  verifyDeterministic : S.VerifyDeterministic
  signingFailure : S.SigningFailureAtMost ε
  signatureSize : S.SignatureSizeAtMost maxSignatureBits
  rejectsOversized : S.RejectsOversized maxSignatureBits
  keygenCost : S.KeygenCostAtMost keygenBudget
  signCost : S.SignCostAtMost signBudget

end TypedScheme

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.Adapter; SHA256 a461f9ce3805cdc5964306c7396ffb8a1b3ab279e6b7da4c705de3926688f10c. -/
section

/-!
Every DAG scheme defines a generic oracle algorithm with the same wire data and oracle programs.
The embedding preserves and reflects strong security; it does not establish generic admissibility.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace AlgorithmAdapter

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- The DAG signature's actual wire contents: nonce bits followed by disclosed bits. -/
def encodeSignature (σ : Signature) : List Bool := toBits σ.1 ++ σ.2

theorem toBits_injective {n : ℕ} : Function.Injective (@toBits n) := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h' := congrArg (fun l : List Bool => l[i]?) h
  simpa [toBits, hi] using h'

theorem encodeSignature_injective : Function.Injective (@encodeSignature) := by
  intro a b h
  have hn : toBits a.1 = toBits b.1 := by
    have ht := congrArg (List.take nonceBits) h
    simpa [encodeSignature, toBits] using ht
  have hp := toBits_injective hn
  have ht : a.2 = b.2 := by
    exact List.append_cancel_left (by simpa only [encodeSignature, hn] using h)
  exact Prod.ext hp ht

@[simp] theorem length_encodeSignature (σ : Signature) :
    (encodeSignature σ).length = nonceBits + σ.2.length := by
  simp [encodeSignature, toBits]

end AlgorithmAdapter

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- Same key generation, signing, verification and wire data; only the interface changes. -/
def Dag.Scheme.toAlgorithm (S : Scheme) : TypedScheme where
  SecretKey := S.graph.Assignment
  Signature := Signature
  encodeSignature := AlgorithmAdapter.encodeSignature
  encodeSignature_injective := AlgorithmAdapter.encodeSignature_injective
  keygen := S.keygen
  sign := S.sign
  verify := S.verify

namespace AlgorithmAdapter

variable (S : Scheme)

def toDAGAdversary (A : S.toAlgorithm.Adversary) : Adversary where
  State := A.State
  choose := A.choose
  forge := A.forge

def fromDAGAdversary (A : Adversary) : S.toAlgorithm.Adversary where
  State := A.State
  choose := A.choose
  forge := A.forge

/-- The adapter preserves the entire forgery experiment, including every party's queries. -/
theorem experiment_eq (A : S.toAlgorithm.Adversary) :
    S.toAlgorithm.experiment A = experiment S (toDAGAdversary S A) := by
  simp only [TypedScheme.experiment, experiment, Scheme.toAlgorithm, toDAGAdversary]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr
  intro ok
  congr 1
  by_cases h : signed.map (fun s => (chosen.1, s)) ≠ some (forged.1, forged.2) <;> simp [h]

theorem experiment_fromDAG_eq (A : Adversary) :
    S.toAlgorithm.experiment (fromDAGAdversary S A) = experiment S A := by
  simp only [TypedScheme.experiment, experiment, Scheme.toAlgorithm, fromDAGAdversary]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr
  intro ok
  congr 1
  by_cases h : signed.map (fun s => (chosen.1, s)) ≠ some (forged.1, forged.2) <;> simp [h]

/-- The embedding preserves and reflects the exact security requirement. -/
theorem secure_iff : S.toAlgorithm.Secure ↔ S.Secure := by
  constructor
  · intro h A B hB
    have he := experiment_fromDAG_eq S A
    rw [← he] at hB ⊢
    exact h (fromDAGAdversary S A) B hB
  · intro h A B hB
    rw [experiment_eq] at hB ⊢
    exact h (toDAGAdversary S A) B hB

end AlgorithmAdapter
end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.AlgorithmCosts; SHA256 22c47a6576cd80d9d272b123cfb9f9df19219a3281ed6ed3b21869522e8c704f. -/
section

/-! Pathwise query-cost bounds for the DAG-to-algorithm adapter.
The bounds cover every oracle-answer path; private randomness costs zero. -/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace AlgorithmCosts

/-! ## Generic rules for `CostAtMost` -/

section Generic

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable {α β : Type}

theorem CostAtMost.mono {oa : OracleComp Spec α} {b b' : ℕ} (h : CostAtMost oa b)
    (hb : b ≤ b') : CostAtMost oa b' := by
  induction oa using OracleComp.inductionOn generalizing b b' with
  | pure _ => trivial
  | query_bind t mx ih =>
      unfold CostAtMost at h ⊢
      rw [isQueryBound_query_bind_iff] at h ⊢
      exact ⟨le_trans h.1 hb, fun u => ih u (h.2 u) (by omega)⟩

theorem costAtMost_pure (x : α) (b : ℕ) : CostAtMost (pure x : OracleComp Spec α) b :=
  trivial

theorem CostAtMost.bind {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    {b₁ b₂ : ℕ} (h₁ : CostAtMost oa b₁) (h₂ : ∀ x, CostAtMost (ob x) b₂) :
    CostAtMost (oa >>= ob) (b₁ + b₂) :=
  isQueryBound_bind (· + ·)
    (fun _ _ _ _ h => ⟨le_add_left h, le_add_right h⟩)
    (fun _ _ _ _ h => ⟨by omega, by omega⟩) h₁ h₂

theorem costAtMost_map_iff (oa : OracleComp Spec α) (f : α → β) (b : ℕ) :
    CostAtMost (f <$> oa) b ↔ CostAtMost oa b :=
  isQueryBound_map_iff _ _ _ _ _

theorem CostAtMost.map {oa : OracleComp Spec α} {b : ℕ} (h : CostAtMost oa b)
    (f : α → β) : CostAtMost (f <$> oa) b :=
  (costAtMost_map_iff oa f b).2 h

theorem costAtMost_liftM_probComp (mx : ProbComp α) (b : ℕ) :
    CostAtMost (liftM mx : OracleComp Spec α) b := by
  change CostAtMost (liftComp mx Spec) b
  induction mx using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [liftComp_bind]
      have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
          (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
        simp [liftComp]; rfl
      rw [hq]
      unfold CostAtMost at ih ⊢
      rw [isQueryBound_query_bind_iff]
      exact ⟨by simp [queryCost], fun u => by simpa [queryCost] using ih u⟩

theorem costAtMost_hash {k : ℕ} (u : BitVec k) {b : ℕ} (hb : blockCost k ≤ b) :
    CostAtMost (hash u) b := by
  unfold CostAtMost hash
  rw [isQueryBound_query_iff]
  exact hb

theorem CostAtMost.bind_le {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    {b₁ b₂ b : ℕ} (h₁ : CostAtMost oa b₁) (h₂ : ∀ x, CostAtMost (ob x) b₂)
    (h : b₁ + b₂ ≤ b) : CostAtMost (oa >>= ob) b :=
  CostAtMost.mono (CostAtMost.bind h₁ h₂) h

theorem costAtMost_foldlM {γ δ : Type} (f : γ → δ → OracleComp Spec γ) (c : δ → ℕ)
    (hf : ∀ x a, CostAtMost (f x a) (c a)) :
    ∀ (l : List δ) (init : γ), CostAtMost (l.foldlM f init) (l.map c).sum
  | [], _ => costAtMost_pure _ _
  | a :: l, init => by
      rw [List.foldlM_cons, List.map_cons, List.sum_cons]
      exact CostAtMost.bind (hf init a) fun y => costAtMost_foldlM f c hf l y

end Generic

/-! ## Graph computations -/

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

theorem costAtMost_evalNode (x : G.Assignment) (v : Fin G.size)
    (s : OracleComp Spec (BitVec (G.len v))) (hs : CostAtMost s 0) :
    CostAtMost (G.evalNode x v s) (G.nodeCost v) := by
  unfold Graph.evalNode Graph.nodeCost
  cases G.kind v with
  | source => exact hs
  | det => exact costAtMost_pure _ _
  | hash p _ h => exact CostAtMost.map (costAtMost_hash _ le_rfl) _

theorem costAtMost_sampleAssignment : CostAtMost G.sampleAssignment 0 := by
  unfold Graph.sampleAssignment
  have := costAtMost_foldlM
    (fun (z : G.Assignment) v => Function.update z v <$> sampleBits (G.len v)) (fun _ => 0)
    (fun _ _ => CostAtMost.map (costAtMost_liftM_probComp _ _) _) (List.finRange G.size) (fun _ => 0)
  simpa using this

theorem costAtMost_evaluate (z : G.Assignment) : CostAtMost (G.evaluate z) G.keygenCost := by
  unfold Graph.evaluate
  have := costAtMost_foldlM
    (fun (x : G.Assignment) v => Function.update x v <$> G.evalNode x v (pure (z v)))
    G.nodeCost (fun x v => CostAtMost.map (costAtMost_evalNode G x v _ (costAtMost_pure _ _)) _)
    (List.finRange G.size) (fun _ => 0)
  rwa [Graph.keygenCost, Fin.sum_univ_def]

theorem costAtMost_keygen : CostAtMost G.keygen G.keygenCost :=
  CostAtMost.bind_le (costAtMost_sampleAssignment G) (fun z => costAtMost_evaluate G z) (by simp)

theorem costAtMost_reconstruct (A : Finset (Fin G.size)) (given : G.Assignment) :
    CostAtMost (G.reconstruct A given) (G.reconstructCost A) := by
  unfold Graph.reconstruct
  refine CostAtMost.mono (costAtMost_foldlM _
    (fun v => if v ∈ A then 0 else if G.Visited A v then G.nodeCost v else 0)
    (fun x v => ?_) (List.finRange G.size) (fun _ => 0)) (le_of_eq ?_)
  · split_ifs
    · exact costAtMost_pure _ _
    · exact CostAtMost.map (costAtMost_evalNode G x v _ (costAtMost_pure _ _)) _
    · exact costAtMost_pure _ _
  · rw [← Fin.sum_univ_def, Graph.reconstructCost, Graph.evaluated, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h₁ : v ∈ A <;> by_cases h₂ : G.Visited A v <;> simp [h₁, h₂]

end Dag.Graph

/-! ## Signing and verification -/

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem costAtMost_index (hidx : blockCost (msgBits + nonceBits) = 1)
    (m : Message) (η : Nonce) : CostAtMost (index m η) 1 :=
  CostAtMost.map (costAtMost_hash _ hidx.le) _

namespace Dag.Scheme

variable (S : Scheme)

theorem costAtMost_keygen : CostAtMost S.keygen keygenBudget :=
  CostAtMost.mono (CostAtMost.bind_le (Graph.costAtMost_keygen S.graph)
    (fun _ => costAtMost_pure _ 0) (by simp)) S.keygen_le

theorem costAtMost_signLoop (hidx : blockCost (msgBits + nonceBits) = 1)
    (x : S.graph.Assignment) (m : Message) :
    ∀ k tried, CostAtMost (S.signLoop x m k tried) k
  | 0, _ => costAtMost_pure _ _
  | k + 1, tried => by
      rw [Scheme.signLoop]
      split_ifs
      · refine CostAtMost.bind_le (costAtMost_liftM_probComp _ 0) (b₂ := k + 1) (fun j => ?_) (by simp)
        refine CostAtMost.bind_le (costAtMost_index hidx _ _) (b₂ := k) (fun i => ?_) (by omega)
        split_ifs with hi
        · exact costAtMost_pure _ _
        · exact costAtMost_signLoop hidx x m k _
      · exact costAtMost_pure _ _

theorem costAtMost_sign (hidx : blockCost (msgBits + nonceBits) = 1)
    (x : S.graph.Assignment) (m : Message) : CostAtMost (S.sign x m) trials :=
  costAtMost_signLoop S hidx x m _ _

theorem costAtMost_verify (hidx : blockCost (msgBits + nonceBits) = 1) {v : ℕ}
    (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) (pk : PublicKey) (m : Message)
    (σ : Signature) : CostAtMost (S.verify pk m σ) (1 + v) := by
  unfold Scheme.verify
  refine CostAtMost.bind_le (costAtMost_index hidx _ _) (b₂ := v) (fun i => ?_) le_rfl
  split_ifs with hi
  · dsimp only
    split_ifs
    · exact CostAtMost.bind_le
        (CostAtMost.mono (Graph.costAtMost_reconstruct S.graph (S.sets ⟨i, hi⟩) _) (hv _))
        (fun _ => costAtMost_pure _ 0) (by simp)
    · exact costAtMost_pure _ _
  · exact costAtMost_pure _ _

end Dag.Scheme

end AlgorithmCosts
end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.Cache; SHA256 3b4b18e5b1855b396872b3d38660e3f38ca0266ea11f8e7d76ea04928cdef9da. -/
section

/-!
# Caches of the lazy random oracle

Generic facts about `oracleImpl` (the lazy random oracle of `OptimalOTS.Dag`) used by the
security proof of the concrete scheme:

* `extend c f` overlays the cache `f` under the cache `c` (entries of `c` take priority);
* `Hits c f` says that some point cached in `f` is also cached in `c`;
* the one-step run lemmas of `oracleImpl`;
* runs only grow the cache (`sub_of_mem_support_run`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- The cache of the random oracle. -/
abbrev Cache := (hashSpec).QueryCache

/-- The lazy random oracle run from cache `c`. -/
abbrev run {α : Type} (oa : OracleComp Spec α) (c : Cache) :
    ProbComp (α × Cache) :=
  (simulateQ (oracleImpl) oa).run c

namespace Cache


/-- Overlay `f` under `c`: entries of `c` take priority. -/
def extend (c f : Cache) : Cache := fun q => (c q).or (f q)

/-- Some point cached in `f` is cached in `c`. -/
def Hits (c f : Cache) : Prop := ∃ q, (f q).isSome ∧ (c q).isSome

/-- `c` has no point in common with `f`. -/
def Disjoint (c f : Cache) : Prop := ∀ q, (f q).isSome → c q = none

/-- Every entry of `c` is an entry of `c'`. -/
def Sub (c c' : Cache) : Prop := ∀ q u, c q = some u → c' q = some u

theorem Sub.refl (c : Cache) : Sub c c := fun _ _ h => h

theorem Sub.trans {c₁ c₂ c₃ : Cache} (h₁ : Sub c₁ c₂) (h₂ : Sub c₂ c₃) : Sub c₁ c₃ :=
  fun q u h => h₂ q u (h₁ q u h)

theorem Sub.isSome {c c' : Cache} (h : Sub c c') {q : Query} (hq : (c q).isSome) :
    (c' q).isSome := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hq
  rw [h q u hu]; rfl

@[simp] theorem extend_apply (c f : Cache) (q : Query) : extend c f q = (c q).or (f q) := rfl

theorem extend_apply_of_some {c f : Cache} {q : Query} {u : BitVec hashBits}
    (h : c q = some u) : extend c f q = some u := by simp [extend, h]

theorem extend_apply_of_none {c f : Cache} {q : Query} (h : c q = none) :
    extend c f q = f q := by simp [extend, h]

@[simp] theorem extend_empty (c : Cache) : extend c ∅ = c := by
  funext q; simp [extend]

@[simp] theorem empty_extend (f : Cache) : extend ∅ f = f := by
  funext q; simp [extend]

theorem extend_cacheQuery (c f : Cache) (q : Query) (u : BitVec hashBits) :
    extend (c.cacheQuery q u) f = (extend c f).cacheQuery q u := by
  funext q'
  by_cases h : q' = q
  · subst h; simp [extend]
  · simp [extend, QueryCache.cacheQuery_of_ne _ _ h]

theorem extend_assoc (c f g : Cache) : extend (extend c f) g = extend c (extend f g) := by
  funext q; simp [extend, Option.or_assoc]

theorem extend_isSome (c f : Cache) (q : Query) :
    (extend c f q).isSome ↔ (c q).isSome ∨ (f q).isSome := by
  simp [extend, Option.isSome_or]

theorem not_hits_empty (f : Cache) : ¬ Hits ∅ f := by
  rintro ⟨q, -, h⟩; simp at h

theorem Disjoint.not_hits {c f : Cache} (h : Disjoint c f) : ¬ Hits c f := by
  rintro ⟨q, hf, hc⟩
  rw [h q hf] at hc; simp at hc

theorem hits_cacheQuery (c f : Cache) (q : Query) (u : BitVec hashBits) :
    Hits (c.cacheQuery q u) f ↔ Hits c f ∨ (f q).isSome := by
  constructor
  · rintro ⟨q', hf, hc⟩
    by_cases h : q' = q
    · subst h; exact Or.inr hf
    · rw [QueryCache.cacheQuery_of_ne _ _ h] at hc
      exact Or.inl ⟨q', hf, hc⟩
  · rintro (⟨q', hf, hc⟩ | hf)
    · by_cases h : q' = q
      · subst h; exact ⟨q', hf, by simp⟩
      · exact ⟨q', hf, by rw [QueryCache.cacheQuery_of_ne _ _ h]; exact hc⟩
    · exact ⟨q, hf, by simp⟩

theorem hits_extend (c f g : Cache) : Hits (extend c f) g ↔ Hits c g ∨ Hits f g := by
  constructor
  · rintro ⟨q, hg, hc⟩
    rw [extend_isSome] at hc
    rcases hc with hc | hc
    · exact Or.inl ⟨q, hg, hc⟩
    · exact Or.inr ⟨q, hg, hc⟩
  · rintro (⟨q, hg, hc⟩ | ⟨q, hg, hc⟩)
    · exact ⟨q, hg, (extend_isSome c f q).2 (Or.inl hc)⟩
    · exact ⟨q, hg, (extend_isSome c f q).2 (Or.inr hc)⟩

theorem disjoint_cacheQuery {c f : Cache} (h : Disjoint c f) {q : Query}
    (hq : f q = none) (u : BitVec hashBits) : Disjoint (c.cacheQuery q u) f := by
  intro q' hq'
  have hne : q' ≠ q := fun e => by rw [e, hq] at hq'; simp at hq'
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact h q' hq'

theorem sub_cacheQuery_of_none {c : Cache} {q : Query} (h : c q = none)
    (u : BitVec hashBits) : Sub c (c.cacheQuery q u) := by
  intro q' u' hq'
  have hne : q' ≠ q := fun e => by rw [e, h] at hq'; cases hq'
  rw [QueryCache.cacheQuery_of_ne _ _ hne]; exact hq'

end Cache

/-! ## One-step run lemmas for the lazy oracle -/

theorem oracleImpl_run_inl (c : Cache) (t : ℕ) :
    (oracleImpl (.inl t)).run c =
      HasQuery.query (spec := unifSpec) (m := ProbComp) t >>= fun u => pure (u, c) := by
  simp [oracleImpl, StateT.run_monadLift]

theorem oracleImpl_run_inr_none {c : Cache} {q : Query} (hc : c q = none) :
    (oracleImpl (.inr q)).run c =
      ($ᵗ BitVec hashBits) >>= fun u => pure (u, c.cacheQuery q u) := by
  have := randomOracle.run_eq (spec₀ := hashSpec) q c
  rw [hc] at this
  exact this

theorem oracleImpl_run_inr_some {c : Cache} {q : Query} {u : BitVec hashBits}
    (hc : c q = some u) : (oracleImpl (.inr q)).run c = pure (u, c) := by
  have := randomOracle.run_eq (spec₀ := hashSpec) q c
  rw [hc] at this
  exact this

theorem run_pure {α : Type} (x : α) (c : Cache) :
    run (pure x) c = pure (x, c) := by
  simp [run]

theorem run_query_bind {α : Type} (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) :
    run (liftM (Spec.query t) >>= k) c =
      (oracleImpl t).run c >>= fun p => run (k p.1) p.2 := by
  simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem run_bind {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (c : Cache) :
    run (oa >>= k) c = run oa c >>= fun p => run (k p.1) p.2 := by
  simp only [run, simulateQ_bind, StateT.run_bind]

theorem run_map {α β : Type} (oa : OracleComp Spec α) (f : α → β)
    (c : Cache) :
    run (f <$> oa) c = (fun p => (f p.1, p.2)) <$> run oa c := by
  simp only [run, simulateQ_map, StateT.run_map]

theorem run'_eq {α : Type} (oa : OracleComp Spec α) (c : Cache) :
    (simulateQ (oracleImpl) oa).run' c = Prod.fst <$> run oa c := by
  simp [run, StateT.run'_eq]

/-- A lifted `ProbComp` runs unchanged and leaves the cache alone. -/
theorem run_liftM {α : Type} (pc : ProbComp α) (c : Cache) :
    run (liftM pc : OracleComp Spec α) c = (fun x => (x, c)) <$> pc := by
  change run (liftComp pc Spec) c = _
  induction pc using OracleComp.inductionOn generalizing c with
  | pure x => simp [liftComp, run_pure]
  | query_bind t mx ih =>
    rw [liftComp_bind]
    have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
        (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
      simp [liftComp]; rfl
    rw [hq, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, ih, map_bind]
    rfl

/-- Runs only grow the cache. -/
theorem sub_of_mem_support_run {α : Type} (oa : OracleComp Spec α) :
    ∀ (c : Cache) (p : α × Cache), p ∈ support (run oa c) → Cache.Sub c p.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c p hp
    rw [run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact Cache.Sub.refl c
  | query_bind t k ih =>
    intro c p hp
    rw [run_query_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
    rcases t with t | q
    · rw [oracleImpl_run_inl, support_bind] at hu
      simp only [Set.mem_iUnion] at hu
      obtain ⟨w, -, hw⟩ := hu
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ih u _ p hp
    · rcases hc : c q with _ | v
      · rw [oracleImpl_run_inr_none hc, support_bind] at hu
        simp only [Set.mem_iUnion] at hu
        obtain ⟨w, -, hw⟩ := hu
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact (Cache.sub_cacheQuery_of_none hc u).trans (ih u _ p hp)
      · rw [oracleImpl_run_inr_some hc, support_pure] at hu
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact ih u _ p hp

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.Semantics; SHA256 6d9cc3050c4df3e9a23d15ac856b9c82e375b4a4ef34936d80f934d6a30d438e. -/
section

/-!
# Pure semantics of computation graphs

Records and deterministic evaluation, used to analyse the model:

* a *record* `ξ : G.Rec` gives a value for every node (only sources matter) and an oracle output
  for every node (only hash nodes matter);
* `evalWith val` evaluates the nodes in order with the local value functions `val`, and
  satisfies the node equations when every `val v` only reads the parents of `v`
  (`evalWith_apply`); `evalRec ξ` is the evaluation of a record.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Dag.NodeKind

variable {N : ℕ} {len : Fin N → ℕ} {v : Fin N}

/-- Length of the oracle input of a node: the parent's length for a hash node, else zero. -/
def inLen : NodeKind N len v → ℕ
  | hash p _ _ => len p
  | _ => 0

/-- The oracle input of a node under the assignment `x`. -/
def input : (k : NodeKind N len v) → ((w : Fin N) → BitVec (len w)) → BitVec k.inLen
  | hash p _ _, x => x p
  | source, _ => 0
  | det _ _ _ _, _ => 0

/-- The value of a node from the values `x` of the other nodes, a source value `s` and an oracle
answer `a`. -/
def value : NodeKind N len v →
    ((w : Fin N) → BitVec (len w)) → BitVec (len v) → BitVec hashBits → BitVec (len v)
  | source, _, s, _ => s
  | det _ _ f _, x, _, _ => f x
  | hash _ _ h, _, _, a => a.cast h.symm

/-- Parents precede their child. -/
theorem lt_of_mem_parents : ∀ (k : NodeKind N len v) {w : Fin N}, w ∈ k.parents → w < v
  | source, _, h => by simp [parents] at h
  | det _ hlt _ _, _, h => hlt _ h
  | hash _ hlt _, _, h => by simp only [parents, Finset.mem_singleton] at h; exact h ▸ hlt

/-- The value computed from an assignment (with oracle answers depending on the node's input)
only depends on the parents' values. -/
theorem value_input_congr (k : NodeKind N len v) (s : BitVec (len v))
    (t : BitVec k.inLen → BitVec hashBits) (x y : (w : Fin N) → BitVec (len w))
    (h : ∀ w ∈ k.parents, x w = y w) :
    k.value x s (t (k.input x)) = k.value y s (t (k.input y)) := by
  cases k with
  | source => rfl
  | det ps _ f hf => exact hf x y h
  | hash p _ hl =>
    simp only [value, input]
    rw [h p (by simp [parents])]

/-- The value computed from an assignment with a fixed oracle answer only depends on the
parents' values. -/
theorem value_congr (k : NodeKind N len v) (s : BitVec (len v)) (a : BitVec hashBits)
    (x y : (w : Fin N) → BitVec (len w)) (h : ∀ w ∈ k.parents, x w = y w) :
    k.value x s a = k.value y s a :=
  value_input_congr k s (fun _ => a) x y h

end Dag.NodeKind

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- Records: a value for every node and an oracle output for every node. -/
abbrev Rec := G.Assignment × (Fin G.size → BitVec hashBits)

/-- Value functions computing each node from an assignment. -/
abbrev ValFn := (v : Fin G.size) → G.Assignment → BitVec (G.len v)

/-- Evaluate the nodes in order with the value functions `val`. -/
def evalWith (val : G.ValFn) : G.Assignment :=
  (List.finRange G.size).foldl (fun x v => Function.update x v (val v x)) (fun _ => 0)

/-- `val v` only depends on the values of the parents of `v`. -/
def ParentLocal (val : G.ValFn) : Prop :=
  ∀ v x x', (∀ w ∈ (G.kind v).parents, x w = x' w) → val v x = val v x'

/-- Evaluation of a record: sources from `ξ.1`, hash nodes from `ξ.2`. -/
def recVal (ξ : G.Rec) : G.ValFn := fun v x => (G.kind v).value x (ξ.1 v) (ξ.2 v)

/-- The node values determined by a record. -/
def evalRec (ξ : G.Rec) : G.Assignment := G.evalWith (G.recVal ξ)

/-! ## Evaluation -/

theorem parentLocal_recVal (ξ : G.Rec) : G.ParentLocal (G.recVal ξ) := by
  intro v x x' h
  exact NodeKind.value_congr _ _ _ x x' h

/-- Folding the evaluation step over an increasing list yields an assignment satisfying the node
equations at the nodes of the list. -/
theorem foldl_step_apply {val : G.ValFn} (hval : G.ParentLocal val) (l : List (Fin G.size))
    (hl : l.Pairwise (· < ·)) (x : G.Assignment) :
    ∀ w ∈ l, (l.foldl (fun x v => Function.update x v (val v x)) x) w =
      val w (l.foldl (fun x v => Function.update x v (val v x)) x) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.pairwise_append] at hl
    obtain ⟨hl, -, hla⟩ := hl
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set R := l.foldl (fun x v => Function.update x v (val v x)) x
    have hagree : ∀ u, u < a → Function.update R a (val a R) u = R u := fun u hu =>
      Function.update_of_ne (ne_of_lt hu) _ _
    intro w hw
    rw [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · have hwa : w < a := hla w hw a (List.mem_singleton_self a)
      rw [hagree w hwa, ih hl w hw]
      exact hval w _ _ fun u hu =>
        (hagree u (lt_trans ((G.kind w).lt_of_mem_parents hu) hwa)).symm
    · rw [Function.update_self]
      exact hval w _ _ fun u hu => (hagree u ((G.kind w).lt_of_mem_parents hu)).symm

/-- Evaluation satisfies the node equations. -/
theorem evalWith_apply {val : G.ValFn} (hval : G.ParentLocal val) (v : Fin G.size) :
    G.evalWith val v = val v (G.evalWith val) := by
  exact G.foldl_step_apply hval _ (List.pairwise_lt_finRange _) _ v (List.mem_finRange v)

/-- The node equation of a record. -/
theorem evalRec_apply (ξ : G.Rec) (v : Fin G.size) :
    G.evalRec ξ v = (G.kind v).value (G.evalRec ξ) (ξ.1 v) (ξ.2 v) :=
  G.evalWith_apply (G.parentLocal_recVal ξ) v

end Dag.Graph

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.KeygenSupport; SHA256 2c2dec264b924b82c068500a47bf754efe314356afdb559f6fd827309b87024c. -/
section

/-! Key generation satisfies its node equations in the final cache, including repeated inputs. -/

open OracleSpec OracleComp ENNReal

noncomputable section
open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- The equations at one node, using answers actually present in the cache. -/
def CacheEqAt (c : Cache) (x : G.Assignment) (v : Fin G.size) : Prop :=
  match G.kind v with
  | .source => True
  | .det _ _ f _ => x v = f x
  | .hash p _ hl => c ⟨G.len p, x p⟩ = some ((x v).cast hl)

def CacheConsistent (x : G.Assignment) (c : Cache) : Prop := ∀ v, G.CacheEqAt c x v

theorem CacheEqAt.mono {c d : Cache} (hcd : Cache.Sub c d)
    {x : G.Assignment} {v : Fin G.size} (h : G.CacheEqAt c x v) : G.CacheEqAt d x v := by
  unfold CacheEqAt at h ⊢
  cases hk : G.kind v with
  | source => trivial
  | det => simpa only [hk] using h
  | hash p hp hl =>
    simp only [hk] at h
    exact hcd _ _ h

theorem CacheEqAt.congr {c : Cache} {x y : G.Assignment} {v : Fin G.size}
    (hxy : ∀ w, w ≤ v → y w = x w) (h : G.CacheEqAt c x v) : G.CacheEqAt c y v := by
  unfold CacheEqAt at h ⊢
  cases hk : G.kind v with
  | source => trivial
  | det ps hps f hf =>
    simp only [hk] at h
    rw [hxy v le_rfl, h]
    exact hf x y fun w hw => (hxy w (hps w hw).le).symm
  | hash p hp hl =>
    simp only [hk] at h
    change c ⟨G.len p, y p⟩ = some ((y v).cast hl)
    rw [hxy p hp.le, hxy v le_rfl]
    exact h

theorem CacheConsistent.mono {c d : Cache} (hcd : Cache.Sub c d)
    {x : G.Assignment} (h : G.CacheConsistent x c) : G.CacheConsistent x d :=
  fun v => CacheEqAt.mono G hcd (h v)

theorem hash_support {k : ℕ} (u : BitVec k) (c : Cache) :
    ∀ p ∈ support (run (hash u) c), Cache.Sub c p.2 ∧ p.2 ⟨k, u⟩ = some p.1 := by
  intro p hp
  have hsub := sub_of_mem_support_run (hash u) c p hp
  refine ⟨hsub, ?_⟩
  unfold hash run at hp
  rw [simulateQ_spec_query] at hp
  rcases hc : c ⟨k, u⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨w, _, hp⟩ := hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    simp
  · rw [oracleImpl_run_inr_some hc, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact hc

def evalStep (z x : G.Assignment) (v : Fin G.size) : OracleComp Spec G.Assignment :=
  Function.update x v <$> G.evalNode x v (pure (z v))

theorem evalStep_support (z x : G.Assignment) (v : Fin G.size) (c : Cache) :
    ∀ p ∈ support (run (G.evalStep z x v) c),
      Cache.Sub c p.2 ∧ (∀ w, w ≠ v → p.1 w = x w) ∧ G.CacheEqAt p.2 p.1 v := by
  intro p hp
  unfold evalStep evalNode at hp
  cases hk : G.kind v with
  | source =>
    simp only [hk, map_pure, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, fun w hw => Function.update_of_ne hw _ _, by simp [CacheEqAt, hk]⟩
  | det ps hps f hf =>
    simp only [hk, map_pure, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl c, fun w hw => Function.update_of_ne hw _ _, ?_⟩
    simp only [CacheEqAt, hk, Function.update_self]
    exact hf x _ fun w hw => (Function.update_of_ne (ne_of_lt (hps w hw)) _ _).symm
  | hash q hq hl =>
    simp only [hk, run_map, support_map, Set.mem_image] at hp
    obtain ⟨⟨a, d⟩, ⟨⟨w, d'⟩, hw, he⟩, he'⟩ := hp
    cases he
    cases he'
    obtain ⟨hsub, hw⟩ := hash_support (x q) c _ hw
    refine ⟨hsub, fun w hw => Function.update_of_ne hw _ _, ?_⟩
    have hne : q ≠ v := ne_of_lt hq
    simp only [CacheEqAt, hk, Function.update_self, BitVec.cast_cast, BitVec.cast_eq]
    rw [Function.update_of_ne hne]
    exact hw

theorem evalFold_support (z : G.Assignment) (c : Cache)
    (l : List (Fin G.size)) (hl : l.Pairwise (· < ·)) :
    ∀ p ∈ support (run (l.foldlM (G.evalStep z) (fun _ => 0)) c),
      Cache.Sub c p.2 ∧ (∀ v ∈ l, G.CacheEqAt p.2 p.1 v) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro p hp
    rw [List.foldlM_nil, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, fun v hv => by simp at hv⟩
  | append_singleton l a ih =>
    rw [List.pairwise_append] at hl
    obtain ⟨hl, _, hla⟩ := hl
    intro p hp
    rw [List.foldlM_append, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨x, d⟩, hx, hp⟩ := hp
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at hp
    obtain ⟨hsub, heq⟩ := ih hl _ hx
    obtain ⟨hsub', hne, ha⟩ := G.evalStep_support z x a d p hp
    refine ⟨hsub.trans hsub', fun v hv => ?_⟩
    rw [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · have hva : v < a := hla v hv a (List.mem_singleton_self a)
      exact CacheEqAt.congr G (fun w hw => hne w (ne_of_lt (hw.trans_lt hva)))
        (CacheEqAt.mono G hsub' (heq v hv))
    · exact ha

theorem evaluate_cacheConsistent (z : G.Assignment) (c : Cache) :
    ∀ p ∈ support (run (G.evaluate z) c), G.CacheConsistent p.1 p.2 := by
  intro p hp
  have h := G.evalFold_support z c _ (List.pairwise_lt_finRange _) p hp
  exact fun v => h.2 v (List.mem_finRange v)

end Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem Dag.Scheme.keygen_cacheConsistent (S : Scheme) (c : Cache) :
    ∀ p ∈ support (run S.keygen c),
      p.1.1 = S.publicKey p.1.2 ∧ S.graph.CacheConsistent p.1.2 p.2 := by
  intro p hp
  simp only [Scheme.keygen, Graph.keygen, run_bind, support_bind, Set.mem_iUnion] at hp
  obtain ⟨⟨x, d⟩, ⟨⟨z, d'⟩, _, hx⟩, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact ⟨rfl, S.graph.evaluate_cacheConsistent z d' _ hx⟩

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.WeightedSampling; SHA256 ed52c935e9d5b7b26cfd8010d63d6c529daa28ae76604702a185d4f78e047b47. -/
section

/-! First-minimum selection with replacement. This is an executable oracle program
and basic structural/resource lemmas, not a security certificate. All trials run;
equal tiers retain their first occurrence. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling

variable {α : Type}

/-- Choose the lower rank; in a tie the left (earlier) value wins. -/
def best (rank : α → ℕ) : Option α → Option α → Option α
  | none, b => b
  | some a, none => some a
  | some a, some b => if rank a ≤ rank b then some a else some b

@[simp] theorem best_none_left (rank : α → ℕ) (b : Option α) :
    best rank none b = b := rfl

@[simp] theorem best_none_right (rank : α → ℕ) (a : Option α) :
    best rank a none = a := by cases a <;> rfl

theorem best_some_source (rank : α → ℕ) (a b : Option α) (v : α)
    (h : best rank a b = some v) : a = some v ∨ b = some v := by
  cases a with
  | none => exact Or.inr h
  | some a =>
    cases b with
    | none => exact Or.inl h
    | some b =>
      simp only [best] at h
      split_ifs at h <;> simp_all

theorem best_eq_none (rank : α → ℕ) (a b : Option α) :
    best rank a b = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp [best]
  split_ifs <;> simp

/-- Process the whole list; recursive unwinding keeps the earliest minimum. -/
def select (rank : α → ℕ) : List (Option α) → Option α
  | [] => none
  | a :: xs => best rank a (select rank xs)

theorem select_source (rank : α → ℕ) (xs : List (Option α)) (v : α)
    (h : select rank xs = some v) : some v ∈ xs := by
  induction xs with
  | nil => simp [select] at h
  | cons a xs ih =>
    rcases best_some_source rank a (select rank xs) v h with ha | ht
    · exact List.mem_cons.mpr (Or.inl ha.symm)
    · exact List.mem_cons.mpr (Or.inr (ih ht))

theorem select_none_iff (rank : α → ℕ) (xs : List (Option α)) :
    select rank xs = none ↔ ∀ a ∈ xs, a = none := by
  induction xs with
  | nil => simp [select]
  | cons a xs ih => simp only [select, best_eq_none, ih, List.forall_mem_cons]

theorem select_rank_le (rank : α → ℕ) (xs : List (Option α)) (v : α)
    (h : select rank xs = some v) :
    ∀ a, some a ∈ xs → rank v ≤ rank a := by
  induction xs generalizing v with
  | nil => simp [select] at h
  | cons b xs ih =>
    intro a ha
    rcases ht : select rank xs with _ | t
    · have hb : b = some v := by simpa [select, ht] using h
      rcases List.mem_cons.mp ha with ha | ha
      · rw [hb] at ha
        cases Option.some.inj ha
        exact le_rfl
      · have hn := (select_none_iff rank xs).mp ht _ ha
        cases hn
    · cases b with
      | none =>
        have hv : t = v := Option.some.inj (by simpa [select, ht] using h)
        subst v
        exact ih t ht a (by simpa using ha)
      | some b =>
        by_cases hb : rank b ≤ rank t
        · have hv : b = v := Option.some.inj (by simpa [select, best, ht, hb] using h)
          subst v
          rcases List.mem_cons.mp ha with ha | ha
          · cases Option.some.inj ha
            exact le_rfl
          · exact hb.trans (ih t ht a ha)
        · have hv : t = v := Option.some.inj (by simpa [select, best, ht, hb] using h)
          subst v
          rcases List.mem_cons.mp ha with ha | ha
          · cases Option.some.inj ha
            exact (lt_of_not_ge hb).le
          · exact ih t ht a ha

/-- Adding a first occurrence whose rank is no larger than the whole suffix
retains that occurrence, including ties and duplicate nonce draws. -/
theorem select_first (rank : α → ℕ) (v : α) (xs : List (Option α))
    (h : ∀ a, some a ∈ xs → rank v ≤ rank a) :
    select rank (some v :: xs) = some v := by
  rcases ht : select rank xs with _ | t
  · simp [select, ht]
  · have hvt := h t (select_source rank xs t ht)
    simp [select, best, ht, hvt]

variable {M : ℕ}

abbrev Nonce (n : ℕ) := BitVec n
abbrev Winner (n M : ℕ) := Nonce n × Fin M

def candidate {n : ℕ} (decode : BitVec hashBits → Option (Fin M)) (η : Nonce n)
    (w : BitVec hashBits) : Option (Winner n M) :=
  (fun i => (η, i)) <$> decode w

/-- Every recursive step samples one nonce independently, pays one hash query,
then chooses the earliest minimum after completing all remaining steps. -/
def loop (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) : ℕ → OracleComp Spec (Option (Winner n M))
  | 0 => pure none
  | k + 1 => do
      let η ← sampleBits n
      let w ← hash (m ++ η)
      let rest ← loop n decode tier m k
      return best (fun r => tier r.2) (candidate decode η w) rest

open AlgorithmCosts

theorem costAtMost_loop (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (hc : blockCost (msgBits + n) = 1) :
    ∀ k, CostAtMost (loop n decode tier m k) k
  | 0 => costAtMost_pure _ _
  | k + 1 => by
    rw [loop]
    refine CostAtMost.bind_le (costAtMost_liftM_probComp _ 0) (b₂ := k+1)
      (fun η => ?_) (by omega)
    refine CostAtMost.bind_le (costAtMost_hash _ hc.le) (b₂ := k)
      (fun w => ?_) (by omega)
    exact CostAtMost.bind_le (costAtMost_loop n decode tier m hc k)
      (fun _ => costAtMost_pure _ 0) (by simp)

theorem index86_cost : blockCost (msgBits + 86) = 1 := by
  norm_num [blockCost, msgBits, blockBits]

theorem costAtMost_loop86 (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) :
    CostAtMost (loop 86 decode tier m signBudget) signBudget :=
  costAtMost_loop 86 decode tier m index86_cost signBudget

theorem run_loop_succ (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (k : ℕ) (c : Cache) :
    run (loop n decode tier m (k+1)) c =
      ($ᵗ BitVec n : ProbComp (BitVec n)) >>= fun η =>
      run (hash (m ++ η)) c >>= fun q =>
      run (loop n decode tier m k) q.2 >>= fun r =>
      pure (best (fun s => tier s.2) (candidate decode η q.1) r.1, r.2) := by
  simp only [loop, run_bind, sampleBits, run_liftM, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind, run_pure]

/-- A returned nonce/class agrees with the actual shared-oracle cache. -/
theorem loop_support (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) :
    ∀ k c p, p ∈ support (run (loop n decode tier m k) c) →
      Cache.Sub c p.2 ∧
      (∀ η i, p.1 = some (η,i) →
        ∃ w, p.2 ⟨msgBits+n, m ++ η⟩ = some w ∧ decode w = some i) := by
  intro k
  induction k with
  | zero =>
    intro c p hp
    rw [loop, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact ⟨Cache.Sub.refl c, fun η i h => by cases h⟩
  | succ k ih =>
    intro c p hp
    rw [run_loop_succ, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨η, _, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨w,d⟩, hd, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨r,e⟩, hr, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst p
    obtain ⟨hcd, hwd⟩ := Dag.Graph.hash_support (m ++ η) c (w,d) hd
    obtain ⟨hde, hret⟩ := ih d (r,e) hr
    refine ⟨hcd.trans hde, ?_⟩
    intro ζ i hi
    rcases best_some_source (fun s : Winner n M => tier s.2)
      (candidate decode η w) r (ζ,i) hi with hf | ht
    · cases hw : decode w with
      | none => simp [candidate, hw] at hf
      | some j =>
        simp only [candidate, hw, Functor.map, Option.map, Option.some.injEq,
          Prod.mk.injEq] at hf
        obtain ⟨rfl,rfl⟩ := hf
        exact ⟨w, hde _ _ hwd, hw⟩
    · exact hret ζ i ht

theorem run_hash_extend {b : ℕ} (u : BitVec b) (c f : Cache)
    (hf : f ⟨b,u⟩ = none) :
    run (hash u) (Cache.extend c f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run (hash u) c := by
  unfold hash run
  rw [simulateQ_spec_query]
  rcases hc : c ⟨b,u⟩ with _ | w
  · have he : Cache.extend c f ⟨b,u⟩ = none := by
      rw [Cache.extend_apply_of_none hc, hf]
    rw [oracleImpl_run_inr_none hc, oracleImpl_run_inr_none he]
    simp only [map_bind, map_pure]
    exact bind_congr fun w => congrArg pure (congrArg (w, ·)
      (Cache.extend_cacheQuery c f ⟨b,u⟩ w).symm)
  · have he := Cache.extend_apply_of_some (f := f) hc
    rw [oracleImpl_run_inr_some hc, oracleImpl_run_inr_some he]
    rfl

/-- Graph caches are irrelevant when their input lengths differ from the
message/nonce input. No early-exit rejection assumption is used. -/
theorem run_loop_extend (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (f : Cache)
    (hf : ∀ η : Nonce n, f ⟨msgBits+n,m++η⟩ = none) :
    ∀ k c, run (loop n decode tier m k) (Cache.extend c f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run (loop n decode tier m k) c := by
  intro k
  induction k with
  | zero => intro c; simp [loop, run_pure]
  | succ k ih =>
    intro c
    rw [run_loop_succ, run_loop_succ, map_bind]
    refine bind_congr fun η => ?_
    rw [run_hash_extend _ c f (hf η)]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun q => ?_
    rw [ih]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

/-- The actual private randomness: independent uniform nonce draws, with repeats. -/
def drawList (n : ℕ) : ℕ → ProbComp (List (Nonce n))
  | 0 => pure []
  | k+1 => do
      let η ← ($ᵗ BitVec n : ProbComp (BitVec n))
      let xs ← drawList n k
      return η :: xs

theorem run_hash_cached {b : ℕ} (u : BitVec b) (c : Cache) (w : BitVec hashBits)
    (h : c ⟨b,u⟩ = some w) : run (hash u) c = pure (w,c) := by
  unfold hash run
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_some h

/-- For a fixed complete oracle row, the executable loop is precisely iid nonce
sampling followed by the first-minimum selector. The shared cache is unchanged.
This does not assert that a lazy row has an unconditional independent posterior. -/
theorem run_loop_fixed_row (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η)) :
    ∀ k, run (loop n decode tier m k) c =
      (fun xs => (select (fun r : Winner n M => tier r.2)
        (xs.map fun η => candidate decode η (table η)), c)) <$> drawList n k := by
  intro k
  induction k with
  | zero => simp [loop, drawList, select, run_pure]
  | succ k ih =>
    rw [run_loop_succ, drawList, map_bind]
    refine bind_congr fun η => ?_
    rw [run_hash_cached _ c (table η) (hc η), pure_bind, ih]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      List.map_cons, select]

#print axioms run_loop_fixed_row

#print axioms loop_support
#print axioms run_loop_extend

#print axioms select_source
#print axioms select_none_iff
#print axioms select_rank_le
#print axioms select_first
#print axioms costAtMost_loop86

end OptimalOTS.WeightedSampling
end
end

/- Original module: Submissions.UpperCompressions.IUB; SHA256 55d9abc33e22900fceb2a63ebb2fa9efcd66f78d84198d6f15f6b65c5373a7a9. -/
section

/-!
# Identical until bad

Running a computation from the cache `extend c f` (the entries of `f` are answered from `f`) is
bounded by running it from `c` alone (the same points get fresh answers), where every run that
ever queries a point of `f` is charged in full:

```
E[φ | run oa (extend c f)] ≤ E[fun (x, d) => if Hits d f then 1 else φ (x, extend d f) | run oa c]
```

for `φ ≤ 1` and `c` disjoint from `f`.  The two runs agree until the first query at a point of
`f`; from then on the right-hand side pays `1`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


/-- Expected value of `g` over a probabilistic computation. -/
abbrev E {α : Type} (p : ProbComp α) (g : α → ℝ≥0∞) : ℝ≥0∞ := expectedValue p g

theorem E_le_one {α : Type} (p : ProbComp α) {g : α → ℝ≥0∞} (hg : ∀ x, g x ≤ 1) : E p g ≤ 1 :=
  (expectedValue_le_of_le p hg).trans (by simp)

theorem E_bind {α β : Type} (p : ProbComp α) (k : α → ProbComp β) (g : β → ℝ≥0∞) :
    E (p >>= k) g = E p fun x => E (k x) g :=
  expectedValue_bind p k g

theorem E_pure {α : Type} (x : α) (g : α → ℝ≥0∞) : E (pure x) g = g x :=
  expectedValue_pure x g

theorem E_mono {α : Type} (p : ProbComp α) {g h : α → ℝ≥0∞} (hgh : ∀ x, g x ≤ h x) :
    E p g ≤ E p h :=
  expectedValue_mono p hgh

theorem E_map {α β : Type} (p : ProbComp α) (f : α → β) (g : β → ℝ≥0∞) :
    E (f <$> p) g = E p fun x => g (f x) :=
  expectedValue_map p f g

theorem E_const_le {α : Type} (p : ProbComp α) (c : ℝ≥0∞) : E p (fun _ => c) ≤ c :=
  expectedValue_le_of_le p fun _ => le_rfl

theorem E_uniform (n : ℕ) (g : BitVec n → ℝ≥0∞) :
    E ($ᵗ BitVec n) g = ∑ x, (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * g x := by
  rw [E, expectedValue_def, tsum_fintype]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [probOutput_uniformSample]

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- **Identical until bad.** -/
theorem iub {α : Type} (oa : OracleComp Spec α) (f : Cache)
    (φ : α × Cache → ℝ≥0∞) (hφ : ∀ p, φ p ≤ 1) :
    ∀ c : Cache, Cache.Disjoint c f →
      E (run oa (Cache.extend c f)) φ ≤
        E (run oa c) fun p => if Cache.Hits p.2 f then 1 else φ (p.1, Cache.extend p.2 f) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c hc
    rw [run_pure, run_pure, E_pure, E_pure]
    simp [hc.not_hits]
  | query_bind t k ih =>
    intro c hc
    rw [run_query_bind, run_query_bind, E_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl, oracleImpl_run_inl, E_bind, E_bind]
      refine E_mono _ fun u => ?_
      rw [E_pure, E_pure]
      exact ih u c hc
    · rcases hcq : c q with _ | v
      · rcases hfq : f q with _ | w
        · -- fresh on both sides
          have hcq' : Cache.extend c f q = none := by simp [Cache.extend, hcq, hfq]
          rw [oracleImpl_run_inr_none hcq, oracleImpl_run_inr_none hcq', E_bind, E_bind]
          refine E_mono _ fun u => ?_
          rw [E_pure, E_pure]
          dsimp only
          rw [← Cache.extend_cacheQuery]
          exact ih u _ (Cache.disjoint_cacheQuery hc hfq u)
        · -- the point is in `f`: the real run answers from `f`, the other side pays `1`
          have hcq' : Cache.extend c f q = some w := by simp [Cache.extend, hcq, hfq]
          rw [oracleImpl_run_inr_some hcq', oracleImpl_run_inr_none hcq, E_pure, E_bind]
          have hw : (f q).isSome := by simp [hfq]
          calc E (run (k w) (Cache.extend c f)) φ ≤ 1 := E_le_one _ hφ
            _ ≤ E ($ᵗ BitVec hashBits) fun u => E (pure (u, c.cacheQuery q u)) fun p =>
                  E (run (k p.1) p.2) fun p =>
                    if Cache.Hits p.2 f then 1 else φ (p.1, Cache.extend p.2 f) := by
                rw [E_uniform]
                have h1 : ∀ u : BitVec hashBits, E (pure (u, c.cacheQuery q u)) (fun p =>
                    E (run (k p.1) p.2) fun p =>
                      if Cache.Hits p.2 f then 1 else φ (p.1, Cache.extend p.2 f)) = 1 := by
                  intro u
                  rw [E_pure]
                  have hsub : ∀ p ∈ support (run (k u) (c.cacheQuery q u)),
                      Cache.Hits p.2 f := fun p hp =>
                    ⟨q, hw, (sub_of_mem_support_run _ _ p hp).isSome (by simp)⟩
                  have : E (run (k u) (c.cacheQuery q u)) (fun p =>
                      if Cache.Hits p.2 f then 1 else φ (p.1, Cache.extend p.2 f)) =
                      E (run (k u) (c.cacheQuery q u)) (fun _ => 1) := by
                    refine expectedValue_congr_of_support fun p hp => ?_
                    rw [if_pos (hsub p hp)]
                  rw [this, E, expectedValue_const (by simp)]
                simp only [h1, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                rw [ENNReal.mul_inv_cancel (by simp) (by simp)]
      · -- cached on both sides
        have hcq' : Cache.extend c f q = some v := by simp [Cache.extend, hcq]
        rw [oracleImpl_run_inr_some hcq, oracleImpl_run_inr_some hcq', E_pure, E_pure]
        exact ih v c hc

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.Master; SHA256 cd84206bbbdb91a9a8170d8bd117e3799f41b2a3d0aeea86168352eb5014e447. -/
section

/-!
# The supermartingale master lemma

Let `Φ` be a potential on caches that grows on average by at most `κ · cost q` at every fresh
hash query `q` (a *charge* of `κ` per compression), and let `I c b` be an invariant of the
cache and the remaining budget.  If every continuation `k x` started from a cache `d` with
budget `b'` is bounded by `Φ d + κ b'`, then the whole computation `oa >>= k` started from `c`
with budget `b` is bounded by `Φ c + κ b`:

```
E[Fv x d | (x, d) ← run oa c] ≤ Φ c + κ b.
```

Query bounds are the pathwise `CostAtMost` of `OptimalOTS.Dag`; the continuation's
budget is whatever is left on the path.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem costAtMost_query_bind_iff {α : Type} (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (b : ℕ) :
    CostAtMost (liftM (Spec.query t) >>= k) b ↔
      queryCost t ≤ b ∧ ∀ u, CostAtMost (k u) (b - queryCost t) := by
  unfold CostAtMost
  rw [isQueryBound_query_bind_iff]

theorem sum_inv_card_mul {n : ℕ} (a : ℝ≥0∞) :
    ∑ _x : BitVec n, (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem kappa_split (κ : ℝ≥0∞) {c b : ℕ} (h : c ≤ b) : κ * c + κ * ((b - c : ℕ) : ℝ≥0∞) = κ * b := by
  rw [← mul_add, ← Nat.cast_add, Nat.add_sub_cancel' h]

/-- **Master lemma.** -/
theorem master {α β : Type} (κ : ℝ≥0∞) (Φ : Cache → ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hΦ : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) ≤
        Φ c + κ * queryCost (.inr q))
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (Fv : α → Cache → ℝ≥0∞)
    (hF : ∀ x d b', I d b' → CostAtMost (k x) b' → Fv x d ≤ Φ d + κ * b') :
    ∀ (c : Cache) (b : ℕ), I c b → CostAtMost (oa >>= k) b →
      E (run oa c) (fun p => Fv p.1 p.2) ≤ Φ c + κ * b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c b hI hB
    rw [pure_bind] at hB
    rw [run_pure, E_pure]
    exact hF x c b hI hB
  | query_bind t k' ih =>
    intro c b hI hB
    rw [bind_assoc, costAtMost_query_bind_iff] at hB
    obtain ⟨hcost, hB⟩ := hB
    rw [run_query_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl, E_bind]
      refine (expectedValue_le_of_le _ fun u => ?_)
      rw [E_pure]
      have := ih u c b hI (hB u)
      simpa [queryCost] using this
    · rcases hcq : c q with _ | v
      · rw [oracleImpl_run_inr_none hcq, E_bind, E_uniform]
        calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
              E (pure (u, c.cacheQuery q u)) (fun p => E (run (k' p.1) p.2) fun p => Fv p.1 p.2)
            ≤ ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                (Φ (c.cacheQuery q u) + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞)) := by
              refine Finset.sum_le_sum fun u _ => ?_
              rw [E_pure]
              dsimp only
              gcongr
              exact ih u _ _ (hI_fresh c b q hI hcq hcost u) (hB u)
          _ = (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u)) +
                κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) := by
              simp only [mul_add, Finset.sum_add_distrib, sum_inv_card_mul]
          _ ≤ Φ c + κ * queryCost (.inr q) + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) :=
              add_le_add_left (hΦ c b q hI hcq hcost) _
          _ = Φ c + κ * b := by rw [add_assoc, kappa_split κ hcost]
      · rw [oracleImpl_run_inr_some hcq, E_pure]
        have hsome : (c q).isSome := by simp [hcq]
        calc E (run (k' v) c) (fun p => Fv p.1 p.2)
            ≤ Φ c + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) :=
              ih v c _ (hI_cached c b q hI hsome hcost) (hB v)
          _ ≤ Φ c + κ * b := by
              gcongr
              exact Nat.sub_le _ _

/-- The master lemma without a continuation. -/
theorem master_single {α : Type} (κ : ℝ≥0∞) (Φ : Cache → ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hΦ : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) ≤
        Φ c + κ * queryCost (.inr q))
    (oa : OracleComp Spec α) (Fv : α → Cache → ℝ≥0∞)
    (hF : ∀ x d, Fv x d ≤ Φ d) :
    ∀ (c : Cache) (b : ℕ), I c b → CostAtMost oa b →
      E (run oa c) (fun p => Fv p.1 p.2) ≤ Φ c + κ * b := by
  intro c b hI hB
  have := master κ Φ I hI_fresh hI_cached hΦ oa pure Fv
    (fun x d b' _ _ => (hF x d).trans le_self_add) c b hI (by rwa [bind_pure])
  exact this

end OptimalOTS

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- **Master lemma, for a family of continuations.** The continuation may depend on an index
`j` (in the application: the hidden part of the key), as long as every member of the family
respects the budget. -/
theorem master_family {α β J : Type} [Nonempty J] (κ : ℝ≥0∞) (Φ : Cache → ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hΦ : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) ≤
        Φ c + κ * queryCost (.inr q))
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β) (Fv : α → Cache → ℝ≥0∞)
    (hF : ∀ x d b', I d b' → (∀ j, CostAtMost (k j x) b') → Fv x d ≤ Φ d + κ * b') :
    ∀ (c : Cache) (b : ℕ), I c b → (∀ j, CostAtMost (oa >>= k j) b) →
      E (run oa c) (fun p => Fv p.1 p.2) ≤ Φ c + κ * b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c b hI hB
    rw [run_pure, E_pure]
    exact hF x c b hI fun j => by simpa [pure_bind] using hB j
  | query_bind t k' ih =>
    intro c b hI hB
    have hcost : queryCost t ≤ b := by
      have := hB (Classical.arbitrary J)
      rw [bind_assoc, costAtMost_query_bind_iff] at this
      exact this.1
    have hB' : ∀ u j, CostAtMost (k' u >>= k j) (b - queryCost t) := fun u j => by
      have := hB j
      rw [bind_assoc, costAtMost_query_bind_iff] at this
      exact this.2 u
    rw [run_query_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl, E_bind]
      refine (expectedValue_le_of_le _ fun u => ?_)
      rw [E_pure]
      have := ih u c b hI (hB' u)
      simpa [queryCost] using this
    · rcases hcq : c q with _ | v
      · rw [oracleImpl_run_inr_none hcq, E_bind, E_uniform]
        calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
              E (pure (u, c.cacheQuery q u)) (fun p => E (run (k' p.1) p.2) fun p => Fv p.1 p.2)
            ≤ ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                (Φ (c.cacheQuery q u) + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞)) := by
              refine Finset.sum_le_sum fun u _ => ?_
              rw [E_pure]
              dsimp only
              gcongr
              exact ih u _ _ (hI_fresh c b q hI hcq hcost u) (hB' u)
          _ = (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u)) +
                κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) := by
              simp only [mul_add, Finset.sum_add_distrib, sum_inv_card_mul]
          _ ≤ Φ c + κ * queryCost (.inr q) + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) :=
              add_le_add_left (hΦ c b q hI hcq hcost) _
          _ = Φ c + κ * b := by rw [add_assoc, kappa_split κ hcost]
      · rw [oracleImpl_run_inr_some hcq, E_pure]
        have hsome : (c q).isSome := by simp [hcq]
        calc E (run (k' v) c) (fun p => Fv p.1 p.2)
            ≤ Φ c + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) :=
              ih v c _ (hI_cached c b q hI hsome hcost) (hB' v)
          _ ≤ Φ c + κ * b := by
              gcongr
              exact Nat.sub_le _ _

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.Reconstruct; SHA256 a3c77306949229e8a573a62e8685541f992d83d2c507265eaf2f4ddd8fa43110. -/
section

/-!
# Reconstruction and verification under the lazy random oracle

Support-level descriptions of the runs of `Graph.reconstruct`, `index` and `Scheme.verify`:
whatever the oracle answers, the final cache contains the answers to every query made, and the
computed assignment satisfies the reconstruction equations with respect to that cache.

Also the two round trips between `Graph.encode` and `Graph.decode`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


/-! ## Bit strings -/

theorem testBit_foldr_bits (l : List Bool) (i : ℕ) :
    (l.foldr (fun (b : Bool) (acc : ℕ) => b.toNat + 2 * acc) 0).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases i with _ | i
    · rw [Nat.testBit_zero]
      cases b <;> simp [Nat.add_mul_mod_self_left]
    · rw [Nat.testBit_succ, List.getD_cons_succ, ← ih i]
      congr 1
      cases b <;> simp
      omega

theorem length_toBits {n : ℕ} (x : BitVec n) : (toBits x).length = n := List.length_ofFn

theorem ofBits_toBits {n : ℕ} (x : BitVec n) : ofBits n (toBits x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, toBits]
  rw [testBit_foldr_bits]
  simp [hi, List.getD_eq_getElem?_getD]

theorem toBits_ofBits {n : ℕ} (l : List Bool) (hl : l.length = n) : toBits (ofBits n l) = l := by
  apply List.ext_getElem
  · rw [length_toBits, hl]
  · intro i h1 h2
    simp only [toBits, List.getElem_ofFn, ofBits, BitVec.getLsbD_ofNat]
    rw [testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rw [length_toBits] at h1
    simp [h1]

/-! ## Chunks of a list along a sorted index list -/

theorem flatMap_congr_mem {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- The offset of `v` in the concatenation of chunks of lengths `len` along a sorted list. -/
def chunkOff {n : ℕ} (len : Fin n → ℕ) (L : List (Fin n)) (v : Fin n) : ℕ :=
  ((L.filter fun w => decide (w < v)).map len).sum

theorem chunkOff_cons_self {n : ℕ} (len : Fin n → ℕ) (a : Fin n) (L : List (Fin n))
    (hL : ∀ w ∈ L, a < w) : chunkOff len (a :: L) a = 0 := by
  unfold chunkOff
  have h : ((a :: L).filter fun w => decide (w < a)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · simp
    · simpa using le_of_lt (hL w hw)
  rw [h]; rfl

theorem chunkOff_cons_of_lt {n : ℕ} (len : Fin n → ℕ) (a : Fin n) (L : List (Fin n))
    {v : Fin n} (hv : a < v) : chunkOff len (a :: L) v = len a + chunkOff len L v := by
  unfold chunkOff
  simp [hv]

theorem chunkOff_add_le {n : ℕ} (len : Fin n → ℕ) :
    ∀ (L : List (Fin n)), L.Pairwise (· < ·) → ∀ v ∈ L,
      chunkOff len L v + len v ≤ (L.map len).sum := by
  intro L
  induction L with
  | nil => intro _ v hv; simp at hv
  | cons a L ih =>
    intro hL v hv
    rw [List.pairwise_cons] at hL
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · rw [chunkOff_cons_self len v L hL.1]
      omega
    · rw [chunkOff_cons_of_lt len a L (hL.1 v hv)]
      have := ih hL.2 v hv
      omega

theorem flatMap_chunks {n : ℕ} (len : Fin n → ℕ) :
    ∀ (L : List (Fin n)), L.Pairwise (· < ·) → ∀ (l : List Bool), l.length = (L.map len).sum →
      L.flatMap (fun v => (l.drop (chunkOff len L v)).take (len v)) = l := by
  intro L
  induction L with
  | nil =>
    intro _ l hl
    simp at hl
    subst hl
    rfl
  | cons a L ih =>
    intro hL l hl
    rw [List.pairwise_cons] at hL
    rw [List.map_cons, List.sum_cons] at hl
    rw [List.flatMap_cons, chunkOff_cons_self len a L hL.1, List.drop_zero]
    have h2 : L.flatMap (fun v => (l.drop (chunkOff len (a :: L) v)).take (len v)) =
        L.flatMap (fun v => ((l.drop (len a)).drop (chunkOff len L v)).take (len v)) := by
      refine flatMap_congr_mem fun v hv => ?_
      rw [chunkOff_cons_of_lt len a L (hL.1 v hv), List.drop_drop]
    rw [h2, ih hL.2 (l.drop (len a)) (by rw [List.length_drop]; omega), List.take_append_drop]

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- The reconstruction equation at a single node. -/
def ReconEqAt (d : Cache) (A : Finset (Fin G.size)) (given y : G.Assignment)
    (v : Fin G.size) : Prop :=
  (v ∈ A → y v = given v) ∧
    (v ∉ A → ¬ G.Visited A v → y v = 0) ∧
    (v ∉ A → G.Visited A v →
      (∀ p hp hl, G.kind v = .hash p hp hl →
        ∃ w, d ⟨G.len p, y p⟩ = some w ∧ y v = w.cast hl.symm) ∧
      (∀ ps hlt f hf, G.kind v = .det ps hlt f hf → y v = f y) ∧
      (G.kind v = .source → y v = 0))

/-- `y` satisfies the reconstruction equations from the values `given` on `A`, with every hash
answer recorded in the cache `d`. -/
def ReconEqs (d : Cache) (A : Finset (Fin G.size)) (given y : G.Assignment) : Prop :=
  ∀ v, (v ∈ A → y v = given v) ∧
    (v ∉ A → ¬ G.Visited A v → y v = 0) ∧
    (v ∉ A → G.Visited A v →
      (∀ p hp hl, G.kind v = .hash p hp hl →
        ∃ w, d ⟨G.len p, y p⟩ = some w ∧ y v = w.cast hl.symm) ∧
      (∀ ps hlt f hf, G.kind v = .det ps hlt f hf → y v = f y) ∧
      (G.kind v = .source → y v = 0))

theorem ReconEqAt.mono {d d' : Cache} (h : Cache.Sub d d') {A : Finset (Fin G.size)}
    {given y : G.Assignment} {v : Fin G.size} (he : G.ReconEqAt d A given y v) :
    G.ReconEqAt d' A given y v := by
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨h1, h2, fun hA hV => ?_⟩
  obtain ⟨h31, h32, h33⟩ := h3 hA hV
  refine ⟨fun p hp hl hk => ?_, h32, h33⟩
  obtain ⟨w, hw, hy⟩ := h31 p hp hl hk
  exact ⟨w, h _ _ hw, hy⟩

/-- The equation at `v` only looks at the values at nodes `≤ v`. -/
theorem ReconEqAt.congr {d : Cache} {A : Finset (Fin G.size)} {given y y' : G.Assignment}
    {v : Fin G.size} (h : ∀ u, u ≤ v → y' u = y u) (he : G.ReconEqAt d A given y v) :
    G.ReconEqAt d A given y' v := by
  obtain ⟨h1, h2, h3⟩ := he
  have hv : y' v = y v := h v le_rfl
  refine ⟨fun hA => by rw [hv]; exact h1 hA, fun hA hV => by rw [hv]; exact h2 hA hV,
    fun hA hV => ?_⟩
  obtain ⟨h31, h32, h33⟩ := h3 hA hV
  refine ⟨fun p hp hl hk => ?_, fun ps hlt f hf hk => ?_, fun hk => by rw [hv]; exact h33 hk⟩
  · obtain ⟨w, hw, hyw⟩ := h31 p hp hl hk
    refine ⟨w, ?_, by rw [hv]; exact hyw⟩
    rw [h p hp.le]; exact hw
  · rw [hv, h32 ps hlt f hf hk]
    exact hf y y' fun w hw => (h w (hlt w hw).le).symm

end Dag.Graph

/-! ## Support of a hash query -/

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- A hash query records its answer in the cache. -/
theorem hash_support {k : ℕ} (u : BitVec k) (c : Cache) :
    ∀ p ∈ support (run (hash u) c), Cache.Sub c p.2 ∧ p.2 ⟨k, u⟩ = some p.1 := by
  intro p hp
  have h : hash u = liftM (Spec.query (.inr ⟨k, u⟩)) >>= pure := (bind_pure _).symm
  rw [h, run_query_bind] at hp
  simp only [run_pure] at hp
  rw [support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨v, c'⟩, hv, hp⟩ := hp
  rw [support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rcases hc : c ⟨k, u⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨w, -, hw⟩ := hv
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨Cache.sub_cacheQuery_of_none hc _, QueryCache.cacheQuery_self ..⟩
  · rw [oracleImpl_run_inr_some hc, support_pure] at hv
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨Cache.Sub.refl _, hc⟩

namespace Dag.Graph

variable (G : Graph)

/-- Support of evaluating one node (with source value `0`). -/
theorem evalNode_support (x : G.Assignment) (v : Fin G.size) (c : Cache) :
    ∀ p ∈ support (run (G.evalNode x v (pure 0)) c),
      Cache.Sub c p.2 ∧
      (∀ q hq hl, G.kind v = .hash q hq hl →
        ∃ w, p.2 ⟨G.len q, x q⟩ = some w ∧ p.1 = w.cast hl.symm) ∧
      (∀ ps hlt f hf, G.kind v = .det ps hlt f hf → p.1 = f x) ∧
      (G.kind v = .source → p.1 = 0) := by
  unfold evalNode
  generalize G.kind v = k
  cases k with
  | source =>
    intro p hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, (fun _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h),
      fun _ => rfl⟩
  | det ps hlt f hf =>
    intro p hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl c, (fun _ _ _ h => nomatch h), fun _ _ _ _ h => ?_,
      (fun h => nomatch h)⟩
    cases h
    rfl
  | hash q hq hl =>
    intro p hp
    rw [run_map, support_map, Set.mem_image] at hp
    obtain ⟨⟨w, c'⟩, hw, rfl⟩ := hp
    obtain ⟨hsub, hc'⟩ := hash_support _ c _ hw
    dsimp only at hsub hc' ⊢
    refine ⟨hsub, fun q' hq' hl' h => ?_, (fun _ _ _ _ h => nomatch h), (fun h => nomatch h)⟩
    cases h
    exact ⟨w, hc', rfl⟩

/-- One step of `reconstruct`. -/
def reconStep (A : Finset (Fin G.size)) (given : G.Assignment) (x : G.Assignment)
    (v : Fin G.size) : OracleComp Spec G.Assignment :=
  if v ∈ A then pure (Function.update x v (given v))
  else if G.Visited A v then Function.update x v <$> G.evalNode x v (pure 0)
  else pure (Function.update x v 0)

theorem reconstruct_eq_foldlM (A : Finset (Fin G.size)) (given : G.Assignment) :
    G.reconstruct A given =
      (List.finRange G.size).foldlM (G.reconStep A given) (fun _ => 0) := rfl

theorem reconStep_support (A : Finset (Fin G.size)) (given : G.Assignment) (x : G.Assignment)
    (a : Fin G.size) (c : Cache) :
    ∀ p ∈ support (run (G.reconStep A given x a) c),
      Cache.Sub c p.2 ∧ (∀ w, w ≠ a → p.1 w = x w) ∧ G.ReconEqAt p.2 A given p.1 a := by
  intro p hp
  unfold reconStep at hp
  by_cases hA : a ∈ A
  · rw [if_pos hA, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl c, fun w hw => Function.update_of_ne hw _ _, ?_⟩
    exact ⟨fun _ => Function.update_self .., fun h => absurd hA h, fun h => absurd hA h⟩
  · rw [if_neg hA] at hp
    by_cases hV : G.Visited A a
    · rw [if_pos hV, run_map, support_map, Set.mem_image] at hp
      obtain ⟨⟨y, c'⟩, hy, rfl⟩ := hp
      obtain ⟨hsub, hhash, hdet, hsrc⟩ := G.evalNode_support x a c ⟨y, c'⟩ hy
      dsimp only at hsub hhash hdet hsrc ⊢
      refine ⟨hsub, fun w hw => Function.update_of_ne hw _ _, ?_⟩
      refine ⟨fun h => absurd h hA, fun _ h => absurd hV h, fun _ _ => ⟨?_, ?_, ?_⟩⟩
      · intro p hp hl hk
        obtain ⟨w, hw, hyw⟩ := hhash p hp hl hk
        refine ⟨w, ?_, ?_⟩
        · rw [Function.update_of_ne (ne_of_lt hp)]; exact hw
        · rw [Function.update_self]; exact hyw
      · intro ps hlt f hf hk
        rw [Function.update_self, hdet ps hlt f hf hk]
        exact hf x _ fun w hw => (Function.update_of_ne (ne_of_lt (hlt w hw)) _ _).symm
      · intro hk
        rw [Function.update_self]
        exact hsrc hk
    · rw [if_neg hV, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨Cache.Sub.refl c, fun w hw => Function.update_of_ne hw _ _, fun h => absurd h hA,
        fun _ _ => Function.update_self .., fun _ h => absurd h hV⟩

/-- Folding the reconstruction step over an increasing list: the equations hold at the nodes of
the list and every other node is still `0`. -/
theorem foldlM_reconStep_support (A : Finset (Fin G.size)) (given : G.Assignment) (c : Cache)
    (l : List (Fin G.size)) (hl : l.Pairwise (· < ·)) :
    ∀ p ∈ support (run (l.foldlM (G.reconStep A given) (fun _ => 0)) c),
      Cache.Sub c p.2 ∧ (∀ v ∈ l, G.ReconEqAt p.2 A given p.1 v) ∧
        (∀ v, v ∉ l → p.1 v = 0) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro p hp
    rw [List.foldlM_nil, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, fun v hv => by simp at hv, fun v _ => rfl⟩
  | append_singleton l a ih =>
    rw [List.pairwise_append] at hl
    obtain ⟨hl, -, hla⟩ := hl
    have hla' : ∀ v ∈ l, v < a := fun v hv => hla v hv a (List.mem_singleton_self a)
    intro p hp
    rw [List.foldlM_append, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨x, c'⟩, hx, hp⟩ := hp
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at hp
    obtain ⟨hsub, heq, hzero⟩ := ih hl ⟨x, c'⟩ hx
    obtain ⟨hsub', hne, ha⟩ := G.reconStep_support A given x a c' p hp
    refine ⟨hsub.trans hsub', fun v hv => ?_, fun v hv => ?_⟩
    · rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · have hva := hla' v hv
        exact ReconEqAt.congr G (fun u hu => hne u (ne_of_lt (lt_of_le_of_lt hu hva)))
          (ReconEqAt.mono G hsub' (heq v hv))
      · exact ha
    · rw [List.mem_append, List.mem_singleton, not_or] at hv
      rw [hne v hv.2]
      exact hzero v hv.1

/-- Every outcome of reconstruction satisfies the reconstruction equations with respect to the
final cache, which extends the initial one. -/
theorem reconstruct_support (A : Finset (Fin G.size)) (given : G.Assignment) (c : Cache) :
    ∀ p ∈ support (run (G.reconstruct A given) c),
      Cache.Sub c p.2 ∧ G.ReconEqs p.2 A given p.1 := by
  intro p hp
  rw [reconstruct_eq_foldlM] at hp
  obtain ⟨hsub, heq, -⟩ :=
    G.foldlM_reconStep_support A given c _ (List.pairwise_lt_finRange _) p hp
  exact ⟨hsub, fun v => heq v (List.mem_finRange v)⟩

/-! ## Encoding and decoding -/

/-- The members of `A` in node order. -/
theorem encode_eq (A : Finset (Fin G.size)) (x : G.Assignment) :
    G.encode A x =
      ((List.finRange G.size).filter fun v => decide (v ∈ A)).flatMap fun v => toBits (x v) := rfl

theorem revealBits_eq (A : Finset (Fin G.size)) :
    G.revealBits A = (((List.finRange G.size).filter fun v => decide (v ∈ A)).map G.len).sum := by
  unfold revealBits
  rw [← List.sum_toFinset _ ((List.nodup_finRange _).filter _)]
  congr 1
  ext v
  simp

theorem offset_eq (A : Finset (Fin G.size)) (v : Fin G.size) :
    G.offset A v = chunkOff G.len ((List.finRange G.size).filter fun v => decide (v ∈ A)) v := by
  unfold offset chunkOff
  rw [← List.sum_toFinset _ (((List.nodup_finRange _).filter _).filter _)]
  congr 1
  ext w
  simp [and_comm]

theorem length_encode (A : Finset (Fin G.size)) (x : G.Assignment) :
    (G.encode A x).length = G.revealBits A := by
  rw [encode_eq, revealBits_eq, List.length_flatMap]
  simp only [length_toBits]

theorem decode_encode (A : Finset (Fin G.size)) (x : G.Assignment) {v : Fin G.size}
    (hv : v ∈ A) : G.decode A (G.encode A x) v = x v := by
  unfold decode
  rw [encode_eq, offset_eq]
  set L := (List.finRange G.size).filter fun v => decide (v ∈ A) with hLdef
  have hL : L.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  have hvL : v ∈ L := by simp [hLdef, hv]
  have hsplit : ∀ (M : List (Fin G.size)), M.Pairwise (· < ·) → v ∈ M →
      M.flatMap (fun w => toBits (x w)) =
        (M.filter fun w => decide (w < v)).flatMap (fun w => toBits (x w)) ++
          (toBits (x v) ++ (M.filter fun w => decide (v < w)).flatMap (fun w => toBits (x w))) := by
    intro M
    induction M with
    | nil => intro _ h; simp at h
    | cons a M ih =>
      intro hM hvM
      rw [List.pairwise_cons] at hM
      rcases List.mem_cons.1 hvM with rfl | hvM
      · have h1 : (M.filter fun w => decide (w < v)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro w hw
          simpa using le_of_lt (hM.1 w hw)
        have h2 : (M.filter fun w => decide (v < w)) = M := by
          rw [List.filter_eq_self]
          intro w hw
          simpa using hM.1 w hw
        simp [h1, h2]
      · have hav : a < v := hM.1 v hvM
        rw [List.flatMap_cons, ih hM.2 hvM]
        simp [hav, not_lt.2 hav.le]
  rw [hsplit L hL hvL]
  have hoff : chunkOff G.len L v =
      ((L.filter fun w => decide (w < v)).flatMap (fun w => toBits (x w))).length := by
    rw [List.length_flatMap]
    simp only [length_toBits]
    rfl
  rw [hoff, List.drop_left, List.take_left' (length_toBits _), ofBits_toBits]

theorem encode_decode (A : Finset (Fin G.size)) (l : List Bool)
    (hl : l.length = G.revealBits A) : G.encode A (G.decode A l) = l := by
  rw [encode_eq]
  unfold decode
  simp only [offset_eq]
  rw [revealBits_eq] at hl
  set L := (List.finRange G.size).filter fun v => decide (v ∈ A) with hLdef
  have hL : L.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  conv_rhs => rw [← flatMap_chunks G.len L hL l hl]
  refine flatMap_congr_mem fun v hv => ?_
  apply toBits_ofBits
  rw [List.length_take, List.length_drop, hl]
  have := chunkOff_add_le G.len L hL v hv
  omega

end Dag.Graph

/-- The index query records its answer in the cache. -/
theorem index_support (m : Message) (η : Nonce) (c : Cache) :
    ∀ p ∈ support (run (index m η) c),
      Cache.Sub c p.2 ∧ ∃ w, p.2 ⟨msgBits + nonceBits, m ++ η⟩ = some w ∧
        p.1 = (w.setWidth idxBits).toNat := by
  intro p hp
  unfold index at hp
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨⟨w, c'⟩, hw, rfl⟩ := hp
  obtain ⟨hsub, hc'⟩ := hash_support _ c _ hw
  dsimp only at hsub hc' ⊢
  exact ⟨hsub, w, hc', rfl⟩

/-- Every accepting run of the verifier is witnessed in the final cache: the index answer, and
an assignment satisfying the reconstruction equations whose root prefix is the public key. -/
theorem verify_support (S : Scheme) (pk : PublicKey) (m : Message)
    (σ : Signature) (c : Cache) :
    ∀ p ∈ support (run (S.verify pk m σ) c),
      Cache.Sub c p.2 ∧ (p.1 = true →
        ∃ w, p.2 ⟨msgBits + nonceBits, m ++ σ.1⟩ = some w ∧
          ∃ hi : (w.setWidth idxBits).toNat < numCuts,
            σ.2.length = S.graph.revealBits (S.sets ⟨_, hi⟩) ∧
            ∃ y : S.graph.Assignment,
              S.graph.ReconEqs p.2 (S.sets ⟨_, hi⟩) (S.graph.decode (S.sets ⟨_, hi⟩) σ.2) y ∧
              S.publicKey y = pk) := by
  intro p hp
  unfold Scheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨i, c₁⟩, hi₁, hp⟩ := hp
  obtain ⟨hsub₁, w, hw, rfl⟩ := index_support m σ.1 c ⟨i, c₁⟩ hi₁
  dsimp only at hp hw
  by_cases hi : (w.setWidth idxBits).toNat < numCuts
  · rw [dif_pos hi] at hp
    by_cases hlen : σ.2.length = S.graph.revealBits (S.sets ⟨_, hi⟩)
    · rw [if_pos hlen, run_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨y, c₂⟩, hy, hp⟩ := hp
      obtain ⟨hsub₂, heq⟩ := S.graph.reconstruct_support _ _ c₁ ⟨y, c₂⟩ hy
      rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
      refine ⟨w, hsub₂ _ _ hw, hi, hlen, y, heq, ?_⟩
      exact of_decide_eq_true hok
    · rw [if_neg hlen, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hsub₁, fun h => by cases h⟩
  · rw [dif_neg hi, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hsub₁, fun h => by cases h⟩

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.NonceCodec; SHA256 2296ce4388d78cc2ff367a63ae4295dbe078b365c2a6c5924fb39e5792f7b71d. -/
section

/-! Width-generic codec for a nonce followed by a disclosure payload. No scheme or
security claim is made here. Short bit strings decode with zero extension; exact
re-encoding is asserted only when the nonce is fully present. -/

namespace OptimalOTS.WeightedConstruction.NonceCodec

abbrev Signature (n : ℕ) := BitVec n × List Bool

def encode {n : ℕ} (σ : Signature n) : List Bool := toBits σ.1 ++ σ.2

def decode (n : ℕ) (bits : List Bool) : Signature n :=
  (ofBits n (bits.take n), bits.drop n)

@[simp] theorem length_encode {n : ℕ} (σ : Signature n) :
    (encode σ).length = n + σ.2.length := by
  simp [encode, toBits]

@[simp] theorem decode_encode {n : ℕ} (σ : Signature n) : decode n (encode σ) = σ := by
  rcases σ with ⟨nonce, payload⟩
  have hn : (toBits nonce).length = n := length_toBits nonce
  simp only [decode, encode, List.take_left' hn, List.drop_left' hn, ofBits_toBits]

theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro a b h
  have := congrArg (decode n) h
  simpa using this

theorem encode_decode {n : ℕ} (bits : List Bool) (hlen : n ≤ bits.length) :
    encode (decode n bits) = bits := by
  change toBits (ofBits n (bits.take n)) ++ bits.drop n = bits
  rw [toBits_ofBits _ (by simp [hlen]), List.take_append_drop]

@[simp] theorem length_payload_decode (n : ℕ) (bits : List Bool) :
    (decode n bits).2.length = bits.length - n := by
  simp [decode]

theorem enough_nonce_of_payload_positive {n : ℕ} {bits : List Bool}
    (h : 0 < (decode n bits).2.length) : n ≤ bits.length := by
  rw [length_payload_decode] at h
  omega

theorem canonical_of_payload_positive {n : ℕ} {bits : List Bool}
    (h : 0 < (decode n bits).2.length) : encode (decode n bits) = bits :=
  encode_decode bits (enough_nonce_of_payload_positive h)

abbrev Signature86 := Signature 86

theorem signature86_length (nonce : BitVec 86) (payload : List Bool)
    (h : payload.length = 42 * 129) : (encode (nonce, payload)).length = 5504 := by
  rw [length_encode, h]

end OptimalOTS.WeightedConstruction.NonceCodec

#print axioms OptimalOTS.WeightedConstruction.NonceCodec.decode_encode
#print axioms OptimalOTS.WeightedConstruction.NonceCodec.encode_injective
#print axioms OptimalOTS.WeightedConstruction.NonceCodec.encode_decode
#print axioms OptimalOTS.WeightedConstruction.NonceCodec.canonical_of_payload_positive
#print axioms OptimalOTS.WeightedConstruction.NonceCodec.signature86_length
end

/- Original module: Submissions.UpperCompressions.Keygen; SHA256 0fe0924c834833c06ba8085a01ecbf2839622614de563bfe64c8dae37ecffbce. -/
section

/-!
# Key generation under the lazy random oracle

Key generation samples every source and queries every hash node once. The oracle has no labels, so
the queries of different hash nodes are kept apart by the strings themselves: a `Graph.Tagging`
reads, from a query, the hash node it belongs to. Under the lazy random oracle started from the
empty cache, key generation of a tagged graph therefore produces, for a uniformly random record
`ξ : G.Rec`, the assignment `G.evalRec ξ` and the cache `G.keygenCache ξ` holding the keygen point
of every hash node.

* `Graph.Tagging`: a public tag function under which the input of every hash node carries the tag
  of that node;
* `E_run_keygen`: the expectation of any function of the output and the final cache is the
  uniform average over records;
* `costAtMost_keygen_bind`: a budget for `S.keygen >>= k` leaves `B - keygenCost` for the
  continuation at every record.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- A public way to read, from a query, the hash node it belongs to. -/
structure Tagging (G : Graph) where
  tag : Query → Option (Fin G.size)
  /-- The parent of every hash node is a deterministic node whose output always carries the tag
  of that hash node. -/
  tag_parent : ∀ v p hp hl, G.kind v = .hash p hp hl →
    ∃ ps hps f hf, G.kind p = .det ps hps f hf ∧ ∀ x, tag ⟨G.len p, f x⟩ = some v

/-- The keygen point of hash node `v` under the assignment `x`: its input, with its length. -/
def point (x : G.Assignment) (v : Fin G.size) : Option Query :=
  match G.kind v with
  | .hash p _ _ => some ⟨G.len p, x p⟩
  | _ => none

/-- The cache written by key generation for the record `ξ`. -/
def keygenCache (ξ : G.Rec) : Cache :=
  (List.finRange G.size).foldl
    (fun c v => match G.point (G.evalRec ξ) v with
      | some q => c.cacheQuery q (ξ.2 v)
      | none => c) ∅

theorem point_eq_some_iff (x : G.Assignment) (v : Fin G.size) (q : Query) :
    G.point x v = some q ↔
      ∃ p hp hl, G.kind v = .hash p hp hl ∧ q = ⟨G.len p, x p⟩ := by
  unfold point
  rcases hk : G.kind v with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
  · simp
  · simp
  · simp only [Option.some.injEq, NodeKind.hash.injEq]
    constructor
    · rintro rfl
      exact ⟨p, hp, hl, rfl, rfl⟩
    · rintro ⟨p', hp', hl', rfl, rfl⟩
      rfl

/-- The points of the assignment `x` carry the tags of their hash nodes. -/
def TagOK (T : G.Tagging) (x : G.Assignment) : Prop :=
  ∀ v q, G.point x v = some q → T.tag q = some v

/-- Points of different hash nodes differ: they carry different tags. -/
theorem point_inj (T : G.Tagging) {x x' : G.Assignment} (hx : G.TagOK T x) (hx' : G.TagOK T x')
    {v v' : Fin G.size} {q : Query}
    (h : G.point x v = some q) (h' : G.point x' v' = some q) : v = v' :=
  Option.some.inj ((hx v q h).symm.trans (hx' v' q h'))

/-- One step of the cache fold: record the keygen point of `v` under `x` with answer `y v`. -/
def cacheStep (x : G.Assignment) (y : Fin G.size → BitVec hashBits) (c : Cache)
    (v : Fin G.size) : Cache :=
  match G.point x v with
  | some q => c.cacheQuery q (y v)
  | none => c

theorem keygenCache_eq (ξ : G.Rec) :
    G.keygenCache ξ = (List.finRange G.size).foldl (G.cacheStep (G.evalRec ξ) ξ.2) ∅ := rfl

theorem cacheStep_of_eq_some (x : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (c : Cache) {v : Fin G.size} {q : Query} (h : G.point x v = some q) :
    G.cacheStep x y c v = c.cacheQuery q (y v) := by
  simp [cacheStep, h]

theorem cacheStep_of_eq_none (x : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (c : Cache) {v : Fin G.size} (h : G.point x v = none) :
    G.cacheStep x y c v = c := by
  simp [cacheStep, h]

theorem foldl_cacheStep_eq_some_iff (T : G.Tagging) {x : G.Assignment} (hx : G.TagOK T x)
    (y : Fin G.size → BitVec hashBits) (q : Query) (w : BitVec hashBits) :
    ∀ (l : List (Fin G.size)) (c : Cache),
      (l.foldl (G.cacheStep x y) c) q = some w ↔
        (∃ v ∈ l, G.point x v = some q ∧ y v = w) ∨
          (c q = some w ∧ ∀ v ∈ l, G.point x v ≠ some q)
  | [], c => by simp
  | a :: l, c => by
    rw [List.foldl_cons, foldl_cacheStep_eq_some_iff T hx y q w l]
    rcases ha : G.point x a with _ | q'
    · rw [G.cacheStep_of_eq_none x y c ha]
      simp only [List.mem_cons, exists_eq_or_imp, ha, reduceCtorEq, false_and, false_or,
        forall_eq_or_imp, ne_eq, not_false_eq_true, true_and]
    · rw [G.cacheStep_of_eq_some x y c ha]
      by_cases hq : q' = q
      · subst hq
        rw [QueryCache.cacheQuery_self]
        simp only [List.mem_cons, exists_eq_or_imp, ha, true_and, forall_eq_or_imp, ne_eq,
          not_true_eq_false, false_and, and_false, or_false, Option.some.injEq]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact Or.inr h
          · exact Or.inl h
        · rintro (h | ⟨v, hv, hvq, hw⟩)
          · by_cases hl : ∃ v ∈ l, G.point x v = some q' ∧ y v = w
            · exact Or.inl hl
            · refine Or.inr ⟨h, fun v hv hvq => hl ⟨v, hv, hvq, ?_⟩⟩
              rw [G.point_inj T hx hx hvq ha, h]
          · exact Or.inl ⟨v, hv, hvq, hw⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]
        have hne : G.point x a ≠ some q := by rw [ha]; intro h; exact hq (Option.some.inj h)
        simp only [List.mem_cons, exists_eq_or_imp, ha, forall_eq_or_imp, ne_eq]
        constructor
        · rintro (h | ⟨hc, hl⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨hc, fun h => hq (Option.some.inj h), hl⟩
        · rintro ((⟨h, -⟩ | h) | ⟨hc, -, hl⟩)
          · exact absurd h (fun h => hq (Option.some.inj h))
          · exact Or.inl h
          · exact Or.inr ⟨hc, hl⟩

/-- The assignment of a record carries the right tags: the parent of a hash node is a
deterministic node, whose value in `G.evalRec ξ` is its function applied to `G.evalRec ξ`. -/
theorem tagOK_evalRec (T : G.Tagging) (ξ : G.Rec) : G.TagOK T (G.evalRec ξ) := by
  intro v q hq
  obtain ⟨p, hp, hl, hk, rfl⟩ := (G.point_eq_some_iff _ v q).1 hq
  obtain ⟨ps, hps, f, hf, hkp, htag⟩ := T.tag_parent v p hp hl hk
  have hval : G.evalRec ξ p = f (G.evalRec ξ) := by
    have h := G.evalRec_apply ξ p
    rw [hkp] at h
    exact h
  rw [hval]
  exact htag _

theorem keygenCache_apply_iff (T : G.Tagging) (ξ : G.Rec) (q : Query) (w : BitVec hashBits) :
    G.keygenCache ξ q = some w ↔ ∃ v, G.point (G.evalRec ξ) v = some q ∧ ξ.2 v = w := by
  rw [keygenCache_eq, G.foldl_cacheStep_eq_some_iff T (G.tagOK_evalRec T ξ)]
  simp [List.mem_finRange]

/-! ## Node-kind case lemmas -/

theorem point_of_kind_eq_hash (x : G.Assignment) {v p : Fin G.size} {hp : p < v}
    {hl : G.len v = hashBits} (hk : G.kind v = .hash p hp hl) :
    G.point x v = some ⟨G.len p, x p⟩ := by
  simp [point, hk]

theorem point_of_kind_eq_source (x : G.Assignment) {v : Fin G.size} (hk : G.kind v = .source) :
    G.point x v = none := by
  simp [point, hk]

theorem point_of_kind_eq_det (x : G.Assignment) {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) : G.point x v = none := by
  simp [point, hk]

theorem recVal_of_kind_eq_hash (ξ : G.Rec) {v p : Fin G.size} {hp : p < v}
    {hl : G.len v = hashBits} (hk : G.kind v = .hash p hp hl) (x : G.Assignment) :
    G.recVal ξ v x = (ξ.2 v).cast hl.symm := by
  simp [recVal, hk, NodeKind.value]

theorem recVal_of_kind_eq_source (ξ : G.Rec) {v : Fin G.size} (hk : G.kind v = .source)
    (x : G.Assignment) : G.recVal ξ v x = ξ.1 v := by
  simp [recVal, hk, NodeKind.value]

theorem recVal_of_kind_eq_det (ξ : G.Rec) {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) (x : G.Assignment) : G.recVal ξ v x = f x := by
  simp [recVal, hk, NodeKind.value]

theorem evalNode_of_kind_eq_hash (x : G.Assignment) {v p : Fin G.size} {hp : p < v}
    {hl : G.len v = hashBits} (hk : G.kind v = .hash p hp hl)
    (s : OracleComp Spec (BitVec (G.len v))) :
    G.evalNode x v s = (fun y => y.cast hl.symm) <$> hash (x p) := by
  simp [evalNode, hk]

theorem evalNode_of_kind_eq_source (x : G.Assignment) {v : Fin G.size} (hk : G.kind v = .source)
    (s : OracleComp Spec (BitVec (G.len v))) : G.evalNode x v s = s := by
  simp [evalNode, hk]

theorem evalNode_of_kind_eq_det (x : G.Assignment) {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) (s : OracleComp Spec (BitVec (G.len v))) :
    G.evalNode x v s = pure (f x) := by
  simp [evalNode, hk]

theorem nodeCost_of_kind_eq_source {v : Fin G.size} (hk : G.kind v = .source) :
    G.nodeCost v = 0 := by
  simp [nodeCost, hk]

theorem nodeCost_of_kind_eq_det {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) : G.nodeCost v = 0 := by
  simp [nodeCost, hk]

end Dag.Graph

/-! ## Folds of updates -/

theorem foldl_update_apply_of_not_mem {ι : Type} [DecidableEq ι] {β : ι → Type}
    (h : ((i : ι) → β i) → (i : ι) → β i) :
    ∀ (l : List ι) (x : (i : ι) → β i) (w : ι), w ∉ l →
      (l.foldl (fun x v => Function.update x v (h x v)) x) w = x w
  | [], _, _, _ => rfl
  | a :: l, x, w, hw => by
    simp only [List.mem_cons, not_or] at hw
    rw [List.foldl_cons, foldl_update_apply_of_not_mem h l _ w hw.2]
    exact Function.update_of_ne hw.1 _ _

theorem foldl_update_apply_of_mem {ι : Type} [DecidableEq ι] {β : ι → Type}
    (y : (i : ι) → β i) :
    ∀ (l : List ι) (x : (i : ι) → β i) (w : ι), w ∈ l →
      (l.foldl (fun x v => Function.update x v (y v)) x) w = y w
  | [], _, _, hw => by simp at hw
  | a :: l, x, w, hw => by
    rw [List.foldl_cons]
    by_cases hl : w ∈ l
    · exact foldl_update_apply_of_mem y l _ w hl
    · have hwa : w = a := by
        simp only [List.mem_cons] at hw
        exact hw.resolve_right hl
      subst hwa
      rw [foldl_update_apply_of_not_mem (fun _ v => y v) l _ w hl, Function.update_self]

theorem foldl_update_finRange {n : ℕ} {β : Fin n → Type} (y x : (i : Fin n) → β i) :
    (List.finRange n).foldl (fun x v => Function.update x v (y v)) x = y := by
  funext w
  exact foldl_update_apply_of_mem y _ x w (List.mem_finRange w)

theorem foldl_update_of_update_not_mem {ι : Type} [DecidableEq ι] {β : ι → Type}
    (y : (i : ι) → β i) {a : ι} (u' : β a) (l : List ι) (ha : a ∉ l) (x : (i : ι) → β i) :
    l.foldl (fun x v => Function.update x v (Function.update y a u' v)) x =
      l.foldl (fun x v => Function.update x v (y v)) x := by
  refine List.foldl_ext _ _ x fun x v hv => ?_
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  rw [Function.update_of_ne hva]

/-! ## Averaging over one coordinate -/

theorem sum_sum_update_pi {ι : Type} [Fintype ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, Fintype (R i)] (H : ((i : ι) → R i) → ℝ≥0∞) (i : ι) :
    ∑ u : R i, ∑ g : (j : ι) → R j, H (Function.update g i u) =
      Fintype.card (R i) * ∑ g, H g := by
  let φ : ((j : ι) → R j) × R i → ((j : ι) → R j) × R i :=
    fun p => (Function.update p.1 i p.2, p.1 i)
  have hφ : Function.Involutive φ := by
    intro p
    simp [φ]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun g u => H (Function.update g i u))]
  have := Equiv.sum_comp hφ.toPerm (fun p => H p.1)
  simp only [Function.Involutive.coe_toPerm, φ] at this
  rw [this, Fintype.sum_prod_type]
  simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, mul_comm]

theorem sum_inv_card_mul' {α : Type} [Fintype α] [Nonempty α] (a : ℝ≥0∞) :
    ∑ _x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

/-- Averaging a function of a fresh uniform coordinate `u` and a uniform table `y` that does not
read `y i` equals averaging over `y` alone with `u := y i`. -/
theorem sum_avg_update {ι : Type} [Fintype ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)] (i : ι) (Φ : R i → ((j : ι) → R j) → ℝ≥0∞)
    (hΦ : ∀ u u' y, Φ u (Function.update y i u') = Φ u y) :
    ∑ u : R i, (Fintype.card (R i) : ℝ≥0∞)⁻¹ *
        ∑ y : (j : ι) → R j, (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * Φ u y =
      ∑ y : (j : ι) → R j, (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * Φ (y i) y := by
  have key := sum_sum_update_pi (fun y => Φ (y i) y) i
  simp only [Function.update_self, hΦ] at key
  have hn0 : (Fintype.card (R i) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnt : (Fintype.card (R i) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [← Finset.mul_sum]
  rw [key]
  calc (Fintype.card (R i) : ℝ≥0∞)⁻¹ * ((Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ *
        (Fintype.card (R i) * ∑ y, Φ (y i) y))
      = ((Fintype.card (R i) : ℝ≥0∞)⁻¹ * Fintype.card (R i)) *
          ((Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * ∑ y, Φ (y i) y) := by ring
    _ = (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * ∑ y, Φ (y i) y := by
        rw [ENNReal.inv_mul_cancel hn0 hnt, one_mul]

/-! ## Running a single query -/

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem run_query (t : Spec.Domain) (c : Cache) :
    run (liftM (Spec.query t)) c = (oracleImpl t).run c := by
  simp only [run, simulateQ_spec_query]

/-! ## Sampling the sources -/

namespace Dag.Graph

variable (G : Graph)

theorem E_run_sampleFold (g : G.Assignment × Cache → ℝ≥0∞) :
    ∀ (l : List (Fin G.size)), l.Nodup → ∀ (z : G.Assignment) (c : Cache),
      E (run (l.foldlM (fun z v => Function.update z v <$> sampleBits (G.len v)) z) c) g =
        ∑ y : G.Assignment, (Fintype.card G.Assignment : ℝ≥0∞)⁻¹ *
          g (l.foldl (fun z v => Function.update z v (y v)) z, c)
  | [], _, z, c => by
    rw [List.foldlM_nil, run_pure, E_pure]
    simp only [List.foldl_nil, sum_inv_card_mul']
  | a :: l, hnd, z, c => by
    rw [List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    rw [List.foldlM_cons, run_bind, E_bind, sampleBits, run_map, run_liftM]
    simp only [E_map, E_uniform, E_run_sampleFold g l hnd, List.foldl_cons]
    refine sum_avg_update (R := fun v => BitVec (G.len v)) a
      (fun u y => g (l.foldl (fun z v => Function.update z v (y v)) (Function.update z a u), c))
      fun u u' y => ?_
    simp only [foldl_update_of_update_not_mem y u' l ha]

theorem E_run_sampleAssignment (g : G.Assignment × Cache → ℝ≥0∞) (c : Cache) :
    E (run G.sampleAssignment c) g =
      ∑ y : G.Assignment, (Fintype.card G.Assignment : ℝ≥0∞)⁻¹ * g (y, c) := by
  unfold Graph.sampleAssignment
  rw [G.E_run_sampleFold g _ (List.nodup_finRange _)]
  simp only [foldl_update_finRange]

/-! ## Evaluating the nodes -/

/-- The cache `c` holds no query tagged with a node of `l`. -/
def Fresh (T : G.Tagging) (l : List (Fin G.size)) (c : Cache) : Prop :=
  ∀ v ∈ l, ∀ q : Query, T.tag q = some v → c q = none

theorem fresh_empty (T : G.Tagging) (l : List (Fin G.size)) : G.Fresh T l ∅ :=
  fun _ _ _ _ => rfl

theorem Fresh.tail {T : G.Tagging} {a : Fin G.size} {l : List (Fin G.size)} {c : Cache}
    (h : G.Fresh T (a :: l) c) : G.Fresh T l c :=
  fun v hv => h v (List.mem_cons_of_mem a hv)

theorem Fresh.cacheQuery {T : G.Tagging} {a : Fin G.size} {l : List (Fin G.size)} {c : Cache}
    (h : G.Fresh T (a :: l) c) (ha : a ∉ l) {q : Query} (hq : T.tag q = some a)
    (u : BitVec hashBits) : G.Fresh T l (c.cacheQuery q u) := by
  intro v hv q' hq'
  have hne : q' ≠ q := by
    rintro rfl
    have hva : v = a := Option.some.inj (hq'.symm.trans hq)
    exact ha (hva ▸ hv)
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact h v (List.mem_cons_of_mem a hv) q' hq'

/-- Every hash node of `l` whose parent is not in `l` (so has been evaluated already) has, in the
assignment `x`, an input carrying its tag. -/
def Tagged (T : G.Tagging) (l : List (Fin G.size)) (x : G.Assignment) : Prop :=
  ∀ v ∈ l, ∀ p hp hl, G.kind v = .hash p hp hl → p ∉ l → T.tag ⟨G.len p, x p⟩ = some v

theorem tagged_finRange (T : G.Tagging) (x : G.Assignment) :
    G.Tagged T (List.finRange G.size) x :=
  fun _ _ p _ _ _ hp => absurd (List.mem_finRange p) hp

/-- Evaluating the head `a` keeps the invariant, provided a deterministic node gets the value of
its function. A source or a hash node is never the parent of a hash node. -/
theorem Tagged.update {T : G.Tagging} {a : Fin G.size} {l : List (Fin G.size)}
    {x : G.Assignment} (h : G.Tagged T (a :: l) x) (u : BitVec (G.len a))
    (hu : ∀ ps hps f hf, G.kind a = .det ps hps f hf → u = f x) :
    G.Tagged T l (Function.update x a u) := by
  intro v hv p hp hl hk hpl
  obtain ⟨ps, hps, f, hf, hkp, htag⟩ := T.tag_parent v p hp hl hk
  by_cases hpa : p = a
  · subst hpa
    rw [Function.update_self, hu ps hps f hf hkp]
    exact htag x
  · rw [Function.update_of_ne hpa]
    refine h v (List.mem_cons_of_mem a hv) p hp hl hk ?_
    simp only [List.mem_cons, not_or]
    exact ⟨hpa, hpl⟩

theorem foldl_recVal_update_of_not_mem (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    {a : Fin G.size} (u' : BitVec hashBits) (l : List (Fin G.size)) (ha : a ∉ l)
    (x : G.Assignment) :
    l.foldl (fun x v => Function.update x v (G.recVal (z, Function.update y a u') v x)) x =
      l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x)) x := by
  refine List.foldl_ext _ _ x fun x v hv => ?_
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  simp only [recVal, Function.update_of_ne hva]

theorem foldl_cacheStep_update_of_not_mem (Fn : G.Assignment) (y : Fin G.size → BitVec hashBits)
    {a : Fin G.size} (u' : BitVec hashBits) (l : List (Fin G.size)) (ha : a ∉ l)
    (c : Cache) :
    l.foldl (G.cacheStep Fn (Function.update y a u')) c = l.foldl (G.cacheStep Fn y) c := by
  refine List.foldl_ext _ _ c fun c v hv => ?_
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  simp only [cacheStep, Function.update_of_ne hva]

theorem E_run_evalFold (T : G.Tagging) (z : G.Assignment)
    (g : G.Assignment × Cache → ℝ≥0∞) :
    ∀ (l : List (Fin G.size)), l.Pairwise (· < ·) → ∀ (x : G.Assignment) (c : Cache),
      G.Fresh T l c → G.Tagged T l x →
      E (run (l.foldlM (fun x v => Function.update x v <$> G.evalNode x v (pure (z v))) x) c)
          g =
        ∑ y : Fin G.size → BitVec hashBits,
          (Fintype.card (Fin G.size → BitVec hashBits) : ℝ≥0∞)⁻¹ *
            g (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x)) x,
              l.foldl (G.cacheStep
                (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x)) x) y) c)
  | [], _, x, c, _, _ => by
    rw [List.foldlM_nil, run_pure, E_pure]
    simp only [List.foldl_nil, sum_inv_card_mul']
  | a :: l, hpw, x, c, hfresh, htagged => by
    rw [List.pairwise_cons] at hpw
    obtain ⟨hlt, hpw⟩ := hpw
    have ha : a ∉ l := fun h => lt_irrefl a (hlt a h)
    rw [List.foldlM_cons, run_bind, E_bind]
    rcases hk : G.kind a with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
    · rw [G.evalNode_of_kind_eq_source x hk, run_map, run_pure, E_map, E_pure]
      rw [E_run_evalFold T z g l hpw _ c (Fresh.tail G hfresh)
        (Tagged.update G htagged _ fun _ _ _ _ h => by rw [hk] at h; cases h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [List.foldl_cons, G.recVal_of_kind_eq_source _ hk,
        G.cacheStep_of_eq_none _ _ _ (G.point_of_kind_eq_source _ hk)]
    · rw [G.evalNode_of_kind_eq_det x hk, run_map, run_pure, E_map, E_pure]
      rw [E_run_evalFold T z g l hpw _ c (Fresh.tail G hfresh)
        (Tagged.update G htagged _ fun _ _ _ _ h => by
          rw [hk, NodeKind.det.injEq] at h; rw [h.2])]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [List.foldl_cons, G.recVal_of_kind_eq_det _ hk,
        G.cacheStep_of_eq_none _ _ _ (G.point_of_kind_eq_det _ hk)]
    · have hpa : p ∉ a :: l := by
        simp only [List.mem_cons, not_or]
        exact ⟨ne_of_lt hp, fun h => lt_asymm hp (hlt p h)⟩
      -- the input of `a` carries the tag of `a`, so the cache does not hold it
      have htq : T.tag ⟨G.len p, x p⟩ = some a :=
        htagged a (List.mem_cons_self ..) p hp hl hk hpa
      have hcq : c ⟨G.len p, x p⟩ = none := hfresh a (List.mem_cons_self ..) _ htq
      rw [G.evalNode_of_kind_eq_hash x hk, hash, run_map, run_map, run_query,
        oracleImpl_run_inr_none hcq]
      simp only [E_map, E_bind, E_pure, E_uniform]
      have key := sum_avg_update (R := fun _ => BitVec hashBits) a
        (fun u y => g (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x))
            (Function.update x a (u.cast hl.symm)),
          l.foldl (G.cacheStep (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x))
            (Function.update x a (u.cast hl.symm))) y)
            (c.cacheQuery ⟨G.len p, x p⟩ u)))
        (fun u u' y => by
          simp only [G.foldl_recVal_update_of_not_mem z y u' l ha,
            G.foldl_cacheStep_update_of_not_mem _ y u' l ha])
      refine Eq.trans ?_ (key.trans ?_)
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [E_run_evalFold T z g l hpw _ _ (Fresh.cacheQuery G hfresh ha htq u)
          (Tagged.update G htagged _ fun _ _ _ _ h => by rw [hk] at h; cases h)]
      · refine Finset.sum_congr rfl fun y _ => ?_
        have hF : G.point ((a :: l).foldl
            (fun x v => Function.update x v (G.recVal (z, y) v x)) x) a =
            some ⟨G.len p, x p⟩ := by
          rw [G.point_of_kind_eq_hash _ hk,
            foldl_update_apply_of_not_mem (fun x v => G.recVal (z, y) v x) _ x p hpa]
        simp only [List.foldl_cons] at hF ⊢
        rw [G.cacheStep_of_eq_some _ _ _ hF, G.recVal_of_kind_eq_hash _ hk]

theorem E_run_evaluate (T : G.Tagging) (z : G.Assignment)
    (g : G.Assignment × Cache → ℝ≥0∞) :
    E (run (G.evaluate z) ∅) g =
      ∑ y : Fin G.size → BitVec hashBits,
        (Fintype.card (Fin G.size → BitVec hashBits) : ℝ≥0∞)⁻¹ *
          g (G.evalRec (z, y), G.keygenCache (z, y)) := by
  unfold Graph.evaluate
  rw [G.E_run_evalFold T z g _ (List.pairwise_lt_finRange _) _ ∅ (G.fresh_empty T _)
    (G.tagged_finRange T _)]
  rfl

end Dag.Graph

/-- Key generation of a tagged graph is a uniform record. -/
theorem E_run_keygen (S : Scheme) (T : S.graph.Tagging)
    (g : (PublicKey × S.graph.Assignment) × Cache → ℝ≥0∞) :
    E (run S.keygen ∅) g =
      ∑ ξ : S.graph.Rec, (Fintype.card S.graph.Rec : ℝ≥0∞)⁻¹ *
        g ((S.publicKey (S.graph.evalRec ξ), S.graph.evalRec ξ), S.graph.keygenCache ξ) := by
  have hA0 : (Fintype.card S.graph.Assignment : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hAt : (Fintype.card S.graph.Assignment : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold Scheme.keygen Graph.keygen
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  rw [run_bind, E_bind, S.graph.E_run_sampleAssignment]
  simp only [S.graph.E_run_evaluate T]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), mul_assoc]

/-! ## Budgets -/

/-- A lifted `ProbComp` costs nothing: the continuation keeps the whole budget. -/
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

namespace Dag.Graph

variable (G : Graph)

theorem costAtMost_sampleFold_bind {β : Type} (k : G.Assignment → OracleComp Spec β)
    {b : ℕ} :
    ∀ (l : List (Fin G.size)) (z : G.Assignment),
      CostAtMost
        (l.foldlM (fun z v => Function.update z v <$> sampleBits (G.len v)) z >>= k) b →
      ∀ y : G.Assignment, CostAtMost (k (l.foldl (fun z v => Function.update z v (y v)) z)) b
  | [], z, h, y => by rwa [List.foldlM_nil, pure_bind] at h
  | a :: l, z, h, y => by
    rw [List.foldlM_cons, bind_assoc, sampleBits, bind_map_left] at h
    have := costAtMost_liftM_bind _ _ h (y a) (by simp)
    exact costAtMost_sampleFold_bind k l _ this y

theorem costAtMost_evalFold_bind (z : G.Assignment) {β : Type}
    (k : G.Assignment → OracleComp Spec β) :
    ∀ (l : List (Fin G.size)) (x : G.Assignment) (b : ℕ),
      CostAtMost
        (l.foldlM (fun x v => Function.update x v <$> G.evalNode x v (pure (z v))) x >>= k) b →
      (l.map G.nodeCost).sum ≤ b ∧
        ∀ y : Fin G.size → BitVec hashBits,
          CostAtMost (k (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x)) x))
            (b - (l.map G.nodeCost).sum)
  | [], x, b, h => by
    refine ⟨by simp, fun y => ?_⟩
    rw [List.foldlM_nil, pure_bind] at h
    simpa using h
  | a :: l, x, b, h => by
    rw [List.foldlM_cons, bind_assoc] at h
    rw [List.map_cons, List.sum_cons]
    rcases hk : G.kind a with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
    · rw [G.evalNode_of_kind_eq_source x hk, map_pure, pure_bind] at h
      obtain ⟨h1, h2⟩ := costAtMost_evalFold_bind z k l _ b h
      rw [G.nodeCost_of_kind_eq_source hk, zero_add]
      refine ⟨h1, fun y => ?_⟩
      simp only [List.foldl_cons, G.recVal_of_kind_eq_source _ hk]
      exact h2 y
    · rw [G.evalNode_of_kind_eq_det x hk, map_pure, pure_bind] at h
      obtain ⟨h1, h2⟩ := costAtMost_evalFold_bind z k l _ b h
      rw [G.nodeCost_of_kind_eq_det hk, zero_add]
      refine ⟨h1, fun y => ?_⟩
      simp only [List.foldl_cons, G.recVal_of_kind_eq_det _ hk]
      exact h2 y
    · rw [G.evalNode_of_kind_eq_hash x hk, hash, bind_map_left, bind_map_left,
        costAtMost_query_bind_iff] at h
      obtain ⟨hc, h⟩ := h
      have hcost : queryCost (.inr ⟨G.len p, x p⟩) = G.nodeCost a := by
        simp [queryCost, nodeCost, hk]
      rw [hcost] at hc h
      refine ⟨?_, fun y => ?_⟩
      · have := (costAtMost_evalFold_bind z k l _ _ (h (0 : BitVec hashBits))).1
        omega
      · have := (costAtMost_evalFold_bind z k l _ _ (h (y a))).2 y
        simp only [List.foldl_cons, G.recVal_of_kind_eq_hash _ hk]
        rw [Nat.sub_add_eq]
        exact this

end Dag.Graph

/-- A budget for `S.keygen >>= k` covers key generation and leaves `B - keygenCost` for the
continuation at every record. -/
theorem costAtMost_keygen_bind (S : Scheme) {β : Type}
    (k : PublicKey × S.graph.Assignment → OracleComp Spec β) {B : ℕ}
    (h : CostAtMost (S.keygen >>= k) B) :
    S.graph.keygenCost ≤ B ∧ ∀ ξ : S.graph.Rec,
      CostAtMost (k (S.publicKey (S.graph.evalRec ξ), S.graph.evalRec ξ))
        (B - S.graph.keygenCost) := by
  have h' : CostAtMost (S.graph.sampleAssignment >>= fun z =>
      S.graph.evaluate z >>= fun x => k (S.publicKey x, x)) B := by
    simpa only [Scheme.keygen, Graph.keygen, bind_assoc, pure_bind] using h
  unfold Graph.sampleAssignment at h'
  have hs := S.graph.costAtMost_sampleFold_bind _ _ _ h'
  simp only [foldl_update_finRange] at hs
  have he : ∀ z : S.graph.Assignment,
      ((List.finRange S.graph.size).map S.graph.nodeCost).sum ≤ B ∧
        ∀ y : Fin S.graph.size → BitVec hashBits,
          CostAtMost (k (S.publicKey (S.graph.evalRec (z, y)), S.graph.evalRec (z, y)))
            (B - ((List.finRange S.graph.size).map S.graph.nodeCost).sum) := fun z =>
    S.graph.costAtMost_evalFold_bind z (fun x => k (S.publicKey x, x)) _ _ B (hs z)
  have hK : S.graph.keygenCost = ((List.finRange S.graph.size).map S.graph.nodeCost).sum := by
    rw [Graph.keygenCost, Fin.sum_univ_def]
  rw [hK]
  exact ⟨(he (fun _ => 0)).1, fun ξ => (he ξ.1).2 ξ.2⟩

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.GraphKeygenBridge; SHA256 87348555b5117ded1cff0e07d94ee9f9d9f1decb0e75a7860666def0b84b5d6b. -/
section

/-! Graph-only key generation wrappers. They deliberately require no scheme,
cut family, nonce width, or signature-size certificate. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedConstruction.GraphKeygenBridge

open OptimalOTS.Dag

/-- Attach any public-key projection to the protected graph key generator. -/
def keygen (G : Graph) {α : Type} (publicKey : G.Assignment → α) :
    OracleComp Spec (α × G.Assignment) := do
  let x ← G.keygen
  pure (publicKey x, x)

/-- The tagged graph's output and lazy-oracle cache are exactly a uniform record. -/
theorem E_run_keygen (G : Graph) {α : Type} (publicKey : G.Assignment → α)
    (T : G.Tagging) (g : (α × G.Assignment) × Cache → ℝ≥0∞) :
    E (run (keygen G publicKey) ∅) g =
      ∑ ξ : G.Rec, (Fintype.card G.Rec : ℝ≥0∞)⁻¹ *
        g ((publicKey (G.evalRec ξ), G.evalRec ξ), G.keygenCache ξ) := by
  have hA0 : (Fintype.card G.Assignment : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hAt : (Fintype.card G.Assignment : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold keygen Graph.keygen
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  rw [run_bind, E_bind, G.E_run_sampleAssignment]
  simp only [G.E_run_evaluate T]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), mul_assoc]

/-- A pathwise budget pays the graph's exact keygen cost before every record's
continuation. This does not use the old fixed-width signature proxy. -/
theorem costAtMost_keygen_bind (G : Graph) {α β : Type}
    (publicKey : G.Assignment → α) (k : α × G.Assignment → OracleComp Spec β) {B : ℕ}
    (h : CostAtMost (keygen G publicKey >>= k) B) :
    G.keygenCost ≤ B ∧ ∀ ξ : G.Rec,
      CostAtMost (k (publicKey (G.evalRec ξ), G.evalRec ξ)) (B - G.keygenCost) := by
  have h' : CostAtMost (G.sampleAssignment >>= fun z =>
      G.evaluate z >>= fun x => k (publicKey x, x)) B := by
    simpa only [keygen, Graph.keygen, bind_assoc, pure_bind] using h
  unfold Graph.sampleAssignment at h'
  have hs := G.costAtMost_sampleFold_bind _ _ _ h'
  simp only [OptimalOTS.foldl_update_finRange] at hs
  have he : ∀ z : G.Assignment,
      ((List.finRange G.size).map G.nodeCost).sum ≤ B ∧
        ∀ y : Fin G.size → BitVec hashBits,
          CostAtMost (k (publicKey (G.evalRec (z, y)), G.evalRec (z, y)))
            (B - ((List.finRange G.size).map G.nodeCost).sum) := fun z =>
    G.costAtMost_evalFold_bind z (fun x => k (publicKey x, x)) _ _ B (hs z)
  have hK : G.keygenCost = ((List.finRange G.size).map G.nodeCost).sum := by
    rw [Graph.keygenCost, Fin.sum_univ_def]
  rw [hK]
  exact ⟨(he (fun _ => 0)).1, fun ξ => (he ξ.1).2 ξ.2⟩

end OptimalOTS.WeightedConstruction.GraphKeygenBridge

#print axioms OptimalOTS.WeightedConstruction.GraphKeygenBridge.E_run_keygen
#print axioms OptimalOTS.WeightedConstruction.GraphKeygenBridge.costAtMost_keygen_bind
end
end

/- Original module: Submissions.UpperCompressions.Resources; SHA256 fa929130369bbac94132097090b0ab744b933cc3ff09a7433d8c76c41edea869. -/
section

/-! Honest-party resource bounds and wire-size bounds for the generic DAG adapter. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.AlgorithmAdapter

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials


theorem length_encode (G : Graph) (A : Finset (Fin G.size)) (x : G.Assignment) :
    (G.encode A x).length = G.revealBits A := by
  unfold Graph.encode Graph.revealBits
  rw [List.length_flatMap]
  simp only [toBits, List.length_ofFn]
  rw [← List.sum_toFinset _ ((List.nodup_finRange _).filter _)]
  congr 1
  ext v
  simp

theorem signLoop_returns (S : Scheme) (x : S.graph.Assignment) (m : Message) :
    ∀ k tried σ, some σ ∈ support (S.signLoop x m k tried) →
      ∃ i, σ.2 = S.graph.encode (S.sets i) x
  | 0, _, _, h => by simp [Scheme.signLoop] at h
  | k + 1, tried, σ, h => by
    rw [Scheme.signLoop] at h
    split_ifs at h with hf
    · rw [support_bind] at h
      simp only [Set.mem_iUnion] at h
      obtain ⟨j, _, h⟩ := h
      rw [support_bind] at h
      simp only [Set.mem_iUnion] at h
      obtain ⟨i, _, h⟩ := h
      split_ifs at h with hi
      · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h
        exact ⟨⟨i, hi⟩, congrArg Prod.snd h⟩
      · exact signLoop_returns S x m k _ σ h
    · simp at h

theorem signatureSize (S : Scheme) :
    S.toAlgorithm.SignatureSizeAtMost (nonceBits + (maxSignatureBits - nonceBits)) := by
  change ∀ (sk : S.graph.Assignment) (m : Message) (σ : Signature),
    some σ ∈ support (S.sign sk m) → (encodeSignature σ).length ≤ nonceBits + (maxSignatureBits - nonceBits)
  intro sk m σ hσ
  obtain ⟨i, hi⟩ := signLoop_returns S sk m trials ∅ σ hσ
  rw [length_encodeSignature, hi, length_encode]
  have h := S.reveal_le i
  omega

theorem rejectsOversized (S : Scheme) :
    S.toAlgorithm.RejectsOversized (nonceBits + (maxSignatureBits - nonceBits)) := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    nonceBits + (maxSignatureBits - nonceBits) < (encodeSignature σ).length →
      true ∉ support (S.verify pk m σ)
  intro pk m σ hlen hmem
  change nonceBits + (maxSignatureBits - nonceBits) < (encodeSignature σ).length at hlen
  rw [length_encodeSignature] at hlen
  change true ∈ support (S.verify pk m σ) at hmem
  rw [Scheme.verify, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨i, _, hmem⟩ := hmem
  by_cases hi : i < numCuts
  · have hwrong : σ.2.length ≠ S.graph.revealBits (S.sets ⟨i, hi⟩) := by
      have h := S.reveal_le ⟨i, hi⟩
      omega
    simp only [dif_pos hi, if_neg hwrong, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
  · simp [hi] at hmem

theorem keygenCost (S : Scheme) : S.toAlgorithm.KeygenCostAtMost keygenBudget :=
  AlgorithmCosts.Dag.Scheme.costAtMost_keygen S

theorem signCost (S : Scheme) (hidx : blockCost (msgBits + nonceBits) = 1) :
    S.toAlgorithm.SignCostAtMost trials :=
  AlgorithmCosts.Dag.Scheme.costAtMost_sign S hidx

theorem verifyCost (S : Scheme) (hidx : blockCost (msgBits + nonceBits) = 1)
    {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    S.toAlgorithm.VerifyCostAtMost (1 + v) :=
  AlgorithmCosts.Dag.Scheme.costAtMost_verify S hidx hv

end OptimalOTS.AlgorithmAdapter
end
end

