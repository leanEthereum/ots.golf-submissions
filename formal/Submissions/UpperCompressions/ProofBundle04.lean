import Submissions.UpperCompressions.ProofBundle02
import Submissions.UpperCompressions.ProofBundle00
import Submissions.UpperCompressions.ProofBundle03
import OptimalOTS.Dag

/- Original module: Submissions.UpperCompressions.WeightedUniform; SHA256 1048401243117e94ff5e784a6fb50e5029194a4c97ff4e2d8291106ed5e242c4. -/
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

#print axioms uniform_option_miss
end OptimalOTS.WeightedSampling.Availability
end
end

/- Original module: Submissions.UpperCompressions.WeightedFreshness; SHA256 1f625e3d86a0e76c02182ee58792a5ec0445872382f3dc5ec5c7f85864a376ab. -/
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

#print axioms OptimalOTS.WeightedFreshness.graph_keygen_preservesLength
end
end

/- Original module: Submissions.UpperCompressions.AvailabilityEnvelope; SHA256 6e558d8908ca589907e19d263a4b238a4927393d45ccc8cfb960a01b37cca146. -/
section

namespace WeightedAvailability
open ENNReal
noncomputable section

def miss : ℝ≥0∞ := 524243/524288

theorem replacement_envelope :
    (miss + (2:ℝ≥0∞)^20 / 2^86)^(2^20:ℕ) ≤ 1/(2:ℝ≥0∞)^129 := by
  have h := ENNReal.ofReal_le_ofReal empirical_failure
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1-8999/104857600)] at h
  have hb : ENNReal.ofReal (1-(8999:ℝ)/104857600) =
      (104848601:ℝ≥0∞)/104857600 := by norm_num [ENNReal.ofReal_div_of_pos]
  have ht : ENNReal.ofReal (((2:ℝ)^129)⁻¹) = 1/(2:ℝ≥0∞)^129 := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hb,ht] at h
  have hbase : miss + (2:ℝ≥0∞)^20/2^86 ≤ (104848601:ℝ≥0∞)/104857600 := by
    have hr : (524243:ℝ)/524288+(2:ℝ)^20/2^86 ≤ 104848601/104857600 := by norm_num
    have he := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_add (by positivity) (by positivity)] at he
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<524288),
      ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ)<2^86),
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<104857600)] at he
    simpa only [miss, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2)] using he
  exact (pow_le_pow_left' hbase _).trans h

#print axioms replacement_envelope
end
end WeightedAvailability
end

/- Original module: Submissions.UpperCompressions.WeightedFibers; SHA256 0c17866699dc7b2c9e6d301594729346a2b81019075810ccb76f70a2b7c58d0d. -/
section

/-! Exact mixed72 decoder fibers, lifted from raw129 aliases to full256 oracle
answers. These are distributional counts, not adaptive security theorems. -/

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

/-- Every predicate on low bits leaves all high bits free. -/
def truncPredicateEquiv {n w : ℕ} (hw : w ≤ n) (p : BitVec w → Prop) :
    {x : BitVec n // p (x.setWidth w)} ≃ {x : BitVec w // p x} × BitVec (n-w) where
  toFun x := (⟨x.val.setWidth w, x.property⟩, (x.val >>> w).setWidth (n-w))
  invFun a := ⟨TruncFiber.join hw a.1.val a.2, by simpa using a.1.property⟩
  left_inv x := Subtype.ext (TruncFiber.join_high hw x.val rfl)
  right_inv a := by
    apply Prod.ext
    · exact Subtype.ext (TruncFiber.low_join hw a.1.val a.2)
    · exact TruncFiber.high_join hw a.1.val a.2

theorem card_truncPredicate {n w : ℕ} (hw : w ≤ n) (p : BitVec w → Prop) [dp : DecidablePred p] :
    (@Finset.filter (BitVec n) (fun x => p (x.setWidth w))
      (fun x => dp (x.setWidth w)) Finset.univ).card =
      (@Finset.filter (BitVec w) p dp Finset.univ).card * 2^(n-w) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (truncPredicateEquiv hw p),
    Fintype.card_prod, Fintype.card_subtype, Fintype.card_bitVec]

theorem decodeRaw_eq_some (x : BitVec 129) (i : Fin M) :
    decodeRaw x = some i ↔ rawClass x = some (classEquiv.symm i) := by
  rw [decodeRaw, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c, hc, hi⟩
    have he : c = classEquiv.symm i := by
      apply classEquiv.injective
      simpa using hi
    simpa [he] using hc
  · intro h
    exact ⟨classEquiv.symm i, h, classEquiv.apply_symm_apply i⟩

theorem decodeRaw_fiber (i : Fin M) :
    (Finset.univ.filter fun x : BitVec 129 => decodeRaw x = some i).card = 2^(tier i+1) := by
  have he : (Finset.univ.filter fun x : BitVec 129 => decodeRaw x = some i) =
      Finset.univ.filter fun x : BitVec 129 => rawClass x = some (classEquiv.symm i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decodeRaw_eq_some]
  rw [he, rawClass_fiber]
  rfl

/-- A raw decoder fiber for any projection of aliases. -/
def rawMapFiberEquiv {β : Type} (f : Alias → β) (b : β) :
    {x : BitVec 129 // (rawAlias x).map f = some b} ≃ {a : Alias // f a = b} :=
  (Equiv.ofBijective
    (fun a : {a : Alias // f a = b} =>
      (⟨aliasRaw a.val, by simp [a.property]⟩ :
        {x : BitVec 129 // (rawAlias x).map f = some b}))
    (by
      constructor
      · intro a c h
        apply Subtype.ext
        have he := congrArg (fun x : {x : BitVec 129 // (rawAlias x).map f = some b} =>
          rawAlias x.val) h
        simpa using he
      · intro x
        have hx := x.property
        rw [Option.map_eq_some_iff] at hx
        obtain ⟨a, ha, hb⟩ := hx
        exact ⟨⟨a, hb⟩, Subtype.ext (aliasRaw_of_rawAlias ha)⟩)).symm

def aliasTierFiberEquiv (j : Tier) :
    {a : Alias // a.1.1 = j} ≃ Fin (population j) × Fin (2^(j.val+1)) where
  toFun a := by
    rcases a with ⟨⟨⟨j', k⟩, r⟩, h⟩
    cases h
    exact (k, r)
  invFun a := ⟨⟨⟨j, a.1⟩, a.2⟩, rfl⟩
  left_inv := by rintro ⟨⟨⟨j', k⟩, r⟩, h⟩; cases h; rfl
  right_inv a := by cases a; rfl

def rawTier (x : BitVec 129) : Option Tier := (rawAlias x).map fun a => a.1.1

theorem rawTier_fiber (j : Tier) :
    (Finset.univ.filter fun x : BitVec 129 => rawTier x = some j).card =
      population j * 2^(j.val+1) := by
  change (Finset.univ.filter fun x : BitVec 129 =>
    (rawAlias x).map (fun a => a.1.1) = some j).card = _
  rw [← Fintype.card_subtype,
    Fintype.card_congr (rawMapFiberEquiv (fun a => a.1.1) j),
    Fintype.card_congr (aliasTierFiberEquiv j), Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

def acceptedEquiv : {x : BitVec 129 // (rawAlias x).isSome} ≃ Alias :=
  (Equiv.ofBijective
    (fun a : Alias => (⟨aliasRaw a, by simp⟩ : {x : BitVec 129 // (rawAlias x).isSome}))
    (by
      constructor
      · intro a b h
        have he := congrArg (fun x : {x : BitVec 129 // (rawAlias x).isSome} => rawAlias x.val) h
        simpa using he
      · intro x
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp x.property
        exact ⟨a, Subtype.ext (aliasRaw_of_rawAlias ha)⟩)).symm

theorem accepted_raw_count :
    (Finset.univ.filter fun x : BitVec 129 => (rawAlias x).isSome).card = A := by
  rw [← Fintype.card_subtype, Fintype.card_congr acceptedEquiv, card_alias]

theorem decodeRaw_isSome (x : BitVec 129) : (decodeRaw x).isSome = (rawAlias x).isSome := by
  simp [decodeRaw, rawClass]

theorem accepted_decodeRaw_count :
    (Finset.univ.filter fun x : BitVec 129 => (decodeRaw x).isSome).card = A := by
  simp only [decodeRaw_isSome]
  exact accepted_raw_count

/-- Every early tier has mass19/2^24, and the final tier has mass91/2^24. -/
theorem tier_alias_count (j : Tier) : population j * 2^(j.val+1) =
    (if j.val < 71 then 19 else 91) * 2^105 := by
  by_cases h : j.val < 71
  · change WeightedResearch92.tierClasses j.val * 2^(j.val+1) = _
    rw [WeightedResearch92.tierClasses, if_pos h, if_pos h, Nat.mul_assoc, ← pow_add]
    have he : 104 - j.val + (j.val+1) = 105 := by omega
    rw [he]
  · have hj : j.val = 71 := by have := j.isLt; omega
    norm_num [population, WeightedResearch92.tierClasses, hj]

theorem rawTier_fiber_exact (j : Tier) :
    (Finset.univ.filter fun x : BitVec 129 => rawTier x = some j).card =
      (if j.val < 71 then 19 else 91) * 2^105 := by
  rw [rawTier_fiber, tier_alias_count]


end
end OptimalOTS.WeightedConstruction.WeightedSchedule

#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.decodeRaw_fiber
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.rawTier_fiber

end

/- Original module: Submissions.UpperCompressions.WeightedOutputFibers; SHA256 8983ac7ee0af77c10d6d1fac294a7eab44afcc98345c47540b5b598a77d25364. -/
section

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter tier
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

theorem decode_fiber (i : Fin M) :
    (Finset.univ.filter fun x : BitVec 256 => decode x = some i).card =
      2^(tier i+1) * 2^127 := by
  have h := card_truncPredicate (n := 256) (w := 129) (by omega)
    (fun x => decodeRaw x = some i)
  exact h.trans (congrArg (fun k : ℕ => k * 2^(256-129)) (decodeRaw_fiber i))


theorem accepted_decode_count :
    (Finset.univ.filter fun x : BitVec 256 => (decode x).isSome).card = A * 2^127 := by
  have h := card_truncPredicate (n := 256) (w := 129) (by omega)
    (fun x => (decodeRaw x).isSome = true)
  exact h.trans (congrArg (fun k : ℕ => k * 2^(256-129)) accepted_decodeRaw_count)



end
end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.decode_fiber
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.accepted_decode_count
end

/- Original module: Submissions.UpperCompressions.WideAvailability; SHA256 3561e0a633e212c12fd0e4d3712a25ffa77088c6e11c3f46272eadb3f78ef170. -/
section

/-! Honest signing availability for the concrete weighted92 construction.
The nonce draws may repeat; the proof uses the actual memoized random oracle.
Strong security remains a separate obligation. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000

namespace OptimalOTS.WeightedConstruction.WideHonest
open WideForest
open WeightedSampling.Availability
attribute [local irreducible] Finset.univ Finset.filter
attribute [local irreducible] WeightedResearch92.classes WeightedResearch92.acceptedAliases

theorem uniform_miss (a : ℝ≥0∞) :
    E ($ᵗ BitVec hashBits) (fun w => if (forestScheme.decode w).isNone then a else 0) =
      _root_.WeightedAvailability.miss*a := by
  change E ($ᵗ BitVec 256) (fun w => if (WeightedSchedule.decode w).isNone then a else 0) = _
  rw [uniform_option_miss WeightedSchedule.decode (WeightedSchedule.A*2^127)
    WeightedSchedule.accepted_decode_count a]
  have hA : WeightedSchedule.A = 45*2^110 := WeightedResearch92.aliases_exact
  rw [hA]
  congr 1
  unfold _root_.WeightedAvailability.miss
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness)
    (by norm_num) (by finiteness)).2
  norm_num

theorem sign_failure_fresh (x : forestScheme.graph.Assignment) (m : Message) (c : Cache)
    (hf : ∀ η : BitVec 86, c ⟨msgBits+86,m++η⟩ = none) :
    E (run (forestScheme.sign x m) c) (fun p => if p.1.isNone then 1 else 0) ≤
      1/(2:ℝ≥0∞)^129 := by
  rw [WeightedScheme.Scheme.sign,run_map,E_map]
  simp only [Option.isNone_map]
  have h := WeightedSampling.Availability.loop_failure 86 forestScheme.decode forestScheme.tier
    m signBudget _root_.WeightedAvailability.miss (fun a => (uniform_miss a).le)
    signBudget ∅ c (by simp) (fun η _ => hf η)
  have hh : (_root_.WeightedAvailability.miss+(signBudget:ℝ≥0∞)/2^86)^signBudget ≤
      1/(2:ℝ≥0∞)^129 := by
    simpa only [signBudget,Nat.cast_pow,Nat.cast_ofNat] using
      _root_.WeightedAvailability.replacement_envelope
  exact h.trans hh

theorem graph_hashInputsAvoid : WeightedFreshness.HashInputsAvoid graph (msgBits+86) := by
  intro v
  obtain ⟨n,rfl⟩ := nameEquiv.surjective v
  erw [graph_kind_fin]
  cases n <;> simp [kindOf,graph_len_fin,Name.len,msgBits]

theorem keygen_fresh (p : (PublicKey × forestScheme.graph.Assignment) × Cache)
    (hp : p ∈ support (run forestScheme.keygen ∅)) (q : Query) (hq : q.1 = msgBits+86) :
    p.2 q = none := by
  have h : WeightedFreshness.PreservesLength (msgBits+86) forestScheme.keygen :=
    WeightedFreshness.PreservesLength.bind
      (WeightedFreshness.graph_keygen_preservesLength graph graph_hashInputsAvoid)
      (fun _ => WeightedFreshness.PreservesLength.of_pure _)
  simpa using h ∅ p hp q hq

theorem signing_failure_half : forestScheme.toAlgorithm.SigningFailureAtMost (1/2^129) := by
  intro message
  change probTrue (do
    let kg ← forestScheme.keygen
    let σ ← forestScheme.sign kg.2 (message kg.1)
    pure σ.isNone) ≤ _
  rw [WeightedFreshness.probTrue_eq_E_run,run_bind,E_bind]
  simp only [run_bind,E_bind,run_pure,E_pure]
  calc
    _ ≤ E (run forestScheme.keygen ∅) (fun _ => (1/2^129 : ℝ≥0∞)) := by
      refine expectedValue_mono_of_support fun p hp => ?_
      apply sign_failure_fresh p.1.2 (message p.1.1) p.2
      intro η
      exact keygen_fresh p hp ⟨msgBits+86,message p.1.1++η⟩ rfl
    _ ≤ _ := E_const_le _ _

theorem signing_failure : forestScheme.toAlgorithm.SigningFailureAtMost (1/2^128) := by
  intro message
  apply (signing_failure_half message).trans
  rw [one_div,one_div]
  apply ENNReal.inv_le_inv.mpr
  norm_num

theorem typed_admissible : forestScheme.toAlgorithm.Admissible (1/2^128) where
  failure_lt_one := by norm_num
  correct := typed_correct
  verifyDeterministic := typed_verifyDeterministic
  signingFailure := signing_failure
  signatureSize := typed_signatureSize
  rejectsOversized := typed_rejectsOversized
  keygenCost := typed_keygenCost
  signCost := typed_signCost

theorem admissible : WideWire.scheme.Admissible :=
  WireAdapter.admissible WideWire.typed WideWire.decode WideWire.decode_encode
    WideWire.canonical typed_admissible

#print axioms uniform_miss
#print axioms signing_failure_half
#print axioms admissible
end OptimalOTS.WeightedConstruction.WideHonest
end
end

/- Original module: Submissions.UpperCompressions.ReplacementSelector; SHA256 15225568de6313f16580cec57ba55192db75670cc49b464a53a716ab9c74770b. -/
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

#print axioms select_eq_firstMinimumEvent
#print axioms firstMinimumEvent_map_iff
#print axioms iid_select_probability
#print axioms tagged_candidate_target_iff
#print axioms iid_tagged_table_probability

end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementProgram; SHA256 3a9cb96d49b4c117c61c2d66a57550bdae8254d4e4359cf60bf02ac0f21f81e9. -/
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

#print axioms E_drawList_ofReal
#print axioms E_loop_fixed_row_target

end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementPrefix; SHA256 ffae57a76caddad93991471b4c95d76011dd81a04e1064c9e64f56b750e0127e. -/
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
local instance stagedLocal_ReplacementPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α

abbrev PublicStep := Σ t : Spec.Domain, Spec.Range t
abbrev PublicTrace := List PublicStep
abbrev PrefixM := OptionT (StateT PublicTrace ProbComp)

/-- Trace is stored in reverse chronological order. `none` means the program
requested the distinguished hash input; that request is not answered. All free
uniform choices are preserved and recorded, so their revelation is allowed. -/
def prefixImpl (u : Query) (table : Query → BitVec hashBits) : QueryImpl Spec PrefixM
  | .inl n => OptionT.mk fun trace => do
      let a ← HasQuery.query (spec := unifSpec) (m := ProbComp) n
      pure (some a, ⟨.inl n, a⟩ :: trace)
  | .inr q => OptionT.mk fun trace =>
      if q = u then pure (none, trace)
      else pure (some (table q), ⟨.inr q, table q⟩ :: trace)

def prefixRun {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) : ProbComp (Option α × PublicTrace) :=
  (OptionT.run (simulateQ (prefixImpl u table) oa)).run []

theorem prefixImpl_target (u : Query) (table : Query → BitVec hashBits) (trace : PublicTrace) :
    (OptionT.run (prefixImpl u table (.inr u))).run trace = pure (none, trace) := by
  simp [prefixImpl, OptionT.run, OptionT.mk, StateT.run]

theorem prefixImpl_hash_of_ne (u q : Query) (table : Query → BitVec hashBits)
    (hqu : q ≠ u) (trace : PublicTrace) :
    (OptionT.run (prefixImpl u table (.inr q))).run trace =
      pure (some (table q), ⟨.inr q, table q⟩ :: trace) := by
  simp [prefixImpl, OptionT.run, OptionT.mk, StateT.run, hqu]

theorem prefixImpl_eq_of_eq_off (u : Query) (table table' : Query → BitVec hashBits)
    (h : ∀ q, q ≠ u → table q = table' q) : prefixImpl u table = prefixImpl u table' := by
  funext t
  cases t with
  | inl n => rfl
  | inr q =>
    by_cases hqu : q = u
    · simp [prefixImpl, hqu]
    · simp [prefixImpl, hqu, h q hqu]

/-- An arbitrary adaptive oracle program, including all its random choices and
every observed response before querying u, has identical prefix distribution
under tables that differ only at u. No nonadaptive-query hypothesis is used. -/
theorem prefixRun_eq_of_eq_off {α : Type} (u : Query)
    (table table' : Query → BitVec hashBits) (oa : OracleComp Spec α)
    (h : ∀ q, q ≠ u → table q = table' q) :
    prefixRun u table oa = prefixRun u table' oa := by
  unfold prefixRun
  rw [prefixImpl_eq_of_eq_off u table table' h]

theorem prefixRun_update {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (y : BitVec hashBits) :
    prefixRun u (Function.update table u y) oa = prefixRun u table oa := by
  apply prefixRun_eq_of_eq_off
  intro q hqu
  exact Function.update_of_ne hqu _ _

/-- Any event about the full public prefix, including a chosen adaptive stopping
trace, supplies evidence whose likelihood is independent of the hidden answer. -/
theorem prefix_event_update {α : Type} (u : Query) (table : Query → BitVec hashBits)
    (oa : OracleComp Spec α) (event : Option α × PublicTrace → Prop)
    (y : BitVec hashBits) :
    E (prefixRun u (Function.update table u y) oa)
        (fun t => if event t then 1 else 0) =
      E (prefixRun u table oa) (fun t => if event t then 1 else 0) := by
  rw [prefixRun_update]

#print axioms prefixRun_eq_of_eq_off
#print axioms prefixRun_update
#print axioms prefix_event_update

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementHybridPrefix; SHA256 4c1b2de956340bfcac04e4a2c4911d852f29dd3dcddb7aaa7da93753db188807. -/
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
local instance stagedLocal_ReplacementHybridPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α

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

#print axioms oracleImpl_overwrite
#print axioms hybridPrefix_overwrite

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementPublicCost; SHA256 11fe4540be39973a30fb18a9667e31327b2ac763310d9d71f0e1331cebb8c693. -/
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

#print axioms publicHit_eq_prefix
#print axioms publicHit_sum_le
#print axioms publicHit_sum_le_indexPaid
#print axioms paid_shared_budget

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.WideQuery; SHA256 877a0f4b5f64b451c8dbbec0c4494472de1e75f3f9e8c157effbf6da6bd9a121. -/
section

namespace OptimalOTS.WeightedConstruction.WideForest

abbrev EncInput := Message × BitVec 86

def encQuery (u : EncInput) : Query := ⟨msgBits + 86, u.1 ++ u.2⟩

theorem encQuery_length (u : EncInput) : (encQuery u).1 = 342 := rfl

theorem ne_encQuery_of_length_ne {q : Query} (hq : q.1 ≠ msgBits + 86)
    (u : EncInput) : q ≠ encQuery u := by
  intro h
  exact hq (congrArg Sigma.fst h)

end OptimalOTS.WeightedConstruction.WideForest
end

/- Original module: Submissions.UpperCompressions.WideValues; SHA256 2b55772377267cc9c5837610c26b8f924eafca0e2472ce309dd846e216c853ea. -/
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

open Name

/-- Records of the concrete graph. -/
abbrev Rec := graph.Rec

/-- The value of node `n` in the record `ξ`. -/
def val (ξ : Rec) (n : Name) : BitVec n.len := (graph.evalRec ξ n.fin).cast (graph_len_fin n)

/-! ### Auxiliary cast lemmas -/

theorem lowWord_cast {n m : ℕ} (h : n = m) (x : BitVec n) : lowWord (x.cast h) = lowWord x := by
  subst h; rfl

theorem lowWord_lowWord {n : ℕ} (x : BitVec n) : lowWord (lowWord x) = lowWord x := BitVec.setWidth_eq _

theorem cast_cast_eq {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x := by
  subst h₁; rfl

/-- The node equation of the concrete graph, with the kind computed by `kindOf`. -/
theorem evalRec_apply_fin (ξ : Rec) (n : Name) :
    graph.evalRec ξ n.fin =
      (kindOf n.fin n (ofFin_fin n)).value (graph.evalRec ξ) (ξ.1 n.fin) (ξ.2 n.fin) := by
  have := Graph.evalRec_apply graph ξ n.fin
  rwa [graph_kind_fin] at this

theorem lowWord_evalRec (ξ : Rec) (n : Name) : lowWord (graph.evalRec ξ n.fin) = lowWord (val ξ n) := by
  unfold val
  exact (lowWord_cast _ _).symm

theorem val_src (ξ : Rec) (k : Fin 54) : val ξ (src k) = (ξ.1 (src k).fin).cast (graph_len_fin _) := by
  unfold val
  rw [evalRec_apply_fin]
  rfl

theorem lowWord_eq_self (x : BitVec 129) : lowWord x = x := BitVec.setWidth_eq _

/-- Truncation loses nothing on a value of 129 bits (e.g. the value of `prev k t`). -/
theorem lowWord_injective_of_len {w : ℕ} (hw : w = 129) :
    Function.Injective (lowWord : BitVec w → BitVec 129) := by
  subst hw
  intro x y e
  rwa [lowWord_eq_self, lowWord_eq_self] at e

/-- The input of the chain hash `ch k t`: its tweak, then the value of `prev k t`. -/
theorem val_ci (ξ : Rec) (k : Fin 54) (t : Fin 18) :
    val ξ (ci k t) = tw (ch k t) ++ lowWord (val ξ (prev k t)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw (ch k t) ++ lowWord (graph.evalRec ξ (prev k t).fin) = _
  rw [lowWord_evalRec]
  rfl

theorem val_ch (ξ : Rec) (k : Fin 54) (t : Fin 18) : val ξ (ch k t) = ξ.2 (ch k t).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem lowWord_val_ch (ξ : Rec) (k : Fin 54) (t : Fin 18) :
    lowWord (graph.evalRec ξ (ch k t).fin) = lowWord (ξ.2 (ch k t).fin) := by
  rw [lowWord_evalRec, val_ch]
  rfl

theorem val_cv (ξ : Rec) (k : Fin 54) (t : Fin 18) : val ξ (cv k t) = lowWord (ξ.2 (ch k t).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show lowWord (graph.evalRec ξ (ch k t).fin) = _
  exact lowWord_val_ch ξ k t

theorem lowWord_val_cv (ξ : Rec) (k : Fin 54) (t : Fin 18) :
    lowWord (graph.evalRec ξ (cv k t).fin) = lowWord (ξ.2 (ch k t).fin) := by
  rw [lowWord_evalRec, val_cv]
  exact lowWord_lowWord _

/-- The first chain input reads the source. -/
theorem val_ci_zero (ξ : Rec) (k : Fin 54) (t : Fin 18) (ht : t.val = 0) :
    val ξ (ci k t) = tw (ch k t) ++ val ξ (src k) := by
  have e : prev k t = src k := by simp [Name.prev, ht]
  rw [val_ci, e]
  exact congrArg (tw (ch k t) ++ ·) (lowWord_eq_self _)

/-- A later chain input reads the previous chain hash. -/
theorem val_ci_succ (ξ : Rec) (k : Fin 54) (t : Fin 18) (ht : ¬ t.val = 0) :
    val ξ (ci k t) = tw (ch k t) ++ lowWord (ξ.2 (ch k ⟨t.val - 1, by omega⟩).fin) := by
  have e : prev k t = cv k ⟨t.val - 1, by omega⟩ := by simp [Name.prev, ht]
  rw [val_ci, e, val_cv]
  exact congrArg (tw (ch k t) ++ ·) (lowWord_lowWord _)

theorem val_gc (ξ : Rec) (j : Fin 18) :
    val ξ (gc j) = tw (gh j) ++ cat3 (lowWord (ξ.2 (ch (chainOf j 0) 17).fin))
      (lowWord (ξ.2 (ch (chainOf j 1) 17).fin)) (lowWord (ξ.2 (ch (chainOf j 2) 17).fin)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw (gh j) ++ cat3 (lowWord (graph.evalRec ξ (cv (chainOf j 0) 17).fin))
    (lowWord (graph.evalRec ξ (cv (chainOf j 1) 17).fin))
    (lowWord (graph.evalRec ξ (cv (chainOf j 2) 17).fin)) = _
  rw [lowWord_val_cv, lowWord_val_cv, lowWord_val_cv]

theorem val_gh (ξ : Rec) (j : Fin 18) : val ξ (gh j) = ξ.2 (gh j).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem lowWord_val_gh (ξ : Rec) (j : Fin 18) :
    lowWord (graph.evalRec ξ (gh j).fin) = lowWord (ξ.2 (gh j).fin) := by
  rw [lowWord_evalRec, val_gh]
  rfl

theorem val_gv (ξ : Rec) (j : Fin 18) : val ξ (gv j) = lowWord (ξ.2 (gh j).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show lowWord (graph.evalRec ξ (gh j).fin) = _
  exact lowWord_val_gh ξ j

theorem lowWord_val_gv (ξ : Rec) (j : Fin 18) :
    lowWord (graph.evalRec ξ (gv j).fin) = lowWord (ξ.2 (gh j).fin) := by
  rw [lowWord_evalRec, val_gv]
  exact lowWord_lowWord _

theorem val_rc (ξ : Rec) : val ξ rc = tw rh ++ cat18 fun l => lowWord (ξ.2 (gh l).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw rh ++ cat18 (fun l => lowWord (graph.evalRec ξ (gv l).fin)) = _
  exact congrArg (fun a => tw rh ++ cat18 a) (funext fun l => lowWord_val_gv ξ l)

theorem val_rh (ξ : Rec) : val ξ rh = ξ.2 rh.fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

/-- The public key of a record: the first 128 bits of the root. -/
def pkOf (ξ : Rec) : BitVec 128 := lowPk (ξ.2 rh.fin)

/-! ## Hash nodes and keygen points -/

/-- The node whose value a hash node hashes: its tweaked input. -/
def hashParent : Name → Option Name
  | ch k t => some (ci k t)
  | gh j => some (gc j)
  | rh => some rc
  | _ => none

theorem hashParent_isSome_iff (h : Name) : (hashParent h).isSome ↔ h.cost ≠ 0 := by
  cases h <;> simp [hashParent, Name.cost]

theorem cost_ne_zero_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.cost ≠ 0 :=
  (hashParent_isSome_iff h).1 (by rw [hp]; rfl)

theorem child_hashParent {h p : Name} (hp : hashParent h = some p) : child p = some h := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  all_goals rfl

/-- The input of a hash node has length 145 (chains), 403 (groups) or 2338 (root). -/
theorem len_hashParent_cases {h p : Name} (hp : hashParent h = some p) :
    p.len = 145 ∨ p.len = 403 ∨ p.len = 2338 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp [Name.len]

/-- The input of a hash node never has the length of an index query. -/
theorem len_hashParent_ne_enc {h p : Name} (hp : hashParent h = some p) :
    p.len ≠ msgBits + 86 := by
  have e : msgBits + 86 = 342 := rfl
  rw [e]
  rcases len_hashParent_cases hp with e | e | e <;> omega

/-- The keygen point of the hash node `h` with parent `p`: the bare input of `h`.  The hash node
is not written next to the input (the oracle has no labels); it is read back from the tweak
(`tagNat_pointOf`). -/
def pointOf (ξ : Rec) (_h p : Name) : Query := ⟨p.len, val ξ p⟩

/-- The value of the parent of a hash node starts with the tweak of that hash node. -/
theorem tagNat_val {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    tagNat ⟨p.len, val ξ p⟩ = h.idx := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · rw [val_ci]; exact tagNat_tw_append (n := 129) _ _
  · rw [val_gc]; exact tagNat_tw_append (n := 387) _ _
  · rw [val_rc]; exact tagNat_tw_append (n := 2322) _ _

/-- A keygen point carries the index of its hash node. -/
theorem tagNat_pointOf {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    tagNat (pointOf ξ h p) = h.idx :=
  tagNat_val hp ξ

theorem pointOf_inj_left {ξ ξ' : Rec} {h h' p p' : Name} (hp : hashParent h = some p)
    (hp' : hashParent h' = some p') (e : pointOf ξ h p = pointOf ξ' h' p') : h = h' := by
  apply Name.idx_injective
  rw [← tagNat_pointOf hp ξ, ← tagNat_pointOf hp' ξ', e]

theorem pointOf_inj_input {ξ ξ' : Rec} {h p : Name} (e : pointOf ξ h p = pointOf ξ' h p) :
    val ξ p = val ξ' p := by
  simp only [pointOf, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
  exact e

/-- A keygen point is not an index query: its length is 145, 403 or 2338, never 387. -/
theorem pointOf_ne_encQuery {h p : Name} (hp : hashParent h = some p) (ξ : Rec)
    (u : EncInput) : pointOf ξ h p ≠ encQuery u :=
  ne_encQuery_of_length_ne (len_hashParent_ne_enc hp) u

/-- A query of the length of a hash input is not an index query. -/
theorem mk_ne_encQuery {h p : Name} (hp : hashParent h = some p) (u' : BitVec p.len)
    (u : EncInput) : (⟨p.len, u'⟩ : Query) ≠ encQuery u :=
  ne_encQuery_of_length_ne (len_hashParent_ne_enc hp) u

theorem sigma_mk_cast_eq {n m : ℕ} (h : n = m) (x : BitVec n) :
    (⟨n, x⟩ : Σ k, BitVec k) = ⟨m, x.cast h⟩ := by
  subst h; rfl

theorem sigma_val (ξ : Rec) (p : Name) :
    (⟨lenF p.fin, graph.evalRec ξ p.fin⟩ : Σ k, BitVec k) = ⟨p.len, val ξ p⟩ := by
  unfold val
  generalize graph.evalRec ξ p.fin = x
  exact sigma_mk_cast_eq (graph_len_fin p) x

theorem graph_point_fin (ξ : Rec) (h : Name) :
    graph.point (graph.evalRec ξ) h.fin = (hashParent h).map fun p => pointOf ξ h p := by
  unfold Graph.point
  rw [graph_kind_fin]
  cases h <;> simp only [kindOf, hashParent, Option.map_some, Option.map_none, pointOf]
  case ch k t => exact congrArg some (sigma_val ξ (ci k t))
  case gh j => exact congrArg some (sigma_val ξ (gc j))
  case rh => exact congrArg some (sigma_val ξ rc)

/-! ## The tagging of the concrete graph -/

/-- The hash node a query belongs to: the node whose index is written in its 16 high bits. -/
def tagOf (q : Query) : Option (Fin N) := if h : tagNat q < N then some ⟨tagNat q, h⟩ else none

theorem tagOf_eq_some_of_tagNat {q : Query} {h : Name} (e : tagNat q = h.idx) :
    tagOf q = some h.fin := by
  unfold tagOf
  rw [dif_pos (by rw [e]; exact h.idx_lt)]
  exact congrArg some (Fin.ext e)

/-- The kind of the parent of a hash node: a deterministic node computing `detVal`. -/
theorem graph_kind_hashParent {h p : Name} (hp : hashParent h = some p) :
    ∃ ps hps hf, graph.kind p.fin =
      .det ps hps (fun x => (detVal p x).cast (graph_len_fin p).symm) hf := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact ⟨_, _, _, rfl⟩

/-- The parent of a hash node of the graph, by name. -/
theorem graph_kind_eq_hash {h : Name} {q : Fin N} {hq : q < h.fin} {hl : lenF h.fin = 256}
    (hk : graph.kind h.fin = .hash q hq hl) : ∃ p, hashParent h = some p ∧ q = p.fin := by
  rw [graph_kind_fin] at hk
  cases h <;> simp only [kindOf, reduceCtorEq] at hk
  case ch k t => exact ⟨ci k t, rfl, (NodeKind.hash.inj hk).symm⟩
  case gh j => exact ⟨gc j, rfl, (NodeKind.hash.inj hk).symm⟩
  case rh => exact ⟨rc, rfl, (NodeKind.hash.inj hk).symm⟩

/-- The input of a hash node carries its tweak, in every assignment. -/
theorem tagNat_detVal_of_hashParent {h p : Name} (hp : hashParent h = some p) (x : Asg) :
    tagNat ⟨p.len, detVal p x⟩ = h.idx :=
  tagNat_detVal (child_hashParent hp) (cost_ne_zero_of_hashParent hp) x

/-- The tagging of the concrete graph: every hash input starts with the index of its hash node. -/
def tagging : graph.Tagging where
  tag q := if h : tagNat q < N then some ⟨tagNat q, h⟩ else none
  tag_parent := by
    intro v q hq hl hk
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨ofFin v, fin_ofFin v⟩
    obtain ⟨p, hp, rfl⟩ := graph_kind_eq_hash hk
    obtain ⟨ps, hps, hf, hkp⟩ := graph_kind_hashParent hp
    refine ⟨ps, hps, _, hf, hkp, fun x => ?_⟩
    exact tagOf_eq_some_of_tagNat
      (tagNat_cast_detVal (child_hashParent hp) (cost_ne_zero_of_hashParent hp) x _)

/-- The cache written by key generation. -/
def kc (ξ : Rec) : Cache := graph.keygenCache ξ

theorem kc_apply_iff (ξ : Rec) (q : Query) (w : BitVec 256) :
    kc ξ q = some w ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p ∧ w = ξ.2 h.fin := by
  refine (Graph.keygenCache_apply_iff graph tagging ξ q w).trans ?_
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨ofFin v, fin_ofFin v⟩
    rw [graph_point_fin, Option.map_eq_some_iff] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact ⟨h, p, hp, rfl, rfl⟩
  · rintro ⟨h, p, hp, rfl, rfl⟩
    exact ⟨h.fin, by rw [graph_point_fin, hp]; rfl, rfl⟩

theorem kc_isSome_iff (ξ : Rec) (q : Query) :
    (kc ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hw
    exact ⟨h, p, hp, hq⟩
  · rintro ⟨h, p, hp, hq⟩
    exact ⟨_, (kc_apply_iff ξ q _).2 ⟨h, p, hp, hq, rfl⟩⟩

/-- The keygen cache holds no index query. -/
theorem kc_enc (ξ : Rec) (u : EncInput) : kc ξ (encQuery u) = none := by
  rcases hk : kc ξ (encQuery u) with _ | w
  · rfl
  · obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ _ w).1 hk
    exact absurd hq.symm (pointOf_ne_encQuery hp ξ u)

/-! ## Exposed and hidden points -/

/-- After signing at the disclosure set `A`, the points of the hash nodes evaluated at `A` are
exposed; when signing failed (`none`), nothing is exposed. -/
def Exposed (A? : Option (Finset Name)) (h : Name) : Prop := ∃ A, A? = some A ∧ Evaluated A h

theorem exposed_some_iff_evaluated (A : Finset Name) (h : Name) : Exposed (some A) h ↔ Evaluated A h := by
  simp [Exposed]

theorem not_exposed_none (h : Name) : ¬ Exposed none h := by
  rintro ⟨A, hA, -⟩
  cases hA

/-- The exposed part of the keygen cache. -/
def fExp (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p then kc ξ q else none

/-- The hidden part of the keygen cache. -/
def fHid (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p then kc ξ q else none

theorem extend_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.extend (fExp A? ξ) (fHid A? ξ) = kc ξ := by
  funext q
  simp only [Cache.extend_apply, fExp, fHid]
  by_cases h1 : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rw [if_pos h1]
    obtain ⟨h, p, hp, -, hq⟩ := h1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩)
    rw [hw]
    rfl
  · rw [if_neg h1, Option.none_or]
    by_cases h2 : ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p
    · rw [if_pos h2]
    · rw [if_neg h2]
      rcases hk : kc ξ q with _ | w
      · rfl
      · exfalso
        obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
        by_cases he : Exposed A? h
        · exact h1 ⟨h, p, hp, he, hq⟩
        · exact h2 ⟨h, p, hp, he, hq⟩

theorem disjoint_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.Disjoint (fExp A? ξ) (fHid A? ξ) := by
  intro q hq
  simp only [fHid] at hq
  split_ifs at hq with h2
  · obtain ⟨h, p, hp, he, hq⟩ := h2
    simp only [fExp]
    rw [if_neg]
    rintro ⟨h', p', hp', he', hq'⟩
    rw [hq] at hq'
    obtain rfl := pointOf_inj_left hp hp' hq'
    exact he he'
  · simp at hq

theorem fHid_isSome_iff (A? : Option (Finset Name)) (ξ : Rec) (q : Query) :
    (fHid A? ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p := by
  simp only [fHid]
  split_ifs with hc
  · obtain ⟨h, p, hp, -, hq⟩ := id hc
    exact iff_of_true ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩) hc
  · exact iff_of_false (by simp) hc

theorem fHid_none (ξ : Rec) : fHid none ξ = kc ξ := by
  funext q
  simp only [fHid]
  split_ifs with hc
  · rfl
  · rcases hk : kc ξ q with _ | w
    · rfl
    · exfalso
      obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
      exact hc ⟨h, p, hp, not_exposed_none h, hq⟩

theorem fExp_none (ξ : Rec) : fExp none ξ = ∅ := by
  funext q
  simp only [fExp]
  rw [if_neg]
  · rfl
  · rintro ⟨h, -, -, he, -⟩
    exact not_exposed_none h he

theorem fExp_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fExp A? ξ (encQuery u) = none := by
  simp only [fExp]
  rw [if_neg]
  rintro ⟨h, p, hp, -, hq⟩
  exact pointOf_ne_encQuery hp ξ u hq.symm

theorem fHid_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fHid A? ξ (encQuery u) = none := by
  simp only [fHid]
  rw [if_neg]
  rintro ⟨h, p, hp, -, hq⟩
  exact pointOf_ne_encQuery hp ξ u hq.symm

/-- A hidden point, when the cache came from a cut, is the point of a hash node that is not
evaluated. -/
theorem fHid_isSome_some_iff (A : Finset Name) (ξ : Rec) (q : Query) :
    (fHid (some A) ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧ q = pointOf ξ h p := by
  simp only [fHid_isSome_iff, exposed_some_iff_evaluated]

/-! ## The event `Spr` -/

/- Some cached answer, at a string carrying the tweak of a hash node but different from the
honest input of that node, begins with the honest output of that node.  The tweak condition makes
a query count for one hash node only: without labels, a string of length `p.len` could otherwise
be a spurious preimage for every hash node with that input length. -/
/-- Internal nodes bind129 bits; the public root binds128 bits. -/
def bindingWidth (h : Name) : ℕ := if h = rh then 128 else 129

def bindingValue (h : Name) (w : BitVec 256) : BitVec (bindingWidth h) :=
  w.setWidth (bindingWidth h)

def Spr (c : Cache) (ξ : Rec) : Prop :=
  ∃ h p, hashParent h = some p ∧ ∃ u : BitVec p.len, u ≠ val ξ p ∧ tagNat ⟨p.len, u⟩ = h.idx ∧
    ∃ w, c ⟨p.len, u⟩ = some w ∧ bindingValue h w = bindingValue h (ξ.2 h.fin)

theorem Spr.mono {c c' : Cache} (h : Cache.Sub c c') {ξ : Rec} (hs : Spr c ξ) :
    Spr c' ξ := by
  obtain ⟨hn, p, hp, u, hu, htag, w, hw, ht⟩ := hs
  exact ⟨hn, p, hp, u, hu, htag, w, h _ _ hw, ht⟩

/-- Caching an index query does not change `Spr`: no hash input has its length. -/
theorem spr_cacheQuery_enc (c : Cache) (ξ : Rec) (u : EncInput)
    (w : BitVec 256) : Spr (c.cacheQuery (encQuery u) w) ξ ↔ Spr c ξ := by
  have key : ∀ (h p : Name), hashParent h = some p → ∀ u' : BitVec p.len,
      c.cacheQuery (encQuery u) w ⟨p.len, u'⟩ = c ⟨p.len, u'⟩ :=
    fun h p hp u' => QueryCache.cacheQuery_of_ne _ _ (mk_ne_encQuery hp u' u)
  constructor
  · rintro ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
    rw [key h p hp] at hw
    exact ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
  · rintro ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
    refine ⟨h, p, hp, u', hu, htag, w', ?_, ht⟩
    rw [key h p hp]
    exact hw

/-- An entry of an overlay is an entry of one of the two caches. -/
theorem spr_of_extend {c f : Cache} {ξ : Rec} (hs : Spr (Cache.extend c f) ξ) :
    Spr c ξ ∨ Spr f ξ := by
  obtain ⟨h, p, hp, u, hu, htag, w, hw, ht⟩ := hs
  rw [Cache.extend_apply, Option.or_eq_some_iff] at hw
  rcases hw with hw | ⟨-, hw⟩
  · exact Or.inl ⟨h, p, hp, u, hu, htag, w, hw, ht⟩
  · exact Or.inr ⟨h, p, hp, u, hu, htag, w, hw, ht⟩

theorem not_spr_kc (ξ : Rec) : ¬ Spr (kc ξ) ξ := by
  rintro ⟨h, p, hp, u, hu, htag, w, hw, -⟩
  obtain ⟨h', p', hp', hq, -⟩ := (kc_apply_iff ξ _ w).1 hw
  have hh : h = h' := by
    apply Name.idx_injective
    rw [← htag, hq, tagNat_pointOf hp' ξ]
  subst hh
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  exact hu (eq_of_heq (Sigma.mk.inj_iff.1 hq).2)

theorem sub_fExp_kc (A? : Option (Finset Name)) (ξ : Rec) : Cache.Sub (fExp A? ξ) (kc ξ) := by
  intro q w hw
  simp only [fExp] at hw
  by_cases hc : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rwa [if_pos hc] at hw
  · rw [if_neg hc] at hw
    cases hw

theorem not_spr_fExp (A? : Option (Finset Name)) (ξ : Rec) : ¬ Spr (fExp A? ξ) ξ :=
  fun hs => not_spr_kc ξ (hs.mono (sub_fExp_kc A? ξ))

theorem not_spr_empty (ξ : Rec) : ¬ Spr ∅ ξ := by
  rintro ⟨h, p, hp, u, hu, -, w, hw, -⟩
  simp at hw

/-- `ε = 2 ^ (-129)`. -/
def ε : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 129)⁻¹

/-- Exact low129 fibers leave127 unconstrained oracle output bits. -/
theorem card_filter_lowWord_le (a : BitVec 129) :
    (Finset.univ.filter fun w : BitVec 256 => lowWord w = a).card ≤ 2 ^ 127 :=
  le_of_eq (TruncFiber.card_256_129 a)

theorem inv_card_bitVec_mul_two_pow :
    (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((2 ^ 127 : ℕ) : ℝ≥0∞) = ε := by
  have h0 : (2 : ℝ≥0∞) ^ 127 ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ 127 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : (2 : ℝ≥0∞) ^ 129 * 2 ^ 127 = 2 ^ 256 := by rw [← pow_add]
  rw [Fintype.card_bitVec, ε]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← e, ENNReal.mul_inv (Or.inr ht) (Or.inr h0), mul_assoc,
    ENNReal.inv_mul_cancel h0 ht, mul_one]

/-! ## Coordinates -/

/-- The record coordinates that the value of a node reads. -/
def deps : Name → Finset Name
  | src k => {src k}
  | ci k t => if h : t.val = 0 then {src k} else {ch k ⟨t.val - 1, by omega⟩}
  | ch k t => {ch k t}
  | cv k t => {ch k t}
  | gc j => {ch (chainOf j 0) 17, ch (chainOf j 1) 17, ch (chainOf j 2) 17}
  | gh j => {gh j}
  | gv j => {gh j}
  | rc => Finset.univ.image gh
  | rh => {rh}

theorem deps_ci_zero (k : Fin 54) (t : Fin 18) (ht : t.val = 0) : deps (ci k t) = {src k} := by
  simp only [deps, dif_pos ht]

theorem deps_ci_succ (k : Fin 54) (t : Fin 18) (ht : ¬ t.val = 0) :
    deps (ci k t) = {ch k ⟨t.val - 1, by omega⟩} := by
  simp only [deps, dif_neg ht]

theorem child_src_ci (k : Fin 54) (t : Fin 18) (ht : t.val = 0) : child (src k) = some (ci k t) := by
  have e : t = 0 := Fin.ext ht
  subst e
  rfl

theorem child_cv_ci (k : Fin 54) (t : Fin 18) (ht : ¬ t.val = 0) :
    child (cv k ⟨t.val - 1, by omega⟩) = some (ci k t) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]
  simp only [Option.some.injEq, Name.ci.injEq, true_and, Fin.ext_iff]
  omega

theorem chainOf_div (j : Fin 18) (a : Fin 3) : ((chainOf j a : Fin 54) : ℕ) / 3 = j := by
  simp only [chainOf]
  omega

theorem child_cv_17 (k : Fin 54) : child (cv k 17) = some (gc ⟨k / 3, by omega⟩) := rfl

theorem child_cv_17_gc (j : Fin 18) (a : Fin 3) : child (cv (chainOf j a) 17) = some (gc j) := by
  rw [child_cv_17]
  exact congrArg some (congrArg gc (Fin.ext (chainOf_div j a)))

/-- Resample a source. -/
def updSrc (ξ : Rec) (k : Fin 54) (b : BitVec 129) : Rec :=
  (Function.update ξ.1 (src k).fin (b.cast (graph_len_fin (src k)).symm), ξ.2)

/-- Resample a hash output. -/
def updHash (ξ : Rec) (s : Name) (b : BitVec 256) : Rec := (ξ.1, Function.update ξ.2 s.fin b)

theorem updHash_snd_self (ξ : Rec) (s : Name) (b : BitVec 256) : (updHash ξ s b).2 s.fin = b :=
  Function.update_self _ _ _

theorem updHash_snd_ne (ξ : Rec) (s : Name) (b : BitVec 256) {n : Name} (h : n ≠ s) :
    (updHash ξ s b).2 n.fin = ξ.2 n.fin := by
  simp only [updHash]
  exact Function.update_of_ne (fun e => h (Name.fin_injective e)) _ _

theorem updSrc_snd (ξ : Rec) (k : Fin 54) (b : BitVec 129) : (updSrc ξ k b).2 = ξ.2 := rfl

theorem val_updHash_of_not_mem_deps (ξ : Rec) (s : Name) (b : BitVec 256) (n : Name)
    (h : s ∉ deps n) : val (updHash ξ s b) n = val ξ n := by
  cases n with
  | src k =>
    rw [val_src, val_src]
    rfl
  | ci k t =>
    by_cases ht : t.val = 0
    · rw [val_ci_zero _ k t ht, val_ci_zero _ k t ht, val_src, val_src]
      rfl
    · rw [deps_ci_succ k t ht, Finset.mem_singleton] at h
      rw [val_ci_succ _ k t ht, val_ci_succ _ k t ht, updHash_snd_ne _ _ _ (Ne.symm h)]
  | ch k t =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_ch, val_ch, updHash_snd_ne _ _ _ (Ne.symm h)]
  | cv k t =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_cv, val_cv, updHash_snd_ne _ _ _ (Ne.symm h)]
  | gc j =>
    simp only [deps, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    obtain ⟨h0, h1, h2⟩ := h
    rw [val_gc, val_gc, updHash_snd_ne _ _ _ (Ne.symm h0), updHash_snd_ne _ _ _ (Ne.symm h1),
      updHash_snd_ne _ _ _ (Ne.symm h2)]
  | gh j =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_gh, val_gh, updHash_snd_ne _ _ _ (Ne.symm h)]
  | gv j =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_gv, val_gv, updHash_snd_ne _ _ _ (Ne.symm h)]
  | rc =>
    simp only [deps, Finset.mem_image, Finset.mem_univ, true_and, not_exists] at h
    rw [val_rc, val_rc]
    exact congrArg (fun a => tw rh ++ cat18 a)
      (funext fun l => by rw [updHash_snd_ne _ _ _ (h l)])
  | rh =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_rh, val_rh, updHash_snd_ne _ _ _ (Ne.symm h)]

theorem val_updSrc_src_of_ne (ξ : Rec) (k : Fin 54) (b : BitVec 129) {k' : Fin 54} (h : ¬ k = k') :
    val (updSrc ξ k b) (src k') = val ξ (src k') := by
  have e : (updSrc ξ k b).1 (src k').fin = ξ.1 (src k').fin :=
    Function.update_of_ne (fun e => h (Name.src.inj (Name.fin_injective e)).symm) _ _
  rw [val_src, val_src, e]

theorem val_updSrc_of_not_mem_deps (ξ : Rec) (k : Fin 54) (b : BitVec 129) (n : Name)
    (h : src k ∉ deps n) : val (updSrc ξ k b) n = val ξ n := by
  cases n with
  | src k' =>
    simp only [deps, Finset.mem_singleton, Name.src.injEq] at h
    exact val_updSrc_src_of_ne ξ k b h
  | ci k' t =>
    by_cases ht : t.val = 0
    · rw [deps_ci_zero k' t ht, Finset.mem_singleton, Name.src.injEq] at h
      rw [val_ci_zero _ k' t ht, val_ci_zero _ k' t ht, val_updSrc_src_of_ne ξ k b h]
    · rw [val_ci_succ _ k' t ht, val_ci_succ _ k' t ht, updSrc_snd]
  | ch k t => rw [val_ch, val_ch, updSrc_snd]
  | cv k t => rw [val_cv, val_cv, updSrc_snd]
  | gc j => rw [val_gc, val_gc, updSrc_snd]
  | gh j => rw [val_gh, val_gh, updSrc_snd]
  | gv j => rw [val_gv, val_gv, updSrc_snd]
  | rc => rw [val_rc, val_rc, updSrc_snd]
  | rh => rw [val_rh, val_rh, updSrc_snd]

theorem val_updSrc_self (ξ : Rec) (k : Fin 54) (b : BitVec 129) :
    val (updSrc ξ k b) (src k) = b := by
  have e : (updSrc ξ k b).1 (src k).fin = b.cast (graph_len_fin (src k)).symm :=
    Function.update_self _ _ _
  rw [val_src, e]
  exact cast_cast_eq _ _ _

theorem snd_updHash_of_ne (ξ : Rec) (s : Name) (b : BitVec 256) (n : Name) (h : n ≠ s) :
    (updHash ξ s b).2 n.fin = ξ.2 n.fin :=
  updHash_snd_ne ξ s b h

theorem snd_updHash_self (ξ : Rec) (s : Name) (b : BitVec 256) :
    (updHash ξ s b).2 s.fin = b :=
  updHash_snd_self ξ s b

theorem snd_updSrc (ξ : Rec) (k : Fin 54) (b : BitVec 129) : (updSrc ξ k b).2 = ξ.2 := rfl

/-! ## The coordinate that randomizes the input of a hash node -/

/-- The coordinate resampled to randomize the input of a hash node (junk for other nodes). -/
def coordOf : Name → Name
  | ch k t => if h : t.val = 0 then src k else ch k ⟨t.val - 1, by omega⟩
  | gh j => ch (chainOf j 2) 17
  | rh => gh 17
  | n => n

theorem coordOf_ne_rh (h : Name) (hh : h.cost ≠ 0) : coordOf h ≠ rh := by
  cases h
  case ch k t =>
    simp only [coordOf]
    split_ifs <;> simp
  case gh j => simp [coordOf]
  case rh => simp [coordOf]
  all_goals exact absurd rfl hh

/-- The coordinate of a hash node lies at most two steps below its parent. -/
theorem coordOf_below {h p : Name} (hp : hashParent h = some p) :
    coordOf h = p ∨ child (coordOf h) = some p ∨ ∃ m, child (coordOf h) = some m ∧ child m = some p := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · rename_i k t
    simp only [coordOf]
    split_ifs with ht
    · exact Or.inr (Or.inl (child_src_ci k t ht))
    · exact Or.inr (Or.inr ⟨cv k ⟨t.val - 1, by omega⟩, rfl, child_cv_ci k t ht⟩)
  · exact Or.inr (Or.inr ⟨cv (chainOf _ 2) 17, rfl, child_cv_17_gc _ 2⟩)
  · exact Or.inr (Or.inr ⟨gv 17, rfl, rfl⟩)

theorem lowWord_cat3 (x y z : BitVec 129) : lowWord (cat3 x y z) = z := by
  unfold cat3
  rw [lowWord_cast]
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

theorem lowWord_cat18 (a : Fin 18 → BitVec 129) : lowWord (cat18 a) = a 17 := by
  unfold cat18
  rw [lowWord_cast]
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

/-- The tweak sits in the high bits: it does not change the 129 low bits of a payload of at least
129 bits. -/
theorem lowWord_tw_append {n : ℕ} (hn : 129 ≤ n) (a : BitVec 16) (x : BitVec n) :
    lowWord (a ++ x) = lowWord x := by
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos hn]

/-- The low 129 bits of a tweaked hash input are those of its payload. -/
theorem lowWord_of_tw_append_eq {n : ℕ} (hn : 129 ≤ n) {a : BitVec 16} {x : BitVec n}
    {u : BitVec (16 + n)} (e : a ++ x = u) : lowWord u = lowWord x := by
  subst e
  exact lowWord_tw_append hn a x

/-- A chain input: the payload is the low 129 bits. -/
theorem lowWord_of_tw_eq {a : BitVec 16} {x : BitVec 129} {u : BitVec 145} (e : a ++ x = u) :
    lowWord u = x :=
  (lowWord_of_tw_append_eq (n := 129) le_rfl e).trans (lowWord_eq_self x)

/-- A tweaked concatenation of three values: the low 129 bits are the last value. -/
theorem lowWord_of_tw_cat3_eq {a : BitVec 16} {x y z : BitVec 129} {u : BitVec 403}
    (e : a ++ cat3 x y z = u) : lowWord u = z :=
  (lowWord_of_tw_append_eq (n := 387) (by norm_num) e).trans (lowWord_cat3 x y z)

/-- A tweaked concatenation of eighteen values: the low 129 bits are the last value. -/
theorem lowWord_of_tw_cat18_eq {a : BitVec 16} {b : Fin 18 → BitVec 129} {u : BitVec 2338}
    (e : a ++ cat18 b = u) : lowWord u = b 17 :=
  (lowWord_of_tw_append_eq (n := 2322) (by norm_num) e).trans (lowWord_cat18 b)

/-- A filter whose members all have the same lowWordation has at most `2 ^ 127` elements. -/
theorem card_filter_le_of_imp (p : BitVec 256 → Prop) [DecidablePred p] (a : BitVec 129)
    (hp : ∀ b, p b → lowWord b = a) : (Finset.univ.filter p).card ≤ 2 ^ 127 :=
  le_trans (Finset.card_le_card fun b hb => Finset.mem_filter.2
    ⟨Finset.mem_univ _, hp b (Finset.mem_filter.1 hb).2⟩) (card_filter_lowWord_le a)

/-- Resampling the coordinate of a hash node makes its input hit any given value with
probability at most `2 ^ (-129)`: hash coordinates. -/
theorem card_updHash_input_le {h p : Name} (hp : hashParent h = some p) (ξ : Rec)
    (hs : ∀ k, coordOf h ≠ src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 256 => val (updHash ξ (coordOf h) b) p = u).card ≤ 2 ^ 127 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · -- `ch k t`
    rename_i k t
    have ht : ¬ t.val = 0 := fun ht => hs k (by simp [coordOf, ht])
    have e1 : coordOf (ch k t) = ch k ⟨t.val - 1, by omega⟩ := by simp [coordOf, ht]
    rw [e1]
    refine card_filter_le_of_imp _ (lowWord u) fun b hb => ?_
    rw [val_ci_succ _ k t ht] at hb
    have := lowWord_of_tw_eq hb
    exact (this.trans (congrArg lowWord (updHash_snd_self _ _ _))).symm
  · -- `gh j`
    refine card_filter_le_of_imp _ (lowWord u) fun b hb => ?_
    rw [val_gc] at hb
    have := lowWord_of_tw_cat3_eq hb
    exact (this.trans (congrArg lowWord (updHash_snd_self _ _ _))).symm
  · -- `rh`
    refine card_filter_le_of_imp _ (lowWord u) fun b hb => ?_
    rw [val_rc] at hb
    have := lowWord_of_tw_cat18_eq hb
    exact (this.trans (congrArg lowWord (updHash_snd_self _ _ _))).symm

/-- Source coordinates. -/
theorem card_updSrc_input_le {h p : Name} (hp : hashParent h = some p) (ξ : Rec) {k : Fin 54}
    (hs : coordOf h = src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 129 => val (updSrc ξ k b) p = u).card ≤ 1 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp only [coordOf] at hs
  · rename_i k' t
    by_cases ht : t.val = 0
    · rw [dif_pos ht] at hs
      obtain rfl : k = k' := (Name.src.inj hs).symm
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, val_ci_zero _ k t ht,
        val_updSrc_self] at ha hb
      exact (append_inj (n := 129) (ha.trans hb.symm)).2
    · rw [dif_neg ht] at hs
      exact absurd hs (by simp)
  all_goals exact absurd hs (by simp)

end WeightedConstruction.WideForest

end OptimalOTS

#print axioms OptimalOTS.WeightedConstruction.WideForest.card_updHash_input_le
#print axioms OptimalOTS.WeightedConstruction.WideForest.card_updSrc_input_le
#print axioms OptimalOTS.WeightedConstruction.WideForest.not_spr_kc
end
end

/- Original module: Submissions.UpperCompressions.WideResample; SHA256 c61d496a4b3810795ca47a8dc1dc6ad475028dbe3ce303a4a913b44bc8a5554d. -/
section

/-!
# Hidden inputs are uniform

The input of a hidden hash node is a function of record coordinates that the public data (the
public key, the revealed values, the exposed keygen points) does not depend on.  Resampling one
such coordinate (`coordOf h`) leaves every record in the fiber of the public data and makes the
input hit any given value with probability at most `ε = 2 ^ (-129)`.

* `sum_updHash`, `sum_updSrc`: change of variables on a set closed under resampling;
* `HiddenCoord`: coordinates the public data does not depend on;
* `hits_charge_A`, `hits_charge_B`: for a fixed query point, at most an `ε` fraction of the
  records of a fiber have that point among their hidden keygen points.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace WeightedConstruction.WideForest

open Name

/-- The weight of a record. -/
def w : ℝ≥0∞ := (Fintype.card Rec : ℝ≥0∞)⁻¹

theorem sum_w : ∑ _ξ : Rec, w = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, w]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- A set of records closed under resampling the coordinate `s`. -/
def ClosedAt (S : Finset Rec) (s : Name) : Prop :=
  match s with
  | src k => ∀ ξ ∈ S, ∀ b : BitVec 129, updSrc ξ k b ∈ S
  | _ => ∀ ξ ∈ S, ∀ b : BitVec 256, updHash ξ s b ∈ S

theorem closedAt_src (S : Finset Rec) (k : Fin 54) :
    ClosedAt S (src k) ↔ ∀ ξ ∈ S, ∀ b : BitVec 129, updSrc ξ k b ∈ S := Iff.rfl

theorem closedAt_of_ne_src (S : Finset Rec) {s : Name} (hs : ∀ k, s ≠ src k) :
    ClosedAt S s ↔ ∀ ξ ∈ S, ∀ b : BitVec 256, updHash ξ s b ∈ S := by
  cases s
  · exact absurd rfl (hs _)
  all_goals exact Iff.rfl

theorem bv_cast_cast {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x := by
  subst h₁; rfl

/-- Resampling a hash coordinate is an involution. -/
theorem updHash_updHash (ξ : Rec) (s : Name) (b : BitVec 256) :
    updHash (updHash ξ s b) s (ξ.2 s.fin) = ξ :=
  Prod.ext rfl (funext fun i => by
    show Function.update (Function.update ξ.2 s.fin b) s.fin (ξ.2 s.fin) i = ξ.2 i
    by_cases hi : i = s.fin
    · subst hi; exact Function.update_self ..
    · exact (Function.update_of_ne hi _ _).trans (Function.update_of_ne hi _ _))

/-- Resampling a source is an involution. -/
theorem updSrc_updSrc (ξ : Rec) (k : Fin 54) (b : BitVec 129) :
    updSrc (updSrc ξ k b) k ((ξ.1 (src k).fin).cast (graph_len_fin _)) = ξ :=
  Prod.ext (funext fun i => by
    show Function.update (Function.update ξ.1 (src k).fin (b.cast _)) (src k).fin
      (((ξ.1 (src k).fin).cast (graph_len_fin _)).cast (graph_len_fin _).symm) i = ξ.1 i
    by_cases hi : i = (src k).fin
    · subst hi; exact (Function.update_self ..).trans (bv_cast_cast _ _ _)
    · exact (Function.update_of_ne hi _ _).trans (Function.update_of_ne hi _ _)) rfl

theorem fst_updSrc_self (ξ : Rec) (k : Fin 54) (b : BitVec 129) :
    ((updSrc ξ k b).1 (src k).fin).cast (graph_len_fin _) = b := by
  show (Function.update ξ.1 (src k).fin (b.cast (graph_len_fin (src k)).symm) (src k).fin).cast
    (graph_len_fin (src k)) = b
  exact (congrArg (BitVec.cast (graph_len_fin (src k)))
    (Function.update_self (src k).fin (b.cast (graph_len_fin (src k)).symm) ξ.1)).trans
    (bv_cast_cast _ _ _)

/-- Change of variables: resampling a hash coordinate. -/
theorem sum_updHash (S : Finset Rec) (s : Name) (_hs : ∀ k, s ≠ src k)
    (hS : ∀ ξ ∈ S, ∀ b : BitVec 256, updHash ξ s b ∈ S) (f : Rec → ℝ≥0∞) :
    ∑ ξ ∈ S, f ξ = ∑ ξ ∈ S, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ∑ b, f (updHash ξ s b) := by
  have key : ∑ ξ ∈ S, ∑ b, f (updHash ξ s b) = ∑ ξ ∈ S, ∑ _b : BitVec 256, f ξ := by
    calc ∑ ξ ∈ S, ∑ b, f (updHash ξ s b)
        = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 256)), f (updHash p.1 s p.2) :=
          (Finset.sum_product' S Finset.univ (fun ξ b => f (updHash ξ s b))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 256)), f p.1 := by
          refine Finset.sum_nbij' (fun p => (updHash p.1 s p.2, p.1.2 s.fin))
            (fun p => (updHash p.1 s p.2, p.1.2 s.fin)) ?_ ?_ ?_ ?_ ?_
          · intro p hp
            rw [Finset.mem_product] at hp ⊢
            exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
          · intro p hp
            rw [Finset.mem_product] at hp ⊢
            exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
          · intro p _
            exact Prod.ext (updHash_updHash _ _ _) (snd_updHash_self _ _ _)
          · intro p _
            exact Prod.ext (updHash_updHash _ _ _) (snd_updHash_self _ _ _)
          · intro p _
            rfl
      _ = ∑ ξ ∈ S, ∑ _b : BitVec 256, f ξ :=
          Finset.sum_product' S Finset.univ (fun ξ _ => f ξ)
  have hc0 : (Fintype.card (BitVec 256) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 256) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- Change of variables: resampling a source. -/
theorem sum_updSrc (S : Finset Rec) (k : Fin 54)
    (hS : ∀ ξ ∈ S, ∀ b : BitVec 129, updSrc ξ k b ∈ S) (f : Rec → ℝ≥0∞) :
    ∑ ξ ∈ S, f ξ = ∑ ξ ∈ S, (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ * ∑ b, f (updSrc ξ k b) := by
  have key : ∑ ξ ∈ S, ∑ b, f (updSrc ξ k b) = ∑ ξ ∈ S, ∑ _b : BitVec 129, f ξ := by
    calc ∑ ξ ∈ S, ∑ b, f (updSrc ξ k b)
        = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 129)), f (updSrc p.1 k p.2) :=
          (Finset.sum_product' S Finset.univ (fun ξ b => f (updSrc ξ k b))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 129)), f p.1 := by
          refine Finset.sum_nbij'
            (fun p => (updSrc p.1 k p.2, (p.1.1 (src k).fin).cast (graph_len_fin _)))
            (fun p => (updSrc p.1 k p.2, (p.1.1 (src k).fin).cast (graph_len_fin _))) ?_ ?_ ?_ ?_ ?_
          · intro p hp
            rw [Finset.mem_product] at hp ⊢
            exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
          · intro p hp
            rw [Finset.mem_product] at hp ⊢
            exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
          · intro p _
            exact Prod.ext (updSrc_updSrc _ _ _) (fst_updSrc_self _ _ _)
          · intro p _
            exact Prod.ext (updSrc_updSrc _ _ _) (fst_updSrc_self _ _ _)
          · intro p _
            rfl
      _ = ∑ ξ ∈ S, ∑ _b : BitVec 129, f ξ :=
          Finset.sum_product' S Finset.univ (fun ξ _ => f ξ)
  have hc0 : (Fintype.card (BitVec 129) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 129) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem card_bitVec_ennreal (n : ℕ) : (Fintype.card (BitVec n) : ℝ≥0∞) = 2 ^ n := by
  simp

theorem inv_card_mul_two_pow : (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 2 ^ 127 = ε := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using inv_card_bitVec_mul_two_pow

/-- On a set closed under resampling the coordinate of a hash node, its input hits any given
value with probability at most `ε`. -/
theorem sum_input_eq_le {h p : Name} (hp : hashParent h = some p) (S : Finset Rec)
    (hS : ClosedAt S (coordOf h)) (u : BitVec p.len) :
    ∑ ξ ∈ S, (if val ξ p = u then w else 0) ≤ ε * ∑ _ξ ∈ S, w := by
  rw [Finset.mul_sum]
  by_cases hsrc : ∃ k, coordOf h = src k
  · obtain ⟨k, hk⟩ := hsrc
    rw [hk, closedAt_src] at hS
    rw [sum_updSrc S k hS (fun ξ => if val ξ p = u then w else 0)]
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updSrc_input_le hp ξ hk u
    have hle' : ((Finset.univ.filter fun b : BitVec 129 => val (updSrc ξ k b) p = u).card : ℝ≥0∞)
        ≤ 1 := by exact_mod_cast hle
    calc (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun b : BitVec 129 => val (updSrc ξ k b) p = u).card : ℝ≥0∞) * w)
        ≤ (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ * (1 * w) := by gcongr
      _ = ε * w := by rw [one_mul, card_bitVec_ennreal, ε]
  · push Not at hsrc
    rw [closedAt_of_ne_src S hsrc] at hS
    rw [sum_updHash S (coordOf h) hsrc hS (fun ξ => if val ξ p = u then w else 0)]
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updHash_input_le hp ξ hsrc u
    have hle' : ((Finset.univ.filter fun b : BitVec 256 =>
        val (updHash ξ (coordOf h) b) p = u).card : ℝ≥0∞) ≤ 2 ^ 127 := by exact_mod_cast hle
    calc (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun b : BitVec 256 =>
            val (updHash ξ (coordOf h) b) p = u).card : ℝ≥0∞) * w)
        ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * (2 ^ 127 * w) := by gcongr
      _ = ε * w := by rw [← mul_assoc, inv_card_mul_two_pow]

/-! ## Hidden coordinates -/

/-- A coordinate the public data after signing at the cut `A` does not depend on: a node
strictly below the cut that is neither a cut node nor the hash node of a cut node. -/
def HiddenCoord (A : Finset Name) (s : Name) : Prop :=
  ¬ Evaluated A s ∧ s ∉ A ∧ ∀ a ∈ A, hashOf a ≠ some s

theorem len_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.len = 256 := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp <;> rfl

/-- A hash node lies strictly above its coordinate. -/
theorem above_coordOf {h p : Name} (hp : hashParent h = some p) : Above h (coordOf h) := by
  have hc := child_hashParent hp
  rcases coordOf_below hp with e | e | ⟨m, e1, e2⟩
  · rw [e]; exact Above.child hc
  · exact Above.step e (Above.child hc)
  · exact Above.step e1 (Above.step e2 (Above.child hc))

theorem coordOf_hiddenCoord {A : Finset Name} (hA : IsCut A) {h p : Name}
    (hp : hashParent h = some p) (hh : ¬ Evaluated A h) : HiddenCoord A (coordOf h) := by
  have hhA : h ∉ A := fun hm => by
    have := hA.values h hm
    rw [len_of_hashParent hp] at this
    omega
  obtain ⟨a, haA, hah⟩ : ∃ a ∈ A, Above a h := by
    by_contra hcon
    push Not at hcon
    exact hh ⟨hhA, fun m hm hmA => hcon m hmA hm⟩
  have hhs : Above h (coordOf h) := above_coordOf hp
  have has : Above a (coordOf h) := hah.trans hhs
  refine ⟨fun he => he.2 a has haA, fun hsA => hA.antichain _ hsA a has haA, fun a' ha' he => ?_⟩
  have hc : child (coordOf h) = some a' := child_hashOf he
  rw [above_of_child hc] at hhs
  rcases hhs with rfl | hhs
  · exact hhA ha'
  · exact hA.antichain a' ha' a (hah.trans hhs) haA

/-- If `s` is not in `A` and its child is evaluated, then `s` is evaluated. -/
theorem evaluated_of_child_res {A : Finset Name} {s n : Name} (hc : child s = some n) (hsA : s ∉ A)
    (hn : Evaluated A n) : Evaluated A s :=
  ⟨hsA, fun m hm => by
    rw [above_of_child hc] at hm
    rcases hm with rfl | hm
    · exact hn.1
    · exact hn.2 m hm⟩

theorem child_cv_chainOf (j : Fin 18) (a : Fin 3) : child (cv (chainOf j a) 17) = some (gc j) := by
  rw [Name.child, dif_pos (show ((17 : Fin 18) : ℕ) = 17 from rfl)]
  simp only [Option.some.injEq, Name.gc.injEq, Fin.ext_iff, Fin.val_mk, chainOf]
  omega

/-- Every coordinate a node reads is the node itself, its hash node, the hash node of one of
its parents, or (for the first input of a chain, which reads a source) its parent. -/
theorem mem_deps_cases' {s n : Name} (h : s ∈ deps n) :
    s = n ∨ hashOf n = some s ∨ (∃ m, hashOf m = some s ∧ child m = some n) ∨
      (child s = some n ∧ n.len ≠ 129) := by
  cases n with
  | src k => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h
  | ci k t =>
    by_cases ht : t.val = 0
    · rw [deps_ci_zero k t ht, Finset.mem_singleton] at h
      subst h
      exact Or.inr (Or.inr (Or.inr ⟨child_src_ci k t ht, by simp [Name.len]⟩))
    · rw [deps_ci_succ k t ht, Finset.mem_singleton] at h
      subst h
      exact Or.inr (Or.inr (Or.inl ⟨cv k ⟨t.val - 1, by omega⟩, rfl, child_cv_ci k t ht⟩))
  | ch k t => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h
  | cv k t => simp only [deps, Finset.mem_singleton] at h; subst h; exact Or.inr (Or.inl rfl)
  | gc j =>
    simp only [deps, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl <;>
      exact Or.inr (Or.inr (Or.inl ⟨cv _ 17, rfl, child_cv_chainOf _ _⟩))
  | gh j => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h
  | gv j => simp only [deps, Finset.mem_singleton] at h; subst h; exact Or.inr (Or.inl rfl)
  | rc =>
    simp only [deps, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨l, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨gv l, rfl, rfl⟩))
  | rh => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h

/-- The child of a value node is not a 129-bit node. -/
theorem len_child_of_hashOf {m s n : Name} (hm : hashOf m = some s) (hc : child m = some n) :
    n.len ≠ 129 := by
  cases m <;> simp only [hashOf, reduceCtorEq] at hm
  · simp only [Name.child] at hc
    split_ifs at hc <;> simp only [Option.some.injEq] at hc <;> subst hc <;> simp [Name.len]
  · simp only [Name.child, Option.some.injEq] at hc; subst hc; simp [Name.len]

theorem not_mem_deps_of_hiddenCoord {A : Finset Name} (hA : IsCut A) {s n : Name}
    (hs : HiddenCoord A s) (hn : Evaluated A n ∨ n ∈ A) : s ∉ deps n := by
  intro hd
  obtain ⟨hsE, hsA, hsH⟩ := hs
  rcases mem_deps_cases' hd with rfl | hh | ⟨m, hm, hc⟩ | ⟨hc, hl⟩
  · rcases hn with hn | hn
    · exact hsE hn
    · exact hsA hn
  · rcases hn with hn | hn
    · exact hsE (evaluated_of_child_res (child_hashOf hh) hsA hn)
    · exact hsH n hn hh
  · have hcs : child s = some m := child_hashOf hm
    rcases hn with hn | hn
    · by_cases hmA : m ∈ A
      · exact hsH m hmA hm
      · exact hsE (evaluated_of_child_res hcs hsA (evaluated_of_child_res hc hmA hn))
    · exact len_child_of_hashOf hm hc (hA.values n hn)
  · rcases hn with hn | hn
    · exact hsE (evaluated_of_child_res hc hsA hn)
    · exact hl (hA.values n hn)

theorem hiddenCoord_ne_rh {A : Finset Name} {s : Name} (hs : HiddenCoord A s) : s ≠ rh := by
  rintro rfl
  exact hs.1 ⟨hs.2.1, fun m hm => absurd hm (not_above_rh m)⟩

/-! ## Invariance of the public data -/

/-- The revealed values at a disclosure set. -/
def revealed (A : Finset Name) (ξ : Rec) : List Bool := graph.encode (fins A) (graph.evalRec ξ)

theorem pkOf_updHash (ξ : Rec) {s : Name} (hs : s ≠ rh) (b : BitVec 256) :
    pkOf (updHash ξ s b) = pkOf ξ := by
  exact congrArg lowPk (snd_updHash_of_ne ξ s b rh (Ne.symm hs))

theorem pkOf_updSrc (ξ : Rec) (k : Fin 54) (b : BitVec 129) : pkOf (updSrc ξ k b) = pkOf ξ := by
  unfold pkOf
  rw [snd_updSrc]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun a' ha' => h a' (by simp [ha'])]

/-- `encode` only reads the values on the encoded set. -/
theorem encode_congr_revealed {B : Finset (Fin graph.size)} {x x' : graph.Assignment}
    (h : ∀ v ∈ B, x v = x' v) : graph.encode B x = graph.encode B x' := by
  unfold Graph.encode
  apply flatMap_congr'
  intro v hv
  rw [List.mem_filter] at hv
  rw [h v (of_decide_eq_true hv.2)]

theorem evalRec_fin_congr {ξ ξ' : Rec} {a : Name} (h : val ξ a = val ξ' a) :
    graph.evalRec ξ a.fin = graph.evalRec ξ' a.fin := by
  unfold val at h
  simpa using congrArg (BitVec.cast (graph_len_fin a).symm) h

theorem revealed_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) : revealed A (updHash ξ s b) = revealed A ξ := by
  unfold revealed
  apply encode_congr_revealed
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v := ⟨ofFin v, fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins A a).mp hv
  exact evalRec_fin_congr
    (val_updHash_of_not_mem_deps ξ s b a (not_mem_deps_of_hiddenCoord hA hs (Or.inr haA)))

theorem revealed_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 54}
    (hs : HiddenCoord A (src k)) (b : BitVec 129) : revealed A (updSrc ξ k b) = revealed A ξ := by
  unfold revealed
  apply encode_congr_revealed
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v := ⟨ofFin v, fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins A a).mp hv
  exact evalRec_fin_congr
    (val_updSrc_of_not_mem_deps ξ k b a (not_mem_deps_of_hiddenCoord hA hs (Or.inr haA)))

theorem exposed_some_iff (A : Finset Name) (h : Name) : Exposed (some A) h ↔ Evaluated A h := by
  simp [Exposed]

/-- The parent of an evaluated hash node is evaluated or in the cut. -/
theorem evaluated_or_mem_of_child {A : Finset Name} {p h : Name} (hc : child p = some h)
    (he : Evaluated A h) : Evaluated A p ∨ p ∈ A := by
  by_cases hpA : p ∈ A
  · exact Or.inr hpA
  · exact Or.inl (evaluated_of_child_res hc hpA he)

theorem pointOf_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) : pointOf (updHash ξ s b) h p = pointOf ξ h p := by
  unfold pointOf
  rw [val_updHash_of_not_mem_deps _ _ _ _ (not_mem_deps_of_hiddenCoord hA hs
    (evaluated_or_mem_of_child (child_hashParent hp) he))]

theorem pointOf_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 54}
    (hs : HiddenCoord A (src k)) (b : BitVec 129) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) : pointOf (updSrc ξ k b) h p = pointOf ξ h p := by
  unfold pointOf
  rw [val_updSrc_of_not_mem_deps _ _ _ _ (not_mem_deps_of_hiddenCoord hA hs
    (evaluated_or_mem_of_child (child_hashParent hp) he))]

/-- The keygen cache at a keygen point. -/
theorem kc_pointOf (ξ : Rec) {h p : Name} (hp : hashParent h = some p) :
    kc ξ (pointOf ξ h p) = some (ξ.2 h.fin) :=
  (kc_apply_iff ξ _ _).mpr ⟨h, p, hp, rfl, rfl⟩

theorem fExp_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) : fExp (some A) (updHash ξ s b) = fExp (some A) ξ := by
  funext q
  have hpt : ∀ h p, hashParent h = some p → Exposed (some A) h →
      pointOf (updHash ξ s b) h p = pointOf ξ h p :=
    fun h p hp he => pointOf_updHash hA ξ hs b hp ((exposed_some_iff A h).mp he)
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf (updHash ξ s b) h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  simp only [fExp]
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p
  · rw [if_pos (hcond.mpr hq), if_pos hq]
    obtain ⟨h, p, hp, he, rfl⟩ := hq
    have hne : h ≠ s := fun e => hs.1 (e ▸ (exposed_some_iff A h).mp he)
    rw [kc_pointOf ξ hp, ← hpt h p hp he, kc_pointOf _ hp, snd_updHash_of_ne _ _ _ _ hne]
  · rw [if_neg (fun h' => hq (hcond.mp h')), if_neg hq]

theorem fExp_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 54}
    (hs : HiddenCoord A (src k)) (b : BitVec 129) : fExp (some A) (updSrc ξ k b) = fExp (some A) ξ := by
  funext q
  have hpt : ∀ h p, hashParent h = some p → Exposed (some A) h →
      pointOf (updSrc ξ k b) h p = pointOf ξ h p :=
    fun h p hp he => pointOf_updSrc hA ξ hs b hp ((exposed_some_iff A h).mp he)
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf (updSrc ξ k b) h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  simp only [fExp]
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p
  · rw [if_pos (hcond.mpr hq), if_pos hq]
    obtain ⟨h, p, hp, he, rfl⟩ := hq
    rw [kc_pointOf ξ hp, ← hpt h p hp he, kc_pointOf _ hp, snd_updSrc]
  · rw [if_neg (fun h' => hq (hcond.mp h')), if_neg hq]

/-! ## Fibers and charges -/

/-- The records with a given public key. -/
def fiberA (pk : BitVec 128) : Finset Rec := Finset.univ.filter fun ξ => pkOf ξ = pk

/-- The public data after signing at `A`. -/
abbrev Data := BitVec 128 × List Bool × Cache

/-- The public data of a record after signing at `A`. -/
def dataOf (A : Finset Name) (ξ : Rec) : Data := (pkOf ξ, revealed A ξ, fExp (some A) ξ)

/-- The records with given public data. -/
def fiberB (A : Finset Name) (d : Data) : Finset Rec := Finset.univ.filter fun ξ => dataOf A ξ = d

theorem fiberA_closedAt (pk : BitVec 128) {s : Name} (hs : s ≠ rh) : ClosedAt (fiberA pk) s := by
  by_cases hsrc : ∃ k, s = src k
  · obtain ⟨k, rfl⟩ := hsrc
    rw [closedAt_src]
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ξ hξ b
    rw [pkOf_updSrc]; exact hξ
  · push Not at hsrc
    rw [closedAt_of_ne_src _ hsrc]
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ξ hξ b
    rw [pkOf_updHash _ hs]; exact hξ

theorem dataOf_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) : dataOf A (updHash ξ s b) = dataOf A ξ := by
  simp only [dataOf, pkOf_updHash _ (hiddenCoord_ne_rh hs), revealed_updHash hA _ hs,
    fExp_updHash hA _ hs]

theorem dataOf_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 54}
    (hs : HiddenCoord A (src k)) (b : BitVec 129) : dataOf A (updSrc ξ k b) = dataOf A ξ := by
  simp only [dataOf, pkOf_updSrc, revealed_updSrc hA _ hs, fExp_updSrc hA _ hs]

theorem fiberB_closedAt {A : Finset Name} (hA : IsCut A) (d : Data) {s : Name}
    (hs : HiddenCoord A s) : ClosedAt (fiberB A d) s := by
  by_cases hsrc : ∃ k, s = src k
  · obtain ⟨k, rfl⟩ := hsrc
    rw [closedAt_src]
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ξ hξ b
    rw [dataOf_updSrc hA _ hs]; exact hξ
  · push Not at hsrc
    rw [closedAt_of_ne_src _ hsrc]
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ξ hξ b
    rw [dataOf_updHash hA _ hs]; exact hξ

/-- Before signing, every keygen point is hidden: a fixed query point is a keygen point of at
most an `ε` fraction of the records with a given public key. -/
theorem hits_charge_A (pk : BitVec 128) (q : Query) :
    ∑ ξ ∈ fiberA pk, (if (kc ξ q).isSome then w else 0) ≤ ε * ∑ _ξ ∈ fiberA pk, w := by
  by_cases hex : ∃ h p, hashParent h = some p ∧ ∃ ξ₀ : Rec, q = pointOf ξ₀ h p
  · obtain ⟨h, p, hp, ξ₀, rfl⟩ := hex
    have key : ∀ ξ : Rec, (kc ξ (pointOf ξ₀ h p)).isSome ↔ val ξ p = val ξ₀ p := by
      intro ξ
      rw [kc_isSome_iff]
      constructor
      · rintro ⟨h', p', hp', e⟩
        obtain rfl := pointOf_inj_left hp hp' e
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact (pointOf_inj_input e).symm
      · intro hv
        exact ⟨h, p, hp, by simp only [pointOf, hv]⟩
    have hcost : h.cost ≠ 0 := (hashParent_isSome_iff h).mp (by rw [hp]; rfl)
    calc ∑ ξ ∈ fiberA pk, (if (kc ξ (pointOf ξ₀ h p)).isSome then w else 0)
        = ∑ ξ ∈ fiberA pk, (if val ξ p = val ξ₀ p then w else 0) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          by_cases hv : val ξ p = val ξ₀ p <;> simp [key, hv]
      _ ≤ _ := sum_input_eq_le hp _ (fiberA_closedAt pk (coordOf_ne_rh h hcost)) _
  · have hz : ∀ ξ : Rec, ¬ (kc ξ q).isSome := by
      intro ξ hk
      rw [kc_isSome_iff] at hk
      obtain ⟨h, p, hp, e⟩ := hk
      exact hex ⟨h, p, hp, ξ, e⟩
    have hsum : ∑ ξ ∈ fiberA pk, (if (kc ξ q).isSome then w else 0) = 0 :=
      Finset.sum_eq_zero fun ξ _ => if_neg (hz ξ)
    exact hsum.le.trans _root_.zero_le

/-- After signing at `A`, a fixed query point is a hidden keygen point of at most an `ε`
fraction of the records with given public data. -/
theorem hits_charge_B {A : Finset Name} (hA : IsCut A) (d : Data) (q : Query) :
    ∑ ξ ∈ fiberB A d, (if (fHid (some A) ξ q).isSome then w else 0) ≤
      ε * ∑ _ξ ∈ fiberB A d, w := by
  by_cases hex : ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧ ∃ ξ₀ : Rec, q = pointOf ξ₀ h p
  · obtain ⟨h, p, hp, hh, ξ₀, rfl⟩ := hex
    have key : ∀ ξ : Rec, (fHid (some A) ξ (pointOf ξ₀ h p)).isSome ↔ val ξ p = val ξ₀ p := by
      intro ξ
      rw [fHid_isSome_some_iff]
      constructor
      · rintro ⟨h', p', hp', _, e⟩
        obtain rfl := pointOf_inj_left hp hp' e
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact (pointOf_inj_input e).symm
      · intro hv
        exact ⟨h, p, hp, hh, by simp only [pointOf, hv]⟩
    calc ∑ ξ ∈ fiberB A d, (if (fHid (some A) ξ (pointOf ξ₀ h p)).isSome then w else 0)
        = ∑ ξ ∈ fiberB A d, (if val ξ p = val ξ₀ p then w else 0) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          by_cases hv : val ξ p = val ξ₀ p <;> simp [key, hv]
      _ ≤ _ := sum_input_eq_le hp _ (fiberB_closedAt hA d (coordOf_hiddenCoord hA hp hh)) _
  · have hz : ∀ ξ : Rec, ¬ (fHid (some A) ξ q).isSome := by
      intro ξ hk
      rw [fHid_isSome_some_iff] at hk
      obtain ⟨h, p, hp, hh, e⟩ := hk
      exact hex ⟨h, p, hp, hh, ξ, e⟩
    have hsum : ∑ ξ ∈ fiberB A d, (if (fHid (some A) ξ q).isSome then w else 0) = 0 :=
      Finset.sum_eq_zero fun ξ _ => if_neg (hz ξ)
    exact hsum.le.trans _root_.zero_le

end WeightedConstruction.WideForest

end OptimalOTS

#print axioms OptimalOTS.WeightedConstruction.WideForest.hits_charge_A
#print axioms OptimalOTS.WeightedConstruction.WideForest.hits_charge_B

#print axioms OptimalOTS.WeightedConstruction.WideForest.hits_charge_A
#print axioms OptimalOTS.WeightedConstruction.WideForest.hits_charge_B
end
end

