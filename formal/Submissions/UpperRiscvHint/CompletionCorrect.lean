import Submissions.UpperRiscvHint.Completion
import Submissions.UpperRiscvHint.HintTransfer
import Submissions.UpperRiscvHint.Layout

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace OptimalOTS.Completion

open OptimalOTS.Dag

attribute [local irreducible] RiscvUpperForest.Wire.scheme Forest.forestScheme
attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits
  keygenBudget signBudget nonceBits idxBits numCuts trials
attribute [local irreducible] GScheme.sign GScheme.signLoop

theorem suffix_enum (l : List Bool) (h : l.length = 3) :
    ∃ j : Fin 8, l = List.ofFn (fun b : Fin 3 => decide ((j.val / 2^b.val) % 2 = 1)) := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp h
  cases a <;> cases b <;> cases c <;> decide +kernel

theorem full_mem_candidates {σ : Signature} (h : σ.length = 5495 ∨ σ.length = 5498) :
    σ ∈ candidates (project σ) := by
  rcases h with h | h
  · simp [project, h, candidates]
  · have hp : (project σ).length = 5495 := by simp [project, h]
    have ht : (σ.drop 5495).length = 3 := by simp [h]
    obtain ⟨j, hj⟩ := suffix_enum _ ht
    rw [candidates, if_pos hp, List.mem_cons]
    right
    apply List.mem_map.mpr
    refine ⟨j, by simp, ?_⟩
    rw [← hj]
    exact List.take_append_drop 5495 σ

theorem signed_full_length (sk : Forest.forestScheme.graph.Assignment) (m : Message) (σ : OptimalOTS.Signature)
    (h : some σ ∈ support (Forest.forestScheme.sign sk m)) :
    (AlgorithmAdapter.encodeSignature σ).length = 5495 ∨
      (AlgorithmAdapter.encodeSignature σ).length = 5498 := by
  unfold GScheme.sign at h
  obtain ⟨i, hi⟩ := AlgorithmAdapter.signLoop_returns Forest.forestScheme sk m trials ∅ σ h
  have hl : (AlgorithmAdapter.encodeSignature σ).length =
      128 + Forest.forestScheme.graph.revealBits (Forest.forestScheme.sets i) := by
    rw [AlgorithmAdapter.length_encodeSignature, hi, AlgorithmAdapter.length_encode]
    unfold nonceBits
    rfl
  rw [Forest.fixed_revealBits] at hl
  unfold Forest.fullSignatureBits at hl
  split_ifs at hl <;> omega

theorem findValid_succeeds (pk : PublicKey) (m : Message) (l : List Signature) (known : Signature)
    (hmem : known ∈ l) (c : Cache)
    (hgood : ∀ d, Cache.Sub c d → ∀ p ∈ support (run (RiscvUpperForest.Wire.scheme.verify pk m known) d),
      p.1 = true) (result : Option Signature) (last : Cache)
    (hrun : (result, last) ∈ support (run (findValid pk m l) c)) : result.isSome = true := by
  induction l generalizing c result last with
  | nil => simp at hmem
  | cons σ rest ih =>
    rw [findValid, run_bind, mem_support_bind_iff] at hrun
    obtain ⟨⟨ok, d⟩, hv, hr⟩ := hrun
    have hcd := sub_of_mem_support_run (RiscvUpperForest.Wire.scheme.verify pk m σ) c _ hv
    cases ok
    · have hne : known ≠ σ := by
        intro e
        subst σ
        have impossible := hgood c (Cache.Sub.refl c) _ hv
        cases impossible
      have hrest : known ∈ rest := (List.mem_cons.mp hmem).resolve_left hne
      exact ih hrest d (fun e hde => hgood e (hcd.trans hde)) result last hr
    · simp only [Bool.true_eq, if_true, run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hr
      rw [hr.1]
      rfl

theorem findValid_replay (pk : PublicKey) (m : Message) (l : List Signature) (full : Signature)
    (c last : Cache) (h : (some full, last) ∈ support (run (findValid pk m l) c)) :
    ∀ d, Cache.Sub last d → run (RiscvUpperForest.Wire.scheme.verify pk m full) d = pure (true, d) := by
  induction l generalizing c last with
  | nil => simp [findValid, run_pure] at h
  | cons σ rest ih =>
    rw [findValid, run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨ok, middle⟩, hv, hr⟩ := h
    cases ok
    · exact ih middle last hr
    · simp only [Bool.true_eq, if_true, run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      intro d hsub
      exact RiscvHint.replay_deterministic _
        (RiscvUpperForest.Wire.admissible.verifyDeterministic pk m full) c last d true hv
        (fun {_ _} hq => hsub _ _ hq)

theorem verify_from_full (pk : PublicKey) (m : Message) (known : Signature)
    (hlen : known.length = 5495 ∨ known.length = 5498) (c : Cache)
    (hgood : ∀ d, Cache.Sub c d → ∀ p ∈ support (run (RiscvUpperForest.Wire.scheme.verify pk m known) d),
      p.1 = true) (p : Bool × Cache)
    (h : p ∈ support (run (scheme.verify pk m (project known)) c)) : p.1 = true := by
  change p ∈ support (run (ProjectionTransfer.verify _ _ _ pk m (project known)) c) at h
  rw [ProjectionTransfer.verify, run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨full, middle⟩, hf, h⟩ := h
  have hsome := findValid_succeeds pk m (candidates (project known)) known
    (full_mem_candidates hlen) c hgood full middle hf
  cases full with
  | none => cases hsome
  | some full =>
    have hmember := findValid_mem pk m (candidates (project known)) full
      (RiscvHint.mem_support_of_mem_support_run _ _ c middle hf)
    have hproject := candidate_project hmember
    rw [run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨ok, last⟩, hv, h⟩ := h
    have replay := findValid_replay pk m (candidates (project known)) full c middle hf middle
      (Cache.Sub.refl middle)
    change (ok, last) ∈ support (run (RiscvUpperForest.Wire.scheme.verify pk m full) middle) at hv
    rw [replay, support_pure, Set.mem_singleton_iff] at hv
    cases hv
    simp only [Option.getD_some, Option.isSome_some, hproject, decide_true, Bool.true_and,
      run_pure, support_pure, Set.mem_singleton_iff] at h
    exact congrArg Prod.fst h

attribute [local semireducible] RiscvUpperForest.Wire.scheme

/-- Any accepted completion remains a witness after the machine's cache grows. -/
theorem verify_from_accepted (pk : PublicKey) (m : Message) (full : Signature)
    (hlen : full.length = 5495 ∨ full.length = 5498) (c₀ c₁ : Cache)
    (hfull : (true, c₁) ∈ support (run (RiscvUpperForest.Wire.scheme.verify pk m full) c₀))
    (c₂ : Cache) (hsub : Cache.Sub c₁ c₂) (p : Bool × Cache)
    (h : p ∈ support (run (scheme.verify pk m (project full)) c₂)) : p.1 = true := by
  apply verify_from_full pk m full hlen c₂ _ p h
  intro d hd p hp
  have replay := RiscvHint.replay_deterministic _
    (RiscvUpperForest.Wire.admissible.verifyDeterministic pk m full) c₀ c₁ d true hfull
    (fun {_ _} hq => hd _ _ (hsub _ _ hq))
  change run (RiscvUpperForest.Wire.scheme.verify pk m full) d = pure (true, d) at replay
  rw [replay, support_pure, Set.mem_singleton_iff] at hp
  exact congrArg Prod.fst hp

theorem verify_path (pk : PublicKey) (m : Message) (σ : Signature) (c₀ c₁ : Cache)
    (h : (true, c₁) ∈ support (run (scheme.verify pk m σ) c₀)) :
    ∃ full middle,
      (some full, middle) ∈ support (run (recover pk m σ) c₀) ∧
      (true, c₁) ∈ support (run (RiscvUpperForest.Wire.scheme.verify pk m full) middle) ∧
      project full = σ := by
  change (true, c₁) ∈ support (run (ProjectionTransfer.verify _ _ _ pk m σ) c₀) at h
  rw [ProjectionTransfer.verify, run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨full, middle⟩, hf, h⟩ := h
  rw [run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨ok, last⟩, hv, h⟩ := h
  rw [run_pure, support_pure, Set.mem_singleton_iff] at h
  have hc : c₁ = last := congrArg Prod.snd h
  subst last
  have hb := (congrArg Prod.fst h).symm
  dsimp only at hb hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  cases full with
  | none => cases hb.1.1
  | some full =>
    have hok : ok = true := hb.2
    subst ok
    exact ⟨full, middle, hf, hv, hb.1.2⟩

/-- Honest signing always leaves enough cached equations for completion to succeed. -/
theorem correct : scheme.Correct := by
  intro message
  simp only [scheme, ProjectionTransfer.scheme, RiscvUpperForest.Wire.scheme,
    WireAdapter.scheme, RiscvUpperForest.scheme, GScheme.toAlgorithm, bind_map_left]
  unfold probTrue
  rw [StateT.run'_eq, probOutput_eq_zero_iff, support_map]
  rintro ⟨⟨b, e⟩, h, hb⟩
  change (b, e) ∈ support (run _ ∅) at h
  rw [run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨⟨pk, sk⟩, c⟩, hk, h⟩ := h
  rw [run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨σ, d⟩, hs, h⟩ := h
  obtain ⟨hpk, hkc⟩ := Forest.forestScheme.keygen_cacheConsistent ∅ _ hk
  dsimp only at hpk hkc
  subst pk
  change b = true at hb
  cases σ with
  | none =>
    simp only [Option.map_none, run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    cases h.1.symm.trans hb
  | some σ =>
    obtain ⟨i, w, hσ, hw, hi⟩ := GenericCorrectness.sign_result Forest.forestScheme sk
      (message (Forest.forestScheme.publicKey sk)) σ c d hs
    have hcd := sub_of_mem_support_run
      (Forest.forestScheme.sign sk (message (Forest.forestScheme.publicKey sk))) c _ hs
    have hdc := Graph.CacheConsistent.mono Forest.forestScheme.graph hcd hkc
    have hgood : ∀ f, Cache.Sub d f → ∀ p ∈ support (run
        (RiscvUpperForest.Wire.scheme.verify (Forest.forestScheme.publicKey sk)
          (message (Forest.forestScheme.publicKey sk)) (AlgorithmAdapter.encodeSignature σ)) f),
        p.1 = true := by
      intro f hdf p hp
      change p ∈ support (run (Forest.forestScheme.verify (Forest.forestScheme.publicKey sk)
        (message (Forest.forestScheme.publicKey sk))
        (RiscvUpperForest.Wire.decode (AlgorithmAdapter.encodeSignature σ))) f) at hp
      rw [RiscvUpperForest.Wire.decode_encode] at hp
      exact GenericCorrectness.verify_accepts Forest.forestScheme sk _ σ f
        (Graph.CacheConsistent.mono _ hdf hdc) i w hσ (hdf _ _ hw) hi p hp
    have hlen := signed_full_length sk _ σ
      (RiscvHint.mem_support_of_mem_support_run _ _ c d hs)
    simp only [Option.map_some] at h
    rw [run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨ok, f⟩, hv, h⟩ := h
    have hok : ok = true := verify_from_full _ _ (AlgorithmAdapter.encodeSignature σ)
      hlen d hgood _ hv
    simp only [hok, Bool.not_true, run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    cases h.1.symm.trans hb

theorem admissible : scheme.Admissible where
  correct := correct
  verifyDeterministic := verify_deterministic
  signingFailure := signing_failure
  signatureSize := signature_size
  rejectsOversized := rejects_oversized
  keygenCost := keygen_cost
  signCost := sign_cost
  verifyCost := OracleAlgorithm.Scheme.VerifyCostAtMost.mono _ verify_cost (by decide)

end OptimalOTS.Completion
