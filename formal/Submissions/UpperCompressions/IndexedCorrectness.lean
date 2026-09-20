import Submissions.UpperCompressions.Correctness
import Submissions.UpperCompressions.IndexedSampling

/-! Perfect correctness for the submitted index threshold, including messages
chosen as arbitrary functions of the public key. Availability and security are
separate properties. The protected graph/cache semantics are reused unchanged. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.IndexedAnalysis.Correctness
open OptimalOTS.Dag
open OptimalOTS.GenericCorrectness (reconstruct_eq)

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem keygen_cacheConsistent (S : IndexedDag.Scheme numCuts) (c : Cache) :
    ∀ p ∈ support (run S.keygen c),
      p.1.1 = S.publicKey p.1.2 ∧ S.graph.CacheConsistent p.1.2 p.2 := by
  intro p hp
  simp only [IndexedDag.Scheme.keygen, Graph.keygen, run_bind, support_bind, Set.mem_iUnion] at hp
  obtain ⟨⟨x, d⟩, ⟨⟨z, d'⟩, _, hx⟩, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact ⟨rfl, S.graph.evaluate_cacheConsistent z d' _ hx⟩

/-- Successful signing records its selected index and returns that cut's complete encoding. -/
theorem sign_result (S : IndexedDag.Scheme numCuts) (x : S.graph.Assignment) (m : Message)
    (σ : Signature) (c d : Cache)
    (h : (some σ, d) ∈ support (run (S.sign x m) c)) :
    ∃ i : Fin numCuts, ∃ w : BitVec hashBits,
      σ.2 = S.graph.encode (S.sets i) x ∧
      d ⟨msgBits + nonceBits, m ++ σ.1⟩ = some w ∧
      (w.setWidth idxBits).toNat = i.val := by
  rw [sign_eq_map, run_map, support_map, Set.mem_image] at h
  obtain ⟨⟨r, d'⟩, hr, he⟩ := h
  cases r with
  | none => simp at he
  | some r =>
    obtain ⟨η, i⟩ := r
    simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at he
    rcases he with ⟨he, rfl⟩
    obtain ⟨w, hw, hi⟩ := (signIdx_support m c _ hr).2.2 η i rfl
    cases he
    exact ⟨i, w, rfl, hw, hi⟩

/-- A signature from a consistent assignment verifies under any extension of its signing cache. -/
theorem verify_accepts (S : IndexedDag.Scheme numCuts) (x : S.graph.Assignment) (m : Message)
    (σ : Signature) (c : Cache) (hc : S.graph.CacheConsistent x c)
    (i : Fin numCuts) (w : BitVec hashBits)
    (hσ : σ.2 = S.graph.encode (S.sets i) x)
    (hw : c ⟨msgBits + nonceBits, m ++ σ.1⟩ = some w)
    (hi : (w.setWidth idxBits).toNat = i.val) :
    ∀ p ∈ support (run (S.verify (S.publicKey x) m σ) c), p.1 = true := by
  intro p hp
  unfold IndexedDag.Scheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨j, d⟩, hj, hp⟩ := hp
  obtain ⟨hcd, w', hw', hj⟩ := index_support m σ.1 c ⟨j, d⟩ hj
  have hww : w' = w := Option.some.inj (hw'.symm.trans (hcd _ _ hw))
  rw [hww] at hj
  have hji : j = i.val := hj.trans hi
  subst j
  rw [dif_pos i.isLt] at hp
  have hlen : σ.2.length = S.graph.revealBits (S.sets i) := by
    rw [hσ, S.graph.length_encode]
  rw [if_pos hlen, run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨y, e⟩, hy, hp⟩ := hp
  obtain ⟨hde, he⟩ := S.graph.reconstruct_support _ _ d ⟨y, e⟩ hy
  rw [hσ] at he
  have hec := Graph.CacheConsistent.mono S.graph (hcd.trans hde) hc
  have hr := reconstruct_eq S.graph (S.sets i) x y e hec (S.no_hidden_source i)
    he S.graph.root Graph.Visited.root
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  simp only [IndexedDag.Scheme.publicKey, hr, decide_true]

/-- Every DAG scheme's generic adapter is perfectly correct, including for messages selected
as an arbitrary function of the public key. Signing failure is handled by the availability bound. -/
theorem correct (S : IndexedDag.Scheme numCuts) : S.toAlgorithm.Correct := by
  intro message
  dsimp only [IndexedDag.Scheme.toAlgorithm]
  unfold probTrue
  rw [StateT.run'_eq, probOutput_eq_zero_iff, support_map]
  rintro ⟨⟨b, e⟩, h, hb⟩
  change (b, e) ∈ support (run _ ∅) at h
  rw [run_bind, support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨⟨pk, sk⟩, c⟩, hk, h⟩ := h
  rw [run_bind, support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨σ, d⟩, hs, h⟩ := h
  obtain ⟨hpk, hkc⟩ := keygen_cacheConsistent S ∅ _ hk
  dsimp only at hpk hkc
  subst pk
  change b = true at hb
  cases σ with
  | none =>
    simp only [run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    cases h.1.symm.trans hb
  | some σ =>
    obtain ⟨i, w, hσ, hw, hi⟩ := sign_result S sk (message (S.publicKey sk)) σ c d hs
    have hcd := sub_of_mem_support_run (S.sign sk (message (S.publicKey sk))) c _ hs
    have hdc := Graph.CacheConsistent.mono S.graph hcd hkc
    rw [run_bind, support_bind] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨⟨ok, f⟩, hv, h⟩ := h
    have hok : ok = true :=
      verify_accepts S sk (message (S.publicKey sk)) σ d hdc i w hσ hw hi _ hv
    simp only [hok, Bool.not_true, run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    cases h.1.symm.trans hb


#print axioms correct
end OptimalOTS.IndexedAnalysis.Correctness
