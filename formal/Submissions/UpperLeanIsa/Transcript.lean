import Submissions.UpperLeanIsa.KeygenBridge
import Submissions.UpperLeanIsa.Master
import Submissions.UpperLeanIsa.Correctness

/-!
# The experiment in stages, and transcripts of the verifier

The strong-unforgeability experiment is `keygen >>= rest A` (`experiment_eq`), where `rest` runs
the first attacker stage, signing (`rest₂`), the second attacker stage and verification (`stB`).

Support-level descriptions of the runs of the chains, the root, the index query and the
verifier under the lazy random oracle: whatever the answers, the final cache contains every
query made, and the computed values are the fixed-table values of the table read off the final
cache (`table`). `ChainPath` and `RootPath` record that every query of the corresponding
evaluation is cached; both are monotone in the cache (`ChainPath.mono`, `RootPath.mono`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

attribute [local irreducible] trials

namespace Params

variable (P : Params) (A : OracleAlgorithm.Adversary)

end Params

/-! ## The table of a cache -/

/-- The fixed oracle table read off a cache; unset points answer `0`. -/
def table (c : Cache) : HashTable := fun q => (c q).getD 0

theorem table_eq_of_some {c : Cache} {q : Query} {u : BitVec hashBits} (h : c q = some u) :
    table c q = u := by
  simp only [table, h, Option.getD_some]

theorem table_of_sub {c c' : Cache} (h : Cache.Sub c c') {q : Query} (hq : (c q).isSome) :
    table c' q = table c q := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hq
  rw [table_eq_of_some hu, table_eq_of_some (h q u hu)]

namespace Params

variable (P : Params)

/-! ## Support of the building blocks -/

theorem run_hash_support {k : ℕ} (u : BitVec k) (c : Cache) :
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

theorem index_support (m : Message) (η : Nonce) (pk : PublicKey) (c : Cache) :
    ∀ p ∈ support (run (P.index m η pk) c), Cache.Sub c p.2 ∧
      (p.2 ⟨896, P.idxInput m η pk⟩).isSome ∧ p.1 = P.idxValue (table p.2) m η pk := by
  intro p hp
  unfold index at hp
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hsub, hc⟩ := run_hash_support _ c q hq
  refine ⟨hsub, Option.isSome_iff_exists.2 ⟨q.1, hc⟩, ?_⟩
  exact congrArg indexSlice (table_eq_of_some hc).symm

/-! ## Verification -/

variable (A : OracleAlgorithm.Adversary)

end Params

end OptimalOTS.LeanIsaBaseline.Layer
