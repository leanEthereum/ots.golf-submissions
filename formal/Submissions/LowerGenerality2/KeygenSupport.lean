import Submissions.LowerGenerality2.Cache
import Submissions.LowerGenerality2.Semantics

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
