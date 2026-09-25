import Submissions.UpperRiscvHint.Values

/-!
# Length-separated key generation leaves index queries fresh

This is a property of the actual cached evaluation, even when keygen queries
collide. No comparison with independent ideal node outputs is needed.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS
open OptimalOTS.Dag

namespace Dag.Graph

variable (G : Graph) (q : Query)
variable (hsep : ∀ (v p : Fin G.size) (hp : p < v) (hl : G.len v = hashBits),
  G.kind v = .hash p hp hl → G.len p ≠ q.1)

include hsep

theorem realStep_preserves_query (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (s : G.Assignment × Cache) (v : Fin G.size) :
    (G.realStep z y s v).2 q = s.2 q := by
  cases hk : G.kind v with
  | source => rw [G.realStep_of_kind_eq_source z y s hk]
  | det ps hps f hf => rw [G.realStep_of_kind_eq_det z y s hk]
  | hash p hp hl =>
    have hq : q ≠ (⟨G.len p, s.1 p⟩ : Query) := by
      intro h
      exact hsep v p hp hl hk (congrArg Sigma.fst h).symm
    cases hc : s.2 ⟨G.len p, s.1 p⟩ with
    | none =>
      rw [G.realStep_of_kind_eq_hash_none z y s hk hc]
      exact QueryCache.cacheQuery_of_ne _ _ hq
    | some w => rw [G.realStep_of_kind_eq_hash_some z y s hk hc]

theorem realFold_preserves_query (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (l : List (Fin G.size)) (s : G.Assignment × Cache) :
    (G.realFold z y l s).2 q = s.2 q := by
  induction l generalizing s with
  | nil => rfl
  | cons v l ih =>
    change (G.realFold z y l (G.realStep z y s v)).2 q = _
    rw [ih, G.realStep_preserves_query q hsep]

theorem realRun_fresh_query (ξ : G.Rec) : (G.realRun ξ).2 q = none := by
  unfold realRun
  rw [G.realFold_preserves_query q hsep]
  rfl

end Dag.Graph

namespace Forest

/-- Index queries are fresh after actual key generation, without a good-record assumption. -/
theorem realRun_enc_fresh (ξ : Rec) (u : EncInput) :
    (graph.realRun ξ).2 (encQuery u) = none := by
  apply graph.realRun_fresh_query
  intro v p hp hl hk
  change Fin N at v p
  obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨ofFin v, fin_ofFin v⟩
  obtain ⟨a, ha, rfl⟩ := graph_kind_eq_hash hk
  rw [graph_len_fin]
  exact len_hashParent_ne_enc ha

end Forest
end OptimalOTS
