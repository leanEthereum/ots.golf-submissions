import Submissions.UpperCompressions.IndexedScheme
import Submissions.UpperCompressions.Reconstruct

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.IndexedAnalysis
open OptimalOTS.Dag
variable {M : ℕ}

/-- Every accepting run of the verifier is witnessed in the final cache: the index answer, and
an assignment satisfying the reconstruction equations whose root prefix is the public key. -/
theorem verify_support (S : IndexedDag.Scheme M) (pk : PublicKey) (m : Message)
    (σ : Signature) (c : Cache) :
    ∀ p ∈ support (run (S.verify pk m σ) c),
      Cache.Sub c p.2 ∧ (p.1 = true →
        ∃ w, p.2 ⟨msgBits + nonceBits, m ++ σ.1⟩ = some w ∧
          ∃ hi : (w.setWidth idxBits).toNat < M,
            σ.2.length = S.graph.revealBits (S.sets ⟨_, hi⟩) ∧
            ∃ y : S.graph.Assignment,
              S.graph.ReconEqs p.2 (S.sets ⟨_, hi⟩) (S.graph.decode (S.sets ⟨_, hi⟩) σ.2) y ∧
              S.publicKey y = pk) := by
  intro p hp
  unfold IndexedDag.Scheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨i, c₁⟩, hi₁, hp⟩ := hp
  obtain ⟨hsub₁, w, hw, rfl⟩ := index_support m σ.1 c ⟨i, c₁⟩ hi₁
  dsimp only at hp hw
  by_cases hi : (w.setWidth idxBits).toNat < M
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


end OptimalOTS.IndexedAnalysis

#print axioms OptimalOTS.IndexedAnalysis.verify_support
