import Submissions.UpperRiscv.KeygenSupport
import Submissions.UpperRiscv.Reconstruct
import Submissions.UpperRiscv.SignIdx
import Submissions.UpperRiscv.Adapter

/-!
Perfect correctness of the DAG adapter. The shared cache preserves the key-generation equations
and the signing index. Reconstructing an honestly encoded cut therefore recovers the public key,
even when oracle inputs repeat. The message may be any function of the public key.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.GenericCorrectness

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials


/-- A reconstruction satisfying the cached equations agrees with the original on visited nodes. -/
theorem reconstruct_eq (G : Graph) (A : Finset (Fin G.size)) (x y : G.Assignment)
    (c : Cache) (hc : G.CacheConsistent x c)
    (hsrc : ∀ v, G.Visited A v → v ∉ A → ¬ (G.kind v).IsSource)
    (hy : G.ReconEqs c A (G.decode A (G.encode A x)) y)
    (v : Fin G.size) (hv : G.Visited A v) : y v = x v := by
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    by_cases hA : v ∈ A
    · exact (hy v).1 hA |>.trans (G.decode_encode A x hA)
    · have hn := (hy v).2.2 hA hv
      have hx := hc v
      have hp : ∀ w ∈ (G.kind v).parents, y w = x w := fun w hw =>
        ih w ((G.kind v).lt_of_mem_parents hw) (Graph.Visited.parent hv hA hw)
      cases hk : G.kind v with
      | source => exact (hsrc v hv hA (by simp [hk, NodeKind.IsSource])).elim
      | det ps hps f hf =>
        have hx' : x v = f x := by simpa [Graph.CacheEqAt, hk] using hx
        exact (hn.2.1 ps hps f hf hk).trans ((hf y x (by simpa [hk, NodeKind.parents] using hp)).trans hx'.symm)
      | hash p hlt hl =>
        obtain ⟨w, hw, hyw⟩ := hn.1 p hlt hl hk
        have hpx : y p = x p := hp p (by simp [hk, NodeKind.parents])
        have hx' : c ⟨G.len p, x p⟩ = some ((x v).cast hl) := by
          simpa [Graph.CacheEqAt, hk] using hx
        rw [hpx, hx'] at hw
        have hw' := Option.some.inj hw
        rw [hyw, ← hw']
        simp

/-- Successful signing records its selected index and returns that cut's complete encoding. -/
theorem sign_result (S : GScheme) (x : S.graph.Assignment) (m : Message)
    (σ : Signature) (c d : Cache)
    (h : (some σ, d) ∈ support (run (S.sign x m) c)) :
    ∃ i : Idx, ∃ w : BitVec hashBits,
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
theorem verify_accepts (S : GScheme) (x : S.graph.Assignment) (m : Message)
    (σ : Signature) (c : Cache) (hc : S.graph.CacheConsistent x c)
    (i : Idx) (w : BitVec hashBits)
    (hσ : σ.2 = S.graph.encode (S.sets i) x)
    (hw : c ⟨msgBits + nonceBits, m ++ σ.1⟩ = some w)
    (hi : (w.setWidth idxBits).toNat = i.val) :
    ∀ p ∈ support (run (S.verify (S.publicKey x) m σ) c), p.1 = true := by
  intro p hp
  unfold GScheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨j, d⟩, hj, hp⟩ := hp
  obtain ⟨hcd, w', hw', hj⟩ := index_support m σ.1 c ⟨j, d⟩ hj
  have hww : w' = w := Option.some.inj (hw'.symm.trans (hcd _ _ hw))
  rw [hww] at hj
  have hji : j = i.val := hj.trans hi
  subst j
  rw [dif_pos i.2] at hp
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
  simp only [GScheme.publicKey, hr, decide_true]

/-- Every DAG scheme's generic adapter is perfectly correct, including for messages selected
as an arbitrary function of the public key. Signing failure is handled by the availability bound. -/
theorem correct (S : GScheme) : S.toAlgorithm.Correct := by
  intro message
  dsimp only [GScheme.toAlgorithm]
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
  obtain ⟨hpk, hkc⟩ := S.keygen_cacheConsistent ∅ _ hk
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

/--
info: 'OptimalOTS.GenericCorrectness.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correct

end OptimalOTS.GenericCorrectness
