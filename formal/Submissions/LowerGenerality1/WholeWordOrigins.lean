import OptimalOTS.WholeWords
import Submissions.LowerGenerality1.DisclosurePatterns

/-!
# Whole-word syntax bounds the number of disclosed hash origins

Every distinct origin requires at least one complete 128-bit word. A hash contributes
one origin and has 256 bits; either permitted half contributes that same single origin
and has 128 bits. A fixed public 128-bit word has no parents and hence no origins. Concatenation takes unions of origins while adding all input lengths,
including repeated inputs. Thus a 5376-bit payload has at most 42 distinct origins.
-/

noncomputable section
open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace WholeWordOrigins

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

private theorem origins_hash {v : Fin G.size} (hv : (G.kind v).IsHash) :
    G.hashOrigins v = {v} := by
  ext h
  rw [G.mem_hashOrigins, Finset.mem_singleton]
  constructor
  · intro ho
    exact Graph.HashOrigin.eq_of_hash G ho hv
  · rintro rfl
    exact Graph.HashOrigin.hash hv

private theorem origins_nonHash {v : Fin G.size} (hv : ¬ (G.kind v).IsHash) :
    G.hashOrigins v = (G.kind v).parents.biUnion G.hashOrigins := by
  ext h
  simp only [G.mem_hashOrigins, Finset.mem_biUnion]
  constructor
  · intro ho
    cases ho with
    | hash hh => exact (hv hh).elim
    | step _ hp ho => exact ⟨_, hp, ho⟩
  · rintro ⟨w, hw, ho⟩
    exact Graph.HashOrigin.step hv hw ho

private theorem sum_toFinset_le {α : Type*} [DecidableEq α] (f : α → ℕ) (ws : List α) :
    ∑ w ∈ ws.toFinset, f w ≤ (ws.map f).sum := by
  induction ws with
  | nil => simp
  | cons a ws ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases ha : a ∈ ws.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      exact ih.trans (Nat.le_add_left _ _)
    · rw [Finset.sum_insert ha]
      exact Nat.add_le_add_left ih _

end WholeWordOrigins

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- Whole-word operations cannot pack a new hash origin into fewer than 128 bits. -/
theorem card_hashOrigins_mul128_le (hwhole : G.WholeWords) (v : Fin G.size) :
    128 * (G.hashOrigins v).card ≤ G.len v := by
  induction v using WellFoundedLT.induction with
  | ind v ih =>
    have hv := hwhole v
    cases hk : G.kind v with
    | source =>
      have hn : ¬ (G.kind v).IsHash := by simp [hk, NodeKind.IsHash]
      rw [WholeWordOrigins.origins_nonHash G hn]
      simp [hk, NodeKind.parents]
    | hash p hp hl =>
      have hh : (G.kind v).IsHash := by simp [hk, NodeKind.IsHash]
      rw [WholeWordOrigins.origins_hash G hh, Finset.card_singleton, Nat.mul_one,
        hl, hashBits]
      omega
    | det ps hp f hf =>
      have hn : ¬ (G.kind v).IsHash := by simp [hk, NodeKind.IsHash]
      simp only [hk] at hv
      rw [WholeWordOrigins.origins_nonHash G hn]
      simp only [hk, NodeKind.parents]
      rcases hv with ⟨hps, _⟩ | ⟨ws, hps, hlen, _⟩ | ⟨p, high, hhash, hps, hlen, _⟩
      · rw [hps, Finset.biUnion_empty, Finset.card_empty, Nat.mul_zero]
        exact Nat.zero_le _
      · calc
          128 * (ps.biUnion G.hashOrigins).card ≤
              128 * ∑ p ∈ ps, (G.hashOrigins p).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
          _ = ∑ p ∈ ps, 128 * (G.hashOrigins p).card := Finset.mul_sum _ _ _
          _ ≤ ∑ p ∈ ps, G.len p := Finset.sum_le_sum fun p hp' => ih p (hp p hp')
          _ ≤ (ws.map G.len).sum := by
            rw [hps]
            exact WholeWordOrigins.sum_toFinset_le G.len ws
          _ = G.len v := hlen.symm
      · rw [hps, Finset.singleton_biUnion, WholeWordOrigins.origins_hash G hhash,
          Finset.card_singleton, hlen, wordBits]

/-- Union over a payload only reduces the origin count relative to adding its values' counts. -/
theorem card_disclosureOrigins_mul128_le (hwhole : G.WholeWords)
    (A : Finset (Fin G.size)) :
    128 * (G.disclosureOrigins A).card ≤ G.revealBits A := by
  calc
    128 * (G.disclosureOrigins A).card ≤ 128 * ∑ v ∈ A, (G.hashOrigins v).card :=
      Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ v ∈ A, 128 * (G.hashOrigins v).card := Finset.mul_sum _ _ _
    _ ≤ G.revealBits A := Finset.sum_le_sum fun v _ => G.card_hashOrigins_mul128_le hwhole v

end Dag.Graph

/-- The whole-word syntactic restriction implies the 42-origin bound from the payload budget. -/
theorem Dag.Scheme.disclosureBound42_of_wholeWords (S : Scheme)
    (hwhole : S.graph.WholeWords) :
    S.DisclosureBound 42 := by
  intro i
  have ho := S.graph.card_disclosureOrigins_mul128_le hwhole (S.sets i)
  have hl := S.reveal_le i
  rw [nonceBits, maxSignatureBits] at hl
  omega

end OptimalOTS
