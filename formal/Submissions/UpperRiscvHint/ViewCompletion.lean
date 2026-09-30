import Submissions.UpperRiscvHint.StagedVerifier
import Submissions.UpperRiscvHint.ViewLayout
import Submissions.UpperRiscvHint.CompletionCorrect
import Submissions.UpperRiscvHint.MixedChainStart

noncomputable section
open scoped Classical
open OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.Dag.Graph

theorem decode_take_reveal (G : Graph) (A : Finset (Fin G.size)) (payload : List Bool)
    (v : Fin G.size) (hv : v ∈ A) :
    G.decode A (payload.take (G.revealBits A)) v = G.decode A payload v := by
  have bound : G.offset A v + G.len v ≤ G.revealBits A := by
    rw [G.offset_eq, G.revealBits_eq]
    exact chunkOff_add_le G.len _ ((List.pairwise_lt_finRange _).filter _) v (by simp [hv])
  unfold decode
  rw [RiscvMixedProgram.ofBits_take, RiscvMixedProgram.ofBits_take]
  exact Riscv2Program.ofBits_drop_take payload bound

end OptimalOTS.Dag.Graph

namespace OptimalOTS.RiscvUpperForest.ForestVerifier
open OptimalOTS.Dag Forest Forest.Name
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits Forest.forestScheme

theorem reconstruct_take (A : Finset Name) (payload : List Bool) :
    reconstruct A (payload.take (graph.revealBits (fins A))) = reconstruct A payload := by
  have same : step A (graph.decode (fins A) (payload.take (graph.revealBits (fins A)))) =
      step A (graph.decode (fins A) payload) := by
    funext x n
    unfold step
    by_cases h : n ∈ A
    · rw [if_pos h, if_pos h, graph.decode_take_reveal _ _ _ ((mem_fins A n).mpr h)]
    · rw [if_neg h, if_neg h]
  simp only [reconstruct, same]

end OptimalOTS.RiscvUpperForest.ForestVerifier

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag Forest Forest.Name RiscvUpperForest.ForestVerifier
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

theorem fullSignatureBits_cases (index : ChainIndex) :
    fullSignatureBits index = 5495 ∨ fullSignatureBits index = 5498 := by
  unfold fullSignatureBits
  split_ifs <;> simp

/-- All weighted pairs are admitted, so staging preserves the full verifier exactly. -/
theorem stagedVerify_eq_wire (pk : PublicKey) (m : Message) (bits : List Bool) :
    stagedVerify pk m bits = RiscvUpperForest.Wire.scheme.verify pk m bits := by
  rw [← directVerify_eq]
  symm
  unfold directVerify stagedVerify packIndex
  rw [bind_map_left]
  apply bind_congr
  intro answer
  dsimp only
  by_cases hi : pack answer ∈ validSet
  · rw [dif_pos hi]
    dsimp +instances only [Idx.toRaw]
    have rank : stagedRank (pack answer) :=
      (stagedRank_and_caps_iff _).mpr (mem_validSet_accepted hi) |>.1
    by_cases hlen : bits.length = fullSignatureBits (ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩)
    · rw [if_pos hlen, if_pos ⟨rank, hlen⟩]
      simpa only [Idx.toRaw] using
        (stagedBlocks_eq_direct (⟨pack answer, hi⟩ : Idx) (bits.drop 128) pk).symm
    · rw [if_neg hlen, if_neg (fun h => hlen h.2)]
  · rw [dif_neg hi]
    rw [if_neg]
    rintro ⟨rank, _⟩
    exact hi (mem_validSet.mpr ⟨pack_lt answer,
      (stagedRank_and_caps_iff _).mp ⟨rank, fun q => pairAllowed_all _ q⟩⟩)

theorem freeBlocks_take (index : Idx) (payload : List Bool) (pk : PublicKey) :
    freeBlocks index (payload.take (fullSignatureBits index - 128)) pk (fun _ => 0) =
      freeBlocks index payload pk (fun _ => 0) := by
  rw [stagedBlocks_eq_direct, stagedBlocks_eq_direct]
  simp only [directReconstruct_eq]
  have size : fullSignatureBits index - 128 = graph.revealBits (fins (setsName index)) :=
    (fixed_revealBits index).symm
  rw [size, reconstruct_take]

/-- A fixed-size view retains the full bottom top for its zero-step case. -/
def padFull (σ : List Bool) : List Bool := σ ++ List.replicate (5498 - σ.length) false

theorem padFull_length {σ : List Bool} (h : σ.length = 5495 ∨ σ.length = 5498) :
    (padFull σ).length = 5498 := by
  simp only [padFull, List.length_append, List.length_replicate]
  rcases h with h | h <;> omega

theorem padFull_project {σ : List Bool} (h : σ.length = 5495 ∨ σ.length = 5498) :
    Completion.project (padFull σ) = Completion.project σ := by
  unfold Completion.project padFull
  apply List.take_append_of_le_length
  rcases h with h | h <;> omega

theorem padFull_take {σ : List Bool} (h : σ.length ≤ 5498) :
    (padFull σ).take σ.length = σ := by
  simp [padFull]

theorem padFull_nonce {σ : List Bool} (h : 128 ≤ σ.length) :
    (padFull σ).take 128 = σ.take 128 := by
  exact List.take_append_of_le_length h

theorem padFull_payload_take {σ : List Bool} (h : 128 ≤ σ.length) :
    ((padFull σ).drop 128).take (σ.length - 128) = σ.drop 128 := by
  unfold padFull
  rw [List.drop_append_of_le_length h, ← List.length_drop (l := σ) (i := 128), List.take_left]

theorem candidate_length {σ full : List Bool} (h : full ∈ Completion.candidates σ) :
    full.length = 5495 ∨ full.length = 5498 := by
  unfold Completion.candidates at h
  split_ifs at h with hlen
  · simp only [List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨j, _, rfl⟩
    · exact Or.inl hlen
    · right
      simp [hlen]
  · simp at h

def viewFull (index : ChainIndex) (view : List Bool) : List Bool :=
  viewNonce view ++ (viewPayload view).take (fullSignatureBits index - 128)

theorem viewFull_length (index : ChainIndex) (view : List Bool) :
    (viewFull index view).length = fullSignatureBits index := by
  rcases fullSignatureBits_cases index with h | h <;> simp [viewFull, h]

theorem viewFull_nonce (index : ChainIndex) (view : List Bool) :
    (viewFull index view).take 128 = viewNonce view := by
  exact List.take_left' (viewNonce_length view)

theorem viewFull_payload (index : ChainIndex) (view : List Bool) :
    (viewFull index view).drop 128 = (viewPayload view).take (fullSignatureBits index - 128) := by
  exact List.drop_left' (viewNonce_length view)

theorem viewFull_project (index : ChainIndex) (view : List Bool) :
    Completion.project (viewFull index view) =
      Completion.project (viewNonce view ++ viewPayload view) := by
  rcases fullSignatureBits_cases index with h | h <;>
    simp [Completion.project, viewFull, List.take_append, List.take_take, h]

theorem padded_blocks (index : Idx) (σ : List Bool)
    (hlen : σ.length = fullSignatureBits index) (pk : PublicKey) :
    freeBlocks index ((padFull σ).drop 128) pk (fun _ => 0) =
      freeBlocks index (σ.drop 128) pk (fun _ => 0) := by
  rw [← freeBlocks_take index ((padFull σ).drop 128), ← hlen, padFull_payload_take]
  rcases fullSignatureBits_cases index with h | h <;> omega

end OptimalOTS.RiscvMixedProgram
