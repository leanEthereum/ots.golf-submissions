import Submissions.UpperRiscv.MixedPhase
import Submissions.UpperRiscv.MixedStagedCost

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open scoped Classical
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] stagedBlocks stagedCost

theorem index_take (bits : List Bool) : ofBits 128 (bits.take 128) = ofBits 128 bits := by
  simpa only [List.drop_zero] using
    ofBits_drop_take bits (cap := 128) (start := 0) (len := 128) le_rfl

theorem image_code : image.code = verifier := rfl

/-- The certified cycle bound on every execution. -/
def cycleBound : ℕ := 348

/-- A chain value lies inside the first 5504 bits, where padding changes nothing. -/
theorem padded_slice (bits : List Bool) (k : Fin 32) :
    ofBits (chainBits k) (((padded bits).drop 128).drop (wireOffset k)) =
      ofBits (chainBits k) ((bits.drop 128).drop (wireOffset k)) := by
  have hc := wireOffset_contained k
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, testBit_foldr_bits,
    List.getD_eq_getElem?_getD, List.getElem?_drop, padded, List.getElem?_append,
    List.length_take, List.getElem?_take, List.getElem?_replicate]
  split_ifs <;> first | rfl | omega | (rw [List.getElem?_eq_none (by omega)]; rfl) | simp_all

theorem initial_chains (pk : PublicKey) (m : Message) (bits : List Bool) (answer : BitVec hashBits)
    (located : Riscv.CodeAt (S0 pk m bits) (W 4096) verifier) (x : graph.Assignment) :
    ChainsInv (rawIdx answer) ((padded bits).drop 128) pk (min bits.length 5505)
      (afterIndex pk m bits answer) x 0 := by
  refine ⟨afterIndex_ctx pk m bits answer located,
    (afterIndex_setupRegs pk m bits answer).2, ?_, (afterIndex_setupRegs pk m bits answer).1,
    ?_, ?_⟩
  · intro h; omega
  · intro j hj
    rw [padded_slice]
    exact afterIndex_payloadFrom pk m bits answer j hj
  · intro j hj; omega

theorem stagedVerify_unfold (pk : PublicKey) (m : Message) (bits : List Bool) :
    some <$> stagedVerify pk m bits = (do
      let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits bits))
      if IndexRank (pack answer) then
        some <$> stagedBlocks (rawIdx answer) (Payload.permute ((padded bits).drop 128)) pk
          (min bits.length 5505) 16 0 (fun _ => 0) 0
      else pure (some false)) := by
  unfold stagedVerify
  have ht : ofBits nonceBits (bits.take 128) = ofBits nonceBits bits := index_take bits
  rw [ht, map_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change some <$> (if IndexRank (pack answer) then _ else _) = _
  split_ifs <;> rfl

/-- Every accepted and rejected execution follows the staged verifier's exact oracle trace. -/
theorem image_refines (pk : PublicKey) (m : Message) (bits : List Bool) :
    Riscv.Refines 1337 (Riscv.initialState image pk m bits) (some <$> stagedVerify pk m bits)
      cycleBound := by
  have located := Riscv.CodeAt.initial image pk m bits image_valid
  rw [image_code] at located
  have pc0 : (Riscv.initialState image pk m bits).pc = Riscv.codeBase := by
    simp [Riscv.initialState]
  rw [← pc0] at located
  have global : Riscv.CodeAt (Riscv.initialState image pk m bits) (W 4096) verifier := by
    rw [pc0] at located
    exact located
  have e : verifier = indexPhase ++ (prologue 0 ++ List.replicate 9 nop ++ tables) := by
    simp only [verifier, List.append_assoc]
  rw [e] at located
  rw [stagedVerify_unfold, show cycleBound = 316 + 32 from rfl]
  apply indexPhase_refines pk m bits _ 316 1337
    (fun answer => some <$> stagedBlocks (rawIdx answer) (Payload.permute ((padded bits).drop 128))
      pk (min bits.length 5505) 16 0 (fun _ => 0) 0) _ (by norm_num) located
    (by rw [indexPhase_length]; norm_num)
  intro answer rank left hleft
  set index := rawIdx answer
  set s := afterIndex pk m bits answer
  have inv := initial_chains pk m bits answer global (fun _ => 0)
  have located2 : ∃ junk, Riscv.CodeAt s s.pc (blockCodeAt 0 ++ junk) := by
    have h := located.append_right (first := indexPhase)
    have hp : (Riscv.initialState image pk m bits).pc + BitVec.ofNat 64 (4 * 35) =
        W blockZero := by rw [pc0]; decide
    rw [indexPhase_length, hp] at h
    have h' := h.code_eq (afterIndex_code pk m bits answer)
    rw [← afterIndex_pc pk m bits answer] at h'
    exact ⟨_, h'⟩
  have bound := stagedCost_le index rank
  exact (stagedBlocks_refines index ((padded bits).drop 128) pk
    (by simp only [padded, List.length_drop, List.length_append, List.length_take,
      List.length_replicate]; omega)
    16 0 rfl (by omega) s (fun _ => 0) left inv located2 (by omega)).mono bound

/--
info: 'OptimalOTS.RiscvMixedProgram.image_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms image_refines

end OptimalOTS.RiscvMixedProgram
