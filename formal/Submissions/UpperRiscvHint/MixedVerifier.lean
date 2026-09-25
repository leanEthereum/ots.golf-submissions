import Submissions.UpperRiscvHint.MixedPhase
import Submissions.UpperRiscvHint.MixedStagedCost

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

/-- The specification after the accepted index and wire-length checks. -/
noncomputable def acceptedTail (pk : PublicKey) (bits : List Bool)
    (answer : BitVec hashBits) : OracleComp Spec (Option Bool) :=
  some <$> (if hi : pack answer ∈ validSet then
      if bits.length = 5504 then (do
        let y ← directReconstruct ⟨_, hi⟩ (Payload.permute (bits.drop 128))
        return decide ((y rh.fin).setWidth 128 = pk))
      else return false
    else return false)

/-- The specified verifier, expressed on the first oracle answer. -/
theorem directVerify_unfold (pk : PublicKey) (m : Message) (bits : List Bool) :
    some <$> directVerify pk m bits = (do
      let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits bits))
      if Accepted (pack answer) ∧ bits.length = 5504 then
        acceptedTail pk bits answer
      else pure (some false)) := by
  unfold directVerify packIndex acceptedTail
  rw [index_take]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  by_cases hi : Accepted (pack answer)
  · have hi' : pack answer ∈ validSet := mem_validSet.mpr ⟨pack_lt answer, hi⟩
    rw [dif_pos hi']
    by_cases hlen : bits.length = 5504
    · rw [if_pos hlen, if_pos ⟨hi, hlen⟩]
    · rw [if_neg hlen, if_neg (fun h => hlen h.2), pure_bind]
      rfl
  · have hi' : ¬ pack answer ∈ validSet := fun h => hi (mem_validSet_accepted h)
    rw [dif_neg hi', if_neg (fun h => hi h.1), pure_bind]
    rfl

theorem image_code : image.code = verifier := rfl

/-- The certified cycle bound on every execution. -/
def cycleBound : ℕ := 349

theorem order_eq : order = chainsFrom 0 ++ [rc, rh] := by
  rw [← chainsFrom_zero]
  rfl

/-- The accepted branch of the specification, as the reader over `order`. -/
theorem acceptedTail_eq (pk : PublicKey) (bits : List Bool) (answer : BitVec hashBits)
    (hi : Accepted (pack answer)) (hlen : bits.length = 5504) :
    acceptedTail pk bits answer =
      runNodes' (acceptedIdx answer hi) (Payload.permute (bits.drop 128)) order (fun _ => 0) 0 >>= fun r =>
        pure (some (@decide ((r.1 rh.fin).setWidth 128 = pk) (Classical.propDecidable _))) := by
  have hi' : pack answer ∈ validSet := (acceptedIdx answer hi).2
  unfold acceptedTail
  rw [dif_pos hi', if_pos hlen]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, directReconstruct,
    runNodes_eq_fst]
  try simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  try rfl

theorem initial_chains (pk : PublicKey) (m : Message) (bits : List Bool) (answer : BitVec hashBits)
    (hlen : bits.length = 5504)
    (located : Riscv.CodeAt (S0 pk m bits) (W 4096) verifier) (x : graph.Assignment) :
    ChainsInv (rawIdx answer) (bits.drop 128) pk (afterIndex pk m bits answer) x 0 := by
  refine ⟨afterIndex_ctx pk m bits answer hlen located,
    (afterIndex_setupRegs pk m bits answer).2, ?_, (afterIndex_setupRegs pk m bits answer).1,
    afterIndex_payloadFrom pk m bits answer, ?_⟩
  · intro h; omega
  · intro j hj; omega

theorem stagedVerify_unfold (pk : PublicKey) (m : Message) (bits : List Bool) :
    some <$> stagedVerify pk m bits = (do
      let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits bits))
      if IndexRank (pack answer) ∧ bits.length = 5504 then
        some <$> stagedBlocks (rawIdx answer) (Payload.permute (bits.drop 128)) pk 16 0 (fun _ => 0) 0
      else pure (some false)) := by
  unfold stagedVerify
  have ht : ofBits nonceBits (bits.take 128) = ofBits nonceBits bits := index_take bits
  rw [ht, map_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change some <$> (if IndexRank (pack answer) ∧ bits.length = 5504 then _ else _) = _
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
  have e : verifier = indexPhase ++ (prologue 0 ++ List.replicate 5 nop ++ tables) := by
    simp only [verifier, List.append_assoc]
  rw [e] at located
  rw [stagedVerify_unfold, show cycleBound = 316 + 33 from rfl]
  apply indexPhase_refines pk m bits _ 316 1337
    (fun answer => some <$> stagedBlocks (rawIdx answer) (Payload.permute (bits.drop 128))
      pk 16 0 (fun _ => 0) 0) _ (by norm_num) located
    (by rw [indexPhase_length]; norm_num)
  intro answer rank hlen left hleft
  set index := rawIdx answer
  set s := afterIndex pk m bits answer
  have inv := initial_chains pk m bits answer hlen global (fun _ => 0)
  have located2 : ∃ junk, Riscv.CodeAt s s.pc (blockCodeAt 0 ++ junk) := by
    have h := located.append_right (first := indexPhase)
    have hp : (Riscv.initialState image pk m bits).pc + BitVec.ofNat 64 (4 * 39) =
        W blockZero := by rw [pc0]; decide
    rw [indexPhase_length, hp] at h
    have h' := h.code_eq (afterIndex_code pk m bits answer)
    rw [← afterIndex_pc pk m bits answer] at h'
    exact ⟨_, h'⟩
  have bound := stagedCost_le index rank
  exact (stagedBlocks_refines index (bits.drop 128) pk (by rw [List.length_drop, hlen])
    16 0 rfl (by omega) s (fun _ => 0) left inv located2 (by omega)).mono bound

/--
info: 'OptimalOTS.RiscvMixedProgram.image_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms image_refines

end OptimalOTS.RiscvMixedProgram
