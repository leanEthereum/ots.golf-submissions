import Submissions.UpperRiscv.MixedPhase

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open scoped Classical
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph

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
def cycleBound : ℕ := 360

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

/-- The image computes exactly the specified verifier within its fuel, and every run costs at
most `cycleBound` cycles. -/
theorem image_refines (pk : PublicKey) (m : Message) (bits : List Bool) :
    Riscv.Refines 1337 (Riscv.initialState image pk m bits) (some <$> directVerify pk m bits)
      cycleBound := by
  have located := Riscv.CodeAt.initial image pk m bits image_valid
  rw [image_code] at located
  have pc0 : (Riscv.initialState image pk m bits).pc = Riscv.codeBase := by
    simp [Riscv.initialState]
  rw [← pc0] at located
  have global : Riscv.CodeAt (Riscv.initialState image pk m bits) (W 4096) verifier := by
    rw [pc0] at located
    exact located
  have e : verifier = indexPhase ++ (prologue 0 ++ (List.range 6).flatMap groupCode) := by
    simp only [verifier, List.append_assoc]
  rw [e] at located
  rw [directVerify_unfold, show cycleBound = (299 + 21) + 40 from rfl]
  apply indexPhase_refines pk m bits _ 321 1337
    (fun answer => acceptedTail pk bits answer) _ (by norm_num) located
    (by rw [indexPhase_length]; norm_num)
  intro answer hi hlen left hleft
  rw [acceptedTail_eq pk bits answer hi hlen, order_eq, runNodes'_append]
  simp only [bind_assoc]
  set index := acceptedIdx answer hi
  set s := afterIndex pk m bits answer
  have inv := initial_chains pk m bits answer hi hlen global (fun _ => 0)
  have located2 : ∃ junk, Riscv.CodeAt s s.pc (blockCodeAt 0 ++ junk) := by
    have h := located.append_right (first := indexPhase)
    have hp : (Riscv.initialState image pk m bits).pc + BitVec.ofNat 64 (4 * 46) =
        W blockZero := by rw [pc0]; decide
    rw [indexPhase_length, hp] at h
    have h' := h.code_eq (afterIndex_code pk m bits answer)
    rw [← afterIndex_pc pk m bits answer] at h'
    exact ⟨_, h'⟩
  rw [← blocksCost_zero index]
  refine blocks_refines index (bits.drop 128) pk _ 21 11
    (by rw [List.length_drop, hlen]) ?_ 16 0 rfl
    (by norm_num) s (fun _ => 0) left inv located2 (by rw [blocksCost_zero]; omega)
  intro u y invU locatedU left2 hleft2
  exact rootDecision_refines index (Payload.permute (bits.drop 128)) pk u y left2
    (final_root index (bits.drop 128) pk invU) locatedU hleft2

/--
info: 'OptimalOTS.RiscvMixedProgram.image_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms image_refines

end OptimalOTS.RiscvMixedProgram
