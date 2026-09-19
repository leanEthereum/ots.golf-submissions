import Submissions.UpperRiscv.RootPhase
import Submissions.UpperRiscv.IndexPhase

/-!
# Exact refinement of the machine image

The image observes exactly the certified raw-signature verifier, preserving every oracle query,
and every run, accepting or rejecting, costs at most `cycleBound = 702` cycles: 71 for the index
phase, `9 + 2 · nibble` per chain (608 in all, since the nibbles sum to 160), and 23 for the root
and the decision.
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open scoped Classical

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph

theorem index_take (bits : List Bool) : ofBits 128 (bits.take 128) = ofBits 128 bits := by
  simpa only [List.drop_zero] using
    ofBits_drop_take bits (cap := 128) (start := 0) (len := 128) le_rfl

/-- The specification after the accepted index and wire-length checks. -/
noncomputable def acceptedTail (pk : PublicKey) (bits : List Bool)
    (answer : BitVec hashBits) : OracleComp Spec (Option Bool) :=
  some <$> (if hi : (answer.setWidth idxBits).toNat ∈ validSet then
      if bits.length = 4224 then (do
        let y ← directReconstruct ⟨_, hi⟩ (bits.drop 128)
        return decide ((y rh.fin).setWidth 128 = pk))
      else return false
    else return false)

/-- The specified verifier, expressed on the first oracle answer. -/
theorem directVerify_unfold (pk : PublicKey) (m : Message) (bits : List Bool) :
    some <$> directVerify pk m bits = (do
      let answer ← hash (m ++ ofBits 128 bits)
      if Accepted (answer.setWidth 128).toNat ∧ bits.length = 4224 then
        acceptedTail pk bits answer
      else pure (some false)) := by
  unfold directVerify index acceptedTail
  rw [index_take]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  by_cases hi : Accepted (answer.setWidth 128).toNat
  · have hi' : (answer.setWidth idxBits).toNat ∈ validSet := (acceptedIdx answer hi).2
    rw [dif_pos hi']
    by_cases hlen : bits.length = 4224
    · rw [if_pos hlen, if_pos ⟨hi, hlen⟩]
    · rw [if_neg hlen, if_neg (fun h => hlen h.2), pure_bind]
      rfl
  · have hi' : ¬ (answer.setWidth idxBits).toNat ∈ validSet :=
      fun h => hi (mem_validSet_accepted h)
    rw [dif_neg hi', if_neg (fun h => hi h.1), pure_bind]
    rfl

theorem image_code : image.code = verifier := rfl

theorem verifier_length : verifier.length = 1337 := by decide +kernel

theorem image_valid : image.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · change verifier.length ≤ 262144
    rw [verifier_length]
    norm_num
  · change dataImage.length ≤ 1048576
    rw [dataImage_length]
    norm_num
  · have checked : verifier.all Riscv.admittedInstruction = true := by decide +kernel
    exact List.all_eq_true.mp checked

/-- The certified cycle bound on every execution. -/
def cycleBound : ℕ := 702

theorem order_eq : order = chainsFrom 0 ++ [rc, rh] := by
  rw [← chainsFrom_zero]
  rfl

theorem chains_length : chains.length = 1248 := by decide +kernel

/-- The accepted branch of the specification, as the reader over `order`. -/
theorem acceptedTail_eq (pk : PublicKey) (bits : List Bool) (answer : BitVec hashBits)
    (hi : Accepted (answer.setWidth 128).toNat) (hlen : bits.length = 4224) :
    acceptedTail pk bits answer =
      runNodes' (acceptedIdx answer hi) (bits.drop 128) order (fun _ => 0) 0 >>= fun r =>
        pure (some (@decide ((r.1 rh.fin).setWidth 128 = pk) (Classical.propDecidable _))) := by
  have hi' : (@BitVec.setWidth hashBits idxBits answer).toNat ∈ validSet := (acceptedIdx answer hi).2
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
  have e : verifier = indexPhase ++ (chains ++ (root ++ decision)) := by
    simp only [verifier, List.append_assoc]
  rw [e] at located
  rw [directVerify_unfold, show cycleBound = (608 + 23) + 71 from rfl]
  apply indexPhase_refines pk m bits (chains ++ (root ++ decision)) 1260 1337
    (fun answer => acceptedTail pk bits answer) _ (by norm_num) located
    (by rw [indexPhase_length])
  intro answer hi hlen left hleft
  rw [acceptedTail_eq pk bits answer hi hlen, order_eq, runNodes'_append]
  simp only [bind_assoc]
  set index := acceptedIdx answer hi
  set s := afterIndex pk m bits answer
  have inv : ChainsInv index (bits.drop 128) pk s (fun _ => 0) 0 := by
    refine ⟨afterIndex_ctx pk m bits answer hi hlen, ?_, afterIndex_pc pk m bits answer, ?_⟩
    · rw [afterIndex_prefixReg _ _ _ _ .x12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), (prefix_effect pk m bits).x12]
      rfl
    · intro h; omega
  have located2 : Riscv.CodeAt s s.pc (blocksFrom 0 ++ (root ++ decision)) := by
    have h := located.append_right (first := indexPhase)
    have hp : (Riscv.initialState image pk m bits).pc + BitVec.ofNat 64 (4 * 77) =
        W (blockStart 0) := by rw [pc0]; decide
    rw [indexPhase_length, blocks_eq, hp] at h
    rw [afterIndex_pc]
    exact h.code_eq (afterIndex_code pk m bits answer)
  rw [← costFrom_zero index]
  apply chainsFrom_refines index (bits.drop 128) pk (root ++ decision) _ 23 12 ?_ 32 0 rfl
    (by norm_num) s (fun _ => 0) left inv located2 (by rw [← blocks_eq, chains_length]; omega)
  intro u y invU locatedU left2 hleft2
  exact rootDecision_refines index (bits.drop 128) pk u y left2 invU locatedU hleft2

/--
info: 'OptimalOTS.RiscvUpperProgram.image_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms image_refines

end OptimalOTS.RiscvUpperProgram
