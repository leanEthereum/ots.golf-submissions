import Submissions.UpperRiscvHint.MixedPrepare
import Submissions.UpperRiscvHint.MixedCost

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (wire : List Bool) (pk : PublicKey)

/-- A chain about to hash its value in place. -/
structure Prepared (s : MachineState) (x : graph.Assignment) (k : Fin 32) : Prop where
  inv : HashInv index wire pk s x k (work k)
  ready : MemBits s (W (work k)) (ofBits (chainBits k) (wire.drop (wireOffset k)))

/-- A fully hidden cap: its view value is its top, and no hash runs. -/
theorem hidden_refines (k : Fin 32) (hidden : 32 ≤ firstAt index k)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c : ℕ)
    (continuation : ∀ z : graph.Assignment, ChainsInv index wire pk s z (k.val+1) →
      Riscv.Refines fuel s (K (z,cursor k+chainBits k)) c)
    (prep : Prepared index wire pk s x k) :
    Riscv.Refines fuel s
      (runNodes' index (viewPayload wire) (chainNodes k) x (cursor k) >>= K) c := by
  have cap : k.val < 16 := by
    by_contra h
    have : firstAt index k ≤ 31 := by
      unfold firstAt firstEval; rw [if_neg h]; exact pos_le index k
    omega
  have hb : topBits k = chainBits k := topBits_of_cap cap
  obtain ⟨x', run, frame⟩ := prefix_run index (viewPayload wire) k 32 hidden x (cursor k)
  rw [chain_split_hidden, runNodes'_append, run, pure_bind,
    top_run_read index (viewPayload wire) k hidden, pure_bind]
  have hc : cursor k + topBits k = cursor k + chainBits k := by rw [hb]
  rw [hc]
  apply continuation
  refine ⟨prep.inv.ctx, ?_, ?_, ?_, prep.inv.payload, ?_⟩
  · rw [prep.inv.input]
    unfold prevInput
    rw [if_neg (by omega), Nat.add_sub_cancel]
  · intro _
    rw [Nat.add_sub_cancel]; exact prep.inv.out
  · rw [prep.inv.length]
    congr 1
  · intro j hj
    by_cases he : j = k
    · subst j
      rw [tops_update_top]
      apply (memBits_cast _ _ _ _).mpr
      rw [ofBits_take]
      have hw : graph.len (top k).fin = chainBits k := by rw [graph_len_fin]; exact hb
      have e : work k = outAddr k := by rw [work_eq' k]; simp [truncOff, cap]
      have key : ∀ n, n = chainBits k →
          MemBits s (W (outAddr k)) (ofBits n ((viewPayload wire).drop (cursor k))) := by
        intro n hn
        subst hn
        rw [viewPayload_read wire k, ← e]
        exact prep.ready
      exact key _ hw
    · rw [tops_update_top_other _ _ _ he, frame]
      exact prep.inv.done j (by have hne : j.val ≠ k.val := fun h => he (Fin.ext h); omega)

/-- The table row runs every hash of the chain, the first on its view value, then commits the
top. -/
theorem table_refines (k : Fin 32) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index wire pk u z (k.val+1) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,cursor k+chainBits k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (prep : Prepared index wire pk s x k)
    (located : Riscv.CodeAt s s.pc (List.replicate (remaining index k) .ECALL ++ tail))
    (bound : remaining index k+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (viewPayload wire) (chainNodes k) x (cursor k) >>= K)
      (remaining index k+c) := by
  set p := firstAt index k with hp
  by_cases h32 : 32 ≤ p
  · have hr : remaining index k = 0 := by unfold remaining; omega
    rw [hr] at located bound ⊢
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add] at located bound ⊢
    exact hidden_refines index wire pk k h32 s x fuel K c
      (fun z inv => continuation s z inv located fuel bound) prep
  have hp32 : p < 32 := by omega
  have finish : ∀ (u : MachineState) (z : graph.Assignment),
      HashInv index wire pk u z k (work k) → MemBits u (W (outAddr k)) (lastOut z k) →
      Riscv.CodeAt u u.pc tail → ∀ left, rest ≤ left →
      Riscv.Refines left u
        (runNodes' index (viewPayload wire) [top k] z (cursor k+chainBits k) >>= K) c := by
    intro u z invU lastU locatedU left hleft
    rw [top_run_eval index (viewPayload wire) k hp32, pure_bind]
    apply continuation u _ _ locatedU left hleft
    refine HashInv.complete index wire pk ⟨invU.ctx, invU.input, invU.inputRange, invU.length,
      invU.out, invU.payload, ?_⟩ ?_
    · intro j hj
      rw [tops_update_top_other _ _ _ (by intro he; subst j; omega)]
      exact invU.done j hj
    · rw [tops_update_top]
      apply (memBits_cast _ _ _ _).mpr
      apply (memBits_cast _ _ _ _).mpr
      exact top_of_answer k lastU
  have he : remaining index k = (32-(p+1))+1 := by unfold remaining; omega
  rw [he] at located bound ⊢
  rw [chain_split_first index k hp32, runNodes'_append, runNodes'_append, bind_assoc, bind_assoc]
  rw [List.replicate_succ, List.cons_append] at located
  rw [show 32-(p+1)+1+c = 1+(32-(p+1)+c) by omega]
  apply read_prefix_refines index wire pk k hp32 (List.replicate (32-(p+1)) .ECALL ++ tail)
    (fun r => runNodes' index (viewPayload wire) (suffixNodes index k) r.1 r.2 >>= fun r' =>
      runNodes' index (viewPayload wire) [top k] r'.1 r'.2 >>= K)
    (32-(p+1)+c) (32-(p+1)+rest) ?_ s x fuel prep.inv prep.ready located (by omega)
  intro u z invU heldU locatedU left hleft
  exact steps_refines index wire pk k tail
    (fun r => runNodes' index (viewPayload wire) [top k] r.1 r.2 >>= K) c rest
    (cursor k+chainBits k) finish
    (32-(p+1)) (p+1) rfl (by omega) (by omega) u z left invU heldU locatedU hleft

end OptimalOTS.RiscvMixedProgram
