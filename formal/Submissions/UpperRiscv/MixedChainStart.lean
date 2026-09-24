import Submissions.UpperRiscv.MixedChainSteps

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (wire : List Bool) (pk : PublicKey)

def readNodes (k : Fin 32) : List Name :=
  src k :: (List.range (RiscvUpperForest.ForestVerifier.pos index k+1)).flatMap (tripleN k)
def suffixNodes (k : Fin 32) : List Name :=
  (List.range' (RiscvUpperForest.ForestVerifier.pos index k+1)
    (32-(RiscvUpperForest.ForestVerifier.pos index k+1))).flatMap (tripleN k)

theorem chain_split_first (k : Fin 32) : chainNodes k = readNodes index k ++ suffixNodes index k := by
  have h := pos_le index k
  rw [chainNodes_eq, range_split (RiscvUpperForest.ForestVerifier.pos index k+1) (by omega),
    List.flatMap_append]
  rfl

/-- The first chain hash includes the reader's pure prefix and its one disclosed input. -/
theorem read_prefix_refines (k : Fin 32) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : wire.length = 5376)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      HashInv index wire pk u z k (wireSlot k) →
      HoldsAt u z k (RiscvUpperForest.ForestVerifier.pos index k+1) →
      Riscv.CodeAt u u.pc tail → ∀ left, rest ≤ left →
      Riscv.Refines left u (K (z,cursor k+chainBits k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : HashInv index wire pk s x k (wireSlot k))
    (held : MemBits s (W (wireSlot k)) (ofBits (chainBits k) (wire.drop (wireOffset k))))
    (located : Riscv.CodeAt s s.pc (.ECALL::tail)) (bound : 1+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (Payload.permute wire) (readNodes index k) x (cursor k) >>= K) (1+c) := by
  set p := RiscvUpperForest.ForestVerifier.pos index k with hp
  have hp32 : p < 32 := by have := pos_le index k; omega
  obtain ⟨x', run, frame⟩ := prefix_run index (Payload.permute wire) k p le_rfl x (cursor k)
  have nodes : readNodes index k =
      (src k :: (List.range p).flatMap (tripleN k)) ++ [ci k ⟨p,hp32⟩,ch k ⟨p,hp32⟩,cv k ⟨p,hp32⟩] := by
    unfold readNodes
    rw [← hp, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.cons_append]
    simp [tripleN, hp32]
  rw [nodes, runNodes'_append, run, pure_bind]
  have inv' : HashInv index wire pk s x' k (wireSlot k) := by
    refine ⟨inv.ctx, inv.input, inv.inputRange, inv.length, inv.out, inv.payload, ?_⟩
    intro j hj
    have he : tops x' j = tops x j := by
      unfold tops
      rw [frame j (by intro he; subst j; omega)]
    rw [he]; exact inv.done j hj
  have held' : MemBits s (W (wireSlot k))
      (ofBits (graph.len (ci k ⟨p,hp32⟩).fin)
        (((Payload.permute wire).drop (cursor k)).take (graph.len (ci k ⟨p,hp32⟩).fin))) := by
    have take : ∀ n, ofBits n (((Payload.permute wire).drop (cursor k)).take n) =
        ofBits n ((Payload.permute wire).drop (cursor k)) := by
      intro n
      simpa only [List.drop_zero] using
        ofBits_drop_take ((Payload.permute wire).drop (cursor k)) (cap := n) (start := 0) (len := n) (by omega)
    rw [take]
    have hw : graph.len (ci k ⟨p,hp32⟩).fin = chainBits k := graph_len_fin _
    rw [hw, permute_read wire hlen k]
    exact held
  apply step_refines index wire pk k ⟨p,hp32⟩ (wireSlot k) tail K c rest
    (cursor k) (cursor k+chainBits k) s x' fuel _
    (triple_run_read index (Payload.permute wire) k ⟨p,hp32⟩ rfl x' (cursor k))
    inv' held' located bound
  intro u y invU answer locatedU left hleft
  exact continuation u _ invU (holdsAt_succ answer) locatedU left hleft

end OptimalOTS.RiscvMixedProgram
