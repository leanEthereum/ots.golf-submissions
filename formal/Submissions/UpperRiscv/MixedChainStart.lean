import Submissions.UpperRiscv.MixedChainSteps

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

variable (index : RawIdx) (v : ℕ) (wire : List Bool) (pk : PublicKey) {a : ℕ}

theorem take_ofBits (l : List Bool) (n : ℕ) : ofBits n (l.take n) = ofBits n l := by
  simpa only [List.drop_zero] using ofBits_drop_take l (cap := n) (start := 0) (len := n) (by omega)

/-- The first chain hash includes the reader's pure prefix and its one disclosed input. -/
theorem read_prefix_refines (k : Fin 33) (hk : RiscvUpperForest.ForestVerifier.pos index v k ≤ 31) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : 5328 ≤ wire.length)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      HashInv index v wire pk a u z k (valueAddr k) →
      HoldsAt u z k (RiscvUpperForest.ForestVerifier.pos index v k+1) →
      Riscv.CodeAt u u.pc tail → ∀ left, rest ≤ left →
      Riscv.Refines left u (K (z, Payload.graphOff k+chainBits k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : HashInv index v wire pk a s x k (valueAddr k))
    (held : MemBits s (W (valueAddr k)) (ofBits (chainBits k) (wire.drop (wireOffset k))))
    (located : Riscv.CodeAt s s.pc (.ECALL::tail)) (bound : 1+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index v (Payload.permute wire) (readNodes index v k) x (Payload.graphOff k) >>= K)
      (1+c) := by
  set p := RiscvUpperForest.ForestVerifier.pos index v k with hp
  have hp32 : p < 32 := by omega
  obtain ⟨x', run, ftp, frame⟩ :=
    prefix_run index v (Payload.permute wire) k p le_rfl (by omega) x (Payload.graphOff k)
  have nodes : readNodes index v k =
      (src k :: (List.range p).flatMap (tripleN k)) ++ [ci k ⟨p,hp32⟩,ch k ⟨p,hp32⟩,cv k ⟨p,hp32⟩] := by
    unfold readNodes
    rw [← hp, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.cons_append]
    simp [tripleN, hp32]
  rw [nodes, runNodes'_append, run, pure_bind]
  have hne1 : TailInv index v wire s x' k := inv.tail
  have inv' : HashInv index v wire pk a s x' k (valueAddr k) := by
    refine ⟨inv.ctx, inv.input, inv.inputRange, inv.length, inv.out, inv.payload, ?_, hne1⟩
    intro j hj
    have he : tops x' j = tops x j := by
      unfold tops
      rw [ftp j]
    rw [he]; exact inv.done j hj
  have held' : MemBits s (W (valueAddr k))
      (ofBits (graph.len (ci k ⟨p,hp32⟩).fin)
        (((Payload.permute wire).drop (Payload.graphOff k)).take (graph.len (ci k ⟨p,hp32⟩).fin))) := by
    rw [take_ofBits]
    have hw : graph.len (ci k ⟨p,hp32⟩).fin = chainBits k := graph_len_fin _
    rw [hw, permute_read wire hlen k]
    exact held
  apply step_refines index v wire pk k ⟨p,hp32⟩ (valueAddr k) tail K c rest
    (Payload.graphOff k) (Payload.graphOff k+chainBits k) s x' fuel _
    (triple_run_read index v (Payload.permute wire) k ⟨p,hp32⟩ rfl x' (Payload.graphOff k))
    inv' held' located bound
  intro u y invU answer locatedU left hleft
  exact continuation u _ invU (holdsAt_succ answer) locatedU left hleft

end OptimalOTS.RiscvMixedProgram
