import Submissions.UpperRiscvHint.MixedChainSteps

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (wire : List Bool) (pk : PublicKey)

def readNodes (k : Chain) : List Name :=
  src k :: (List.range (firstAt index k+1)).flatMap (tripleN k)
def suffixNodes (k : Chain) : List Name :=
  (List.range' (firstAt index k+1) (32-(firstAt index k+1))).flatMap (tripleN k)

theorem chain_split_first (k : Chain) (h : firstAt index k < 32) :
    chainNodes k = (readNodes index k ++ suffixNodes index k) ++ [top k] := by
  rw [chainNodes_eq, range_split (firstAt index k+1) (by omega), List.flatMap_append]
  rfl

/-- A fully hidden chain: every level is a pure zero, before the top. -/
theorem chain_split_hidden (k : Chain) :
    chainNodes k = (src k :: (List.range 32).flatMap (tripleN k)) ++ [top k] :=
  chainNodes_eq k

theorem ofBits_take (payload : List Bool) (c n : ℕ) :
    ofBits n ((payload.drop c).take n) = ofBits n (payload.drop c) := by
  simpa only [List.drop_zero] using
    ofBits_drop_take (payload.drop c) (cap := n) (start := 0) (len := n) (by omega)

/-- The first chain hash includes the reader's pure prefix and its one disclosed input. -/
theorem read_prefix_refines (k : Chain) (h32 : firstAt index k < 32) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      HashInv index wire pk u z k (work k) →
      HoldsAt u z k (firstAt index k+1) →
      Riscv.CodeAt u u.pc tail → ∀ left, rest ≤ left →
      Riscv.Refines left u (K (z,cursor k+chainBits k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : HashInv index wire pk s x k (work k))
    (held : MemBits s (W (work k)) (ofBits (chainBits k) (wire.drop (wireOffset k))))
    (located : Riscv.CodeAt s s.pc (.ECALL::tail)) (bound : 1+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (viewPayload wire) (readNodes index k) x (cursor k) >>= K) (1+c) := by
  set p := firstAt index k with hp
  obtain ⟨x', run, frame⟩ := prefix_run index (viewPayload wire) k p le_rfl x (cursor k)
  have nodes : readNodes index k =
      (src k :: (List.range p).flatMap (tripleN k)) ++ [ci k ⟨p,h32⟩,ch k ⟨p,h32⟩,cv k ⟨p,h32⟩] := by
    unfold readNodes
    rw [← hp, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.cons_append]
    simp [tripleN, h32]
  rw [nodes, runNodes'_append, run, pure_bind]
  have inv' : HashInv index wire pk s x' k (work k) :=
    ⟨inv.ctx, inv.input, inv.inputRange, inv.length, inv.out, inv.payload, frame ▸ inv.done⟩
  have held' : MemBits s (W (work k))
      (ofBits (graph.len (ci k ⟨p,h32⟩).fin)
        (((viewPayload wire).drop (cursor k)).take (graph.len (ci k ⟨p,h32⟩).fin))) := by
    rw [ofBits_take]
    have hw : graph.len (ci k ⟨p,h32⟩).fin = chainBits k := graph_len_fin _
    rw [hw, viewPayload_read wire k]
    exact held
  apply step_refines index wire pk k ⟨p,h32⟩ (work k) tail K c rest
    (cursor k) (cursor k+chainBits k) s x' fuel _
    (triple_run_read index (viewPayload wire) k ⟨p,h32⟩ rfl x' (cursor k))
    inv' held' located bound
  intro u y invU answer locatedU left hleft
  exact continuation u _ invU (holdsAt_succ answer) locatedU left hleft

end OptimalOTS.RiscvMixedProgram
