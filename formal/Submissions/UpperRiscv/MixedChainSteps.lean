import Submissions.UpperRiscv.MixedHashStep
import Submissions.UpperRiscv.MixedPayload

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (wire : List Bool) (pk : PublicKey)

/-- Invariant at a chain hash, with either its wire or expanded input address. -/
structure HashInv (s : MachineState) (x : graph.Assignment) (k : Fin 32) (base : ℕ) : Prop where
  ctx : Ctx s index pk
  input : s.getReg .x10 = W base
  inputRange : 32 ≤ base ∧ base+24 ≤ 0x78000000
  length : s.getReg .x11 = W (chainBits k)
  out : s.getReg .x12 = W (outAddr k)
  payload : PayloadFrom s wire (k.val+1)
  done : Completed s (tops x) k

theorem HashInv.writeHash {s : MachineState} {x : graph.Assignment} {k : Fin 32} {base : ℕ}
    (inv : HashInv index wire pk s x k base) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    HashInv index wire pk (Riscv.writeHash s y) (tripleUpdate x k t v y) k base := by
  refine ⟨inv.ctx.writeHash k y inv.out, ?_, inv.inputRange, ?_, ?_,
    inv.payload.writeHash k y inv.out, ?_⟩
  · rw [writeHash_regs]; exact inv.input
  · rw [writeHash_regs]; exact inv.length
  · rw [writeHash_regs]; exact inv.out
  · have h := inv.done.writeHash k y inv.out
    intro j hj
    rw [tops_tripleUpdate x k t v y j (by intro he; subst j; omega)]
    exact h j hj

/-- A graph hash triple and one actual HASH have the same oracle input and state effect. -/
theorem step_refines (k : Fin 32) (t : Fin 32) (base : ℕ)
    (tail : Code) (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool))
    (c budget cursor cursor' : ℕ) (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (v : BitVec (graph.len (ci k t).fin))
    (hrun : runNodes' index (Payload.permute wire) [ci k t, ch k t, cv k t] x cursor =
      hash v >>= fun y => pure (tripleUpdate x k t v y, cursor'))
    (inv : HashInv index wire pk s x k base) (held : MemBits s (W base) v)
    (located : Riscv.CodeAt s s.pc (.ECALL :: tail)) (bound : 1+budget ≤ fuel)
    (continuation : ∀ (u : MachineState) (y : BitVec hashBits),
      HashInv index wire pk u (tripleUpdate x k t v y) k base →
      MemBits u (W (outAddr k)) y → Riscv.CodeAt u u.pc tail →
      ∀ left, budget ≤ left → Riscv.Refines left u (K (tripleUpdate x k t v y, cursor')) c) :
    Riscv.Refines fuel s
      (runNodes' index (Payload.permute wire) [ci k t, ch k t, cv k t] x cursor >>= K) (1+c) := by
  rw [hrun]
  simp only [bind_assoc, pure_bind]
  have valid := chain_hashValid s k base inv.input inv.out inv.length inv.inputRange
  have hin : Riscv.hashInput s = ⟨graph.len (ci k t).fin, v⟩ := by
    apply hashInput_of_memBits inv.input
    · rw [inv.length, graph_len_fin]
      exact W_toNat _ (by have := chainBits_le k; omega)
    · exact held
  have blocks : blockCost (graph.len (ci k t).fin) = 1 := by
    rw [graph_len_fin]; exact chain_blockCost k
  rw [show fuel = (fuel-1)+1 by omega]
  have h := Riscv.Refines.hash (fuel := fuel-1) located.head inv.ctx.call valid
    (k := fun y => K (tripleUpdate x k t v y, cursor')) (c := c) ?_
  · rw [hin, blocks] at h
    exact h
  intro y
  have b := output_bounds k
  have answer := writeHash_memBits s y (by rw [inv.out]; exact aligned_W _ b.2.2 (by omega))
  rw [inv.out] at answer
  apply continuation (Riscv.writeHash s y) y (HashInv.writeHash index wire pk inv t v y) answer
    (located.tail.code_eq (writeHash_code s y)) (fuel-1) (by omega)

/-- What the working address holds before level t, or the full output after level 31. -/
def HoldsAt (s : MachineState) (x : graph.Assignment) (k : Fin 32) (t : ℕ) : Prop :=
  if h : t < 32 then
    MemBits s (W (work k))
      ((Forest.trunc k (x (prev k ⟨t,h⟩).fin)).cast (graph_len_fin (ci k ⟨t,h⟩)).symm)
  else MemBits s (W (outAddr k)) (tops x k)

theorem prev_succ (k : Fin 32) (t : Fin 32) (ht : t.val < 31) :
    prev k ⟨t.val+1, by omega⟩ = cv k t := by simp [prev]

/-- A full answer represents the next state at the chain's working address. -/
theorem holds_of_memAnswer {u : MachineState} (k : Fin 32) {y : BitVec 256}
    (answer : MemBits u (W (outAddr k)) y) : MemBits u (W (work k)) (Forest.trunc k y) := by
  have h := memBits_extract (start := truncOff k) (len := chainBits k) answer
    (truncOff_mod8 k) (truncOff_add_le k)
  rw [W_add, ← work_eq' k] at h
  unfold Forest.trunc
  rw [Nat.min_eq_left (by have := truncOff_add_le k; omega : truncOff k ≤ 256-chainBits k)]
  exact h

theorem holdsAt_succ {u : MachineState} {x : graph.Assignment} {k : Fin 32} {t : Fin 32}
    {v : BitVec (graph.len (ci k t).fin)} {y : BitVec hashBits}
    (answer : MemBits u (W (outAddr k)) y) :
    HoldsAt u (tripleUpdate x k t v y) k (t.val+1) := by
  unfold HoldsAt
  by_cases h : t.val+1 < 32
  · rw [dif_pos h]
    apply (memBits_cast _ _ _ _).mpr
    rw [prev_succ k t (by omega), trunc_tripleUpdate_cv]
    exact holds_of_memAnswer k answer
  · rw [dif_neg h]
    have ht : t = 31 := Fin.ext (by have := t.isLt; omega)
    subst ht
    unfold tops
    rw [tripleUpdate_cv]
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    exact answer

/-- Levels `t` to `31` of chain `k`, above the disclosed level. -/
theorem steps_refines (k : Fin 32) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' cursor : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      HashInv index wire pk u y k (work k) → MemBits u (W (outAddr k)) (tops y k) →
      Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor)) c) :
    ∀ (n t : ℕ), 32 - t = n → t ≤ 32 → RiscvUpperForest.ForestVerifier.pos index k < t →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      HashInv index wire pk s x k (work k) → HoldsAt s x k t →
      Riscv.CodeAt s s.pc (List.replicate (32 - t) .ECALL ++ tail) →
      (32 - t) + rest' ≤ fuel →
      Riscv.Refines fuel s
        (runNodes' index (Payload.permute wire) ((List.range' t (32 - t)).flatMap (tripleN k)) x cursor >>= K)
        ((32 - t) + c) := by
  intro n
  induction n with
  | zero =>
    intro t ht _ _ s x fuel inv held located bound
    have h32 : t = 32 := by omega
    subst h32
    simp only [Nat.sub_self, List.range'_zero, List.flatMap_nil, List.nil_append, runNodes',
      pure_bind, List.replicate_zero, Nat.zero_add] at located bound ⊢
    unfold HoldsAt at held
    rw [dif_neg (by omega)] at held
    exact continuation s x inv held located fuel bound
  | succ n ih =>
    intro t hn ht hp s x fuel inv held located bound
    have ht' : t < 32 := by omega
    have hsucc : 32 - t = (32 - (t + 1)) + 1 := by omega
    rw [hsucc] at located bound ⊢
    rw [List.range'_succ, List.flatMap_cons, runNodes'_append, bind_assoc]
    have triple : tripleN k t = [ci k ⟨t, ht'⟩, ch k ⟨t, ht'⟩, cv k ⟨t, ht'⟩] := by
      simp [tripleN, ht']
    rw [triple]
    rw [List.replicate_succ, List.cons_append] at located
    rw [show 32 - (t + 1) + 1 + c = 1 + (32 - (t + 1) + c) by omega]
    unfold HoldsAt at held
    rw [dif_pos ht'] at held
    apply step_refines index wire pk k ⟨t, ht'⟩ (work k)
      (tail := List.replicate (32 - (t + 1)) .ECALL ++ tail)
      (fun r => runNodes' index (Payload.permute wire) ((List.range' (t + 1) (32 - (t + 1))).flatMap (tripleN k))
        r.1 r.2 >>= K)
      (32 - (t + 1) + c) (32 - (t + 1) + rest') cursor cursor s x fuel _
      (triple_run_step index (Payload.permute wire) k ⟨t, ht'⟩ hp x cursor) inv held located (by omega)
    intro u y inv' answer located' left hleft
    exact ih (t + 1) (by omega) (by omega) (by omega) u _ left inv' (holdsAt_succ answer)
      located' (by omega)


end OptimalOTS.RiscvMixedProgram
