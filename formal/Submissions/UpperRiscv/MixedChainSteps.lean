import Submissions.UpperRiscv.MixedHashStep
import Submissions.UpperRiscv.MixedPayload

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

variable (index : RawIdx) (v : ℕ) (wire : List Bool) (pk : PublicKey) {a : ℕ}

/-- The six bytes past the region stay zero throughout the chain phase. -/
def tailAfter (_index : RawIdx) (_v : ℕ) (_wire : List Bool) (_x : graph.Assignment) : BitVec 48 := 0

/-- The six bytes past the region at the boundary before chain `k`. -/
def TailInv (_index : RawIdx) (_v : ℕ) (_wire : List Bool)
    (s : MachineState) (_x : graph.Assignment) (_k : ℕ) : Prop :=
  MemBits s (W tailAddr) (0 : BitVec 48)

variable (a) in
/-- Invariant at a chain hash, with either its value or its working input address. -/
structure HashInv (s : MachineState) (x : graph.Assignment) (k : Fin 33) (base : ℕ) : Prop where
  ctx : Ctx s index v pk a
  input : s.getReg .x10 = W base
  inputRange : 32 ≤ base ∧ base+24 ≤ 0x78000000
  length : s.getReg .x11 = W (chainBits k)
  out : s.getReg .x12 = W (outAddr k)
  payload : PayloadFrom s wire (k.val+1)
  done : Completed s x k
  tail : TailInv index v wire s x k

theorem tailAfter_tripleUpdate (x : graph.Assignment) (k : Fin 33) (hk : k.val ≠ 1) (t : Fin 32)
    (u : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    tailAfter index v wire (tripleUpdate x k t u y) = tailAfter index v wire x := by
  rfl

theorem HashInv.writeHash {s : MachineState} {x : graph.Assignment} {k : Fin 33} {base : ℕ}
    (inv : HashInv index v wire pk a s x k base) (t : Fin 32)
    (u : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    HashInv index v wire pk a (Riscv.writeHash s y) (tripleUpdate x k t u y) k base := by
  refine ⟨inv.ctx.writeHash k y inv.out, ?_, inv.inputRange, ?_, ?_,
    inv.payload.writeHash k y inv.out, ?_, ?_⟩
  · rw [writeHash_regs]; exact inv.input
  · rw [writeHash_regs]; exact inv.length
  · rw [writeHash_regs]; exact inv.out
  · have h := inv.done.writeHash k y inv.out
    intro j hj
    rw [tops_tripleUpdate x k t u y j]
    exact h j hj
  · exact tail_writeHash _ inv.tail k y inv.out

theorem HashInv.frame {s t : MachineState} {x : graph.Assignment} {k : Fin 33} {base : ℕ}
    (inv : HashInv index v wire pk a s x k base) (next : ℕ) (hp : t.getReg .x10 = W next)
    (hb : 32 ≤ next ∧ next+24 ≤ 0x78000000)
    (regs : ∀ r, r ≠ .x10 → r ≠ .x28 → t.getReg r = s.getReg r)
    (mem : t.mem = s.mem) (code : t.code = s.code) : HashInv index v wire pk a t x k next := by
  refine ⟨inv.ctx.frame (fun r hr => ?_) mem code, hp, hb, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact regs _ (by decide) (by decide)
  · rw [regs .x11 (by decide) (by decide)]; exact inv.length
  · rw [regs .x12 (by decide) (by decide)]; exact inv.out
  · intro j hj; exact memBits_of_mem_eq mem (inv.payload j hj)
  · intro j hj; exact memBits_of_mem_eq mem (inv.done j hj)
  · exact memBits_of_mem_eq mem inv.tail

/-- A graph hash triple and one actual HASH have the same oracle input and state effect. -/
theorem step_refines (k : Fin 33) (t : Fin 32) (base : ℕ)
    (tail : Code) (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool))
    (c budget cursor cursor' : ℕ) (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (u : BitVec (graph.len (ci k t).fin))
    (hrun : runNodes' index v (Payload.permute wire) [ci k t, ch k t, cv k t] x cursor =
      hash u >>= fun y => pure (tripleUpdate x k t u y, cursor'))
    (inv : HashInv index v wire pk a s x k base) (held : MemBits s (W base) u)
    (located : Riscv.CodeAt s s.pc (.ECALL :: tail)) (bound : 1+budget ≤ fuel)
    (continuation : ∀ (w : MachineState) (y : BitVec hashBits),
      HashInv index v wire pk a w (tripleUpdate x k t u y) k base →
      MemBits w (W (outAddr k)) y → Riscv.CodeAt w w.pc tail →
      ∀ left, budget ≤ left → Riscv.Refines left w (K (tripleUpdate x k t u y, cursor')) c) :
    Riscv.Refines fuel s
      (runNodes' index v (Payload.permute wire) [ci k t, ch k t, cv k t] x cursor >>= K) (1+c) := by
  rw [hrun]
  simp only [bind_assoc, pure_bind]
  have valid := chain_hashValid s k base inv.input inv.out inv.length inv.inputRange
  have hin : Riscv.hashInput s = ⟨graph.len (ci k t).fin, u⟩ := by
    apply hashInput_of_memBits inv.input
    · rw [inv.length, graph_len_fin]
      exact W_toNat _ (by have := chainBits_le k; omega)
    · exact held
  have blocks : blockCost (graph.len (ci k t).fin) = 1 := by
    rw [graph_len_fin]; exact chain_blockCost k
  rw [show fuel = (fuel-1)+1 by omega]
  have h := Riscv.Refines.hash (fuel := fuel-1) located.head inv.ctx.call valid
    (k := fun y => K (tripleUpdate x k t u y, cursor')) (c := c) ?_
  · rw [hin, blocks] at h
    exact h
  intro y
  have b := output_bounds k
  have answer := writeHash_memBits s y (by
    rw [inv.out]; exact aligned_W _ b.2.2 (by unfold laneBase at b; omega))
  rw [inv.out] at answer
  apply continuation (Riscv.writeHash s y) y (HashInv.writeHash index v wire pk inv t u y) answer
    (located.tail.code_eq (writeHash_code s y)) (fuel-1) (by omega)

/-- What the working address holds before level `t`, or the full last answer after level 31. -/
def HoldsAt (s : MachineState) (x : graph.Assignment) (k : Fin 33) (t : ℕ) : Prop :=
  if h : t < 32 then
    MemBits s (W (work k))
      ((Forest.trunc k (x (prev k ⟨t,h⟩).fin)).cast (graph_len_fin (ci k ⟨t,h⟩)).symm)
  else MemBits s (W (outAddr k)) (lastAnswer x k)

theorem prev_succ (k : Fin 33) (t : Fin 32) (ht : t.val < 31) :
    prev k ⟨t.val+1, by omega⟩ = cv k t := by simp [prev]

/-- A full answer represents the next state at the chain's working address. -/
theorem holds_of_memAnswer {w : MachineState} (k : Fin 33) {y : BitVec 256}
    (answer : MemBits w (W (outAddr k)) y) : MemBits w (W (work k)) (Forest.trunc k y) := by
  have h := memBits_extract (start := truncOff k) (len := chainBits k) answer
    (truncOff_mod8 k) (truncOff_add_le k)
  rw [W_add, ← work_eq k] at h
  unfold Forest.trunc
  rw [Nat.min_eq_left (by have := truncOff_add_le k; omega : truncOff k ≤ 256-chainBits k)]
  exact h

theorem holdsAt_succ {w : MachineState} {x : graph.Assignment} {k : Fin 33} {t : Fin 32}
    {u : BitVec (graph.len (ci k t).fin)} {y : BitVec hashBits}
    (answer : MemBits w (W (outAddr k)) y) :
    HoldsAt w (tripleUpdate x k t u y) k (t.val+1) := by
  unfold HoldsAt
  by_cases h : t.val+1 < 32
  · rw [dif_pos h]
    apply (memBits_cast _ _ _ _).mpr
    rw [prev_succ k t (by omega), trunc_tripleUpdate_cv]
    exact holds_of_memAnswer k answer
  · rw [dif_neg h]
    have ht : t = 31 := Fin.ext (by have := t.isLt; omega)
    subst ht
    rw [lastAnswer_tripleUpdate]
    exact answer

theorem holdsAt_frame {s t : MachineState} {x : graph.Assignment} {k : Fin 33} {level : ℕ}
    (mem : t.mem = s.mem) (held : HoldsAt s x k level) : HoldsAt t x k level := by
  unfold HoldsAt at *
  split_ifs at * <;> exact memBits_of_mem_eq mem held

/-- Levels `t` to `31` of chain `k`, above the disclosed level. -/
theorem steps_refines (k : Fin 33) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' cursor : ℕ)
    (continuation : ∀ (w : MachineState) (y : graph.Assignment),
      HashInv index v wire pk a w y k (work k) → MemBits w (W (outAddr k)) (lastAnswer y k) →
      Riscv.CodeAt w w.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left w (K (y, cursor)) c) :
    ∀ (n t : ℕ), 32 - t = n → t ≤ 32 → RiscvUpperForest.ForestVerifier.pos index v k < t →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      HashInv index v wire pk a s x k (work k) → HoldsAt s x k t →
      Riscv.CodeAt s s.pc (List.replicate (32 - t) .ECALL ++ tail) →
      (32 - t) + rest' ≤ fuel →
      Riscv.Refines fuel s
        (runNodes' index v (Payload.permute wire)
          ((List.range' t (32 - t)).flatMap (tripleN k)) x cursor >>= K)
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
    apply step_refines index v wire pk k ⟨t, ht'⟩ (work k)
      (tail := List.replicate (32 - (t + 1)) .ECALL ++ tail)
      (fun r => runNodes' index v (Payload.permute wire)
        ((List.range' (t + 1) (32 - (t + 1))).flatMap (tripleN k)) r.1 r.2 >>= K)
      (32 - (t + 1) + c) (32 - (t + 1) + rest') cursor cursor s x fuel _
      (triple_run_step index v (Payload.permute wire) k ⟨t, ht'⟩ hp x cursor) inv held located
      (by omega)
    intro w y inv' answer located' left hleft
    exact ih (t + 1) (by omega) (by omega) (by omega) w _ left inv' (holdsAt_succ answer)
      located' (by omega)

end OptimalOTS.RiscvMixedProgram
