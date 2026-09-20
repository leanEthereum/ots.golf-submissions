import Submissions.UpperRiscv.ChainBlock

/-!
# The chain phase

The 28 chain blocks run one after the other, in the specification's chain-major node order.
After chain `k`, the low 192 bits of the tops of chains `0 … k - 1` form the prefix of the root
input in memory and the full top of chain `k` lies below its slot. The phase costs `4 + (32 - p)`
cycles per chain, `355` in all.
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (payload : List Bool) (pk : PublicKey)

/-- Chains `k` and later, in specification order. -/
def chainsFrom (k : ℕ) : List Name :=
  if h : k < 28 then chainNodes ⟨k, h⟩ ++ chainsFrom (k + 1) else []
termination_by 28 - k

/-- The blocks of chains `k` and later. -/
def blocksFrom (k : ℕ) : Code :=
  if k < 28 then chainBlock k ++ blocksFrom (k + 1) else []
termination_by 28 - k

set_option maxRecDepth 100000 in
theorem chainsFrom_zero : (List.finRange 28).flatMap chainNodes = chainsFrom 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem blocks_eq : chains = blocksFrom 0 := by
  decide +kernel

theorem blocksFrom_nil (k : ℕ) (hk : ¬ k < 28) : blocksFrom k = [] := by
  rw [blocksFrom, if_neg hk]

theorem blocksFrom_cons (k : ℕ) (hk : k < 28) :
    blocksFrom k = chainBlock k ++ blocksFrom (k + 1) := by
  rw [blocksFrom, if_pos hk]

/-- The cycles of chains `k` and later. -/
def costFrom (k : ℕ) : ℕ :=
  if h : k < 28 then 4 + (32 - RiscvUpperForest.ForestVerifier.pos index ⟨k, h⟩) + costFrom (k + 1)
  else 0
termination_by 28 - k

theorem costFrom_eq : ∀ (n k : ℕ), 28 - k = n → costFrom index k =
    ∑ k' : Fin 28, if k ≤ k'.val then 4 + (32 - RiscvUpperForest.ForestVerifier.pos index k')
      else 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    rw [costFrom, dif_neg (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro k' _
    rw [if_neg]
    have := k'.isLt
    omega
  | succ n ih =>
    intro k hk
    have hk28 : k < 28 := by omega
    rw [costFrom, dif_pos hk28, ih (k + 1) (by omega)]
    have single : 4 + (32 - RiscvUpperForest.ForestVerifier.pos index ⟨k, hk28⟩) =
        ∑ k' : Fin 28, if k' = ⟨k, hk28⟩ then
          (if k ≤ k'.val then 4 + (32 - RiscvUpperForest.ForestVerifier.pos index k') else 0)
        else 0 := by
      rw [Finset.sum_ite_eq' Finset.univ (⟨k, hk28⟩ : Fin 28)
        (fun k' : Fin 28 => if k ≤ k'.val then
          4 + (32 - RiscvUpperForest.ForestVerifier.pos index k') else 0),
        if_pos (Finset.mem_univ _)]
      simp only [le_refl, if_true]
    rw [single, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k' _
    by_cases he : k' = ⟨k, hk28⟩
    · subst he
      simp only [↓reduceIte, le_refl]
      split_ifs <;> omega
    · rw [if_neg he, Nat.zero_add]
      have hne : k'.val ≠ k := fun h => he (Fin.ext h)
      split_ifs <;> omega

/-- The 28 prologues and 243 hash steps cost 355 cycles on every accepted index. -/
theorem costFrom_zero : costFrom index 0 = 355 := by
  rw [costFrom_eq index 28 0 rfl]
  simp only [Nat.zero_le, if_true]
  rw [Finset.sum_add_distrib, Finset.sum_const]
  have hs : ∑ k' : Fin 28, (32 - RiscvUpperForest.ForestVerifier.pos index k') = target + 28 :=
    fixedPositions_sum index
  rw [hs]
  rfl

/-- Chains `k` and later refine the reader over their nodes. -/
theorem chainsFrom_refines (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y 28 → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 5376)) c) :
    ∀ (n k : ℕ), 28 - k = n → k ≤ 28 →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      ChainsInv index payload pk s x k →
      Riscv.CodeAt s s.pc (blocksFrom k ++ tail) →
      (blocksFrom k).length + rest' ≤ fuel →
      Riscv.Refines fuel s (runNodes' index payload (chainsFrom k) x (192 * k) >>= K)
        (costFrom index k + c) := by
  intro n
  induction n with
  | zero =>
    intro k hk hk' s x fuel inv located bound
    have hk28 : k = 28 := by omega
    subst hk28
    rw [chainsFrom, dif_neg (by omega), costFrom, dif_neg (by omega), Nat.zero_add, runNodes',
      pure_bind]
    rw [blocksFrom_nil 28 (by omega), List.nil_append] at located
    rw [blocksFrom_nil 28 (by omega), List.length_nil, Nat.zero_add] at bound
    exact continuation s x inv located fuel bound
  | succ n ih =>
    intro k hk hk' s x fuel inv located bound
    have hk28 : k < 28 := by omega
    rw [chainsFrom, dif_pos hk28, costFrom, dif_pos hk28, runNodes'_append, bind_assoc]
    rw [blocksFrom_cons k hk28, List.append_assoc] at located
    rw [blocksFrom_cons k hk28, List.length_append, chainBlock_length] at bound
    have hp := pos_le index ⟨k, hk28⟩
    have hl : 32 - RiscvUpperForest.ForestVerifier.pos index ⟨k, hk28⟩ ≤ levels k :=
      levels_ge index ⟨k, hk28⟩
    rw [Nat.add_assoc]
    apply chain_refines index payload pk ⟨k, hk28⟩ (blocksFrom (k + 1) ++ tail)
      (fun r => runNodes' index payload (chainsFrom (k + 1)) r.1 r.2 >>= K)
      (costFrom index (k + 1) + c) ((blocksFrom (k + 1)).length + rest') ?_ s x fuel inv located
      (by unfold blockLength at bound; omega)
    intro u y inv' located' left hleft
    dsimp only
    rw [show 192 * k + 192 = 192 * (k + 1) by ring]
    exact ih (k + 1) (by omega) (by omega) u y left inv' located' hleft

end OptimalOTS.Riscv2Program
