import Submissions.UpperRiscv.ChainBlock

/-!
# The chain phase

The 16 blocks run one after the other, covering the 28 chains in the specification's chain-major
node order: block `q < 12` hashes chains `2q` and `2q + 1`, block `12 + s` hashes chain `24 + s`.
The phase costs `6 + (32 - p) + (32 - p')` cycles per pair and `4 + (32 - p)` per single, `331` in
all.
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

set_option maxRecDepth 100000 in
theorem chainsFrom_zero : (List.finRange 28).flatMap chainNodes = chainsFrom 0 := by
  decide +kernel

theorem chainsFrom_cons (k : ℕ) (hk : k < 28) :
    chainsFrom k = chainNodes ⟨k, hk⟩ ++ chainsFrom (k + 1) := by
  rw [chainsFrom, dif_pos hk]

theorem chainsFrom_nil (k : ℕ) (hk : ¬ k < 28) : chainsFrom k = [] := by
  rw [chainsFrom, dif_neg hk]

/-- The blocks split the chains in order. -/
theorem chainsFrom_block (q : ℕ) (hq : q < 16) :
    chainsFrom (firstChain q) = blockNodes q ++ chainsFrom (firstChain (q + 1)) := by
  unfold blockNodes
  by_cases h : q < 12
  · rw [dif_pos h]
    have e0 : firstChain q = 2 * q := by unfold firstChain; rw [if_pos h]
    have e1 : firstChain (q + 1) = 2 * q + 2 := by
      unfold firstChain
      split_ifs <;> omega
    rw [e0, e1, chainsFrom_cons (2 * q) (by omega), chainsFrom_cons (2 * q + 1) (by omega),
      List.append_assoc]
  · rw [dif_neg h, dif_pos hq]
    have e0 : firstChain q = 12 + q := by unfold firstChain; rw [if_neg h]
    have e1 : firstChain (q + 1) = 12 + q + 1 := by unfold firstChain; split_ifs <;> omega
    rw [e0, e1, chainsFrom_cons (12 + q) (by omega)]

theorem firstChain_sixteen : firstChain 16 = 28 := by unfold firstChain; rw [if_neg (by omega)]

/-! ## The cost -/

/-- The hash steps of chain `k` above its disclosed position. -/
def stepsN (k : ℕ) : ℕ :=
  if h : k < 28 then 32 - RiscvUpperForest.ForestVerifier.pos index ⟨k, h⟩ else 0

theorem blockCycles_eq (q : ℕ) : blockCycles index q =
    if q < 12 then 6 + stepsN index (2 * q) + stepsN index (2 * q + 1)
    else if q < 16 then 4 + stepsN index (12 + q) else 0 := by
  unfold blockCycles stepsN
  split_ifs <;> first | rfl | omega

/-- The steps of chains `k` and later. -/
def stepsFrom (k : ℕ) : ℕ := if k < 28 then stepsN index k + stepsFrom (k + 1) else 0
termination_by 28 - k

theorem stepsFrom_eq : ∀ (n k : ℕ), 28 - k = n → stepsFrom index k =
    ∑ k' : Fin 28, if k ≤ k'.val then stepsN index k' else 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    rw [stepsFrom, if_neg (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro k' _
    rw [if_neg]
    have := k'.isLt
    omega
  | succ n ih =>
    intro k hk
    have hk28 : k < 28 := by omega
    rw [stepsFrom, if_pos hk28, ih (k + 1) (by omega)]
    have single : stepsN index k =
        ∑ k' : Fin 28, if k' = ⟨k, hk28⟩ then
          (if k ≤ k'.val then stepsN index k' else 0) else 0 := by
      rw [Finset.sum_ite_eq' Finset.univ (⟨k, hk28⟩ : Fin 28)
        (fun k' : Fin 28 => if k ≤ k'.val then stepsN index k' else 0),
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

/-- The 243 hash steps of an accepted index. -/
theorem stepsFrom_zero : stepsFrom index 0 = 243 := by
  rw [stepsFrom_eq index 28 0 rfl]
  simp only [Nat.zero_le, if_true]
  have hs := fixedPositions_sum index
  have e : ∑ k' : Fin 28, stepsN index k' =
      ∑ k' : Fin 28, (32 - (fixedPositions index k').val) := by
    apply Finset.sum_congr rfl
    intro k' _
    unfold stepsN
    rw [dif_pos k'.isLt]
  rw [e, hs]
  rfl

theorem stepsFrom_cons (k : ℕ) (hk : k < 28) :
    stepsFrom index k = stepsN index k + stepsFrom index (k + 1) := by
  rw [stepsFrom, if_pos hk]

/-- The cycles of blocks `q` and later. -/
def blocksCost (q : ℕ) : ℕ := if q < 16 then blockCycles index q + blocksCost (q + 1) else 0
termination_by 16 - q

/-- The fixed overhead of blocks `q` and later: six cycles per pair, four per single. -/
def overhead (q : ℕ) : ℕ := if q < 12 then 6 * (12 - q) + 16 else 4 * (16 - q)

theorem blocksCost_eq : ∀ (n q : ℕ), 16 - q = n → q ≤ 16 →
    blocksCost index q = overhead q + stepsFrom index (firstChain q) := by
  intro n
  induction n with
  | zero =>
    intro q hq _
    obtain rfl : q = 16 := by omega
    rw [blocksCost, if_neg (by omega), firstChain_sixteen, stepsFrom, if_neg (by omega)]
    rfl
  | succ n ih =>
    intro q hq hq'
    have hq16 : q < 16 := by omega
    rw [blocksCost, if_pos hq16, ih (q + 1) (by omega) (by omega), blockCycles_eq]
    by_cases h : q < 12
    · have e0 : firstChain q = 2 * q := by unfold firstChain; rw [if_pos h]
      have e1 : firstChain (q + 1) = 2 * q + 1 + 1 := by unfold firstChain; split_ifs <;> omega
      rw [e0, e1, if_pos h, stepsFrom_cons index (2 * q) (by omega),
        stepsFrom_cons index (2 * q + 1) (by omega)]
      unfold overhead
      split_ifs <;> omega
    · have e0 : firstChain q = 12 + q := by unfold firstChain; rw [if_neg h]
      have e1 : firstChain (q + 1) = 12 + q + 1 := by unfold firstChain; split_ifs <;> omega
      rw [e0, e1, if_neg h, if_pos hq16, stepsFrom_cons index (12 + q) (by omega)]
      unfold overhead
      split_ifs <;> omega

/-- The 16 blocks cost 331 cycles on every accepted index. -/
theorem blocksCost_zero : blocksCost index 0 = 331 := by
  rw [blocksCost_eq index 16 0 rfl (by norm_num), show firstChain 0 = 0 from rfl,
    stepsFrom_zero]
  rfl

/-! ## Refinement -/

/-- The code the machine sits on before block `q`: its prologue, or the root after the last. -/
def blockCodeAt (q : ℕ) : Code := if q < 16 then prologue q else root ++ decision

theorem nextCode_eq (q : ℕ) : nextCode q = blockCodeAt (q + 1) := rfl

/-- Blocks `q` and later refine the reader over their chains. -/
theorem blocksFrom_refines
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y 28 → Riscv.CodeAt u u.pc (root ++ decision) →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 5376)) c) :
    ∀ (n q : ℕ), 16 - q = n → q ≤ 16 →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      ChainsInv index payload pk s x (firstChain q) →
      (∃ junk, Riscv.CodeAt s s.pc (blockCodeAt q ++ junk)) →
      blocksCost index q + rest' ≤ fuel →
      Riscv.Refines fuel s
        (runNodes' index payload (chainsFrom (firstChain q)) x (192 * firstChain q) >>= K)
        (blocksCost index q + c) := by
  intro n
  induction n with
  | zero =>
    intro q hq _ s x fuel inv located bound
    obtain rfl : q = 16 := by omega
    rw [firstChain_sixteen] at inv ⊢
    rw [chainsFrom_nil 28 (by omega), blocksCost, if_neg (by omega), Nat.zero_add, runNodes',
      pure_bind]
    obtain ⟨junk, located⟩ := located
    unfold blockCodeAt at located
    rw [if_neg (by omega)] at located
    rw [blocksCost, if_neg (by omega), Nat.zero_add] at bound
    exact continuation s x inv located.append_left fuel bound
  | succ n ih =>
    intro q hq hq' s x fuel inv located bound
    have hq16 : q < 16 := by omega
    rw [chainsFrom_block q hq16, runNodes'_append, bind_assoc, blocksCost, if_pos hq16,
      Nat.add_assoc]
    rw [blocksCost, if_pos hq16] at bound
    unfold blockCodeAt at located
    rw [if_pos hq16] at located
    by_cases h : q < 12
    · have e0 : firstChain q = 2 * q := by unfold firstChain; rw [if_pos h]
      have e1 : firstChain (q + 1) = 2 * q + 2 := by unfold firstChain; split_ifs <;> omega
      rw [e0] at inv ⊢
      apply pair_refines index payload pk q h
        (fun r => runNodes' index payload (chainsFrom (firstChain (q + 1))) r.1 r.2 >>= K)
        (blocksCost index (q + 1) + c) (blocksCost index (q + 1) + rest') ?_ s x fuel inv located
        (by omega)
      intro u y inv' located' left hleft
      dsimp only
      rw [← e1] at inv' ⊢
      apply ih (q + 1) (by omega) (by omega) u y left inv' ?_ hleft
      unfold blockCodeAt
      rw [if_pos (by omega)]
      exact located'
    · have e0 : firstChain q = 12 + q := by unfold firstChain; rw [if_neg h]
      have e1 : firstChain (q + 1) = 12 + q + 1 := by unfold firstChain; split_ifs <;> omega
      rw [e0] at inv ⊢
      apply single_refines index payload pk q (by omega) hq16
        (fun r => runNodes' index payload (chainsFrom (firstChain (q + 1))) r.1 r.2 >>= K)
        (blocksCost index (q + 1) + c) (blocksCost index (q + 1) + rest') ?_ s x fuel inv located
        (by omega)
      intro u y inv' located' left hleft
      dsimp only
      rw [← e1] at inv' ⊢
      rw [nextCode_eq] at located'
      exact ih (q + 1) (by omega) (by omega) u y left inv' located' hleft

end OptimalOTS.Riscv2Program
