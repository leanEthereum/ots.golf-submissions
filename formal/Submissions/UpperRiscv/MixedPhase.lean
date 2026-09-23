import Submissions.UpperRiscv.MixedPair

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (wire : List Bool) (pk : PublicKey)

def chainsFrom (k : ℕ) : List Name :=
  if h : k < 32 then chainNodes ⟨k,h⟩ ++ chainsFrom (k+1) else []
termination_by 32-k

set_option maxRecDepth 100000 in
theorem chainsFrom_zero : (List.finRange 32).flatMap chainNodes = chainsFrom 0 := by decide +kernel

theorem chainsFrom_pair (q : Fin 16) : chainsFrom (2*q.val) =
    (chainNodes (leftChain q) ++ chainNodes (rightChain q)) ++ chainsFrom (2*(q.val+1)) := by
  have hq := q.isLt
  rw [chainsFrom, dif_pos (by omega), chainsFrom, dif_pos (by omega)]
  have h : 2*q.val+1+1=2*(q.val+1) := by omega
  rw [h, List.append_assoc]
  rfl

def blockCodeAt (q : ℕ) : Code := if q < 16 then prologue q else root ++ decision

theorem nextCode_eq (q : Fin 16) : nextCode q = blockCodeAt (q.val+1) := by
  have h := q.isLt
  unfold nextCode blockCodeAt
  split_ifs <;> first | rfl | omega

def blocksCost (q : ℕ) : ℕ := ∑ j : Fin 16, if q ≤ j.val then pairCost index j else 0

theorem blocksCost_end : blocksCost index 16 = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (by have := j.isLt; omega)]

theorem blocksCost_step (q : Fin 16) :
    blocksCost index q = pairCost index q + blocksCost index (q.val+1) := by
  have single : pairCost index q = ∑ j : Fin 16, if j=q then pairCost index j else 0 := by simp
  rw [single, blocksCost, blocksCost, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : j=q
  · subst j; simp
  · have hne : j.val ≠ q.val := fun h => he (Fin.ext h)
    rw [if_neg he]
    split_ifs <;> omega

theorem sum_pairs (f : Fin 32 → ℕ) :
    ∑ q : Fin 16, (f (leftChain q)+f (rightChain q)) = ∑ k : Fin 32, f k := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero, leftChain, rightChain]
  simp only [Nat.add_assoc]
  rfl

theorem blocksCost_zero : blocksCost index 0 = 299 := by
  have overhead : ∑ q : Fin 16,
      ((lengthSetup q).length+6+earlyHash (leftChain q)+earlyHash (rightChain q)) = 110 := by
    decide +kernel
  have hashes : (∑ q : Fin 16, (32-RiscvUpperForest.ForestVerifier.pos index (leftChain q))) +
      (∑ q : Fin 16, (32-RiscvUpperForest.ForestVerifier.pos index (rightChain q))) = 189 := by
    rw [← Finset.sum_add_distrib, sum_pairs (fun k => 32-RiscvUpperForest.ForestVerifier.pos index k), all_chain_hashes]
  simp only [Finset.sum_add_distrib] at overhead
  simp only [blocksCost, Nat.zero_le, if_true, pairCost_eq, Finset.sum_add_distrib]
  omega

/-- All sixteen pairs refine all thirty-two chains. -/
theorem blocks_refines
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : wire.length = 5376)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index wire pk u z 32 → Riscv.CodeAt u u.pc (root ++ decision) →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,5376)) c) :
    ∀ (n q : ℕ), 16-q=n → q ≤ 16 →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      ChainsInv index wire pk s x (2*q) →
      (∃ junk, Riscv.CodeAt s s.pc (blockCodeAt q ++ junk)) →
      blocksCost index q+rest ≤ fuel →
      Riscv.Refines fuel s
        (runNodes' index (Payload.permute wire) (chainsFrom (2*q)) x (cursor (2*q)) >>= K)
        (blocksCost index q+c) := by
  intro n
  induction n with
  | zero =>
    intro q hq _ s x fuel inv located bound
    have hq16 : q=16 := by omega
    subst q
    rw [blocksCost_end, Nat.zero_add] at bound ⊢
    rw [chainsFrom, dif_neg (by omega), runNodes', pure_bind]
    obtain ⟨junk, located⟩ := located
    unfold blockCodeAt at located
    rw [if_neg (by omega)] at located
    exact continuation s x inv located.append_left fuel bound
  | succ n ih =>
    intro q hq hq' s x fuel inv located bound
    have hq16 : q < 16 := by omega
    let Q : Fin 16 := ⟨q,hq16⟩
    rw [chainsFrom_pair Q, runNodes'_append, bind_assoc, blocksCost_step index Q, Nat.add_assoc]
    rw [blocksCost_step index Q] at bound
    change pairCost index Q+blocksCost index (q+1)+rest ≤ fuel at bound
    unfold blockCodeAt at located
    rw [if_pos hq16] at located
    apply pair_refines index wire pk Q
      (fun r => runNodes' index (Payload.permute wire) (chainsFrom (2*(q+1))) r.1 r.2 >>= K)
      (blocksCost index (q+1)+c) (blocksCost index (q+1)+rest) hlen ?_
      s x fuel inv located (by omega)
    intro u z invU locU left hleft
    dsimp only
    apply ih (q+1) (by omega) (by omega) u z left invU ?_ hleft
    simpa only [nextCode_eq Q] using locU

end OptimalOTS.RiscvMixedProgram
