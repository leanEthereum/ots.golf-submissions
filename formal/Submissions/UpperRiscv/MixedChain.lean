import Submissions.UpperRiscv.MixedPrepare
import Submissions.UpperRiscv.MixedCost

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (wire : List Bool) (pk : PublicKey)

def entryNodes (k : Fin 32) : List Name := if expands k then readNodes index k else []
def tableNodes (k : Fin 32) : List Name := if expands k then suffixNodes index k else chainNodes k
def entryCursor (k : Fin 32) : ℕ := cursor k + if expands k then chainBits k else 0
def remaining (k : Fin 32) : ℕ := 32-RiscvUpperForest.ForestVerifier.pos index k-earlyHash k

theorem chain_entry_split (k : Fin 32) : chainNodes k = entryNodes index k ++ tableNodes index k := by
  unfold entryNodes tableNodes
  split_ifs
  · exact chain_split_first index k
  · rfl

structure Prepared (s : MachineState) (x : graph.Assignment) (k : Fin 32) : Prop where
  inv : HashInv index wire pk s x k (work k)
  ready : if expands k then HoldsAt s x k (RiscvUpperForest.ForestVerifier.pos index k+1)
    else MemBits s (W (work k)) (ofBits (chainBits k) (wire.drop (wireOffset k)))

/-- Chain entry accounts for the first hash and redirect exactly when the chain expands. -/
theorem enter_refines (k : Fin 32) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : wire.length = 5376)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      Prepared index wire pk u z k → Riscv.CodeAt u u.pc tail →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,entryCursor k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (ctx : Ctx s index pk) (input : s.getReg .x10 = W (prevInput k))
    (len : s.getReg .x11 = W (chainBits k)) (payload : PayloadFrom s wire k)
    (done : Completed s (tops x) k)
    (located : Riscv.CodeAt s s.pc (enter k (prevInput k) ++ tail))
    (bound : 2+2*earlyHash k+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (Payload.permute wire) (entryNodes index k) x (cursor k) >>= K)
      (2+2*earlyHash k+c) := by
  rw [enter_parts, List.append_assoc] at located
  by_cases hn : expands k = true
  · rw [if_pos hn] at located
    simp only [↓reduceIte, entryNodes, hn, earlyHash, Nat.mul_one] at bound ⊢
    rw [show 2+2+c = 2+(1+(1+c)) by omega]
    apply move_refines index wire pk k s x ([.ECALL,.ADDI .x10 .x12 8] ++ tail)
      ctx input len payload done located _ (1+(1+c)) fuel (by omega)
    intro u invU heldU locatedU
    apply read_prefix_refines index wire pk k ([Instr.ADDI .x10 .x12 8] ++ tail) K (1+c) (1+rest) hlen
      ?_ u x (fuel-2) invU heldU locatedU (by omega)
    intro v z invV heldV locatedV left hleft
    apply redirect_refines index wire pk k (wireSlot k) v z tail invV locatedV _ c left (by omega)
    intro w invW memW locatedW
    have readyW : Prepared index wire pk w z k := by
      refine ⟨(by rw [work_of_expands hn]; exact invW), ?_⟩
      rw [if_pos hn]
      exact holdsAt_frame memW heldV
    have h := continuation w z readyW locatedW (left-1) (by omega)
    simpa only [Bool.false_eq_true, ↓reduceIte, entryCursor, hn, if_true] using h
  · rw [if_neg hn, List.nil_append] at located
    simp only [Bool.false_eq_true, ↓reduceIte, entryNodes, hn, runNodes', pure_bind, earlyHash, Nat.mul_zero,
      Nat.add_zero] at bound ⊢
    apply move_refines index wire pk k s x tail ctx input len payload done located _ c fuel (by omega)
    intro u invU heldU locatedU
    have he : wireSlot k = work k := (work_of_not_expands hn).symm
    rw [he] at invU heldU
    have prep : Prepared index wire pk u x k := ⟨invU, by rw [if_neg hn]; exact heldU⟩
    have h := continuation u x prep locatedU (fuel-2) (by omega)
    simpa only [Bool.false_eq_true, ↓reduceIte, entryCursor, hn, if_false, Nat.add_zero] using h

/-- The table finishes whichever hashes were not already executed at entry. -/
theorem table_refines (k : Fin 32) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : wire.length = 5376)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index wire pk u z (k.val+1) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,cursor k+chainBits k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (prep : Prepared index wire pk s x k)
    (located : Riscv.CodeAt s s.pc (List.replicate (remaining index k) .ECALL ++ tail))
    (bound : remaining index k+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (Payload.permute wire) (tableNodes index k) x (entryCursor k) >>= K)
      (remaining index k+c) := by
  set p := RiscvUpperForest.ForestVerifier.pos index k with hp
  have hp32 : p < 32 := by have := pos_le index k; omega
  have finish : ∀ (u : MachineState) (z : graph.Assignment),
      HashInv index wire pk u z k (work k) → MemBits u (W (outAddr k)) (tops z k) →
      Riscv.CodeAt u u.pc tail → ∀ left, rest ≤ left →
      Riscv.Refines left u (K (z,cursor k+chainBits k)) c := by
    intro u z invU topU locatedU left hleft
    exact continuation u z (HashInv.complete index wire pk invU topU) locatedU left hleft
  by_cases hn : expands k = true
  · have he : remaining index k = 32-(p+1) := by
      simp only [↓reduceIte, remaining, earlyHash, hn]
      omega
    rw [he] at located bound ⊢
    simp only [↓reduceIte, tableNodes, entryCursor, hn, suffixNodes]
    have ready := prep.ready
    rw [if_pos hn] at ready
    exact steps_refines index wire pk k tail K c rest (cursor k+chainBits k) finish
      (32-(p+1)) (p+1) rfl (by omega) (by omega) s x fuel prep.inv ready located bound
  · have he : remaining index k = 32-p := by simp only [Bool.false_eq_true, ↓reduceIte, remaining, earlyHash, hn, Nat.sub_zero]; rfl
    have hw : wireSlot k = work k := (work_of_not_expands hn).symm
    rw [he] at located bound ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, tableNodes, entryCursor, hn, Nat.add_zero]
    rw [chain_split_first index k, runNodes'_append, bind_assoc]
    have hcount : 32-p = (32-(p+1))+1 := by omega
    rw [hcount] at located bound ⊢
    rw [List.replicate_succ, List.cons_append] at located
    rw [show 32-(p+1)+1+c = 1+(32-(p+1)+c) by omega]
    have inv : HashInv index wire pk s x k (wireSlot k) := by rw [hw]; exact prep.inv
    have held : MemBits s (W (wireSlot k)) (ofBits (chainBits k) (wire.drop (wireOffset k))) := by
      rw [hw]; have h := prep.ready; rw [if_neg hn] at h; exact h
    apply read_prefix_refines index wire pk k (List.replicate (32-(p+1)) .ECALL ++ tail)
      (fun r => runNodes' index (Payload.permute wire) (suffixNodes index k) r.1 r.2 >>= K)
      (32-(p+1)+c) (32-(p+1)+rest) hlen ?_ s x fuel inv held located (by omega)
    intro u z invU heldU locatedU left hleft
    rw [hw] at invU
    exact steps_refines index wire pk k tail K c rest (cursor k+chainBits k) finish
      (32-(p+1)) (p+1) rfl (by omega) (by omega) u z left invU heldU locatedU hleft

end OptimalOTS.RiscvMixedProgram
