import Submissions.UpperRiscv.MixedPrepare
import Submissions.UpperRiscv.MixedCost

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

variable (index : RawIdx) (v : ℕ) (wire : List Bool) (pk : PublicKey) {a : ℕ}

def entryCursor (k : Fin 33) : ℕ := Payload.graphOff k + if expands k then chainBits k else 0
/-- Hash steps executed from the table: all but the entry hash. -/
def remaining (k : Fin 33) : ℕ := 32-RiscvUpperForest.ForestVerifier.pos index v k-earlyHash k

variable (a) in
structure Prepared (s : MachineState) (x : graph.Assignment) (k : Fin 33) : Prop where
  inv : HashInv index v wire pk a s x k (work k)
  ready : if expands k then HoldsAt s x k (RiscvUpperForest.ForestVerifier.pos index v k+1)
    else MemBits s (W (work k)) (ofBits (chainBits k) (wire.drop (wireOffset k)))
  tail1 : k.val = 1 → MemBits s (W tailAddr) (0 : BitVec 48)

theorem Prepared.frame {s t : MachineState} {x : graph.Assignment} {k : Fin 33}
    (prep : Prepared index v wire pk a s x k) (inv : HashInv index v wire pk a t x k (work k))
    (mem : t.mem=s.mem) : Prepared index v wire pk a t x k := by
  refine ⟨inv, ?_, fun h => memBits_of_mem_eq mem (prep.tail1 h)⟩
  have h := prep.ready
  split_ifs at *
  · exact holdsAt_frame mem h
  · exact memBits_of_mem_eq mem h

/-- Chain entry accounts for the first hash and redirect exactly when the chain expands. -/
theorem enter_refines (k : Fin 33) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : 5328 ≤ wire.length)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      Prepared index v wire pk a u z k → Riscv.CodeAt u u.pc tail →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,entryCursor k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (ctx : Ctx s index v pk a) (input : s.getReg .x10 = W (prevInput k))
    (len : s.getReg .x11 = W (chainBits k)) (payload : PayloadFrom s wire k)
    (done : Completed s x k) (tailInv : TailInv index v wire s x k)
    (located : Riscv.CodeAt s s.pc (enter k (prevInput k) ++ tail))
    (bound : 2+2*earlyHash k+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index v (Payload.permute wire) (entryNodes index v k) x (Payload.graphOff k) >>= K)
      (2+2*earlyHash k+c) := by
  rw [enter_parts, List.append_assoc] at located
  by_cases hn : expands k = true
  · rw [if_pos hn] at located
    simp only [↓reduceIte, entryNodes, hn, earlyHash, Nat.mul_one] at bound ⊢
    rw [show 2+2+c = 2+(1+(1+c)) by omega]
    apply move_refines index v wire pk k s x (([.ECALL] ++ redirectCode k) ++ tail)
      ctx input len payload done tailInv (by simpa only [List.append_assoc] using located)
      _ (1+(1+c)) fuel (by omega)
    intro u invU heldU tailU locatedU
    apply read_prefix_refines index v wire pk k (pos_le_of_expands index v k hn)
      (redirectCode k ++ tail) K (1+c) (1+rest) hlen
      ?_ u x (fuel-2) invU heldU
      (by simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using locatedU)
      (by omega)
    intro w z invW heldW locatedW left hleft
    apply redirect_refines index v wire pk k (valueAddr k) w z tail invW locatedW _ c left (by omega)
    intro y invY memY locatedY
    have readyY : Prepared index v wire pk a y z k := by
      refine ⟨invY, ?_, fun h1 => ?_⟩
      · rw [if_pos hn]
        exact holdsAt_frame memY heldW
      · exact invY.tail
    have h := continuation y z readyY locatedY (left-1) (by omega)
    simpa only [↓reduceIte, entryCursor, hn, if_true] using h
  · rw [if_neg hn, List.nil_append] at located
    simp only [Bool.false_eq_true, ↓reduceIte, entryNodes, hn, runNodes', pure_bind, earlyHash,
      Nat.mul_zero, Nat.add_zero] at bound ⊢
    apply move_refines index v wire pk k s x tail ctx input len payload done tailInv located _ c
      fuel (by omega)
    intro u invU heldU tailU locatedU
    have he : valueAddr k = work k := (work_value' k (by simpa using hn)).symm
    rw [he] at invU heldU
    have prep : Prepared index v wire pk a u x k := by
      refine ⟨invU, by rw [if_neg hn]; exact heldU, fun h1 => ?_⟩
      exact tailU
    have h := continuation u x prep locatedU (fuel-2) (by omega)
    simpa only [Bool.false_eq_true, ↓reduceIte, entryCursor, hn, if_false, Nat.add_zero] using h

/-- The top step of a chain that hashed. -/
theorem top_refines (k : Fin 33) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest cursor : ℕ)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index v wire pk a u z (k.val+1) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,cursor)) c)
    (hashed : RiscvUpperForest.ForestVerifier.pos index v k ≠ 32)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : HashInv index v wire pk a s x k (work k))
    (answer : MemBits s (W (outAddr k)) (lastAnswer x k))
    (located : Riscv.CodeAt s s.pc tail) (bound : rest ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index v (Payload.permute wire) [tp k] x cursor >>= K) c := by
  rw [top_run_eval index v _ k hashed, pure_bind]
  exact continuation s _ (HashInv.complete index v wire pk inv answer hashed) located fuel bound

/-- The table finishes whichever hashes were not already executed at entry, then the top. -/
theorem table_refines (k : Fin 33) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : 5328 ≤ wire.length)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index v wire pk a u z (k.val+1) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,Payload.graphOff k+chainBits k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (prep : Prepared index v wire pk a s x k)
    (located : Riscv.CodeAt s s.pc (List.replicate (remaining index v k) .ECALL ++ tail))
    (bound : remaining index v k+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index v (Payload.permute wire) (tableNodes index v k) x (entryCursor k) >>= K)
      (remaining index v k+c) := by
  set p := RiscvUpperForest.ForestVerifier.pos index v k with hp
  have hp32 : p ≤ 32 := pos_le index v k
  -- the levels above `t`, then the top
  have finish : ∀ t, p < t → t ≤ 32 → ∀ (u : MachineState) (z : graph.Assignment) (left : ℕ),
      HashInv index v wire pk a u z k (work k) → HoldsAt u z k t →
      Riscv.CodeAt u u.pc (List.replicate (32 - t) .ECALL ++ tail) → (32 - t) + rest ≤ left →
      Riscv.Refines left u
        (runNodes' index v (Payload.permute wire)
          ((List.range' t (32 - t)).flatMap (tripleN k) ++ [tp k]) z
          (Payload.graphOff k+chainBits k) >>= K) ((32 - t) + c) := by
    intro t hpt ht u z left invU heldU locU boundU
    rw [runNodes'_append, bind_assoc]
    apply steps_refines index v wire pk k tail
      (fun r => runNodes' index v (Payload.permute wire) [tp k] r.1 r.2 >>= K) c rest
      (Payload.graphOff k+chainBits k) ?_ (32 - t) t rfl ht hpt u z left invU heldU locU boundU
    intro w y invW answer locW left' hleft'
    exact top_refines index v wire pk k tail K c rest _ continuation (by omega) w y left' invW
      answer locW hleft'
  by_cases hn : expands k = true
  · have he : remaining index v k = 32-(p+1) := by
      simp only [↓reduceIte, remaining, earlyHash, hn]
      omega
    have hp31 := pos_le_of_expands index v k hn
    rw [he] at located bound ⊢
    simp only [↓reduceIte, tableNodes, entryCursor, hn, suffixNodes]
    have ready := prep.ready
    rw [if_pos hn] at ready
    exact finish (p+1) (by omega) (by omega) s x fuel prep.inv ready located bound
  · have hw : valueAddr k = work k := (work_value' k (by simpa using hn)).symm
    simp only [Bool.false_eq_true, ↓reduceIte, tableNodes, entryCursor, hn, Nat.add_zero]
    by_cases h32 : p = 32
    · -- a cap with digit zero reveals its top: no hash
      have he : remaining index v k = 0 := by
        simp only [remaining, earlyHash, hn, Bool.false_eq_true, ↓reduceIte]; omega
      rw [he] at located bound ⊢
      simp only [List.replicate_zero, List.nil_append, Nat.zero_add] at located bound ⊢
      have hcap : isCap k := by
        by_contra hc
        have e : p = topPos k - digitV index v k := posV_val index v k
        unfold topPos at e
        rw [if_neg hc] at e
        omega
      have hcapc : capChain k = true := (capChain_iff' k).mpr hcap
      obtain ⟨hslot, hwork⟩ := cap_value_slot' k hcapc
      rw [chainNodes_eq]
      obtain ⟨x', run, ftp, frame⟩ :=
        prefix_run index v (Payload.permute wire) k 32 (by omega) le_rfl x (Payload.graphOff k)
      rw [← List.cons_append, runNodes'_append, run, pure_bind,
        top_run_read index v _ k (by omega), pure_bind]
      have ht := topBits_cap hcap
      rw [show Payload.graphOff k + topBits k = Payload.graphOff k + chainBits k by rw [ht]]
      have inv := prep.inv
      have held := prep.ready
      rw [if_neg hn] at held
      set w := ofBits (graph.len (tp k).fin)
        (((Payload.permute wire).drop (Payload.graphOff k)).take (graph.len (tp k).fin)) with hwdef
      apply continuation s _ ?_ located fuel bound
      have lastEq : ∀ j, lastAnswer (Function.update x' (tp k).fin w) j = lastAnswer x' j :=
        fun j => lastAnswer_update_tp x' k j w
      refine ⟨inv.ctx, ?_, ?_, ?_, inv.payload, ?_, ?_⟩
      · rw [inv.input]; unfold prevInput; rw [if_neg (by omega), Nat.add_sub_cancel]
      · intro _; rw [Nat.add_sub_cancel]; exact inv.out
      · rw [inv.length, prevBits_succ']
      · intro j hj
        by_cases he : j = k
        · subst he
          intro i hi
          have hi' : i < chainBits j := by rw [← ht]; exact hi
          have hm := held i hi'
          rw [show slotAddr j = work j by rw [← hslot, hwork], hm]
          have hl : i < lenF (tp j).fin := by rw [lenF_fin]; exact hi
          unfold tops
          rw [Function.update_self]
          change _ = w.getLsbD i
          rw [hwdef]
          simp only [ofBits, BitVec.getLsbD_ofNat, testBit_foldr_bits,
            List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take, hl, hi',
            decide_true, Bool.true_and, if_true]
          rw [Payload.getElem?_permute_chain wire (by unfold Payload.valueBits; omega) j.isLt
            (by rw [(wireOff_eq' j).2]; exact hi'), (wireOff_eq' j).1]
        · have e1 : tops (Function.update x' (tp k).fin w) j = tops x' j :=
            tops_update_ne x' k j he w
          have e2 : tops x' j = tops x j := by unfold tops; rw [ftp j]
          rw [e1, e2]
          exact inv.done j (by have : j.val ≠ k.val := fun h => he (Fin.ext h); omega)
      · exact inv.tail
    · -- the value is read in place, then the levels above it
      have he : remaining index v k = (32-(p+1))+1 := by
        simp only [remaining, earlyHash, hn, Bool.false_eq_true, ↓reduceIte]; omega
      rw [he] at located bound ⊢
      rw [chain_split_first index v k (by omega), runNodes'_append, bind_assoc]
      rw [List.replicate_succ, List.cons_append] at located
      rw [show 32-(p+1)+1+c = 1+(32-(p+1)+c) by omega]
      have inv : HashInv index v wire pk a s x k (valueAddr k) := by rw [hw]; exact prep.inv
      have held : MemBits s (W (valueAddr k)) (ofBits (chainBits k) (wire.drop (wireOffset k))) := by
        rw [hw]; have h := prep.ready; rw [if_neg hn] at h; exact h
      apply read_prefix_refines index v wire pk k (by omega) (List.replicate (32-(p+1)) .ECALL ++ tail)
        (fun r => runNodes' index v (Payload.permute wire) (suffixNodes index v k) r.1 r.2 >>= K)
        (32-(p+1)+c) (32-(p+1)+rest) hlen ?_ s x fuel inv held located (by omega)
      intro u z invU heldU locatedU left hleft
      rw [hw] at invU
      unfold suffixNodes
      exact finish (p+1) (by omega) (by omega) u z left invU heldU locatedU hleft

end OptimalOTS.RiscvMixedProgram
