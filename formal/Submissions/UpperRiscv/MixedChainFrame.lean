import Submissions.UpperRiscv.MixedChainStart

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

variable (index : RawIdx) (v : ℕ) (wire : List Bool) (pk : PublicKey) {a : ℕ}

/-- Hash-input width in `x11` at the boundary before chain `k`: the previous chain's width. -/
def prevBits (k : ℕ) : ℕ := if k = 0 then 144 else 8 * chainBytes (k-1)

theorem prevBits_succ' : ∀ k : Fin 33, prevBits (k.val+1) = chainBits k := by decide +kernel

variable (a) in
/-- State at a boundary between complete chains. -/
structure ChainsInv (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop where
  ctx : Ctx s index v pk a
  input : s.getReg .x10 = W (prevInput k)
  out : 1 ≤ k → s.getReg .x12 = W (outAddr (k-1))
  length : s.getReg .x11 = W (prevBits k)
  payload : PayloadFrom s wire k
  done : Completed s x k
  tail : TailInv index v wire s x k

/-- The assignment after a chain's top step. -/
def setTop (x : graph.Assignment) (k : Fin 33) (u : BitVec (topBits k)) : graph.Assignment :=
  Function.update x (tp k).fin (u.cast (graph_len_fin (tp k)).symm)

theorem Completed.addTop {s : MachineState} {x : graph.Assignment} {k : Fin 33}
    (done : Completed s x k) (u : BitVec (topBits k)) (hu : MemBits s (W (slotAddr k)) u) :
    Completed s (setTop x k u) (k.val+1) := by
  intro j hj
  by_cases he : j = k
  · subst he
    rw [setTop, tops_update_self]
    exact hu
  · rw [setTop, tops_update_ne x k j he]
    exact done j (by have : j.val ≠ k.val := fun h => he (Fin.ext h); omega)

theorem tailAfter_setTop (x : graph.Assignment) (k : Fin 33) (u : BitVec (topBits k)) :
    tailAfter index v wire (setTop x k u) = tailAfter index v wire x := by
  unfold tailAfter setTop
  rw [lastAnswer_update_tp]

/-- A chain that hashed completes with the root slot of its last answer. -/
theorem HashInv.complete {s : MachineState} {x : graph.Assignment} {k : Fin 33}
    (inv : HashInv index v wire pk a s x k (work k))
    (answer : MemBits s (W (outAddr k)) (lastAnswer x k))
    (hashed : RiscvUpperForest.ForestVerifier.pos index v k ≠ 32) :
    ChainsInv index v wire pk a s (setTop x k (topSlice k (lastAnswer x k))) (k.val+1) := by
  refine ⟨inv.ctx, ?_, ?_, ?_, inv.payload, ?_, ?_⟩
  · rw [inv.input]
    unfold prevInput
    rw [if_neg (by omega), Nat.add_sub_cancel]
  · intro _
    rw [Nat.add_sub_cancel]; exact inv.out
  · rw [inv.length, prevBits_succ']
  · exact inv.done.addTop _ (topSlice_of_answer s k _ answer)
  · unfold TailInv
    by_cases h1 : k.val = 1
    · have hk : k = 1 := Fin.ext h1
      subst hk
      rw [if_neg (by omega), tailAfter_setTop]
      unfold tailAfter
      rw [if_neg hashed]
      exact tail_of_answer answer
    · have h := inv.tail h1
      unfold TailInv at h
      rw [tailAfter_setTop]
      by_cases h0 : k.val = 0
      · rw [if_pos (by omega)]
        rw [if_pos (by omega)] at h
        exact h
      · rw [if_neg (by omega)]
        rw [if_neg (by omega)] at h
        exact h

/-- After the last chain `x10` is its working address; the region and the six bytes past it
are the root input. -/
theorem final_root {s : MachineState} {x : graph.Assignment}
    (inv : ChainsInv index v wire pk a s x 33) :
    RootInv index v pk a s (tailAfter index v wire x ++ rootRegion (tops x)) := by
  refine ⟨inv.ctx, ?_, inv.out (by decide), ?_⟩
  · rw [inv.input]; rfl
  · have region := memBits_region s (tops x) (fun k => inv.done k k.isLt)
    have tail := inv.tail
    unfold TailInv at tail
    rw [if_neg (by decide)] at tail
    apply memBits_append (by decide) region
    have e : W regionAddr + BitVec.ofNat 64 (Name.rootBits / 8) = W tailAddr := by decide
    rw [e]
    exact tail

end OptimalOTS.RiscvMixedProgram
