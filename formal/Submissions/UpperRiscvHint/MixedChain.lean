import Submissions.UpperRiscvHint.MixedChainStart
import Submissions.UpperRiscvHint.MixedChainFrame
import Submissions.UpperRiscvHint.MixedCode

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name OracleComp
open Riscv2Program

/-- The pointer move from chain `2q + 1` to chain `k = 2q + 2` preserves every value and slice. -/
theorem move_refines (index : RawIdx) (wire : List Bool) (pk : PublicKey)
    (q : Fin 16) (k : Chain) (hk : k.val = 2*q.val+2)
    (s : MachineState) (x : graph.Assignment) (tail : Code)
    (ctx : Ctx s index wire pk) (input : s.getReg .x10 = W (prevInput k))
    (out : s.getReg .x12 = W (outAddr (2*q.val+1)))
    (len : s.getReg .x11 = W (chainBits k)) (payload : PayloadFrom s wire k)
    (done : Completed s (tops x) k)
    (located : Riscv.CodeAt s s.pc (enter k (prevInput k) ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : 2 ≤ fuel)
    (continuation : ∀ u, HashInv index wire pk u x k (work k) →
      MemBits u (W (work k)) (ofBits (chainBits k) (wire.drop (wireOffset k))) →
      Riscv.CodeAt u u.pc tail → Riscv.Refines (fuel-2) u Q c) :
    Riscv.Refines fuel s Q (2+c) := by
  have E := enter_effect s k input
  have ready := enter_ready s k (prevInput k)
  let u := (enter k (prevInput k)).foldl execInstrBr s
  have prev : prevInput k = work (2*q.val+1) := by
    unfold prevInput; rw [if_neg (by omega)]; congr 1; omega
  have uctx : Ctx u index wire pk :=
    ctx.enter q (input.trans (by rw [prev])) out (E.input.trans (by rw [hk]))
      (E.out.trans (by rw [hk])) E.regs E.mem E.code
  have urange : 32 ≤ work k ∧ work k+24 ≤ 0x78000000 := by
    have h := wireOffset_contained k
    unfold honestViewBits at h
    rw [work_eq_view]; omega
  have inv : HashInv index wire pk u x k (work k) := by
    refine ⟨uctx, E.input, urange, ?_, E.out, ?_, ?_⟩
    · rw [E.regs .x11 (by decide) (by decide)]; exact len
    · intro j hj; exact memBits_of_mem_eq E.mem (payload j (by omega))
    · intro j hj; exact memBits_of_mem_eq E.mem (done j hj)
  have held := memBits_of_mem_eq E.mem (payload k le_rfl)
  have loc : Riscv.CodeAt u u.pc tail := by
    rw [E.pc]
    exact located.append_right.code_eq E.code
  rw [show fuel = (enter k (prevInput k)).length+(fuel-2) by change fuel=2+(fuel-2); omega]
  exact Riscv.Refines.linear _ located.append_left ready (continuation u inv held loc)

end OptimalOTS.RiscvMixedProgram

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

/-- The hashes of chain `k`: its digit for the free chain and a cap, its digit plus one for a
normal chain. -/
def remaining (index : RawIdx) (k : Chain) : ℕ := 32-firstAt index k

theorem steps_eq_digit (index : RawIdx) (k : Chain) :
    remaining index k = chainDigit index.val k + 1 - if k.val < 13 ∨ 31 ≤ k.val then 1 else 0 := by
  have h := chainDigit_lt_32 index.val k
  unfold remaining firstAt firstEval
  rw [fixedPositions_val]
  split_ifs <;> omega

theorem lead_pair (q : ℕ) (j : ℕ) (hj : j < 2) :
    (if 2*q+1+j < 13 ∨ 31 ≤ 2*q+1+j then 1 else 0) = lead q := by
  unfold lead; split_ifs <;> omega

theorem fineDigit_lt (index : RawIdx) (q : ℕ) (hq : q < 16) :
    digit index.val (2*q) < 2^fineWidth q := by
  have h := digit_lt index.val (2*q)
  have he : wid (2*q) = fineWidth q := by
    simp [wid, fineWidth, show 2*q < 32 by omega]
  rw [he] at h; exact h

theorem coarseDigit_lt_copies (index : RawIdx) (q : ℕ) (hq : q < 16) :
    coarseDigit index q < copies q := by
  have h := digit_lt index.val (2*q+1)
  have he : 2^wid (2*q+1) = copies q := by
    simp [wid, copies, show 2*q+1 < 32 by omega]
  rw [he] at h; exact h

/-- The packed subtraction selects the coarse copy and the fine table entry, one row later for a
cap pair. -/
theorem pair_landing (index : RawIdx) (q : ℕ) (hq : q < 16) :
    landing0 q+4*lead q-dispatch index q = copyStart q (coarseDigit index q) +
      4*(2^fineWidth q-1-digit index.val (2*q)+lead q) := by
  have hc := coarseDigit_lt_copies index q hq
  have hf := fineDigit_lt index q hq
  have e : copyStart q 0 = copyStart q (coarseDigit index q)+1024*coarseDigit index q := by
    unfold copyStart
    omega
  unfold landing0 dispatch
  rw [e]
  omega

end OptimalOTS.RiscvMixedProgram

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (wire : List Bool) (pk : PublicKey)

/-- A chain about to hash its value in place. -/
structure Prepared (s : MachineState) (x : graph.Assignment) (k : Chain) : Prop where
  inv : HashInv index wire pk s x k (work k)
  ready : MemBits s (W (work k)) (ofBits (chainBits k) (wire.drop (wireOffset k)))

/-- A fully hidden cap or free chain: its view value is its top, and no hash runs. -/
theorem hidden_refines (k : Chain) (hidden : 32 ≤ firstAt index k)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c : ℕ)
    (continuation : ∀ z : graph.Assignment, ChainsInv index wire pk s z (k.val+1) →
      Riscv.Refines fuel s (K (z,cursor k+chainBits k)) c)
    (prep : Prepared index wire pk s x k) :
    Riscv.Refines fuel s
      (runNodes' index (viewPayload wire) (chainNodes k) x (cursor k) >>= K) c := by
  have cap : k.val < 13 ∨ 31 ≤ k.val := by
    by_contra h
    have : firstAt index k ≤ 31 := by
      unfold firstAt firstEval; rw [if_neg h]; exact pos_le index k
    omega
  have hb : topBits k = chainBits k := topBits_of_cap cap
  obtain ⟨x', run, frame⟩ := prefix_run index (viewPayload wire) k 32 hidden x (cursor k)
  rw [chain_split_hidden, runNodes'_append, run, pure_bind,
    top_run_read index (viewPayload wire) k hidden, pure_bind]
  have hc : cursor k + topBits k = cursor k + chainBits k := by rw [hb]
  rw [hc]
  apply continuation
  refine ⟨prep.inv.ctx, ?_, ?_, ?_, prep.inv.payload, ?_⟩
  · rw [prep.inv.input]
    unfold prevInput
    rw [if_neg (by omega), Nat.add_sub_cancel]
  · intro _
    rw [Nat.add_sub_cancel]; exact prep.inv.out
  · rw [prep.inv.length]
    congr 1
  · intro j hj
    by_cases he : j = k
    · subst j
      rw [tops_update_top]
      apply (memBits_cast _ _ _ _).mpr
      rw [ofBits_take]
      have hw : graph.len (top k).fin = chainBits k := by rw [graph_len_fin]; exact hb
      have e : work k = topAddr k := by
        rw [work_eq' k]
        unfold topAddr
        rw [topOff_cap cap]
      have key : ∀ n, n = chainBits k →
          MemBits s (W (topAddr k)) (ofBits n ((viewPayload wire).drop (cursor k))) := by
        intro n hn
        subst hn
        rw [viewPayload_read wire k, ← e]
        exact prep.ready
      exact key _ hw
    · rw [tops_update_top_other _ _ _ he, frame]
      exact prep.inv.done j (by have hne : j.val ≠ k.val := fun h => he (Fin.ext h); omega)

/-- The table row runs every hash of the chain, the first on its view value, then commits the
top. -/
theorem table_refines (k : Chain) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ) (P : Word)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index wire pk u z (k.val+1) → Riscv.CodeAt u u.pc tail → u.pc = P →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,cursor k+chainBits k)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (prep : Prepared index wire pk s x k)
    (located : Riscv.CodeAt s s.pc (List.replicate (remaining index k) .ECALL ++ tail))
    (hP : s.pc + W (4 * remaining index k) = P)
    (bound : remaining index k+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (viewPayload wire) (chainNodes k) x (cursor k) >>= K)
      (remaining index k+c) := by
  set p := firstAt index k with hp
  by_cases h32 : 32 ≤ p
  · have hr : remaining index k = 0 := by unfold remaining; omega
    rw [hr] at located bound hP ⊢
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add] at located bound ⊢
    have hpc : s.pc = P := by simpa using hP
    exact hidden_refines index wire pk k h32 s x fuel K c
      (fun z inv => continuation s z inv located hpc fuel bound) prep
  have hp32 : p < 32 := by omega
  have finish : ∀ (u : MachineState) (z : graph.Assignment),
      HashInv index wire pk u z k (work k) → MemBits u (W (outAddr k)) (lastOut z k) →
      Riscv.CodeAt u u.pc tail → u.pc = P → ∀ left, rest ≤ left →
      Riscv.Refines left u
        (runNodes' index (viewPayload wire) [top k] z (cursor k+chainBits k) >>= K) c := by
    intro u z invU lastU locatedU upc left hleft
    rw [top_run_eval index (viewPayload wire) k hp32, pure_bind]
    apply continuation u _ _ locatedU upc left hleft
    refine HashInv.complete index wire pk ⟨invU.ctx, invU.input, invU.inputRange, invU.length,
      invU.out, invU.payload, ?_⟩ ?_
    · intro j hj
      rw [tops_update_top_other _ _ _ (by intro he; subst j; omega)]
      exact invU.done j hj
    · rw [tops_update_top]
      apply (memBits_cast _ _ _ _).mpr
      apply (memBits_cast _ _ _ _).mpr
      exact top_of_answer k lastU
  have he : remaining index k = (32-(p+1))+1 := by unfold remaining; omega
  rw [he] at located bound hP ⊢
  rw [chain_split_first index k hp32, runNodes'_append, runNodes'_append, bind_assoc, bind_assoc]
  rw [List.replicate_succ, List.cons_append] at located
  rw [show 32-(p+1)+1+c = 1+(32-(p+1)+c) by omega]
  apply read_prefix_refines index wire pk k hp32 (List.replicate (32-(p+1)) .ECALL ++ tail)
    (fun r => runNodes' index (viewPayload wire) (suffixNodes index k) r.1 r.2 >>= fun r' =>
      runNodes' index (viewPayload wire) [top k] r'.1 r'.2 >>= K)
    (32-(p+1)+c) (32-(p+1)+rest) (s.pc + W 4) ?_ s x fuel prep.inv prep.ready located rfl
    (by omega)
  intro u z invU heldU locatedU upc left hleft
  refine steps_refines index wire pk k tail
    (fun r => runNodes' index (viewPayload wire) [top k] r.1 r.2 >>= K) c rest
    (cursor k+chainBits k) P finish
    (32-(p+1)) (p+1) rfl (by omega) (by omega) u z left invU heldU locatedU ?_ hleft
  rw [upc, BitVec.add_assoc, W_add, ← hP]
  congr 2
  omega

end OptimalOTS.RiscvMixedProgram
