import Submissions.UpperRiscvHint.MixedPair
import Submissions.UpperRiscvHint.StagedVerifier

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (wire : List Bool) (pk : PublicKey)

def blockCodeAt (q : ℕ) : Code := if q < 16 then prologue q else root ++ decision

theorem nextCode_eq (q : Fin 16) : nextCode q = blockCodeAt (q.val+1) := by
  have h := q.isLt
  unfold nextCode blockCodeAt
  split_ifs <;> first | rfl | omega

/-- Trace refinement of the staged run: a forbidden landing rejects before any hash of its pair,
and a completed run ends in the machine's decision on the root. -/
theorem stagedRun_refines
    (short : wire.length = honestViewBits) :
    ∀ (n q : ℕ), 16-q=n → q ≤ 16 →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      ChainsInv index wire pk s x (2*q) →
      (∃ junk, Riscv.CodeAt s s.pc (blockCodeAt q ++ junk)) →
      stagedCost index n q ≤ fuel →
      Riscv.Refines fuel s
        ((fun o => o.elim (some false) (decisionOutcome · pk)) <$>
          stagedRun index (viewPayload wire) n q x (cursor (2*q)))
        (stagedCost index n q) := by
  intro n
  induction n with
  | zero =>
    intro q hq _ s x fuel inv located bound
    have hq16 : q=16 := by omega
    subst q
    obtain ⟨junk, located⟩ := located
    unfold blockCodeAt at located
    rw [if_neg (by omega)] at located
    simp only [stagedCost, stagedRun, map_bind, map_pure, Option.elim] at bound ⊢
    exact rootDecision_refines index (viewPayload wire) wire pk s x fuel
      (final_root index wire pk short inv) located.append_left (by omega)
  | succ n ih =>
    intro q hq hq' s x fuel inv located bound
    have hq16 : q < 16 := by omega
    let Q : Fin 16 := ⟨q,hq16⟩
    rw [stagedRun, dif_pos hq16]
    rw [stagedCost, dif_pos hq16] at bound ⊢
    unfold blockCodeAt at located
    rw [if_pos hq16] at located
    by_cases good : PairAllowed index.val q
    · simp only [if_pos good, map_bind] at bound ⊢
      apply pair_refines index wire pk Q good short
        (fun r => (fun o => o.elim (some false) (decisionOutcome · pk)) <$>
          stagedRun index (viewPayload wire) n (q+1) r.1 r.2)
        (stagedCost index n (q+1)) (stagedCost index n (q+1)) ?_
        s x fuel inv located bound
      intro u z invU locU left hleft
      apply ih (q+1) (by omega) (by omega) u z left invU ?_ hleft
      simpa only [nextCode_eq Q] using locU
    · simp only [if_neg good, map_pure, Option.elim] at bound ⊢
      exact pair_bad_refines index wire pk Q (by
        change ¬ (digit index.val (2*q)+coarseDigit index q ≤ pairCap q) at good
        dsimp only [Q]
        omega) short s x fuel inv located bound

end OptimalOTS.RiscvMixedProgram
