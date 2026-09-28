import Submissions.UpperRiscv.MixedFree
import Submissions.UpperRiscv.StagedVerifier

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

variable (index : RawIdx) (v : ℕ) (wire : List Bool) (pk : PublicKey) {a : ℕ}

def blockCodeAt (q : ℕ) : Code := if q < 16 then prologue q else root ++ decision

theorem nextCode_eq (q : Fin 16) : nextCode q = blockCodeAt (q.val+1) := by
  have h := q.isLt
  unfold nextCode blockCodeAt
  split_ifs <;> first | rfl | omega

theorem rootTail_eq (x : graph.Assignment) :
    rootTail index v (ofBits 56 (wire.drop 5328)) x = tailAfter index v wire x := rfl

/-- Complete trace refinement of the pairs and the root, including the hashes made before a
forbidden landing. -/
theorem stagedBlocks_refines (hv : v < 16) (hlen : 5328 ≤ wire.length) :
    ∀ (n q : ℕ), 16-q=n → q ≤ 16 →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      ChainsInv index v wire pk a s x (2*q+1) →
      (∃ junk, Riscv.CodeAt s s.pc (blockCodeAt q ++ junk)) →
      stagedCost index v n q ≤ fuel →
      Riscv.Refines fuel s
        (some <$> stagedBlocks index v (Payload.permute wire) pk a (ofBits 56 (wire.drop 5328))
          n q x (Payload.graphOff (2*q+1)))
        (stagedCost index v n q) := by
  intro n
  induction n with
  | zero =>
    intro q hq _ s x fuel inv located bound
    have hq16 : q=16 := by omega
    subst q
    obtain ⟨junk, located⟩ := located
    unfold blockCodeAt at located
    rw [if_neg (by omega)] at located
    simp only [stagedCost] at bound ⊢
    rw [stagedBlocks_some_zero, rootTail_eq]
    exact rootDecision_refines index v pk s _ fuel (final_root index v wire pk inv)
      located.append_left (by omega)
  | succ n ih =>
    intro q hq hq' s x fuel inv located bound
    have hq16 : q < 16 := by omega
    let Q : Fin 16 := ⟨q,hq16⟩
    rw [stagedBlocks_some_succ _ _ _ _ _ _ _ _ hq16]
    rw [stagedCost, dif_pos hq16] at bound ⊢
    unfold blockCodeAt at located
    rw [if_pos hq16] at located
    by_cases good : PairAllowed index.val q
    · simp only [if_pos good] at bound ⊢
      have spec : (runNodes' index v (Payload.permute wire) (entryNodes index v ⟨2*q+1, by omega⟩) x
            (Payload.graphOff (2*q+1)) >>= fun r =>
            runNodes' index v (Payload.permute wire)
              (tableNodes index v ⟨2*q+1, by omega⟩ ++ chainNodes ⟨2*q+2, by omega⟩) r.1 r.2 >>=
              fun r' => some <$> stagedBlocks index v (Payload.permute wire) pk a
                (ofBits 56 (wire.drop 5328)) n (q+1) r'.1 r'.2) =
          (runNodes' index v (Payload.permute wire)
            (entryNodes index v (leftChain Q) ++ tableNodes index v (leftChain Q) ++
              chainNodes (rightChain Q)) x (Payload.graphOff (leftChain Q)) >>= fun r =>
            some <$> stagedBlocks index v (Payload.permute wire) pk a (ofBits 56 (wire.drop 5328))
              n (q+1) r.1 r.2) := by
        rw [List.append_assoc, runNodes'_append, bind_assoc]
        rfl
      rw [spec]
      have e : Payload.graphOff (2*(q+1)+1) = Payload.graphOff (2*(Q.val+1)+1) := rfl
      apply pair_refines index v wire pk Q hv good
        (fun r => some <$> stagedBlocks index v (Payload.permute wire) pk a
          (ofBits 56 (wire.drop 5328)) n (q+1) r.1 r.2)
        (stagedCost index v n (q+1)) (stagedCost index v n (q+1)) hlen ?_
        s x fuel inv located bound
      intro u z invU locU left hleft
      apply ih (q+1) (by omega) (by omega) u z left invU ?_ hleft
      simpa only [nextCode_eq Q] using locU
    · simp only [if_neg good] at bound ⊢
      exact pair_bad_refines index v wire pk Q (by
        change ¬ (digit index.val (2*q)+coarseDigit index q ≤ pairCap q) at good
        dsimp only [Q]
        omega) hlen s x fuel inv located bound

end OptimalOTS.RiscvMixedProgram
