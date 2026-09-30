import Submissions.UpperRiscvHint.StagedVerifier
import Submissions.UpperRiscvHint.MixedRoot

noncomputable section
open scoped Classical
namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph

/-- Full recoded chains, followed by the delayed checksum and, only if it passes, the root. -/
def checkedRun (index : ChainIndex) (payload : List Bool) (pk : PublicKey) (ok : Bool) :
    (n q : ℕ) → graph.Assignment → ℕ → OracleComp Spec (Option Bool)
  | 0, _, x, cursor => if ok then do
      let r ← runNodes' index payload [rc,rh] x cursor
      pure (decisionOutcome ((r.1 rh.fin).setWidth 128) pk)
    else pure none
  | n+1, q, x, cursor => if hq : q < 16 then do
      let r ← runNodes' index payload
        (chainNodes ⟨2*q+1,by omega⟩ ++ chainNodes ⟨2*q+2,by omega⟩) x cursor
      checkedRun index payload pk ok n (q+1) r.1 r.2
    else pure none

def checkedFreeDecision (index : ChainIndex) (payload : List Bool) (pk : PublicKey) (ok : Bool) :
    OracleComp Spec (Option Bool) := do
  let r ← runNodes' index payload (chainNodes 0) (fun _ => 0) 0
  checkedRun index payload pk ok 16 0 r.1 r.2

/-- The canonical verifier's decision. -/
def freeDecision (index : ChainIndex) (payload : List Bool) (pk : PublicKey) :
    OracleComp Spec (Option Bool) :=
  (fun o => o.elim (some false) (decisionOutcome · pk)) <$> freeRun index payload (fun _ => 0)

theorem checkedRun_true (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (hq : q+n ≤ 16) (x : graph.Assignment) (cursor : ℕ) :
    checkedRun index payload pk true n q x cursor =
      (fun o => o.elim (some false) (decisionOutcome · pk)) <$>
        stagedRun index payload n q x cursor := by
  induction n generalizing q x cursor with
  | zero => simp only [checkedRun,stagedRun,if_true,map_bind,map_pure,Option.elim]
  | succ n ih =>
    rw [checkedRun,dif_pos (show q<16 by omega),stagedRun,
      dif_pos (show q<16 by omega),if_pos (pairAllowed_all _ _),map_bind]
    exact bind_congr fun r => ih (q+1) (by omega) r.1 r.2

theorem checkedFreeDecision_true (index : ChainIndex) (payload : List Bool) (pk : PublicKey) :
    checkedFreeDecision index payload pk true = freeDecision index payload pk := by
  simp only [checkedFreeDecision,freeDecision,freeRun,map_bind,
    checkedRun_true index payload pk 16 0 (by omega)]

theorem checkedRun_false (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    ∀ o ∈ support (checkedRun index payload pk false n q x cursor), o = none := by
  induction n generalizing q x cursor with
  | zero => simp [checkedRun]
  | succ n ih =>
    rw [checkedRun]
    split_ifs
    · intro o ho
      rw [mem_support_bind_iff] at ho
      obtain ⟨r,-,hr⟩ := ho
      exact ih _ _ _ o hr
    · simp

theorem checkedFreeDecision_false (index : ChainIndex) (payload : List Bool) (pk : PublicKey) :
    some true ∉ support (checkedFreeDecision index payload pk false) := by
  intro h
  rw [checkedFreeDecision,mem_support_bind_iff] at h
  obtain ⟨r,-,hr⟩ := h
  have := checkedRun_false index payload pk 16 0 r.1 r.2 (some true) hr
  contradiction

theorem checkedRun_deterministic (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (ok : Bool) (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    Deterministic (checkedRun index payload pk ok n q x cursor) := by
  induction n generalizing q x cursor with
  | zero =>
    rw [checkedRun]
    split_ifs
    · exact Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
        fun _ => Deterministic.of_pure _
    · exact Deterministic.of_pure _
  | succ n ih =>
    rw [checkedRun]
    split_ifs
    · exact Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
        fun r => ih _ r.1 r.2
    · exact Deterministic.of_pure _

theorem checkedFreeDecision_deterministic (index : ChainIndex) (payload : List Bool)
    (pk : PublicKey) (ok : Bool) : Deterministic (checkedFreeDecision index payload pk ok) :=
  Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
    fun r => checkedRun_deterministic _ _ _ _ _ _ r.1 r.2

end OptimalOTS.RiscvMixedProgram
