import Submissions.UpperRiscv.ForestVerifierProof

/-!
# The sequential reader, node by node

`runNodes'` is the specification's sequential reader also returning its cursor. This file
states the reader's step at each chain node: a chain's source and its levels below the disclosed
position are pure zeros, the disclosed input reads the next 192 payload bits, and the levels from
the disclosed position on hash.
-/

open OracleComp
noncomputable section
open scoped Classical

namespace OptimalOTS.RiscvUpperForest.ForestVerifier

open OptimalOTS.Dag
open Forest Forest.Name

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (payload : List Bool)

/-- The sequential reader, also returning its final cursor. -/
def runNodes' : List Name → graph.Assignment → ℕ →
    OracleComp Spec (graph.Assignment × ℕ)
  | [], x, cursor => pure (x, cursor)
  | n :: ns, x, cursor => cursorStep index payload x cursor n >>= fun r => runNodes' ns r.1 r.2

theorem runNodes_eq_fst (nodes : List Name) (x : graph.Assignment) (cursor : ℕ) :
    runNodes index payload nodes x cursor = Prod.fst <$> runNodes' index payload nodes x cursor := by
  induction nodes generalizing x cursor with
  | nil => simp [runNodes, runNodes']
  | cons n ns ih =>
    rw [runNodes, runNodes', map_bind]
    congr 1
    funext r
    rcases r with ⟨y, next⟩
    exact ih y next

theorem runNodes'_append (l₁ l₂ : List Name) (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index payload (l₁ ++ l₂) x cursor =
      runNodes' index payload l₁ x cursor >>= fun r => runNodes' index payload l₂ r.1 r.2 := by
  induction l₁ generalizing x cursor with
  | nil => simp only [List.nil_append, runNodes', pure_bind]
  | cons n ns ih =>
    rw [List.cons_append, runNodes', runNodes', bind_assoc]
    simp only [ih]

/-- The disclosed position of chain `k`. -/
abbrev pos (k : Fin 32) : ℕ := (fixedPositions index k).val

theorem pos_le (k : Fin 32) : pos index k ≤ 31 := by
  show (fixedPositions index k).val ≤ 31
  have := (fixedPositions index k).isLt
  omega

theorem cursorStep_src (k : Fin 32) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (src k) = pure (Function.update x (src k).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, evaluated, Bool.false_eq_true, if_false]

theorem cursorStep_ci (k : Fin 32) (t : Fin 32) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (ci k t) =
      if pos index k = t.val then
        pure (Function.update x (ci k t).fin
          (ofBits (graph.len (ci k t).fin) ((payload.drop cursor).take (graph.len (ci k t).fin))),
          cursor + chainBits k)
      else if pos index k < t.val then
        pure (Function.update x (ci k t).fin
          ((Forest.trunc k (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm), cursor)
      else pure (Function.update x (ci k t).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, evaluated, decide_eq_true_eq, Fin.ext_iff]
  split_ifs
  · rfl
  · simp only [evalName, map_pure, detVal_ci]
  · rfl

theorem cursorStep_ch (k : Fin 32) (t : Fin 32) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (ch k t) =
      if pos index k ≤ t.val then
        (fun y =>
          (Function.update x (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm), cursor)) <$>
          hash (x (ci k t).fin)
      else pure (Function.update x (ch k t).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, Bool.false_eq_true, if_false, evaluated, decide_eq_true_eq]
  split_ifs
  · simp only [evalName, Functor.map_map]
  · rfl

theorem cursorStep_cv (k : Fin 32) (t : Fin 32) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (cv k t) =
      if pos index k ≤ t.val then
        pure (Function.update x (cv k t).fin
          ((x (ch k t).fin).cast (lenF_ch k t) |>.cast (graph_len_fin (cv k t)).symm), cursor)
      else pure (Function.update x (cv k t).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, Bool.false_eq_true, if_false, evaluated, decide_eq_true_eq]
  split_ifs
  · simp only [evalName, map_pure, detVal_cv]
  · rfl

/-- The root input node: the concatenation of the chain tops. -/
theorem cursorStep_rc (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor rc =
      pure (Function.update x rc.fin
        ((rootCat fun k => (x (cv k 31).fin).cast (lenF_fin _)).cast (graph_len_fin rc).symm),
        cursor) := by
  unfold cursorStep
  simp only [disclosed, evaluated, Bool.false_eq_true, if_false, if_true]
  simp only [evalName, map_pure, detVal_rc]

/-- The root hash. -/
theorem cursorStep_rh (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor rh =
      (fun y => (Function.update x rh.fin (y.cast (graph_len_fin rh).symm), cursor)) <$>
        hash (x rc.fin) := by
  unfold cursorStep
  simp only [disclosed, evaluated, Bool.false_eq_true, if_false, if_true]
  simp only [evalName, Functor.map_map]

end OptimalOTS.RiscvUpperForest.ForestVerifier
