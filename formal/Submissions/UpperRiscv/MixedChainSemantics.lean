import Submissions.UpperRiscv.MixedMemory
import Submissions.UpperRiscv.ChainSplit

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

/-- The last answer of chain `k`. -/
def lastAnswer (x : graph.Assignment) (k : Fin 33) : BitVec 256 :=
  (x (cv k 31).fin).cast (lenF_fin _)

variable (index : RawIdx) (v : ℕ) (payload : List Bool)

theorem fin_ne_of_ne {m n : Name} (h : m ≠ n) : m.fin ≠ n.fin :=
  fun e => h (Name.fin_injective e)

/-- The three specification steps of a level, as one hash of the input `u`. -/
def tripleUpdate (x : graph.Assignment) (k : Fin 33) (t : Fin 32)
    (u : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) : graph.Assignment :=
  Function.update (Function.update (Function.update x (ci k t).fin u)
    (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm))
    (cv k t).fin (((y.cast (graph_len_fin (ch k t)).symm).cast (lenF_ch k t)).cast
      (graph_len_fin (cv k t)).symm)

/-- The disclosed level: the input is read from the payload. -/
theorem triple_run_read (k : Fin 33) (t : Fin 32) (ht : RiscvUpperForest.ForestVerifier.pos index v k = t.val)
    (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index v payload [ci k t, ch k t, cv k t] x cursor =
      hash (ofBits (graph.len (ci k t).fin) ((payload.drop cursor).take (graph.len (ci k t).fin)))
        >>= fun y => pure (tripleUpdate x k t
          (ofBits (graph.len (ci k t).fin) ((payload.drop cursor).take (graph.len (ci k t).fin))) y,
          cursor + chainBits k) := by
  have hle : RiscvUpperForest.ForestVerifier.pos index v k ≤ t.val := le_of_eq ht
  simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_pos ht, if_pos hle,
    pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def, Function.update_self,
    tripleUpdate]

/-- A level above the disclosed one: the input is the previous value. -/
theorem triple_run_step (k : Fin 33) (t : Fin 32) (ht : RiscvUpperForest.ForestVerifier.pos index v k < t.val)
    (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index v payload [ci k t, ch k t, cv k t] x cursor =
      hash ((Forest.trunc k (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm)
        >>= fun y => pure (tripleUpdate x k t
          ((Forest.trunc k (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm) y, cursor) := by
  have hne : ¬ RiscvUpperForest.ForestVerifier.pos index v k = t.val := by omega
  have hle : RiscvUpperForest.ForestVerifier.pos index v k ≤ t.val := le_of_lt ht
  simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hne, if_pos ht,
    if_pos hle, pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
    Function.update_self, tripleUpdate]

theorem tripleUpdate_cv (x : graph.Assignment) (k : Fin 33) (t : Fin 32)
    (u : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    tripleUpdate x k t u y (cv k t).fin =
      ((y.cast (graph_len_fin (ch k t)).symm).cast (lenF_ch k t)).cast
        (graph_len_fin (cv k t)).symm := by
  simp only [tripleUpdate, Function.update_self]

theorem tripleUpdate_other (x : graph.Assignment) (k : Fin 33) (t : Fin 32)
    (u : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits)
    (n : Name) (h1 : n ≠ ci k t) (h2 : n ≠ ch k t) (h3 : n ≠ cv k t) :
    tripleUpdate x k t u y n.fin = x n.fin := by
  simp only [tripleUpdate]
  rw [Function.update_of_ne (fin_ne_of_ne h3), Function.update_of_ne (fin_ne_of_ne h2),
    Function.update_of_ne (fin_ne_of_ne h1)]

/-- The trunc of the value node is the trunc of the answer. -/
theorem trunc_tripleUpdate_cv (x : graph.Assignment) (k : Fin 33) (t : Fin 32)
    (u : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    Forest.trunc k (tripleUpdate x k t u y (cv k t).fin) = Forest.trunc k y := by
  rw [tripleUpdate_cv]
  apply BitVec.eq_of_toNat_eq
  simp only [Forest.trunc, BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_cast, lenF_fin]
  rfl

theorem lastAnswer_tripleUpdate (x : graph.Assignment) (k : Fin 33)
    (u : BitVec (graph.len (ci k 31).fin)) (y : BitVec hashBits) :
    lastAnswer (tripleUpdate x k 31 u y) k = y := by
  unfold lastAnswer
  rw [tripleUpdate_cv]
  rfl

theorem tops_tripleUpdate (x : graph.Assignment) (k : Fin 33) (t : Fin 32)
    (u : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) (k' : Fin 33) :
    tops (tripleUpdate x k t u y) k' = tops x k' := by
  unfold tops
  rw [tripleUpdate_other x k t u y (tp k') (by simp) (by simp) (by simp)]

theorem lastAnswer_tripleUpdate_ne (x : graph.Assignment) (k : Fin 33) (t : Fin 32)
    (u : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) (k' : Fin 33) (hk : k' ≠ k) :
    lastAnswer (tripleUpdate x k t u y) k' = lastAnswer x k' := by
  unfold lastAnswer
  rw [tripleUpdate_other x k t u y (cv k' 31) (by simp) (by simp)
    (fun e => hk (Name.cv.inj e).1)]

/-- Before its disclosed level, a chain's nodes are pure zeros. -/
theorem prefix_run (k : Fin 33) :
    ∀ (q : ℕ), q ≤ RiscvUpperForest.ForestVerifier.pos index v k → q ≤ 32 → ∀ (x : graph.Assignment) (cursor : ℕ),
    ∃ x' : graph.Assignment,
      runNodes' index v payload (src k :: (List.range q).flatMap (tripleN k)) x cursor =
        pure (x', cursor) ∧
      (∀ k' : Fin 33, x' (tp k').fin = x (tp k').fin) ∧
      (∀ k' : Fin 33, k' ≠ k → x' (cv k' 31).fin = x (cv k' 31).fin) := by
  intro q
  induction q with
  | zero =>
    intro _ _ x cursor
    have run : runNodes' index v payload (src k :: (List.range 0).flatMap (tripleN k)) x cursor =
        cursorStep index v payload x cursor (src k) := by
      simp only [List.range_zero, List.flatMap_nil, runNodes', Prod.mk.eta, bind_pure]
    rw [run, cursorStep_src]
    refine ⟨_, rfl, ?_, ?_⟩
    · intro k'; exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
    · intro k' _; exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
  | succ q ih =>
    intro hq hq32 x cursor
    obtain ⟨x₁, run₁, ftp, frame₁⟩ := ih (by omega) (by omega) x cursor
    have hq32' : q < 32 := by omega
    have hne : ¬ (RiscvUpperForest.ForestVerifier.pos index v k = q) := by omega
    have hlt : ¬ (RiscvUpperForest.ForestVerifier.pos index v k < q) := by omega
    have hle : ¬ (RiscvUpperForest.ForestVerifier.pos index v k ≤ q) := by omega
    have triple : tripleN k q = [ci k ⟨q, hq32'⟩, ch k ⟨q, hq32'⟩, cv k ⟨q, hq32'⟩] := by
      simp [tripleN, hq32']
    have run : runNodes' index v payload (src k :: (List.range (q + 1)).flatMap (tripleN k)) x cursor =
        runNodes' index v payload [ci k ⟨q, hq32'⟩, ch k ⟨q, hq32'⟩, cv k ⟨q, hq32'⟩] x₁ cursor := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, triple, ← List.cons_append,
        runNodes'_append, run₁, pure_bind]
    rw [run]
    simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hne, if_neg hlt,
      if_neg hle, pure_bind, Prod.mk.eta, bind_pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · intro k'
      rw [Function.update_of_ne (fin_ne_of_ne (by simp)),
        Function.update_of_ne (fin_ne_of_ne (by simp)),
        Function.update_of_ne (fin_ne_of_ne (by simp))]
      exact ftp k'
    · intro k' hk'
      rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk' (Name.cv.inj h).1)),
        Function.update_of_ne (fin_ne_of_ne (by simp)),
        Function.update_of_ne (fin_ne_of_ne (by simp))]
      exact frame₁ k' hk'

/-- The top after the last level: the root slot of the last answer. -/
theorem top_run_eval (k : Fin 33) (h : RiscvUpperForest.ForestVerifier.pos index v k ≠ 32) (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index v payload [tp k] x cursor =
      pure (Function.update x (tp k).fin
        ((topSlice k (lastAnswer x k)).cast (graph_len_fin (tp k)).symm), cursor) := by
  simp only [runNodes', cursorStep_tp, if_neg h, pure_bind]
  rfl

/-- A cap with digit zero reveals its top. -/
theorem top_run_read (k : Fin 33) (h : RiscvUpperForest.ForestVerifier.pos index v k = 32) (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index v payload [tp k] x cursor =
      pure (Function.update x (tp k).fin
        (ofBits (graph.len (tp k).fin) ((payload.drop cursor).take (graph.len (tp k).fin))),
        cursor + topBits k) := by
  simp only [runNodes', cursorStep_tp, if_pos h, pure_bind]

theorem tops_update_self (x : graph.Assignment) (k : Fin 33) (u : BitVec (topBits k)) :
    tops (Function.update x (tp k).fin (u.cast (graph_len_fin (tp k)).symm)) k = u := by
  unfold tops
  rw [Function.update_self]
  rfl

theorem tops_update_ne (x : graph.Assignment) (k k' : Fin 33) (hk : k' ≠ k)
    (u : BitVec (graph.len (tp k).fin)) :
    tops (Function.update x (tp k).fin u) k' = tops x k' := by
  unfold tops
  rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk (Name.tp.inj h)))]

theorem lastAnswer_update_tp (x : graph.Assignment) (k k' : Fin 33)
    (u : BitVec (graph.len (tp k).fin)) :
    lastAnswer (Function.update x (tp k).fin u) k' = lastAnswer x k' := by
  unfold lastAnswer
  rw [Function.update_of_ne (fin_ne_of_ne (by simp))]

end OptimalOTS.RiscvMixedProgram
