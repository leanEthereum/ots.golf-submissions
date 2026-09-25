import Submissions.UpperRiscvHint.MixedMemory

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

def tops (x : graph.Assignment) (k : Fin 32) : BitVec 256 :=
  (x (cv k 31).fin).cast (lenF_fin _)

variable (index : RawIdx) (payload : List Bool)

theorem fin_ne_of_ne {m n : Name} (h : m ≠ n) : m.fin ≠ n.fin :=
  fun e => h (Name.fin_injective e)

theorem writeHash_regs (w : MachineState) (a : BitVec hashBits) (r : Reg) :
    (Riscv.writeHash w a).getReg r = w.getReg r := by
  simp [Riscv.writeHash]

theorem writeHash_code (w : MachineState) (a : BitVec hashBits) :
    (Riscv.writeHash w a).code = w.code := by
  simp [Riscv.writeHash]

theorem writeHash_pc (w : MachineState) (a : BitVec hashBits) :
    (Riscv.writeHash w a).pc = w.pc + 4 := rfl

/-- The three specification steps of a level, as one hash of the input `v`. -/
def tripleUpdate (x : graph.Assignment) (k : Fin 32) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) : graph.Assignment :=
  Function.update (Function.update (Function.update x (ci k t).fin v)
    (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm))
    (cv k t).fin (((y.cast (graph_len_fin (ch k t)).symm).cast (lenF_ch k t)).cast
      (graph_len_fin (cv k t)).symm)

/-- The disclosed level: the input is read from the payload. -/
theorem triple_run_read (k : Fin 32) (t : Fin 32) (ht : RiscvUpperForest.ForestVerifier.pos index k = t.val)
    (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index payload [ci k t, ch k t, cv k t] x cursor =
      hash (ofBits (graph.len (ci k t).fin) ((payload.drop cursor).take (graph.len (ci k t).fin)))
        >>= fun y => pure (tripleUpdate x k t
          (ofBits (graph.len (ci k t).fin) ((payload.drop cursor).take (graph.len (ci k t).fin))) y,
          cursor + chainBits k) := by
  have hle : RiscvUpperForest.ForestVerifier.pos index k ≤ t.val := le_of_eq ht
  simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_pos ht, if_pos hle,
    pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def, Function.update_self,
    tripleUpdate]

/-- A level above the disclosed one: the input is the previous value. -/
theorem triple_run_step (k : Fin 32) (t : Fin 32) (ht : RiscvUpperForest.ForestVerifier.pos index k < t.val)
    (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index payload [ci k t, ch k t, cv k t] x cursor =
      hash ((Forest.trunc k (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm)
        >>= fun y => pure (tripleUpdate x k t
          ((Forest.trunc k (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm) y, cursor) := by
  have hne : ¬ RiscvUpperForest.ForestVerifier.pos index k = t.val := by omega
  have hle : RiscvUpperForest.ForestVerifier.pos index k ≤ t.val := le_of_lt ht
  simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hne, if_pos ht,
    if_pos hle, pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
    Function.update_self, tripleUpdate]

theorem tripleUpdate_cv (x : graph.Assignment) (k : Fin 32) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    tripleUpdate x k t v y (cv k t).fin =
      ((y.cast (graph_len_fin (ch k t)).symm).cast (lenF_ch k t)).cast
        (graph_len_fin (cv k t)).symm := by
  simp only [tripleUpdate, Function.update_self]

theorem tripleUpdate_other (x : graph.Assignment) (k : Fin 32) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits)
    (n : Name) (h1 : n ≠ ci k t) (h2 : n ≠ ch k t) (h3 : n ≠ cv k t) :
    tripleUpdate x k t v y n.fin = x n.fin := by
  simp only [tripleUpdate]
  rw [Function.update_of_ne (fin_ne_of_ne h3), Function.update_of_ne (fin_ne_of_ne h2),
    Function.update_of_ne (fin_ne_of_ne h1)]

/-- The trunc of the value node is the trunc of the answer. -/
theorem trunc_tripleUpdate_cv (x : graph.Assignment) (k : Fin 32) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    Forest.trunc k (tripleUpdate x k t v y (cv k t).fin) = Forest.trunc k y := by
  rw [tripleUpdate_cv]
  apply BitVec.eq_of_toNat_eq
  simp only [Forest.trunc, BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_cast, lenF_fin]
  rfl

theorem tops_tripleUpdate (x : graph.Assignment) (k : Fin 32) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) (k' : Fin 32) (hk : k' ≠ k) :
    tops (tripleUpdate x k t v y) k' = tops x k' := by
  unfold tops
  rw [tripleUpdate_other x k t v y (cv k' 31) (by simp) (by simp)
    (fun e => hk (Name.cv.inj e).1)]

def tripleN (k : Fin 32) (t : ℕ) : List Name :=
  if h : t < 32 then [ci k ⟨t, h⟩, ch k ⟨t, h⟩, cv k ⟨t, h⟩] else []

theorem chainNodes_eq (k : Fin 32) :
    chainNodes k = src k :: (List.range 32).flatMap (tripleN k) := by
  simp only [chainNodes, List.finRange, List.range]
  rfl

theorem range_split (p : ℕ) (hp : p ≤ 32) :
    List.range 32 = List.range p ++ List.range' p (32 - p) := by
  have h := @List.range'_append_1 0 p (32 - p)
  rw [Nat.zero_add, Nat.add_sub_cancel' hp] at h
  rw [List.range_eq_range', List.range_eq_range', h]

/-- Before its disclosed level, a chain's nodes are pure zeros. -/
theorem prefix_run (k : Fin 32) :
    ∀ (q : ℕ), q ≤ RiscvUpperForest.ForestVerifier.pos index k → ∀ (x : graph.Assignment) (cursor : ℕ),
    ∃ x' : graph.Assignment,
      runNodes' index payload (src k :: (List.range q).flatMap (tripleN k)) x cursor =
        pure (x', cursor) ∧
      (∀ k' : Fin 32, k' ≠ k → x' (cv k' 31).fin = x (cv k' 31).fin) := by
  intro q
  induction q with
  | zero =>
    intro _ x cursor
    have run : runNodes' index payload (src k :: (List.range 0).flatMap (tripleN k)) x cursor =
        cursorStep index payload x cursor (src k) := by
      simp only [List.range_zero, List.flatMap_nil, runNodes', Prod.mk.eta, bind_pure]
    rw [run, cursorStep_src]
    refine ⟨_, rfl, ?_⟩
    intro k' _
    exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
  | succ q ih =>
    intro hq x cursor
    obtain ⟨x₁, run₁, frame₁⟩ := ih (by omega) x cursor
    have hq32 : q < 32 := by
      have := pos_le index k
      omega
    have hne : ¬ (RiscvUpperForest.ForestVerifier.pos index k = q) := by omega
    have hlt : ¬ (RiscvUpperForest.ForestVerifier.pos index k < q) := by omega
    have hle : ¬ (RiscvUpperForest.ForestVerifier.pos index k ≤ q) := by omega
    have triple : tripleN k q = [ci k ⟨q, hq32⟩, ch k ⟨q, hq32⟩, cv k ⟨q, hq32⟩] := by
      simp [tripleN, hq32]
    have run : runNodes' index payload (src k :: (List.range (q + 1)).flatMap (tripleN k)) x cursor =
        runNodes' index payload [ci k ⟨q, hq32⟩, ch k ⟨q, hq32⟩, cv k ⟨q, hq32⟩] x₁ cursor := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, triple, ← List.cons_append,
        runNodes'_append, run₁, pure_bind]
    rw [run]
    simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hne, if_neg hlt,
      if_neg hle, pure_bind, Prod.mk.eta, bind_pure]
    refine ⟨_, rfl, ?_⟩
    intro k' hk'
    rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk' (Name.cv.inj h).1)),
      Function.update_of_ne (fin_ne_of_ne (by simp)),
      Function.update_of_ne (fin_ne_of_ne (by simp))]
    exact frame₁ k' hk'


end OptimalOTS.RiscvMixedProgram
