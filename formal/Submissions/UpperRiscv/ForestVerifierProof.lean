import Submissions.UpperRiscv.ForestVerifier
import Submissions.UpperRiscv.Layout

/-! The sequential signature reader used by the machine compiler. -/

open OracleComp
noncomputable section
open scoped Classical

namespace OptimalOTS.RiscvUpperForest.ForestVerifier

open OptimalOTS.Dag


open Forest Forest.Name

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.setsName Forest.fixedChoice Forest.fixedPositions Forest.fixedDigits

/-- The bits consumed by earlier disclosures in a list of named nodes. -/
def precedingBits (i : Idx) (nodes : List Name) (n : Name) : ℕ :=
  ((nodes.filter fun w => disclosed (fixedPositions i) w && decide (w.idx < n.idx)).map Name.len).sum

/-- Sequential disclosure offsets agree with the graph's bit-string encoding. -/
theorem precedingBits_eq (i : Idx) (n : Name) :
    precedingBits i order n = graph.offset (fins (setsName i)) n.fin := by
  rw [Graph.offset_eq]
  change _ = chunkOff graph.len ((List.finRange N).filter _) n.fin
  rw [← order_fin]
  simp only [chunkOff, List.filter_map, List.map_map]
  simp only [Function.comp_def, mem_fins, ← disclosed_eq]
  simp only [List.filter_filter]
  simp only [precedingBits, Fin.lt_def, Name.fin, Bool.decide_coe, Bool.and_comm]
  apply congrArg List.sum
  apply congrArg (fun f => List.map f _)
  funext x
  exact (lenF_fin x).symm

/-- Number of signature bits consumed at a named node. -/
def consumedBits (i : Idx) (n : Name) : ℕ :=
  if disclosed (fixedPositions i) n then n.len else 0

/-- A machine step with a running signature cursor measured in bits. -/
def cursorStep (i : Idx) (payload : List Bool)
    (x : graph.Assignment) (cursor : ℕ) (n : Name) :
    OracleComp Spec (graph.Assignment × ℕ) :=
  if disclosed (fixedPositions i) n then
    pure (Function.update x n.fin
      (ofBits (graph.len n.fin) ((payload.drop cursor).take (graph.len n.fin))), cursor + n.len)
  else if evaluated (fixedPositions i) n then
    (fun y => (Function.update x n.fin y, cursor)) <$> runOp x n
  else pure (Function.update x n.fin 0, cursor)

private theorem evaluated_iff_reachable (i : Idx) (n : Name)
    (hn : n ∉ setsName i) :
    evaluated (fixedPositions i) n = true ↔ reachable (setsName i) n = true := by
  rw [evaluated_eq, reachable_eq_true, visited_iff]
  exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

/-- A cursor step agrees with an offset read when its cursor names the next disclosure. -/
theorem cursorStep_eq (i : Idx) (payload : List Bool)
    (x : graph.Assignment) (cursor : ℕ) (n : Name)
    (hc : disclosed (fixedPositions i) n = true →
      cursor = graph.offset (fins (setsName i)) n.fin) :
    cursorStep i payload x cursor n =
      (fun y => (y, cursor + consumedBits i n)) <$>
        step (setsName i) (graph.decode (fins (setsName i)) payload) x n := by
  by_cases hd : disclosed (fixedPositions i) n = true
  · have hn := (disclosed_eq i n).mp hd
    simp only [cursorStep, hd, if_true, consumedBits, step, hn, map_pure]
    rw [hc hd]
    rfl
  · have hn : n ∉ setsName i := mt (disclosed_eq i n).mpr hd
    simp only [cursorStep, hd, Bool.false_eq_true, if_false, consumedBits, Nat.add_zero, step, hn]
    simp only [evaluated_iff_reachable i n hn]
    split_ifs <;> simp only [map_pure, Functor.map_map, runOp_eq]

/-- Execute the node sequence, consuming signature words in topological order. -/
def runNodes (i : Idx) (payload : List Bool) :
    List Name → graph.Assignment → ℕ → OracleComp Spec graph.Assignment
  | [], x, _ => pure x
  | n :: ns, x, cursor => do
      let (y, next) ← cursorStep i payload x cursor n
      runNodes i payload ns y next

private theorem precedingBits_head (i : Idx) (n : Name) (nodes : List Name)
    (hs : (n :: nodes).Pairwise (fun a b => a.idx < b.idx)) :
    precedingBits i (n :: nodes) n = 0 := by
  have hn := (List.pairwise_cons.mp hs).1
  have hf : nodes.filter (fun w => disclosed (fixedPositions i) w && decide (w.idx < n.idx)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro w hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro _
    exact Nat.not_lt_of_ge (hn w hw).le
  simp only [precedingBits, Nat.lt_irrefl, decide_false, Bool.and_false,
    List.filter_cons_of_neg, Bool.false_eq_true, not_false_eq_true, hf, List.map_nil, List.sum_nil]

private theorem precedingBits_cons (i : Idx) (n m : Name) (nodes : List Name)
    (hnm : n.idx < m.idx) :
    precedingBits i (n :: nodes) m = consumedBits i n + precedingBits i nodes m := by
  simp only [precedingBits, hnm, decide_true, Bool.and_true, List.filter_cons]
  by_cases hd : disclosed (fixedPositions i) n = true
  · simp only [hd, if_true, List.map_cons, List.sum_cons, consumedBits]
  · simp only [hd, Bool.false_eq_true, if_false, consumedBits, Nat.zero_add]

/-- The sequential reader and the graph decoder have identical oracle behavior. -/
theorem runNodes_eq (i : Idx) (payload : List Bool) (nodes : List Name)
    (hs : nodes.Pairwise (fun a b => a.idx < b.idx))
    (x : graph.Assignment) (cursor : ℕ)
    (hc : ∀ n ∈ nodes, cursor + precedingBits i nodes n =
      graph.offset (fins (setsName i)) n.fin) :
    runNodes i payload nodes x cursor =
      nodes.foldlM (step (setsName i) (graph.decode (fins (setsName i)) payload)) x := by
  induction nodes generalizing x cursor with
  | nil => rfl
  | cons n nodes ih =>
    have hn := (List.pairwise_cons.mp hs).1
    have htail := (List.pairwise_cons.mp hs).2
    have hcursor : cursor = graph.offset (fins (setsName i)) n.fin := by
      simpa only [precedingBits_head i n nodes hs, Nat.add_zero] using hc n (by simp)
    rw [runNodes, cursorStep_eq i payload x cursor n (fun _ => hcursor)]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind, List.foldlM_cons]
    apply congrArg (fun f => step (setsName i) (graph.decode (fins (setsName i)) payload) x n >>= f)
    funext y
    apply ih htail
    intro m hm
    have h := hc m (List.mem_cons_of_mem n hm)
    rw [precedingBits_cons i n m nodes (hn m hm)] at h
    simpa only [Nat.add_assoc] using h

/-- All nodes have unique slots, traversed in increasing slot order. -/
theorem order_sorted : order.Pairwise (fun a b => a.idx < b.idx) := by
  have h := List.pairwise_lt_finRange N
  rw [← order_fin, List.pairwise_map] at h
  exact h

/-- The direct compiler's high-level reconstruction, with a sequential disclosure cursor. -/
def directReconstruct (i : Idx) (payload : List Bool) :
    OracleComp Spec graph.Assignment :=
  runNodes i payload order (fun _ => 0) 0

/-- Direct reconstruction is exactly the certified DAG reconstruction. -/
theorem directReconstruct_eq (i : Idx) (payload : List Bool) :
    directReconstruct i payload = reconstruct (setsName i) payload := by
  apply runNodes_eq i payload order order_sorted
  intro n _
  simpa only [Nat.zero_add] using precedingBits_eq i n

/-- The complete verifier compiled to the direct node program. -/
def directVerify (pk : PublicKey) (m : Message) (bits : List Bool) :
    OracleComp Spec Bool := do
  let i ← index m (ofBits 128 (bits.take 128))
  if hi : i ∈ validSet then
    if bits.length = 4224 then
      let y ← directReconstruct ⟨i, hi⟩ (bits.drop 128)
      return decide ((y rh.fin).setWidth 128 = pk)
    else return false
  else return false

/-- The compiler target preserves the entire certified raw-signature verifier. -/
theorem directVerify_eq (pk : PublicKey) (m : Message) (bits : List Bool) :
    directVerify pk m bits = Wire.scheme.verify pk m bits := by
  rw [← verify_eq]
  unfold directVerify verify
  apply congrArg (fun f => index m (ofBits 128 (bits.take 128)) >>= f)
  funext i
  by_cases hi : i ∈ validSet
  · rw [dif_pos hi, dif_pos hi]
    have hlen := Wire.payload_length_iff bits ⟨i, hi⟩
    change (bits.drop 128).length = graph.revealBits (fins (setsName ⟨i, hi⟩)) ↔ bits.length = 4224 at hlen
    simp only [hlen, directReconstruct_eq]
  · rw [dif_neg hi, dif_neg hi]

/-- The sequential disclosure cursor advances by one word exactly at disclosed nodes. -/
theorem consumedBits_word (i : Idx) (n : Name) :
    consumedBits i n = if disclosed (fixedPositions i) n then 128 else 0 := by
  unfold consumedBits
  split_ifs with hd
  · exact (fixedCut_isCut i).values n (by simpa only [setsName] using (disclosed_eq i n).mp hd)
  · rfl

/--
info: 'OptimalOTS.RiscvUpperForest.ForestVerifier.directVerify_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms directVerify_eq

end OptimalOTS.RiscvUpperForest.ForestVerifier
