import OptimalOTS.Dag

/-!
# Pure semantics of computation graphs

Records and deterministic evaluation, used to analyse the model:

* a *record* `ξ : G.Rec` gives a value for every node (only sources matter) and an oracle output
  for every node (only hash nodes matter);
* `evalWith val` evaluates the nodes in order with the local value functions `val`, and
  satisfies the node equations when every `val v` only reads the parents of `v`
  (`evalWith_apply`); `evalRec ξ` is the evaluation of a record.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Dag.NodeKind

variable {N : ℕ} {len : Fin N → ℕ} {v : Fin N}

/-- Length of the oracle input of a node: the parent's length for a hash node, else zero. -/
def inLen : NodeKind N len v → ℕ
  | hash p _ _ => len p
  | _ => 0

/-- The oracle input of a node under the assignment `x`. -/
def input : (k : NodeKind N len v) → ((w : Fin N) → BitVec (len w)) → BitVec k.inLen
  | hash p _ _, x => x p
  | source, _ => 0
  | det _ _ _ _, _ => 0

/-- The value of a node from the values `x` of the other nodes, a source value `s` and an oracle
answer `a`. -/
def value : NodeKind N len v →
    ((w : Fin N) → BitVec (len w)) → BitVec (len v) → BitVec hashBits → BitVec (len v)
  | source, _, s, _ => s
  | det _ _ f _, x, _, _ => f x
  | hash _ _ h, _, _, a => a.cast h.symm

/-- Parents precede their child. -/
theorem lt_of_mem_parents : ∀ (k : NodeKind N len v) {w : Fin N}, w ∈ k.parents → w < v
  | source, _, h => by simp [parents] at h
  | det _ hlt _ _, _, h => hlt _ h
  | hash _ hlt _, _, h => by simp only [parents, Finset.mem_singleton] at h; exact h ▸ hlt

/-- The value computed from an assignment (with oracle answers depending on the node's input)
only depends on the parents' values. -/
theorem value_input_congr (k : NodeKind N len v) (s : BitVec (len v))
    (t : BitVec k.inLen → BitVec hashBits) (x y : (w : Fin N) → BitVec (len w))
    (h : ∀ w ∈ k.parents, x w = y w) :
    k.value x s (t (k.input x)) = k.value y s (t (k.input y)) := by
  cases k with
  | source => rfl
  | det ps _ f hf => exact hf x y h
  | hash p _ hl =>
    simp only [value, input]
    rw [h p (by simp [parents])]

/-- The value computed from an assignment with a fixed oracle answer only depends on the
parents' values. -/
theorem value_congr (k : NodeKind N len v) (s : BitVec (len v)) (a : BitVec hashBits)
    (x y : (w : Fin N) → BitVec (len w)) (h : ∀ w ∈ k.parents, x w = y w) :
    k.value x s a = k.value y s a :=
  value_input_congr k s (fun _ => a) x y h

end Dag.NodeKind

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- Records: a value for every node and an oracle output for every node. -/
abbrev Rec := G.Assignment × (Fin G.size → BitVec hashBits)

/-- Value functions computing each node from an assignment. -/
abbrev ValFn := (v : Fin G.size) → G.Assignment → BitVec (G.len v)

/-- Evaluate the nodes in order with the value functions `val`. -/
def evalWith (val : G.ValFn) : G.Assignment :=
  (List.finRange G.size).foldl (fun x v => Function.update x v (val v x)) (fun _ => 0)

/-- `val v` only depends on the values of the parents of `v`. -/
def ParentLocal (val : G.ValFn) : Prop :=
  ∀ v x x', (∀ w ∈ (G.kind v).parents, x w = x' w) → val v x = val v x'

/-- Evaluation of a record: sources from `ξ.1`, hash nodes from `ξ.2`. -/
def recVal (ξ : G.Rec) : G.ValFn := fun v x => (G.kind v).value x (ξ.1 v) (ξ.2 v)

/-- The node values determined by a record. -/
def evalRec (ξ : G.Rec) : G.Assignment := G.evalWith (G.recVal ξ)

/-! ## Evaluation -/

theorem parentLocal_recVal (ξ : G.Rec) : G.ParentLocal (G.recVal ξ) := by
  intro v x x' h
  exact NodeKind.value_congr _ _ _ x x' h

/-- Folding the evaluation step over an increasing list yields an assignment satisfying the node
equations at the nodes of the list. -/
theorem foldl_step_apply {val : G.ValFn} (hval : G.ParentLocal val) (l : List (Fin G.size))
    (hl : l.Pairwise (· < ·)) (x : G.Assignment) :
    ∀ w ∈ l, (l.foldl (fun x v => Function.update x v (val v x)) x) w =
      val w (l.foldl (fun x v => Function.update x v (val v x)) x) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.pairwise_append] at hl
    obtain ⟨hl, -, hla⟩ := hl
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set R := l.foldl (fun x v => Function.update x v (val v x)) x
    have hagree : ∀ u, u < a → Function.update R a (val a R) u = R u := fun u hu =>
      Function.update_of_ne (ne_of_lt hu) _ _
    intro w hw
    rw [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · have hwa : w < a := hla w hw a (List.mem_singleton_self a)
      rw [hagree w hwa, ih hl w hw]
      exact hval w _ _ fun u hu =>
        (hagree u (lt_trans ((G.kind w).lt_of_mem_parents hu) hwa)).symm
    · rw [Function.update_self]
      exact hval w _ _ fun u hu => (hagree u ((G.kind w).lt_of_mem_parents hu)).symm

/-- Evaluation satisfies the node equations. -/
theorem evalWith_apply {val : G.ValFn} (hval : G.ParentLocal val) (v : Fin G.size) :
    G.evalWith val v = val v (G.evalWith val) := by
  exact G.foldl_step_apply hval _ (List.pairwise_lt_finRange _) _ v (List.mem_finRange v)

/-- The node equation of a record. -/
theorem evalRec_apply (ξ : G.Rec) (v : Fin G.size) :
    G.evalRec ξ v = (G.kind v).value (G.evalRec ξ) (ξ.1 v) (ξ.2 v) :=
  G.evalWith_apply (G.parentLocal_recVal ξ) v

end Dag.Graph

end OptimalOTS
