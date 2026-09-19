import OptimalOTS.Dag

/-!
# Pure semantics of computation graphs

Records, oracle tables and deterministic evaluation, used to analyse the model:

* a *record* `ξ : G.Rec` gives a value for every node (only sources matter) and a putative oracle
  output for every node (only hash nodes matter); records here are algebraic objects, not a claim
  about independent random-oracle outputs;
* a *node table* `t : G.Tab` gives, for every node, a function from its oracle input to an
  output; a bare oracle induces these tables by using the same function on all strings;
* `evalWith val` evaluates the nodes in order with the local value functions `val`.
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

/-- The oracle output stored in the value of a hash node (zero for other nodes). -/
def output : NodeKind N len v → BitVec (len v) → BitVec hashBits
  | hash _ _ h, a => a.cast h
  | _, _ => 0

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

/-- Oracle tables: for every node, a function from its oracle input to an output. -/
abbrev Tab := (v : Fin G.size) → BitVec (G.kind v).inLen → BitVec hashBits

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

/-- Evaluation with sources `z` and oracle tables `t`. -/
def tabVal (z : G.Assignment) (t : G.Tab) : G.ValFn :=
  fun v x => (G.kind v).value x (z v) (t v ((G.kind v).input x))

/-- The node values computed from sources `z` and oracle tables `t`. -/
def evalTab (z : G.Assignment) (t : G.Tab) : G.Assignment := G.evalWith (G.tabVal z t)

/-- The record produced by key generation with sources `z` and oracle tables `t`. -/
def recOf (z : G.Assignment) (t : G.Tab) : G.Rec :=
  (z, fun v => t v ((G.kind v).input (G.evalTab z t)))

/-- The hash nodes evaluated when reconstructing from `A`. -/
def evalHash (A : Finset (Fin G.size)) : Finset (Fin G.size) :=
  (G.evaluated A).filter fun v => (G.kind v).IsHash

/-- Root reconstruction with oracle tables `tg` from the values `given` on `A`. -/
def reconVal (tg : G.Tab) (A : Finset (Fin G.size)) (given : G.Assignment) : G.ValFn :=
  fun v x =>
    if v ∈ A then given v
    else if G.Visited A v then (G.kind v).value x 0 (tg v ((G.kind v).input x))
    else 0

/-- The node values computed by root reconstruction with oracle tables `tg`. -/
def reconTab (tg : G.Tab) (A : Finset (Fin G.size)) (given : G.Assignment) : G.Assignment :=
  G.evalWith (G.reconVal tg A given)

/-! ## Evaluation -/

theorem parentLocal_recVal (ξ : G.Rec) : G.ParentLocal (G.recVal ξ) := by
  intro v x x' h
  exact NodeKind.value_congr _ _ _ x x' h

theorem parentLocal_tabVal (z : G.Assignment) (t : G.Tab) : G.ParentLocal (G.tabVal z t) := by
  intro v x x' h
  exact NodeKind.value_input_congr _ _ (t v) x x' h

theorem parentLocal_reconVal (tg : G.Tab) (A : Finset (Fin G.size)) (given : G.Assignment) :
    G.ParentLocal (G.reconVal tg A given) := by
  intro v x x' h
  simp only [reconVal]
  split_ifs
  · rfl
  · exact NodeKind.value_input_congr _ _ (tg v) x x' h
  · rfl

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

/-- Two solutions of parent-local node equations agree. -/
theorem eq_of_node_eqs {val : G.ValFn} (hval : G.ParentLocal val) (a b : G.Assignment)
    (ha : ∀ v, a v = val v a) (hb : ∀ v, b v = val v b) : a = b := by
  funext v
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    rw [ha v, hb v]
    exact hval v a b fun w hw => ih w ((G.kind v).lt_of_mem_parents hw)

/-- The node equations have a unique solution. -/
theorem eq_evalWith {val : G.ValFn} (hval : G.ParentLocal val) (a : G.Assignment)
    (ha : ∀ v, a v = val v a) : a = G.evalWith val := by
  exact G.eq_of_node_eqs hval a _ ha (G.evalWith_apply hval)

/-- The node equation of a record. -/
theorem evalRec_apply (ξ : G.Rec) (v : Fin G.size) :
    G.evalRec ξ v = (G.kind v).value (G.evalRec ξ) (ξ.1 v) (ξ.2 v) :=
  G.evalWith_apply (G.parentLocal_recVal ξ) v

theorem evalRec_recOf (z : G.Assignment) (t : G.Tab) :
    G.evalRec (G.recOf z t) = G.evalTab z t := by
  refine (G.eq_evalWith (G.parentLocal_recVal _) _ fun v => ?_).symm
  exact G.evalWith_apply (G.parentLocal_tabVal z t) v

/-! ## Reconstruction -/

/-- Reconstruction with tables `tg` from the values of an assignment `a` on `A` recovers `a` on
every visited node, provided `a` satisfies the node equations at the evaluated nodes. -/
theorem reconTab_eq_of_visited (tg : G.Tab) (A : Finset (Fin G.size)) (a : G.Assignment)
    (hsrc : ∀ v, G.Visited A v → v ∉ A → ¬ (G.kind v).IsSource)
    (ha : ∀ v, G.Visited A v → v ∉ A → a v = (G.kind v).value a 0 (tg v ((G.kind v).input a)))
    (v : Fin G.size) (hv : G.Visited A v) :
    G.reconTab tg A a v = a v := by
  have _ := hsrc
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    rw [reconTab, G.evalWith_apply (G.parentLocal_reconVal tg A a) v]
    by_cases hA : v ∈ A
    · simp [reconVal, hA]
    · simp only [reconVal, hA, if_false, hv, if_true]
      rw [ha v hv hA]
      refine NodeKind.value_input_congr _ _ (tg v) _ _ fun w hw => ?_
      exact ih w ((G.kind v).lt_of_mem_parents hw) (Graph.Visited.parent hv hA hw)

end Dag.Graph

end OptimalOTS
