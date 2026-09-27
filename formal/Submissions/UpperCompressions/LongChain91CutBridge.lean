import Submissions.UpperCompressions.ProofBundle03
import Submissions.UpperCompressions.LongChain91Geometry

/-!
# Concrete DAG for the cost-87 fused shared-DAG construction

This module turns the names of `LongChain91Geometry` into the `Dag.Graph`
consumed by the generic weighted scheme: three blocks of fourteen length-18
chains and twenty ternary hashes with shared inputs, under a fifteen-word root
hash.
-/

open OracleSpec OracleComp ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag

abbrev N : ℕ := nodeCount

namespace Name

/-- Inverse of the compact topological numbering. -/
def ofFin (v : Fin N) : Name :=
  if h₀ : v.val < 42 then .src ⟨v.val / 14, by omega⟩ ⟨v.val % 14, by omega⟩
  else if h₁ : v.val < 2310 then
    let m := v.val - 42
    let t : Fin 18 := ⟨m / 126, by omega⟩
    let r := m % 126
    if h₂ : r < 42 then .ci ⟨r / 14, by omega⟩ ⟨r % 14, by omega⟩ t
    else if h₃ : r < 84 then .ch ⟨(r - 42) / 14, by omega⟩ ⟨(r - 42) % 14, by omega⟩ t
    else .cv ⟨(r - 84) / 14, by omega⟩ ⟨(r - 84) % 14, by omega⟩ t
  else if h₄ : v.val < 2490 then
    let m := v.val - 2310
    let b : Fin 3 := ⟨m / 60, by omega⟩
    let j : Fin 20 := ⟨m % 60 / 3, by omega⟩
    if m % 3 = 0 then .hc b j
    else if m % 3 = 1 then .hh b j
    else .hv b j
  else if h₅ : v.val < 2491 then .rc
  else .rh

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 2492 := v.isLt
  rw [Fin.ext_iff]
  simp only [ofFin]
  split_ifs <;> simp only [fin, idx] <;> omega

@[simp] theorem ofFin_fin (n : Name) : ofFin n.fin = n :=
  idx_injective (congrArg Fin.val (fin_ofFin_aux n.fin))

@[simp] theorem fin_ofFin (v : Fin N) : (ofFin v).fin = v := fin_ofFin_aux v

def nameEquiv : Name ≃ Fin N where
  toFun := fin
  invFun := ofFin
  left_inv := ofFin_fin
  right_inv := fin_ofFin

/-- The graph inputs of each node. -/
def parents : Name → Finset Name
  | .src _ _ => ∅
  | .ci b k t => {prev b k t}
  | .ch b k t => {.ci b k t}
  | .cv b k t => {.ch b k t}
  | .hc b j => Finset.univ.image fun i : Fin 3 => (kid j i).name b
  | .hh b j => {.hc b j}
  | .hv b j => {.hh b j}
  | .rc => Finset.univ.image rootIn
  | .rh => {.rc}

@[simp] theorem mem_parents_hc (m : Name) (b : Fin 3) (j : Fin 20) :
    m ∈ parents (.hc b j) ↔ ∃ i, (kid j i).name b = m := by
  simp [parents]

@[simp] theorem mem_parents_rc (m : Name) :
    m ∈ parents .rc ↔ ∃ r, rootIn r = m := by
  simp [parents]

theorem kid_name_idx_lt (b : Fin 3) (j : Fin 20) (i : Fin 3) :
    ((kid j i).name b).idx < (Name.hc b j).idx := by
  cases hk : kid j i with
  | c k => simp only [Kid.name, idx]; omega
  | h j' =>
      have := kid_h_lt hk
      simp only [Kid.name, idx]
      omega

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  cases n with
  | src b k => simp [parents] at h
  | ci b k t =>
      rw [parents, Finset.mem_singleton] at h
      subst h
      unfold prev
      split_ifs <;> simp only [idx] <;> omega
  | hc b j =>
      obtain ⟨i, rfl⟩ := (mem_parents_hc m b j).1 h
      exact kid_name_idx_lt b j i
  | rc =>
      obtain ⟨r, rfl⟩ := (mem_parents_rc m).1 h
      simp only [rootIn, idx]
      omega
  | ch b k t | cv b k t | hh b j | hv b j | rh =>
      rw [parents, Finset.mem_singleton] at h
      subst h
      simp only [idx]
      omega

theorem fin_lt_fin_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.fin < n.fin :=
  idx_lt_of_mem_parents h

def parentFins (n : Name) : Finset (Fin N) := (parents n).map nameEquiv.toEmbedding

theorem fin_mem_parentFins {m n : Name} (h : m ∈ parents n) : m.fin ∈ parentFins n :=
  Finset.mem_map_of_mem _ h

end Name

open Name

/-! ## Tweaks and deterministic inputs -/

def tw (h : Name) : BitVec 16 := BitVec.ofNat 16 h.idx

theorem tw_toNat (h : Name) : (tw h).toNat = h.idx := by
  have hi := h.idx_lt
  unfold nodeCount at hi
  rw [tw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  omega

def lenF (v : Fin N) : ℕ := (Name.ofFin v).len

@[simp] theorem lenF_fin (n : Name) : lenF n.fin = n.len := by simp [lenF]

/-- Concatenation of 129-bit words; index `0` is the high word and the last
index the low word. -/
def catW : {n : ℕ} → (Fin n → BitVec 129) → BitVec (129 * n)
  | 0, _ => 0
  | _ + 1, a => (a 0 ++ catW fun i => a i.succ).cast (by omega)

def lowWord {w : ℕ} (x : BitVec w) : BitVec 129 := x.setWidth 129
def lowPk {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

abbrev Asg := (v : Fin N) → BitVec (lenF v)

/-- Deterministic node functions.  A hash input puts the exclusive kid in the
low slot. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | Name.ci b k t => tw (Name.ch b k t) ++ lowWord (x (prev b k t).fin)
  | Name.cv b k t => lowWord (x (Name.ch b k t).fin)
  | Name.hc b j => tw (Name.hh b j) ++ catW fun i => lowWord (x ((kid j i).name b).fin)
  | Name.hv b j => lowWord (x (Name.hh b j).fin)
  | Name.rc => tw Name.rh ++ catW fun r => lowWord (x (rootIn r).fin)
  | _ => 0

theorem eq_fin_of_ofFin_eq {v : Fin N} {n : Name} (h : Name.ofFin v = n) : v = n.fin := by
  rw [← h, Name.fin_ofFin]

theorem hash_parent_lt {v : Fin N} {n m : Name} (h : Name.ofFin v = n)
    (hm : m ∈ parents n) : m.fin < v := by
  rw [eq_fin_of_ofFin_eq h]
  exact Name.fin_lt_fin_of_mem_parents hm

theorem det_parents_lt {v : Fin N} {n : Name} (h : Name.ofFin v = n) :
    ∀ w ∈ Name.parentFins n, w < v := by
  intro w hw
  obtain ⟨m, hm, rfl⟩ := Finset.mem_map.1 hw
  exact hash_parent_lt h hm

theorem detVal_local (n : Name) (x y : Asg)
    (hxy : ∀ w ∈ Name.parentFins n, x w = y w) :
    detVal n x = detVal n y := by
  have hp : ∀ m, m ∈ parents n → x m.fin = y m.fin :=
    fun m hm => hxy _ (Name.fin_mem_parentFins hm)
  cases n with
  | ci b k t =>
      show tw (Name.ch b k t) ++ lowWord (x (prev b k t).fin) =
        tw (Name.ch b k t) ++ lowWord (y (prev b k t).fin)
      rw [hp _ (Finset.mem_singleton_self _)]
  | cv b k t =>
      show lowWord (x (Name.ch b k t).fin) = lowWord (y (Name.ch b k t).fin)
      rw [hp _ (Finset.mem_singleton_self _)]
  | hc b j =>
      show tw (Name.hh b j) ++ catW (fun i => lowWord (x ((kid j i).name b).fin)) =
        tw (Name.hh b j) ++ catW (fun i => lowWord (y ((kid j i).name b).fin))
      have he : (fun i => lowWord (x ((kid j i).name b).fin)) =
          fun i => lowWord (y ((kid j i).name b).fin) := by
        funext i
        rw [hp _ ((mem_parents_hc _ b j).2 ⟨i, rfl⟩)]
      rw [he]
  | hv b j =>
      show lowWord (x (Name.hh b j).fin) = lowWord (y (Name.hh b j).fin)
      rw [hp _ (Finset.mem_singleton_self _)]
  | rc =>
      show tw Name.rh ++ catW (fun r => lowWord (x (rootIn r).fin)) =
        tw Name.rh ++ catW (fun r => lowWord (y (rootIn r).fin))
      have he : (fun r => lowWord (x (rootIn r).fin)) =
          fun r => lowWord (y (rootIn r).fin) := by
        funext r
        rw [hp _ ((mem_parents_rc _).2 ⟨r, rfl⟩)]
      rw [he]
  | src _ _ | ch _ _ _ | hh _ _ | rh => rfl

/-! ## `Dag.Graph` instance -/

def kindOf (v : Fin N) : (n : Name) → Name.ofFin v = n → NodeKind N lenF v
  | Name.src _ _, _ => .source
  | Name.ci b k t, h => .det (Name.parentFins (Name.ci b k t))
      (det_parents_lt h)
      (fun x => (detVal (Name.ci b k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.ch b k t, h => .hash (Name.ci b k t).fin
      (hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | Name.cv b k t, h => .det (Name.parentFins (Name.cv b k t))
      (det_parents_lt h)
      (fun x => (detVal (Name.cv b k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.hc b j, h => .det (Name.parentFins (Name.hc b j))
      (det_parents_lt h)
      (fun x => (detVal (Name.hc b j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.hh b j, h => .hash (Name.hc b j).fin
      (hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | Name.hv b j, h => .det (Name.parentFins (Name.hv b j))
      (det_parents_lt h)
      (fun x => (detVal (Name.hv b j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.rc, h => .det (Name.parentFins Name.rc)
      (det_parents_lt h)
      (fun x => (detVal Name.rc x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.rh, h => .hash Name.rc.fin
      (hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)

theorem kindOf_isHash (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    (kindOf v n h).IsHash ↔ n.cost ≠ 0 := by
  cases n <;> simp [kindOf, NodeKind.IsHash, Name.cost]

theorem kindOf_isSource (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    (kindOf v n h).IsSource ↔ ∃ b k, n = .src b k := by
  cases n <;> simp [kindOf, NodeKind.IsSource]

theorem kindOf_parents (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    (kindOf v n h).parents = (parents n).map Name.nameEquiv.toEmbedding := by
  cases n <;> simp [kindOf, NodeKind.parents, Name.parentFins, parents, nameEquiv]

def graph : Graph where
  size := N
  len := lenF
  kind v := kindOf v (Name.ofFin v) rfl
  root := Name.rh.fin
  root_isHash := (kindOf_isHash _ _ rfl).2 (by rw [Name.ofFin_fin]; decide)

theorem graph_kind_eq (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    graph.kind v = kindOf v n h := by subst h; rfl

theorem graph_kind_fin (n : Name) :
    graph.kind n.fin = kindOf n.fin n (Name.ofFin_fin n) := graph_kind_eq _ _ _

@[simp] theorem graph_len_fin (n : Name) : graph.len n.fin = n.len := lenF_fin n

theorem graph_parents_fin (n : Name) :
    (graph.kind n.fin).parents = (parents n).map Name.nameEquiv.toEmbedding := by
  rw [graph_kind_fin]
  exact kindOf_parents _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ b k, n = .src b k := by
  rw [graph_kind_fin]
  exact kindOf_isSource _ _ _

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits]

theorem graph_keygenCost : graph.keygenCost = 820 := by
  show ∑ v : Fin N, graph.nodeCost v = 820
  rw [← Fintype.sum_equiv Name.nameEquiv
    (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v) (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  exact sum_name_cost.trans keygenCost_eq

end OptimalOTS.WeightedConstruction.LongChain91

/-!
# Concrete cut bridge for the cost-87 fused shared-DAG graph

This module connects the combinatorial cuts of `LongChain91Geometry` to the
protected `Dag.Graph` interface.  The visited set of a supported cut is
characterized by name (`VisN`): a block's needed hash values, its expanded
triples, and each needed chain from its disclosure position upward.  From it we
read off the exact reconstruction cost 87, the disclosure size, injectivity of
the codec, the binding rule, and the equal-cost cross-cut witness.
-/

open OracleSpec OracleComp ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Names and graph sets -/

/-- The name/index equivalence, viewed at the graph's definitional size. -/
def graphNameEquiv : Name ≃ Fin graph.size :=
  Name.nameEquiv

def nameEmbedding : Name ↪ Fin graph.size :=
  graphNameEquiv.toEmbedding

@[simp] theorem nameEmbedding_apply (n : Name) : nameEmbedding n = n.fin := rfl

/-- Map a set of concrete names to the corresponding graph vertices. -/
def fins (A : Finset Name) : Finset (Fin graph.size) :=
  A.map nameEmbedding

@[simp] theorem mem_fins_embedding (A : Finset Name) (n : Name) :
    nameEmbedding n ∈ fins A ↔ n ∈ A :=
  Finset.mem_map' nameEmbedding

@[simp] theorem mem_fins_fin (A : Finset Name) (n : Name) :
    n.fin ∈ fins A ↔ n ∈ A :=
  Finset.mem_map' nameEmbedding

/-- Graph parent membership is exactly the concrete input relation. -/
theorem mem_graph_parents_iff (m n : Name) :
    m.fin ∈ (graph.kind n.fin).parents ↔ m ∈ parents n := by
  rw [graph_parents_fin]
  exact Finset.mem_map' _

/-! ## A generic visited characterization -/

theorem kind_parents_lt (G : Graph) {w v : Fin G.size}
    (h : v ∈ (G.kind w).parents) : v < w := by
  generalize G.kind w = k at h
  cases k with
  | source => simp [NodeKind.parents] at h
  | det ps hlt _ _ => exact hlt v h
  | hash p hp _ =>
      simp only [NodeKind.parents, Finset.mem_singleton] at h
      subst h
      exact hp

/-- A predicate containing the root, closed under reading the inputs of an
unrevealed node, and supported from above is exactly `Visited`. -/
theorem visited_iff_of_closed (G : Graph) (A : Finset (Fin G.size))
    (P : Fin G.size → Prop) (hroot : P G.root)
    (hclosed : ∀ w v, P w → w ∉ A → v ∈ (G.kind w).parents → P v)
    (hsupp : ∀ v, P v → v ≠ G.root → ∃ w, P w ∧ w ∉ A ∧ v ∈ (G.kind w).parents)
    (v : Fin G.size) : G.Visited A v ↔ P v := by
  constructor
  · intro h
    induction h with
    | root => exact hroot
    | parent _ hwA hv ih => exact hclosed _ _ ih hwA hv
  · suffices ∀ n, ∀ v : Fin G.size, G.size - v.val = n → P v → G.Visited A v from
      this _ v rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro v hn hv
        by_cases hr : v = G.root
        · subst hr
          exact Graph.Visited.root
        · obtain ⟨w, hw, hwA, hvw⟩ := hsupp v hv hr
          have hlt : v < w := kind_parents_lt G hvw
          have hwlt : w.val < G.size := w.isLt
          have hlt' : v.val < w.val := hlt
          exact Graph.Visited.parent (ih (G.size - w.val) (by omega) w rfl hw) hwA hvw

/-! ## The visited set of a cut -/

/-- Nodes visited when reconstructing from `cutOf c`, by name. -/
def VisN (c : Choice) : Name → Prop
  | .src b k => k ∈ neededC (c b).1 ∧ ((c b).2 k).val = 0
  | .ci b k t => k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ t.val
  | .ch b k t => k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ t.val
  | .cv b k t => k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ t.val + 1
  | .hc b j => j ∈ (c b).1
  | .hh b j => j ∈ (c b).1
  | .hv b j => j ∈ neededH (c b).1
  | .rc => True
  | .rh => True

theorem cv_eq_chainNode (b : Fin 3) (k : Fin 14) (t : Fin 18) :
    Name.cv b k t = chainNode b k t.succ := by
  simp [chainNode]

theorem src_eq_chainNode (b : Fin 3) (k : Fin 14) :
    Name.src b k = chainNode b k 0 := by
  simp [chainNode]

theorem visN_chainNode (c : Choice) (b : Fin 3) (k : Fin 14) (p : Fin 19) :
    VisN c (chainNode b k p) ↔ k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ p.val := by
  unfold chainNode
  split_ifs with hp
  · simp only [VisN, hp]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  · simp only [VisN]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem visN_kid_name (c : Choice) (b : Fin 3) (x : Kid) :
    VisN c (x.name b) ↔ Needed (c b).1 x := by
  cases x with
  | c k =>
      simp only [Kid.name, VisN, mem_neededC]
      have := ((c b).2 k).isLt
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        have h17 : ((17 : Fin 18) : ℕ) = 17 := rfl
        omega
  | h j => simp [Kid.name, VisN]

theorem not_mem_cutOf_of_len {c : Choice} {n : Name} (h : n.len ≠ 129) : n ∉ cutOf c :=
  fun hn => h (cutOf_values c n hn)

theorem cv_mem_cutOf (c : Choice) (b : Fin 3) (k : Fin 14) (t : Fin 18) :
    Name.cv b k t ∈ cutOf c ↔ k ∈ neededC (c b).1 ∧ ((c b).2 k).val = t.val + 1 := by
  rw [cv_eq_chainNode, chainNode_mem_cutOf, Fin.ext_iff, Fin.val_succ]

theorem prev_succ (b : Fin 3) (k : Fin 14) (t : Fin 18) (ht : t.val < 17) :
    prev b k ⟨t.val + 1, by omega⟩ = Name.cv b k t := by
  simp [prev]

theorem visN_closed (c : Choice) (w v : Name) (hw : VisN c w) (hwA : w ∉ cutOf c)
    (hv : v ∈ parents w) : VisN c v := by
  cases w with
  | src b k => simp [parents] at hv
  | ci b k t =>
      rw [parents, Finset.mem_singleton] at hv
      subst hv
      rw [prev_eq_chainNode, visN_chainNode]
      exact hw
  | ch b k t =>
      rw [parents, Finset.mem_singleton] at hv
      subst hv
      exact hw
  | cv b k t =>
      rw [parents, Finset.mem_singleton] at hv
      subst hv
      rw [cv_mem_cutOf] at hwA
      refine ⟨hw.1, ?_⟩
      have := hw.2
      have hne : ¬ ((c b).2 k).val = t.val + 1 := fun h => hwA ⟨hw.1, h⟩
      omega
  | hc b j =>
      obtain ⟨i, rfl⟩ := (mem_parents_hc v b j).1 hv
      exact (visN_kid_name c b _).2 (needed_kid hw i)
  | hh b j =>
      rw [parents, Finset.mem_singleton] at hv
      subst hv
      exact hw
  | hv b j =>
      rw [parents, Finset.mem_singleton] at hv
      subst hv
      rw [hv_mem_cutOf] at hwA
      by_contra hj
      exact hwA ⟨hw, hj⟩
  | rc =>
      obtain ⟨r, rfl⟩ := (mem_parents_rc v).1 hv
      exact top_mem_neededH _ _
  | rh =>
      rw [parents, Finset.mem_singleton] at hv
      subst hv
      trivial

theorem visN_supported (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1) (v : Name)
    (hv : VisN c v) (hr : v ≠ .rh) : ∃ w, VisN c w ∧ w ∉ cutOf c ∧ v ∈ parents w := by
  cases v with
  | src b k =>
      have h2 := hv.2
      refine ⟨.ci b k 0, ⟨hv.1, show _ ≤ (0 : ℕ) by omega⟩,
        not_mem_cutOf_of_len (by simp [Name.len]), ?_⟩
      simp [parents, prev]
  | ci b k t =>
      exact ⟨.ch b k t, hv, not_mem_cutOf_of_len (by simp [Name.len]),
        Finset.mem_singleton_self _⟩
  | ch b k t =>
      refine ⟨.cv b k t, ⟨hv.1, by have := hv.2; omega⟩, ?_, Finset.mem_singleton_self _⟩
      rw [cv_mem_cutOf]
      have := hv.2
      omega
  | cv b k t =>
      by_cases ht : t.val = 17
      · have hn := (mem_neededC _ _).1 hv.1
        rcases hn with ⟨s, h⟩ | ⟨e, he, i, hi⟩
        · cases h
        · refine ⟨.hc b e, he, not_mem_cutOf_of_len (hc_len_ne b e), ?_⟩
          rw [mem_parents_hc]
          refine ⟨i, ?_⟩
          rw [hi]
          simp only [Kid.name]
          congr 1
          exact Fin.ext (by simp [ht])
      · refine ⟨.ci b k ⟨t.val + 1, by omega⟩, ⟨hv.1, hv.2⟩,
          not_mem_cutOf_of_len (by simp [Name.len]), ?_⟩
        rw [parents, Finset.mem_singleton, prev_succ b k t (by omega)]
  | hc b j =>
      exact ⟨.hh b j, hv, not_mem_cutOf_of_len (by simp [Name.len]),
        Finset.mem_singleton_self _⟩
  | hh b j =>
      refine ⟨.hv b j, hvalid b hv, ?_, Finset.mem_singleton_self _⟩
      rw [hv_mem_cutOf]
      exact fun h => h.2 hv
  | hv b j =>
      rcases (mem_neededH _ _).1 hv with ⟨s, h⟩ | ⟨e, he, i, hi⟩
      · cases h
        exact ⟨.rc, trivial, not_mem_cutOf_of_len (by simp [Name.len]),
          (mem_parents_rc _).2 ⟨⟨5 * b.val + s.val, by omega⟩, rootIn_mk b s⟩⟩
      · refine ⟨.hc b e, he, not_mem_cutOf_of_len (hc_len_ne b e), ?_⟩
        rw [mem_parents_hc]
        exact ⟨i, by rw [hi]; rfl⟩
  | rc =>
      exact ⟨.rh, trivial, not_mem_cutOf_of_len (by simp [Name.len]),
        Finset.mem_singleton_self _⟩
  | rh => exact absurd rfl hr

/-- Exact visited set of a cut with valid block shapes. -/
theorem visited_cutOf_iff (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1) (n : Name) :
    graph.Visited (fins (cutOf c)) n.fin ↔ VisN c n := by
  have key := visited_iff_of_closed graph (fins (cutOf c))
    (fun v => VisN c (Name.ofFin v)) ?_ ?_ ?_ n.fin
  · simpa only [Name.ofFin_fin] using key
  · show VisN c (Name.ofFin Name.rh.fin)
    rw [Name.ofFin_fin]
    trivial
  · intro w v hw hwA hvw
    obtain ⟨w', rfl⟩ : ∃ w' : Name, w'.fin = w := ⟨_, Name.fin_ofFin w⟩
    obtain ⟨v', rfl⟩ : ∃ v' : Name, v'.fin = v := ⟨_, Name.fin_ofFin v⟩
    simp only [Name.ofFin_fin] at hw ⊢
    exact visN_closed c w' v' hw ((mem_fins_fin _ _).not.1 hwA)
      ((mem_graph_parents_iff v' w').1 hvw)
  · intro v hv hr
    obtain ⟨v', rfl⟩ : ∃ v' : Name, v'.fin = v := ⟨_, Name.fin_ofFin v⟩
    simp only [Name.ofFin_fin] at hv
    have hr' : v' ≠ .rh := fun h => hr (by subst h; rfl)
    obtain ⟨w, hw, hwA, hvw⟩ := visN_supported c hvalid v' hv hr'
    exact ⟨w.fin, by simpa only [Name.ofFin_fin] using hw,
      (mem_fins_fin _ _).not.2 hwA, (mem_graph_parents_iff v' w).2 hvw⟩

/-! ## Evaluated nodes and cost -/

/-- A concrete name is evaluated exactly when the generic reconstruction
visits it and it is not itself disclosed. -/
def Evaluated (A : Finset Name) (n : Name) : Prop :=
  graph.Visited (fins A) (nameEmbedding n) ∧ n ∉ A

theorem mem_evaluated_iff (A : Finset Name) (n : Name) :
    nameEmbedding n ∈ graph.evaluated (fins A) ↔ Evaluated A n := by
  unfold Graph.evaluated Evaluated
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_fins_embedding]

def evaluatedNames (A : Finset Name) : Finset Name :=
  Finset.univ.filter (Evaluated A)

theorem evaluated_eq_fins (A : Finset Name) :
    graph.evaluated (fins A) = fins (evaluatedNames A) := by
  ext v
  obtain ⟨n, rfl⟩ : ∃ n : Name, nameEmbedding n = v :=
    ⟨graphNameEquiv.symm v, graphNameEquiv.apply_symm_apply v⟩
  rw [mem_evaluated_iff, mem_fins_embedding]
  simp [evaluatedNames]

theorem evaluated_cutOf_iff (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1) (n : Name) :
    Evaluated (cutOf c) n ↔ VisN c n ∧ n ∉ cutOf c := by
  rw [Evaluated, nameEmbedding_apply, visited_cutOf_iff c hvalid]

theorem evaluated_hh_iff (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1)
    (b : Fin 3) (j : Fin 20) : Evaluated (cutOf c) (.hh b j) ↔ j ∈ (c b).1 := by
  rw [evaluated_cutOf_iff c hvalid]
  exact ⟨fun h => h.1, fun h => ⟨h, not_mem_cutOf_of_len (by simp [Name.len])⟩⟩

theorem evaluated_ch_iff (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1)
    (b : Fin 3) (k : Fin 14) (t : Fin 18) : Evaluated (cutOf c) (.ch b k t) ↔
      k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ t.val := by
  rw [evaluated_cutOf_iff c hvalid]
  exact ⟨fun h => h.1, fun h => ⟨h, not_mem_cutOf_of_len (by simp [Name.len])⟩⟩

theorem evaluated_rh (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1) :
    Evaluated (cutOf c) .rh :=
  (evaluated_cutOf_iff c hvalid _).2 ⟨trivial, not_mem_cutOf_of_len (by simp [Name.len])⟩

/-- The compression charge of each evaluated node. -/
def charge (c : Choice) : Name → ℕ
  | .ch b k t => if k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ t.val then 1 else 0
  | .hh b j => if j ∈ (c b).1 then 1 else 0
  | .rh => 4
  | _ => 0

theorem evaluated_cost_eq_charge (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1)
    (n : Name) : (if Evaluated (cutOf c) n then n.cost else 0) = charge c n := by
  cases n with
  | ch b k t => simp only [evaluated_ch_iff c hvalid, charge, Name.cost]
  | hh b j => simp only [evaluated_hh_iff c hvalid, charge, Name.cost]
  | rh => simp [evaluated_rh c hvalid, charge, Name.cost]
  | src _ _ | ci _ _ _ | cv _ _ _ | hc _ _ | hv _ _ | rc => simp [charge, Name.cost]

/-! Splitting sums over `Name` by constructor. -/

abbrev NameSum :=
  (Fin 3 × Fin 14) ⊕ (Fin 3 × Fin 14 × Fin 18) ⊕ (Fin 3 × Fin 14 × Fin 18) ⊕
    (Fin 3 × Fin 14 × Fin 18) ⊕ (Fin 3 × Fin 20) ⊕ (Fin 3 × Fin 20) ⊕
      (Fin 3 × Fin 20) ⊕ Unit ⊕ Unit

def Name.ofSum : NameSum → Name
  | .inl (b, k) => .src b k
  | .inr (.inl (b, k, t)) => .ci b k t
  | .inr (.inr (.inl (b, k, t))) => .ch b k t
  | .inr (.inr (.inr (.inl (b, k, t)))) => .cv b k t
  | .inr (.inr (.inr (.inr (.inl (b, j))))) => .hc b j
  | .inr (.inr (.inr (.inr (.inr (.inl (b, j)))))) => .hh b j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (b, j))))))) => .hv b j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))) => .rc
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))) => .rh

def Name.toSum : Name → NameSum
  | .src b k => .inl (b, k)
  | .ci b k t => .inr (.inl (b, k, t))
  | .ch b k t => .inr (.inr (.inl (b, k, t)))
  | .cv b k t => .inr (.inr (.inr (.inl (b, k, t))))
  | .hc b j => .inr (.inr (.inr (.inr (.inl (b, j)))))
  | .hh b j => .inr (.inr (.inr (.inr (.inr (.inl (b, j))))))
  | .hv b j => .inr (.inr (.inr (.inr (.inr (.inr (.inl (b, j)))))))
  | .rc => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
  | .rh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))))

def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with ⟨b, k⟩ | ⟨b, k, t⟩ | ⟨b, k, t⟩ | ⟨b, k, t⟩ | ⟨b, j⟩ | ⟨b, j⟩ | ⟨b, j⟩ |
      ⟨⟩ | ⟨⟩ <;> rfl

theorem sum_names {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n =
      (∑ b, ∑ k, f (.src b k)) + (∑ b, ∑ k, ∑ t, f (.ci b k t)) +
      (∑ b, ∑ k, ∑ t, f (.ch b k t)) + (∑ b, ∑ k, ∑ t, f (.cv b k t)) +
      (∑ b, ∑ j, f (.hc b j)) + (∑ b, ∑ j, f (.hh b j)) + (∑ b, ∑ j, f (.hv b j)) +
      f .rc + f .rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f
    (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique,
    Name.ofSum, add_assoc]

theorem sum_fin18_ge (v : ℕ) :
    ∑ t : Fin 18, (if v ≤ t.val then 1 else 0) = 18 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 18,
    ← Finset.card_filter]
  have h : (Finset.range 18).filter (fun t => v ≤ t) = Finset.Ico v 18 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h, Nat.card_Ico]

theorem sum_charge (c : Choice) : ∑ n, charge c n = reconstructionCost c := by
  rw [sum_names]
  simp only [charge, Finset.sum_const_zero, zero_add, add_zero]
  have hchain : ∀ b, (∑ k : Fin 14, ∑ t : Fin 18,
      (if k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ t.val then 1 else 0)) =
        localChainCost (c b) := by
    intro b
    have hinner : ∀ k : Fin 14,
        (∑ t : Fin 18,
          (if k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ t.val then 1 else 0)) =
          if k ∈ neededC (c b).1 then 18 - ((c b).2 k).val else 0 := by
      intro k
      by_cases hk : k ∈ neededC (c b).1
      · simp only [hk, true_and, if_true]
        exact sum_fin18_ge _
      · simp [hk]
    simp only [hinner, localChainCost]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hhash : ∀ b, (∑ j : Fin 20, (if j ∈ (c b).1 then 1 else 0)) = (c b).1.card := by
    intro b
    rw [Finset.sum_boole]
    simp
  simp only [hchain, hhash]
  rw [reconstructionCost, choiceCost]
  simp only [localCost, Finset.sum_add_distrib]
  ring

theorem reconstructCost_as_sum (A : Finset Name) :
    graph.reconstructCost (fins A) =
      ∑ n : Name, if Evaluated A n then n.cost else 0 := by
  unfold Graph.reconstructCost
  rw [evaluated_eq_fins]
  refine (Finset.sum_map (evaluatedNames A) nameEmbedding
    graph.nodeCost).trans ?_
  rw [evaluatedNames, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => by
    rw [nameEmbedding_apply, graph_nodeCost_fin]

theorem reconstructCost_cutOf_eq (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1) :
    graph.reconstructCost (fins (cutOf c)) = reconstructionCost c := by
  rw [reconstructCost_as_sum, ← sum_charge]
  exact Finset.sum_congr rfl fun n _ => evaluated_cost_eq_charge c hvalid n

theorem reconstructCost_supported {c : Choice} (hc : c ∈ supportedChoices) :
    graph.reconstructCost (fins (cutOf c)) = 87 :=
  (reconstructCost_cutOf_eq c (shapeValid_of_supported hc)).trans (reconstructionCost_eq hc)

/-! ## Disclosure size -/

theorem revealBits_fins (A : Finset Name) :
    graph.revealBits (fins A) = ∑ n ∈ A, n.len := by
  unfold Graph.revealBits
  refine (Finset.sum_map A nameEmbedding graph.len).trans ?_
  exact Finset.sum_congr rfl fun n _ => by
    rw [nameEmbedding_apply, graph_len_fin]

theorem revealBits_cutOf (c : Choice) :
    graph.revealBits (fins (cutOf c)) = 129 * choiceWords c := by
  rw [revealBits_fins, Finset.sum_congr rfl (cutOf_values c), Finset.sum_const,
    smul_eq_mul, card_cutOf, mul_comm]

/-! ## Codec injectivity -/

theorem cutOf_injOn : Set.InjOn cutOf (supportedChoices : Set Choice) := by
  intro c hc d hd hcut
  have hvc := shapeValid_of_supported hc
  have hvd := shapeValid_of_supported hd
  have hE : ∀ b, (c b).1 = (d b).1 := by
    intro b
    ext j
    rw [← evaluated_hh_iff c hvc, ← evaluated_hh_iff d hvd, hcut]
  funext b
  refine Prod.ext (hE b) (funext fun k => ?_)
  by_cases hk : k ∈ neededC (c b).1
  · have hm : chainNode b k ((c b).2 k) ∈ cutOf d := by
      rw [← hcut]
      exact (chainNode_mem_cutOf c b k _).2 ⟨hk, rfl⟩
    exact ((chainNode_mem_cutOf d b k _).1 hm).2.symm
  · rw [canonical_of_supported hc b k hk,
      canonical_of_supported hd b k (by rwa [← hE b])]

/-! ## Cut families -/

/-- All supported cuts. -/
def fullFamily : Finset (Finset Name) := supportedChoices.image cutOf

theorem card_fullFamily : fullFamily.card = supportedChoices.card :=
  Finset.card_image_of_injOn cutOf_injOn

theorem K91_le_card_fullFamily : K91 ≤ fullFamily.card := by
  rw [card_fullFamily]
  exact K91_le_card_supportedChoices

/-- The scheme family: the first `K91` supported cuts. -/
def family : Finset (Finset Name) :=
  Finset.univ.map ⟨selectCut K91_le_card_fullFamily, selectCut_injective _⟩

theorem card_family_exact :
    family.card = 676013856769711926075368867014708 := by
  rw [family, Finset.card_map, Finset.card_univ, Fintype.card_fin, K91]

theorem family_subset_fullFamily : family ⊆ fullFamily := by
  intro A hA
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hA
  exact selectCut_mem _ i

theorem exists_choice_of_mem_family {A : Finset Name} (hA : A ∈ family) :
    ∃ c ∈ supportedChoices, cutOf c = A :=
  Finset.mem_image.1 (family_subset_fullFamily hA)

/-- Semantic cut interface: a supported codec cut. -/
def IsCut (A : Finset Name) : Prop := ∃ c ∈ supportedChoices, cutOf c = A

theorem isCut_of_mem_family {A : Finset Name} (hA : A ∈ family) : IsCut A :=
  exists_choice_of_mem_family hA

theorem IsCut.values {A : Finset Name} (hA : IsCut A) : ∀ n ∈ A, n.len = 129 := by
  obtain ⟨c, _, rfl⟩ := hA
  exact cutOf_values c

theorem visited_of_mem_cutOf (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1)
    {n : Name} (hn : n ∈ cutOf c) : graph.Visited (fins (cutOf c)) n.fin := by
  rw [visited_cutOf_iff c hvalid]
  rcases (mem_cutOf c n).1 hn with ⟨b, j, hj, _, rfl⟩ | ⟨b, k, hk, rfl⟩
  · exact hj
  · exact (visN_chainNode c b k _).2 ⟨hk, le_rfl⟩

/-- Every disclosed value is needed by the reconstruction. -/
theorem IsCut.visited_of_mem {A : Finset Name} (hA : IsCut A) {n : Name} (hn : n ∈ A) :
    graph.Visited (fins A) n.fin := by
  obtain ⟨c, hc, rfl⟩ := hA
  exact visited_of_mem_cutOf c (shapeValid_of_supported hc) hn

/-- A visited source is disclosed. -/
theorem IsCut.src_mem_of_visited {A : Finset Name} (hA : IsCut A) {b : Fin 3} {k : Fin 14}
    (hv : graph.Visited (fins A) (Name.src b k).fin) : Name.src b k ∈ A := by
  obtain ⟨c, hc, rfl⟩ := hA
  have h := (visited_cutOf_iff c (shapeValid_of_supported hc) _).1 hv
  rw [src_eq_chainNode, chainNode_mem_cutOf]
  exact ⟨h.1, Fin.ext h.2⟩

/-! ## Family-level statements consumed by the scheme -/

theorem family_root_not_mem {A : Finset Name} (hA : A ∈ family) :
    graph.root ∉ fins A := by
  obtain ⟨c, _, rfl⟩ := exists_choice_of_mem_family hA
  change Name.rh.fin ∉ fins (cutOf c)
  rw [mem_fins_fin]
  exact not_mem_cutOf_of_len (by simp [Name.len])

theorem family_no_hidden_source {A : Finset Name} (hA : A ∈ family) :
    ∀ v, graph.Visited (fins A) v → v ∉ fins A →
      ¬ (graph.kind v).IsSource := by
  intro v hv hvA hs
  obtain ⟨n, rfl⟩ : ∃ n : Name, n.fin = v := ⟨Name.ofFin v, Name.fin_ofFin v⟩
  obtain ⟨b, k, rfl⟩ := (graph_isSource_fin n).mp hs
  exact hvA ((mem_fins_fin _ _).2 ((isCut_of_mem_family hA).src_mem_of_visited hv))

theorem family_reconstructCost_eq {A : Finset Name} (hA : A ∈ family) :
    graph.reconstructCost (fins A) = 87 := by
  obtain ⟨c, hc, rfl⟩ := exists_choice_of_mem_family hA
  exact reconstructCost_supported hc

theorem family_reconstructCost {A : Finset Name} (hA : A ∈ family) :
    graph.reconstructCost (fins A) ≤ 87 :=
  (family_reconstructCost_eq hA).le

theorem family_disclosure_and_nonce {A : Finset Name} (hA : A ∈ family) :
    graph.revealBits (fins A) + 86 ≤ 5504 := by
  obtain ⟨c, hc, rfl⟩ := exists_choice_of_mem_family hA
  rw [revealBits_cutOf]
  have := choiceWords_le hc
  omega

theorem family_revealBits_pos {A : Finset Name} (hA : A ∈ family) :
    0 < graph.revealBits (fins A) := by
  obtain ⟨c, hc, rfl⟩ := exists_choice_of_mem_family hA
  rw [revealBits_cutOf]
  have h0 : 1 ≤ localWords (c 0) :=
    shapeWords_pos _ ((mem_validShapes _).2 (shapeValid_of_supported hc 0))
  have : localWords (c 0) ≤ choiceWords c :=
    Finset.single_le_sum (f := fun b => localWords (c b)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ 0)
  omega

/-! ## Binding rule and equal-cost cross-cut witness -/

/-- Binding rule: the exclusive (last-slot) kid of every unexpanded hash node
is outside the needed set, hence neither visited nor disclosed. -/
theorem binding_rule (c : Choice) (hvalid : ∀ b, ShapeValid (c b).1) (b : Fin 3)
    (j : Fin 20) (hj : j ∉ (c b).1) :
    ¬ graph.Visited (fins (cutOf c)) ((kid j 2).name b).fin ∧
      (kid j 2).name b ∉ cutOf c := by
  have hnv : ¬ graph.Visited (fins (cutOf c)) ((kid j 2).name b).fin := by
    rw [visited_cutOf_iff c hvalid, visN_kid_name, needed_kid_excl_iff]
    exact hj
  exact ⟨hnv, fun hm => hnv (visited_of_mem_cutOf c hvalid hm)⟩

/-- Equal cost forces incomparability: distinct supported cuts have a hash node
evaluated under the second but not the first, whose 129-bit input value is not
visited (so hidden) under the first. -/
theorem exists_hidden_of_ne {c d : Choice} (hc : c ∈ supportedChoices)
    (hd : d ∈ supportedChoices) (hne : cutOf c ≠ cutOf d) :
    ∃ u, Evaluated (cutOf d) u ∧ ¬ Evaluated (cutOf c) u ∧ u.cost ≠ 0 ∧
      ∃ q ∈ parents u, ∃ w ∈ parents q, w.len = 129 ∧
        ¬ graph.Visited (fins (cutOf c)) w.fin := by
  have hvc := shapeValid_of_supported hc
  have hvd := shapeValid_of_supported hd
  obtain ⟨u, hud, huc, hu⟩ : ∃ u, Evaluated (cutOf d) u ∧ ¬ Evaluated (cutOf c) u ∧
      u.cost ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let f : Choice → Name → ℕ := fun x n => if Evaluated (cutOf x) n then n.cost else 0
    have hle : ∀ n ∈ (Finset.univ : Finset Name), f d n ≤ f c n := by
      intro n _
      simp only [f]
      by_cases h : Evaluated (cutOf d) n
      · by_cases hcn : Evaluated (cutOf c) n
        · rw [if_pos h, if_pos hcn]
        · rw [if_pos h, if_neg hcn, hcon n h hcn]
      · rw [if_neg h]
        exact Nat.zero_le _
    have hsum : ∑ n, f d n = ∑ n, f c n := by
      simp only [f]
      rw [← reconstructCost_as_sum, ← reconstructCost_as_sum,
        reconstructCost_supported hc, reconstructCost_supported hd]
    have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum
    have hiff : ∀ n, n.cost ≠ 0 → (Evaluated (cutOf d) n ↔ Evaluated (cutOf c) n) := by
      intro n h0
      have := heq n (Finset.mem_univ _)
      simp only [f] at this
      constructor
      · intro hdn
        by_contra hcn
        rw [if_pos hdn, if_neg hcn] at this
        exact h0 this
      · intro hcn
        by_contra hdn
        rw [if_neg hdn, if_pos hcn] at this
        exact h0 this.symm
    have hE : ∀ b, (d b).1 = (c b).1 := by
      intro b
      ext j
      rw [← evaluated_hh_iff d hvd, ← evaluated_hh_iff c hvc]
      exact hiff _ (by simp [Name.cost])
    have hpos : ∀ b k, (d b).2 k = (c b).2 k := by
      intro b k
      by_cases hk : k ∈ neededC (c b).1
      · have hkd : k ∈ neededC (d b).1 := by rwa [hE b]
        have ht : ∀ t : Fin 18, ((d b).2 k).val ≤ t.val ↔ ((c b).2 k).val ≤ t.val := by
          intro t
          have h := hiff (.ch b k t) (by simp [Name.cost])
          rw [evaluated_ch_iff d hvd, evaluated_ch_iff c hvc] at h
          constructor
          · intro hle
            exact (h.1 ⟨hkd, hle⟩).2
          · intro hle
            exact (h.2 ⟨hk, hle⟩).2
        apply Fin.ext
        by_contra hpq
        rcases Nat.lt_or_gt_of_ne hpq with h | h
        · have h19 := ((c b).2 k).isLt
          have := (ht ⟨((d b).2 k).val, by omega⟩).1 le_rfl
          exact absurd this (by show ¬ ((c b).2 k).val ≤ ((d b).2 k).val; omega)
        · have h19 := ((d b).2 k).isLt
          have := (ht ⟨((c b).2 k).val, by omega⟩).2 le_rfl
          exact absurd this (by show ¬ ((d b).2 k).val ≤ ((c b).2 k).val; omega)
      · rw [canonical_of_supported hc b k hk,
          canonical_of_supported hd b k (by rwa [hE b])]
    have hcd : d = c := by
      funext b
      exact Prod.ext (hE b) (funext fun k => hpos b k)
    exact hne (by rw [hcd])
  refine ⟨u, hud, huc, hu, ?_⟩
  cases u with
  | hh b j =>
      have hjd := (evaluated_hh_iff d hvd b j).1 hud
      have hjc : j ∉ (c b).1 := fun h => huc ((evaluated_hh_iff c hvc b j).2 h)
      refine ⟨.hc b j, Finset.mem_singleton_self _, (kid j 2).name b,
        (mem_parents_hc _ b j).2 ⟨2, rfl⟩, ?_, (binding_rule c hvc b j hjc).1⟩
      cases kid j 2 <;> rfl
  | ch b k t =>
      have hcn : ¬ (k ∈ neededC (c b).1 ∧ ((c b).2 k).val ≤ t.val) :=
        fun h => huc ((evaluated_ch_iff c hvc b k t).2 h)
      refine ⟨.ci b k t, Finset.mem_singleton_self _, prev b k t,
        Finset.mem_singleton_self _, ?_, ?_⟩
      · rw [prev_eq_chainNode]
        exact chainNode_len _ _ _
      · rw [visited_cutOf_iff c hvc, prev_eq_chainNode, visN_chainNode]
        simpa using hcn
  | rh => exact absurd (evaluated_rh c hvc) huc
  | src _ _ | ci _ _ _ | cv _ _ _ | hc _ _ | hv _ _ | rc => simp [Name.cost] at hu

end OptimalOTS.WeightedConstruction.LongChain91
