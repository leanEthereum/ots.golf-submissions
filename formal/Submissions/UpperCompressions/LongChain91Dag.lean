import Submissions.UpperCompressions.LongChain91Geometry
import Submissions.UpperCompressions.ProofBundle03

/-!
# Concrete DAG for the cost-89 fused shared-DAG construction

This module turns the names of `LongChain91Geometry` into the `Dag.Graph`
consumed by the generic weighted scheme: seven blocks of eight length-18 chains
and eleven ternary hashes with shared inputs, under a seven-word root hash.
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
  if h₀ : v.val < 56 then .src ⟨v.val / 8, by omega⟩ ⟨v.val % 8, by omega⟩
  else if h₁ : v.val < 3080 then
    let m := v.val - 56
    let t : Fin 18 := ⟨m / 168, by omega⟩
    let r := m % 168
    if h₂ : r < 56 then .ci ⟨r / 8, by omega⟩ ⟨r % 8, by omega⟩ t
    else if h₃ : r < 112 then .ch ⟨(r - 56) / 8, by omega⟩ ⟨(r - 56) % 8, by omega⟩ t
    else .cv ⟨(r - 112) / 8, by omega⟩ ⟨(r - 112) % 8, by omega⟩ t
  else if h₄ : v.val < 3311 then
    let m := v.val - 3080
    let b : Fin 7 := ⟨m / 33, by omega⟩
    let j : Fin 11 := ⟨m % 33 / 3, by omega⟩
    if m % 3 = 0 then .hc b j
    else if m % 3 = 1 then .hh b j
    else .hv b j
  else if h₅ : v.val < 3312 then .rc
  else .rh

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 3313 := v.isLt
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
  | .rc => Finset.univ.image fun b : Fin 7 => .hv b 10
  | .rh => {.rc}

@[simp] theorem mem_parents_hc (m : Name) (b : Fin 7) (j : Fin 11) :
    m ∈ parents (.hc b j) ↔ ∃ i, (kid j i).name b = m := by
  simp [parents]

@[simp] theorem mem_parents_rc (m : Name) :
    m ∈ parents .rc ↔ ∃ b, Name.hv b 10 = m := by
  simp [parents]

theorem kid_name_idx_lt (b : Fin 7) (j : Fin 11) (i : Fin 3) :
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
      obtain ⟨b, rfl⟩ := (mem_parents_rc m).1 h
      simp only [idx]
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

theorem tw_injective : Function.Injective tw := by
  intro h h' e
  apply Name.idx_injective
  rw [← tw_toNat h, ← tw_toNat h', e]

def lenF (v : Fin N) : ℕ := (Name.ofFin v).len

@[simp] theorem lenF_fin (n : Name) : lenF n.fin = n.len := by simp [lenF]

def cat3 (a b c : BitVec 129) : BitVec 387 := (a ++ b ++ c).cast (by norm_num)

def cat7 (a : Fin 7 → BitVec 129) : BitVec 903 :=
  (a 0 ++ a 1 ++ a 2 ++ a 3 ++ a 4 ++ a 5 ++ a 6).cast (by norm_num)

def lowWord {w : ℕ} (x : BitVec w) : BitVec 129 := x.setWidth 129
def lowPk {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

abbrev Asg := (v : Fin N) → BitVec (lenF v)

/-- Deterministic node functions.  A ternary input puts the exclusive kid in
the low slot. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | Name.ci b k t => tw (Name.ch b k t) ++ lowWord (x (prev b k t).fin)
  | Name.cv b k t => lowWord (x (Name.ch b k t).fin)
  | Name.hc b j => tw (Name.hh b j) ++ cat3
      (lowWord (x ((kid j 0).name b).fin))
      (lowWord (x ((kid j 1).name b).fin))
      (lowWord (x ((kid j 2).name b).fin))
  | Name.hv b j => lowWord (x (Name.hh b j).fin)
  | Name.rc => tw Name.rh ++ cat7 fun b => lowWord (x (Name.hv b 10).fin)
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
      show tw (Name.hh b j) ++ cat3
          (lowWord (x ((kid j 0).name b).fin))
          (lowWord (x ((kid j 1).name b).fin))
          (lowWord (x ((kid j 2).name b).fin)) =
        tw (Name.hh b j) ++ cat3
          (lowWord (y ((kid j 0).name b).fin))
          (lowWord (y ((kid j 1).name b).fin))
          (lowWord (y ((kid j 2).name b).fin))
      have hk (i : Fin 3) : (kid j i).name b ∈ parents (Name.hc b j) :=
        (mem_parents_hc _ b j).2 ⟨i, rfl⟩
      rw [hp _ (hk 0), hp _ (hk 1), hp _ (hk 2)]
  | hv b j =>
      show lowWord (x (Name.hh b j).fin) = lowWord (y (Name.hh b j).fin)
      rw [hp _ (Finset.mem_singleton_self _)]
  | rc =>
      show tw Name.rh ++ cat7 (fun b => lowWord (x (Name.hv b 10).fin)) =
        tw Name.rh ++ cat7 (fun b => lowWord (y (Name.hv b 10).fin))
      have he : (fun b => lowWord (x (Name.hv b 10).fin)) =
          fun b => lowWord (y (Name.hv b 10).fin) := by
        funext b
        rw [hp _ ((mem_parents_rc _).2 ⟨b, rfl⟩)]
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

def publicKey (x : graph.Assignment) : PublicKey := lowPk (x graph.root)

theorem graph_kind_eq (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    graph.kind v = kindOf v n h := by subst h; rfl

theorem graph_kind_fin (n : Name) :
    graph.kind n.fin = kindOf n.fin n (Name.ofFin_fin n) := graph_kind_eq _ _ _

@[simp] theorem graph_len_fin (n : Name) : graph.len n.fin = n.len := lenF_fin n

theorem graph_parents_fin (n : Name) :
    (graph.kind n.fin).parents = (parents n).map Name.nameEquiv.toEmbedding := by
  rw [graph_kind_fin]
  exact kindOf_parents _ _ _

theorem graph_isHash_fin (n : Name) : (graph.kind n.fin).IsHash ↔ n.cost ≠ 0 := by
  rw [graph_kind_fin]
  exact kindOf_isHash _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ b k, n = .src b k := by
  rw [graph_kind_fin]
  exact kindOf_isSource _ _ _

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits]

theorem graph_keygenCost : graph.keygenCost = 1087 := by
  show ∑ v : Fin N, graph.nodeCost v = 1087
  rw [← Fintype.sum_equiv Name.nameEquiv
    (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v) (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  exact sum_name_cost.trans keygenCost_eq

theorem hash_output_width (n : Name) (hn : n.cost ≠ 0) : n.len = 256 := by
  cases n <;> simp [Name.cost] at hn <;> rfl

/-- Every hash input (chain stage, ternary compress input, root input) avoids
the 342-bit index query length. -/
theorem graph_hash_input_length_ne_index {p h : Name}
    (hp : p ∈ parents h) (hh : h.cost ≠ 0) : p.len ≠ 342 := by
  cases h <;> simp [Name.cost] at hh <;> simp [parents] at hp <;> subst hp <;>
    simp [Name.len]

theorem input_costs :
    blockCost 145 = 1 ∧ blockCost 403 = 1 ∧ blockCost 919 = 2 := by
  norm_num [blockCost, blockBits]

#print axioms graph_keygenCost
#print axioms hash_output_width
#print axioms input_costs

end OptimalOTS.WeightedConstruction.LongChain91
