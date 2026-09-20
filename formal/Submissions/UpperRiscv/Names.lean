import OptimalOTS.Dag
import Submissions.UpperRiscv.Semantics

/-!
# The bare-chain scheme: nodes and the computation graph

The scheme has 28 hash chains of 32 hash steps and a root over the 28 full chain tops. Every hash
node outputs 256 bits; the 192-bit chain values are separate deterministic truncation nodes and are
the bare inputs of the next hash node: there are no headers or level tags. The random oracle has no
labels; the three input lengths (192 for chains, 384 for the index, 5440 for the root) are
distinct, and distinct chain nodes are told apart by their values only.

| name | meaning | length | kind |
|---|---|---|---|
| `src k` | source `z_k` | 192 | source |
| `ci k t` | `c_{k,t}`: `z_k` for `t = 0`, else the low 192 bits of `cv k (t-1)` | 192 | det |
| `ch k t` | `H(c_{k,t})` | 256 | hash, parent `ci k t` |
| `cv k t` | `ch k t` again (the value node read by the next level or the root) | 256 | det |
| `rc` | `rootCat` of the 28 tops `cv k 31` | 5440 | det |
| `rh` | the root `H(rc)` | 256 | hash |

The root input is the memory region left by the machine: the full 256-bit top of chain `0`, then
the high 192 bits of every further top (`rootCat`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace Forest

/-- Node names. -/
inductive Name where
  | src (k : Fin 28)
  | ci (k : Fin 28) (t : Fin 32)
  | ch (k : Fin 28) (t : Fin 32)
  | cv (k : Fin 28) (t : Fin 32)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 2718

namespace Name

/-- Topological index. Chain `k` occupies `97 k, …, 97 k + 96`: its source, then input, hash and
value of each of its 32 levels. -/
def idx : Name → ℕ
  | src k => 97 * k
  | ci k t => 97 * k + 1 + 3 * t
  | ch k t => 97 * k + 2 + 3 * t
  | cv k t => 97 * k + 3 + 3 * t
  | rc => 2716
  | rh => 2717

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src _ => 192
  | ci _ _ => 192
  | ch _ _ => 256
  | cv _ _ => 256
  | rc => 5440
  | rh => 256

/-- Query cost of a node: one compression for every chain hash, eleven for the root. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | rh => 11
  | _ => 0

/-- The value node feeding the chain input `ci k t`: the source for `t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 28) (t : Fin 32) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ci k 0)
  | ci k t => some (ch k t)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 31 then some rc else some (ci k ⟨t + 1, by omega⟩)
  | rc => some rh
  | rh => none

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ci k t => {prev k t}
  | ch k t => {ci k t}
  | cv k t => {ch k t}
  | rc => Finset.univ.image fun k => cv k 31
  | rh => {rc}

theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  cases n <;> cases m <;>
    simp only [parents, child, prev, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.notMem_empty, Option.some.injEq,
      reduceCtorEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Fin.ext_iff,
      Fin.val_zero, iff_true, iff_false, false_iff, or_false, exists_false] <;>
    (try split_ifs) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Name.src.injEq, Name.ci.injEq,
      Name.cv.injEq, Fin.ext_iff, iff_false, false_iff, not_false_eq_true]) <;>
    first | omega | exact ⟨_, rfl⟩ | (constructor <;> intro h <;> first | trivial | omega | (obtain ⟨_, h1, h2⟩ := h; omega) | exact ⟨_, rfl, by omega⟩)

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  rw [mem_parents_iff] at h
  cases m <;> simp only [child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;> subst h <;>
    simp only [idx, Fin.val_zero] <;> omega

end Name

/-- The inverse of `Name.fin`. -/
def ofFin (v : Fin N) : Name :=
  if h₁ : v.val < 2716 then
    let k : Fin 28 := ⟨v.val / 97, by omega⟩
    let r := v.val % 97
    if h₂ : r = 0 then .src k
    else
      let t : Fin 32 := ⟨(r - 1) / 3, by omega⟩
      if h₃ : (r - 1) % 3 = 0 then .ci k t
      else if h₃' : (r - 1) % 3 = 1 then .ch k t
      else .cv k t
  else if h₁₀ : v.val < 2717 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Fin.ext_iff,
      reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 2718 := v.isLt
  rw [Fin.ext_iff]
  simp only [ofFin]
  split_ifs <;> simp only [Name.fin, Name.idx] <;> omega

theorem ofFin_fin (n : Name) : ofFin n.fin = n :=
  Name.idx_injective (congrArg Fin.val (fin_ofFin_aux n.fin))

theorem fin_ofFin (v : Fin N) : (ofFin v).fin = v := fin_ofFin_aux v

def nameEquiv : Name ≃ Fin N where
  toFun := Name.fin
  invFun := ofFin
  left_inv := ofFin_fin
  right_inv := fin_ofFin

theorem Name.fin_injective : Function.Injective Name.fin := nameEquiv.injective

abbrev NameSum := Fin 28 ⊕ (Fin 28 × Fin 32) ⊕ (Fin 28 × Fin 32) ⊕ (Fin 28 × Fin 32) ⊕
  Unit ⊕ Unit

def Name.toSum : Name → NameSum
  | src k => .inl k
  | ci k t => .inr (.inl (k, t))
  | ch k t => .inr (.inr (.inl (k, t)))
  | cv k t => .inr (.inr (.inr (.inl (k, t))))
  | rc => .inr (.inr (.inr (.inr (.inl ()))))
  | rh => .inr (.inr (.inr (.inr (.inr ()))))

def Name.ofSum : NameSum → Name
  | .inl k => src k
  | .inr (.inl (k, t)) => ci k t
  | .inr (.inr (.inl (k, t))) => ch k t
  | .inr (.inr (.inr (.inl (k, t)))) => cv k t
  | .inr (.inr (.inr (.inr (.inl ())))) => rc
  | .inr (.inr (.inr (.inr (.inr ())))) => rh

def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | ⟨k, t⟩ | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ci k t)) + (∑ k, ∑ t, f (ch k t)) +
      (∑ k, ∑ t, f (cv k t)) + f rc + f rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## The root input

The machine runs the chains from `0` up to `27`, hashing each 192-bit value at its slot with the
32-byte answer written eight bytes below the slot: the high 192 bits of the answer land on the slot
and feed the next step, and the low eight bytes overwrite the tail of the previous, already final,
top. The 680-byte region from eight bytes below chain `0`'s slot then holds the low 192 bits of
every top and the full top of chain `27`. -/

/-- The low 192 bits of a top. -/
def lo192 (x : BitVec 256) : BitVec 192 := x.setWidth 192

/-- The low 192 bits of the tops of chains `0 … j`: `lo192 (c j) ‖ ⋯ ‖ lo192 (c 0)`, with
`c 0` in the low bits, as the tops lie in memory. -/
def lowCat (c : ℕ → BitVec 256) : (j : ℕ) → BitVec (192 * (j + 1))
  | 0 => lo192 (c 0)
  | j + 1 => (lo192 (c (j + 1)) ++ lowCat c j).cast (by omega)

/-- The chain tops as a function on naturals. -/
def topFun (c : Fin 28 → BitVec 256) (j : ℕ) : BitVec 256 := if h : j < 28 then c ⟨j, h⟩ else 0

/-- The root input: the full top of chain `27` above the low 192 bits of the other tops. -/
def rootCat (c : Fin 28 → BitVec 256) : BitVec 5440 :=
  (c 27 ++ lowCat (topFun c) 26).cast (by norm_num)

/-! ## The graph -/

def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- The chain value carried by a node: its top 192 bits (all of a 192-bit value, the high 192
bits of a 256-bit hash output). -/
def trunc {w : ℕ} (x : BitVec w) : BitVec 192 := x.extractLsb' (w - 192) 192

abbrev Asg := (v : Fin N) → BitVec (lenF v)

theorem lenF_ch (k : Fin 28) (t : Fin 32) : lenF (Name.ch k t).fin = (Name.cv k t).len := lenF_fin _

/-- The deterministic value of a node, as a function of the assignment. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .ci k t => trunc (x (Name.prev k t).fin)
  | .cv k t => (x (Name.ch k t).fin).cast (lenF_ch k t)
  | .rc => rootCat fun k => (x (Name.cv k 31).fin).cast (lenF_fin _)
  | _ => 0

theorem detVal_ci (k : Fin 28) (t : Fin 32) (x : Asg) :
    detVal (.ci k t) x = trunc (x (Name.prev k t).fin) := rfl

theorem detVal_cv (k : Fin 28) (t : Fin 32) (x : Asg) :
    detVal (.cv k t) x = (x (Name.ch k t).fin).cast (lenF_ch k t) := rfl

theorem detVal_rc (x : Asg) :
    detVal .rc x = rootCat fun k => (x (Name.cv k 31).fin).cast (lenF_fin _) := rfl

theorem eq_fin_of_ofFin_eq {v : Fin N} {n : Name} (h : ofFin v = n) : v = n.fin := by
  rw [← h, fin_ofFin]

theorem Name.fin_lt_fin_of_mem_parents {m n : Name} (h : m ∈ Name.parents n) : m.fin < n.fin :=
  Name.idx_lt_of_mem_parents h

theorem hash_parent_lt {v : Fin N} {n m : Name} (h : ofFin v = n) (hm : m ∈ Name.parents n) :
    m.fin < v := by
  rw [eq_fin_of_ofFin_eq h]
  exact Name.fin_lt_fin_of_mem_parents hm

theorem det_parents_lt {v : Fin N} {n : Name} (h : ofFin v = n) :
    ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, w < v := by
  intro w hw
  rw [Finset.mem_map] at hw
  obtain ⟨m, hm, rfl⟩ := hw
  exact hash_parent_lt h hm

theorem detVal_local (n : Name) (x y : Asg)
    (hxy : ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, x w = y w) :
    detVal n x = detVal n y := by
  have key : ∀ m ∈ Name.parents n, x m.fin = y m.fin := fun m hm =>
    hxy m.fin (Finset.mem_map_of_mem _ hm)
  cases n with
  | ci k t =>
    show trunc (x (Name.prev k t).fin) = trunc (y (Name.prev k t).fin)
    rw [key (Name.prev k t) (by simp [Name.parents])]
  | cv k t =>
    show (x (Name.ch k t).fin).cast (lenF_ch k t) = (y (Name.ch k t).fin).cast (lenF_ch k t)
    rw [key (Name.ch k t) (by simp [Name.parents])]
  | rc =>
    show rootCat (fun k => (x (Name.cv k 31).fin).cast (lenF_fin _)) =
      rootCat (fun k => (y (Name.cv k 31).fin).cast (lenF_fin _))
    exact congrArg rootCat (funext fun k => by
      rw [key (Name.cv k 31) (Finset.mem_image_of_mem _ (Finset.mem_univ _))])
  | src _ => rfl
  | ch _ _ => rfl
  | rh => rfl

/-- The kind of the node `v = n.fin`. -/
def kindOf (v : Fin N) : (n : Name) → ofFin v = n → NodeKind N lenF v
  | .src _, _ => .source
  | .ci k t, h => .det ((Name.parents (.ci k t)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.ci k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .ch k t, h => .hash (Name.ci k t).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .cv k t, h => .det ((Name.parents (.cv k t)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.cv k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .rc, h => .det ((Name.parents .rc).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal .rc x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .rh, h => .hash Name.rc.fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)

theorem kindOf_isHash (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsHash ↔ n.cost ≠ 0 := by
  cases n <;> simp [kindOf, NodeKind.IsHash, Name.cost]

theorem kindOf_isSource (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsSource ↔ ∃ k, n = .src k := by
  cases n <;> simp [kindOf, NodeKind.IsSource]

theorem kindOf_parents (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  cases n <;> simp [kindOf, NodeKind.parents, Name.parents, nameEquiv]

/-- The computation graph of the scheme. -/
def graph : Graph where
  size := N
  len := lenF
  kind v := kindOf v (ofFin v) rfl
  root := Name.rh.fin
  root_isHash := (kindOf_isHash _ _ rfl).2 (by rw [ofFin_fin]; decide)

theorem graph_kind_eq (v : Fin N) (n : Name) (h : ofFin v = n) : graph.kind v = kindOf v n h := by
  subst h; rfl

theorem graph_kind_fin (n : Name) : graph.kind n.fin = kindOf n.fin n (ofFin_fin n) :=
  graph_kind_eq _ _ _

theorem graph_len_fin (n : Name) : graph.len n.fin = n.len := lenF_fin n

theorem graph_parents_fin (n : Name) :
    (graph.kind n.fin).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  rw [graph_kind_fin]; exact kindOf_parents _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ k, n = .src k := by
  rw [graph_kind_fin]; exact kindOf_isSource _ _ _

theorem Name.len_prev (k : Fin 28) (t : Fin 32) : (Name.prev k t).len = if t.val = 0 then 192 else 256 := by
  unfold Name.prev; split_ifs <;> rfl

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits]

theorem graph_keygenCost : graph.keygenCost = 907 := by
  show ∑ v : Fin N, graph.nodeCost v = 907
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

end Forest

end OptimalOTS
