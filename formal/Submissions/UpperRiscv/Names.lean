import OptimalOTS.Dag
import Submissions.UpperRiscv.Semantics
import Submissions.UpperRiscv.Constants

/-!
# The concrete scheme: nodes and the computation graph

The scheme has 32 hash chains of length 15 and a root over the 32 chain tops. Every hash node
outputs 256 bits; the 128-bit values are separate deterministic truncation nodes, and the inputs
of the hash nodes are separate deterministic nodes.

Nodes are named by `Name`; `Name.fin` embeds the names into `Fin N` in a topological order
(chain by chain, then the root) and `ofFin` is its inverse.

The random oracle has no labels, so the scheme separates its hash nodes itself. The input of the
chain hash `ch k t` is `c_{k,t} ++ hdr k t`: the 64-bit header `hdr k t` (the slot address of
chain `k` and the level tag of `t`, `Flat.hdrNat`) occupies the LOW bits, as it precedes the value
in the machine's memory. The root input is the only input of 6080 bits.

| name | meaning | length | kind |
|---|---|---|---|
| `src k` | source `z_k = c_{k,0}` | 128 | source |
| `ci k t` | `c_{k,t} ++ hdr k t`, the input of `ch k t` | 192 | det, parent `prev k t` |
| `ch k t` | `H(ci k t)` | 256 | hash |
| `cv k t` | `c_{k,t+1}` = low 128 bits of `ch k t` | 128 | det |
| `rc` | `c_{31,15} ‖ h_31 ‖ ⋯ ‖ h_1 ‖ c_{0,15}` (`rootCat`) | 6080 | det |
| `rh` | the root `H(rc)` | 256 | hash |
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

/-- Node names. -/
inductive Name where
  | src (k : Fin 32)
  | ci (k : Fin 32) (t : Fin 15)
  | ch (k : Fin 32) (t : Fin 15)
  | cv (k : Fin 32) (t : Fin 15)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 1474

namespace Name

/-- Topological index. Chains come first, chain by chain: chain `k` occupies the indices
`46 k, …, 46 k + 45` (its source, then input, hash and value of each of its 15 levels). -/
def idx : Name → ℕ
  | src k => 46 * k
  | ci k t => 46 * k + 1 + 3 * t
  | ch k t => 46 * k + 2 + 3 * t
  | cv k t => 46 * k + 3 + 3 * t
  | rc => 1472
  | rh => 1473

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

/-- The index as an element of `Fin N`. -/
def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src _ => 128
  | ci _ _ => 192
  | ch _ _ => 256
  | cv _ _ => 128
  | rc => 6080
  | rh => 256

/-- Query cost of a node: one compression for every chain hash, twelve for the root. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | rh => 12
  | _ => 0

/-- The value node feeding the chain hash `ch k t` (through its input `ci k t`): the source for
`t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 32) (t : Fin 15) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ci k 0)
  | ci k t => some (ch k t)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 14 then some rc else some (ci k ⟨t + 1, by omega⟩)
  | rc => some rh
  | rh => none

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ci k t => {prev k t}
  | ch k t => {ci k t}
  | cv k t => {ch k t}
  | rc => Finset.univ.image fun k => cv k 14
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
  if h₁ : v.val < 1472 then
    let k : Fin 32 := ⟨v.val / 46, by omega⟩
    let r := v.val % 46
    if h₂ : r = 0 then .src k
    else
      let t : Fin 15 := ⟨(r - 1) / 3, by omega⟩
      if h₃ : (r - 1) % 3 = 0 then .ci k t
      else if h₃' : (r - 1) % 3 = 1 then .ch k t
      else .cv k t
  else if h₁₀ : v.val < 1473 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Fin.ext_iff,
      reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 1474 := v.isLt
  rw [Fin.ext_iff]
  simp only [ofFin]
  split_ifs <;> simp only [Name.fin, Name.idx] <;> omega

theorem ofFin_fin (n : Name) : ofFin n.fin = n :=
  Name.idx_injective (congrArg Fin.val (fin_ofFin_aux n.fin))

theorem fin_ofFin (v : Fin N) : (ofFin v).fin = v := fin_ofFin_aux v

/-- Names and indices. -/
def nameEquiv : Name ≃ Fin N where
  toFun := Name.fin
  invFun := ofFin
  left_inv := ofFin_fin
  right_inv := fin_ofFin

theorem Name.fin_injective : Function.Injective Name.fin := nameEquiv.injective

/-- The finite sum type behind `Name`. -/
abbrev NameSum := Fin 32 ⊕ (Fin 32 × Fin 15) ⊕ (Fin 32 × Fin 15) ⊕ (Fin 32 × Fin 15) ⊕
  Unit ⊕ Unit

/-- `Name` as a sum type. -/
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

/-- `Name` is a sum type. -/
def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | ⟨k, t⟩ | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

/-- Sums over names split by constructor. -/
theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ci k t)) + (∑ k, ∑ t, f (ch k t)) +
      (∑ k, ∑ t, f (cv k t)) + f rc + f rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## Headers

The random oracle has no labels: a hash node queries it on its parent's value alone. The scheme
keeps its hash nodes apart by the inputs themselves. A chain input is `c ++ hdr k t`, with the
64-bit header in the LOW bits (`BitVec.append`, whose left argument is the most significant one);
the header is read back by `tagNat` from the low 64 bits of a 192-bit query. The root input is the
only input of 6080 bits. -/

/-- The header of the hash step at level `t` of chain `k`. -/
def hdr (k : Fin 32) (t : Fin 15) : BitVec 64 := BitVec.ofNat 64 (Flat.hdrNat k t)

theorem hdr_toNat (k : Fin 32) (t : Fin 15) : (hdr k t).toNat = Flat.hdrNat k t := by
  rw [hdr, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Flat.hdrNat_lt k t k.isLt)

theorem hdr_injective {k k' : Fin 32} {t t' : Fin 15} (h : hdr k t = hdr k' t') :
    k = k' ∧ t = t' := by
  have e := congrArg BitVec.toNat h
  rw [hdr_toNat, hdr_toNat] at e
  obtain ⟨h1, h2⟩ := Flat.hdrNat_injective k.isLt k'.isLt t.isLt t'.isLt e
  exact ⟨Fin.ext h1, Fin.ext h2⟩

/-- A hash input determines its payload and its header. -/
theorem append_inj {n m : ℕ} {x x' : BitVec n} {y y' : BitVec m} (e : x ++ y = x' ++ y') :
    x = x' ∧ y = y' := by
  constructor
  · have := congrArg (fun z => z.extractLsb' m n) e
    simpa only [BitVec.extractLsb'_append_eq_left] using this
  · have := congrArg (fun z => z.extractLsb' 0 m) e
    simpa only [BitVec.extractLsb'_append_eq_right] using this

/-- Equal chain inputs belong to the same chain hash and have the same payload. -/
theorem hdr_append_inj {k k' : Fin 32} {t t' : Fin 15} {u u' : BitVec 128}
    (e : u ++ hdr k t = u' ++ hdr k' t') : k = k' ∧ t = t' ∧ u = u' :=
  ⟨(hdr_injective (append_inj e).2).1, (hdr_injective (append_inj e).2).2, (append_inj e).1⟩

/-- The chain hash whose header is written in the low 64 bits of a number. -/
def decodeHdr (h : ℕ) : ℕ :=
  if e : ∃ p : Fin 32 × Fin 15, Flat.hdrNat p.1 p.2 = h then (Name.ch e.choose.1 e.choose.2).idx
  else N

theorem decodeHdr_hdrNat (k : Fin 32) (t : Fin 15) :
    decodeHdr (Flat.hdrNat k t) = (Name.ch k t).idx := by
  have e : ∃ p : Fin 32 × Fin 15, Flat.hdrNat p.1 p.2 = Flat.hdrNat k t := ⟨(k, t), rfl⟩
  unfold decodeHdr
  rw [dif_pos e]
  obtain ⟨h1, h2⟩ := Flat.hdrNat_injective e.choose.1.isLt k.isLt e.choose.2.isLt t.isLt
    e.choose_spec
  rw [show e.choose.1 = k from Fin.ext h1, show e.choose.2 = t from Fin.ext h2]

/-- The index of the hash node a query belongs to (`N` when none): the chain hash named by the
header of a 192-bit query, or the root for a 6080-bit query. -/
def tagNat (q : Query) : ℕ :=
  if q.1 = 6080 then Name.rh.idx
  else if q.1 = 192 then decodeHdr (q.2.toNat % 2 ^ 64)
  else N

/-- The header is read back from a chain input. -/
theorem tagNat_hdr_append (k : Fin 32) (t : Fin 15) (u : BitVec 128) :
    tagNat ⟨192, u ++ hdr k t⟩ = (Name.ch k t).idx := by
  unfold tagNat
  simp only [show (192 : ℕ) ≠ 6080 by decide, if_false, if_true]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (hdr k t).isLt, Nat.shiftLeft_eq,
    Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hdr k t).isLt, hdr_toNat,
    decodeHdr_hdrNat]

/-- A 6080-bit query belongs to the root. -/
theorem tagNat_root (u : BitVec 6080) : tagNat ⟨6080, u⟩ = Name.rh.idx := by
  simp [tagNat]

/-- `tagNat` ignores casts. -/
theorem tagNat_cast {n m : ℕ} (e : n = m) (u : BitVec n) :
    tagNat ⟨m, u.cast e⟩ = tagNat ⟨n, u⟩ := by
  subst e; rfl

/-- The header between the values of chains `k - 1` and `k` in the root input: the header after
the last step, whose level tag is zero. -/
def rootHdr (k : ℕ) : BitVec 64 := BitVec.ofNat 64 (Flat.slotAddr k)

/-- The root input over the first `j + 1` chain tops: `c j ‖ h_j ‖ ⋯ ‖ h_1 ‖ c 0`, with `c 0` in
the low bits, as the tops lie in memory. -/
def rootAcc (c : ℕ → BitVec 128) : (j : ℕ) → BitVec (128 + 192 * j)
  | 0 => c 0
  | j + 1 => ((c (j + 1) ++ rootHdr (j + 1)) ++ rootAcc c j).cast (by omega)

/-- The chain tops as a function on naturals. -/
def topFun (c : Fin 32 → BitVec 128) (j : ℕ) : BitVec 128 := if h : j < 32 then c ⟨j, h⟩ else 0

/-- The root input: the 32 chain tops with the headers between them. -/
def rootCat (c : Fin 32 → BitVec 128) : BitVec 6080 := (rootAcc (topFun c) 31).cast (by norm_num)

/-! ## The graph -/

/-- Output lengths, indexed by `Fin N`. -/
def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- The 128-bit truncation. -/
def trunc {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

/-- Assignments of the concrete graph. -/
abbrev Asg := (v : Fin N) → BitVec (lenF v)

/-- The deterministic value of a node, as a function of the assignment (only used for the
deterministic nodes; the function is defined on all names for convenience). -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .ci k t => trunc (x (Name.prev k t).fin) ++ hdr k t
  | .cv k t => trunc (x (Name.ch k t).fin)
  | .rc => rootCat fun k => trunc (x (Name.cv k 14).fin)
  | _ => 0

theorem detVal_ci (k : Fin 32) (t : Fin 15) (x : Asg) :
    detVal (.ci k t) x = trunc (x (Name.prev k t).fin) ++ hdr k t := rfl

theorem detVal_rc (x : Asg) :
    detVal .rc x = rootCat fun k => trunc (x (Name.cv k 14).fin) := rfl

/-- The value of the parent `p` of a hash node `h` carries the tag of `h`. -/
theorem tagNat_detVal {p h : Name} (hc : Name.child p = some h) (hh : h.cost ≠ 0) (x : Asg) :
    tagNat ⟨p.len, detVal p x⟩ = h.idx := by
  cases p with
  | ci k t =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_hdr_append k t _
  | rc =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_root _
  | cv k t =>
    simp only [Name.child] at hc
    split_ifs at hc <;>
      (simp only [Option.some.injEq] at hc; subst hc; exact absurd rfl hh)
  | rh => simp only [Name.child, reduceCtorEq] at hc
  | src k => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | ch k t => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh

/-- The same, for the value as stored in the graph (cast to the length `graph.len p.fin`). -/
theorem tagNat_cast_detVal {p h : Name} (hc : Name.child p = some h) (hh : h.cost ≠ 0) (x : Asg)
    {m : ℕ} (e : p.len = m) : tagNat ⟨m, (detVal p x).cast e⟩ = h.idx := by
  rw [tagNat_cast, tagNat_detVal hc hh]

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
    show trunc (x (Name.prev k t).fin) ++ hdr k t = trunc (y (Name.prev k t).fin) ++ hdr k t
    rw [key (Name.prev k t) (by simp [Name.parents])]
  | cv k t =>
    show trunc (x (Name.ch k t).fin) = trunc (y (Name.ch k t).fin)
    rw [key (Name.ch k t) (by simp [Name.parents])]
  | rc =>
    show rootCat (fun k => trunc (x (Name.cv k 14).fin)) =
      rootCat (fun k => trunc (y (Name.cv k 14).fin))
    have e : (fun k => trunc (x (Name.cv k 14).fin)) = fun k => trunc (y (Name.cv k 14).fin) := by
      funext k
      rw [key (Name.cv k 14) (Finset.mem_image_of_mem _ (Finset.mem_univ _))]
    rw [e]
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

/-- The parents of a node, in the graph. -/
theorem graph_parents_fin (n : Name) :
    (graph.kind n.fin).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  rw [graph_kind_fin]; exact kindOf_parents _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ k, n = .src k := by
  rw [graph_kind_fin]; exact kindOf_isSource _ _ _

theorem Name.len_prev (k : Fin 32) (t : Fin 15) : (Name.prev k t).len = 128 := by
  unfold Name.prev; split_ifs <;> rfl

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits]

theorem graph_keygenCost : graph.keygenCost = 492 := by
  show ∑ v : Fin N, graph.nodeCost v = 492
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

end Forest

end OptimalOTS
