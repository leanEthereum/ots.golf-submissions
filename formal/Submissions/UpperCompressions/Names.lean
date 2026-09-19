import OptimalOTS.Dag
import Submissions.UpperCompressions.Semantics

/-!
# The concrete scheme: nodes and the computation graph

The scheme hangs 54 hash chains of length 14 under a tree with 18 group digests, 6 subtree
digests and a root.  Every hash node outputs 256 bits; the 128-bit values
of the paper are separate deterministic truncation nodes, and the inputs of the grouping hashes
are separate concatenation nodes.

Nodes are named by `Name`; `Name.fin` embeds the names into `Fin N` in a topological order
(parents first) and `ofFin` is its inverse.

The random oracle has no labels, so the scheme separates its hash nodes itself: the input of the
hash node `h` starts with the 16-bit tweak `tw h` (the index of `h`), in the high bits, i.e. it is
`tw h ++ payload`.  The inputs are deterministic nodes of their own.

| name | meaning | length | kind |
|---|---|---|---|
| `src k` | source `z_k = c_{k,0}` | 128 | source |
| `ci k t` | `tw (ch k t) ++ c_{k,t}`, the input of `ch k t` | 144 | det, parent `prev k t` |
| `ch k t` | `H(ci k t)` | 256 | hash |
| `cv k t` | `c_{k,t+1}` = first 128 bits of `ch k t` | 128 | det |
| `gc j` | `tw (gh j) ++ c_{3j,14} ‖ c_{3j+1,14} ‖ c_{3j+2,14}` | 400 | det |
| `gh j` | `H(gc j)` | 256 | hash |
| `gv j` | `g_j` = first 128 bits of `gh j` | 128 | det |
| `ec l` | `tw (eh l) ++ g_{3l} ‖ g_{3l+1} ‖ g_{3l+2}` | 400 | det |
| `eh l` | `H(ec l)` | 256 | hash |
| `ev l` | `e_l` = first 128 bits of `eh l` | 128 | det |
| `rc` | `tw rh ++ e_0 ‖ ⋯ ‖ e_5` | 784 | det |
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
  | src (k : Fin 54)
  | ci (k : Fin 54) (t : Fin 14)
  | ch (k : Fin 54) (t : Fin 14)
  | cv (k : Fin 54) (t : Fin 14)
  | gc (j : Fin 18)
  | gh (j : Fin 18)
  | gv (j : Fin 18)
  | ec (l : Fin 6)
  | eh (l : Fin 6)
  | ev (l : Fin 6)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 2396

namespace Name

/-- Topological index. -/
def idx : Name → ℕ
  | src k => k
  | ci k t => 54 + 162 * t + k
  | ch k t => 108 + 162 * t + k
  | cv k t => 162 + 162 * t + k
  | gc j => 2322 + j
  | gh j => 2340 + j
  | gv j => 2358 + j
  | ec l => 2376 + l
  | eh l => 2382 + l
  | ev l => 2388 + l
  | rc => 2394
  | rh => 2395

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

/-- The index as an element of `Fin N`. -/
def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src _ => 128
  | ci _ _ => 144
  | ch _ _ => 256
  | cv _ _ => 128
  | gc _ => 400
  | gh _ => 256
  | gv _ => 128
  | ec _ => 400
  | eh _ => 256
  | ev _ => 128
  | rc => 784
  | rh => 256

/-- Query cost of a node: one compression for every hash node except the root, which costs two. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | gh _ => 1
  | eh _ => 1
  | rh => 2
  | _ => 0

/-- The value node feeding the chain hash `ch k t` (through its input `ci k t`): the source for
`t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 54) (t : Fin 14) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The `a`-th chain of group `j`. -/
def chainOf (j : Fin 18) (a : Fin 3) : Fin 54 := ⟨3 * j + a, by omega⟩

/-- The `a`-th group of subtree `l`. -/
def groupOf (l : Fin 6) (a : Fin 3) : Fin 18 := ⟨3 * l + a, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ci k 0)
  | ci k t => some (ch k t)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 13 then some (gc ⟨k / 3, by omega⟩) else some (ci k ⟨t + 1, by omega⟩)
  | gc j => some (gh j)
  | gh j => some (gv j)
  | gv j => some (ec ⟨j / 3, by omega⟩)
  | ec l => some (eh l)
  | eh l => some (ev l)
  | ev _ => some rc
  | rc => some rh
  | rh => none

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ci k t => {prev k t}
  | ch k t => {ci k t}
  | cv k t => {ch k t}
  | gc j => {cv (chainOf j 0) 13, cv (chainOf j 1) 13, cv (chainOf j 2) 13}
  | gh j => {gc j}
  | gv j => {gh j}
  | ec l => {gv (groupOf l 0), gv (groupOf l 1), gv (groupOf l 2)}
  | eh l => {ec l}
  | ev l => {eh l}
  | rc => Finset.univ.image ev
  | rh => {rc}

theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  cases n <;> cases m <;>
    simp only [parents, child, prev, chainOf, groupOf, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.notMem_empty, Option.some.injEq,
      reduceCtorEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.gc.injEq, Name.gh.injEq,
      Name.gv.injEq, Name.ec.injEq, Name.eh.injEq, Name.ev.injEq, Fin.ext_iff,
      Fin.val_zero, iff_true, iff_false, false_iff, or_false, exists_false] <;>
    (try split_ifs) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Name.src.injEq, Name.ci.injEq,
      Name.cv.injEq, Name.gc.injEq, Fin.ext_iff, iff_false, false_iff, not_false_eq_true]) <;>
    first | omega | exact ⟨_, rfl⟩

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  rw [mem_parents_iff] at h
  cases m <;> simp only [child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;> (try simp only [Option.some.injEq] at h) <;> subst h <;>
    simp only [idx, Fin.val_zero] <;> omega

end Name

/-- The inverse of `Name.fin`. -/
def ofFin (v : Fin N) : Name :=
  if h₁ : v.val < 54 then .src ⟨v.val, h₁⟩
  else if h₂ : v.val < 2322 then
    let m := v.val - 54
    let t : Fin 14 := ⟨m / 162, by omega⟩
    let r := m % 162
    if h₃ : r < 54 then .ci ⟨r, h₃⟩ t
    else if h₃' : r < 108 then .ch ⟨r - 54, by omega⟩ t
    else .cv ⟨r - 108, by omega⟩ t
  else if h₄ : v.val < 2340 then .gc ⟨v.val - 2322, by omega⟩
  else if h₅ : v.val < 2358 then .gh ⟨v.val - 2340, by omega⟩
  else if h₆ : v.val < 2376 then .gv ⟨v.val - 2358, by omega⟩
  else if h₇ : v.val < 2382 then .ec ⟨v.val - 2376, by omega⟩
  else if h₈ : v.val < 2388 then .eh ⟨v.val - 2382, by omega⟩
  else if h₉ : v.val < 2394 then .ev ⟨v.val - 2388, by omega⟩
  else if h₁₀ : v.val < 2395 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.gc.injEq,
      Name.gh.injEq, Name.gv.injEq, Name.ec.injEq, Name.eh.injEq, Name.ev.injEq, Fin.ext_iff,
      reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 2396 := v.isLt
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
abbrev NameSum := Fin 54 ⊕ (Fin 54 × Fin 14) ⊕ (Fin 54 × Fin 14) ⊕ (Fin 54 × Fin 14) ⊕
  Fin 18 ⊕ Fin 18 ⊕ Fin 18 ⊕ Fin 6 ⊕ Fin 6 ⊕ Fin 6 ⊕ Unit ⊕ Unit

/-- `Name` as a sum type. -/
def Name.toSum : Name → NameSum
  | src k => .inl k
  | ci k t => .inr (.inl (k, t))
  | ch k t => .inr (.inr (.inl (k, t)))
  | cv k t => .inr (.inr (.inr (.inl (k, t))))
  | gc j => .inr (.inr (.inr (.inr (.inl j))))
  | gh j => .inr (.inr (.inr (.inr (.inr (.inl j)))))
  | gv j => .inr (.inr (.inr (.inr (.inr (.inr (.inl j))))))
  | ec l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))
  | eh l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))))
  | ev l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))))
  | rc => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))
  | rh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))))))

def Name.ofSum : NameSum → Name
  | .inl k => src k
  | .inr (.inl (k, t)) => ci k t
  | .inr (.inr (.inl (k, t))) => ch k t
  | .inr (.inr (.inr (.inl (k, t)))) => cv k t
  | .inr (.inr (.inr (.inr (.inl j)))) => gc j
  | .inr (.inr (.inr (.inr (.inr (.inl j))))) => gh j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl j)))))) => gv j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))) => ec l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))) => eh l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))))) => ev l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))))) => rc
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))))))) => rh

/-- `Name` is a sum type. -/
def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | ⟨k, t⟩ | j | j | j | l | l | l | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

/-- Sums over names split by constructor. -/
theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ci k t)) + (∑ k, ∑ t, f (ch k t)) +
      (∑ k, ∑ t, f (cv k t)) +
      (∑ j, f (gc j)) + (∑ j, f (gh j)) + (∑ j, f (gv j)) +
      (∑ l, f (ec l)) + (∑ l, f (eh l)) + (∑ l, f (ev l)) + f rc + f rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## Tweaks

The random oracle has no labels: a hash node queries it on its parent's value alone.  The scheme
keeps its hash nodes apart by starting every hash input with a 16-bit tweak naming the hash node.
Convention: the tweak occupies the HIGH bits, i.e. the input of the hash node `h` is
`tw h ++ payload` (`BitVec.append`, whose left argument is the most significant one).  The
payload is recovered by `setWidth`/`extractLsb' 0`, the tweak by `extractLsb' n 16` or
`tagNat`. -/

/-- The tweak of the hash node `h`: its topological index, on 16 bits. -/
def tw (h : Name) : BitVec 16 := BitVec.ofNat 16 h.idx

theorem tw_toNat (h : Name) : (tw h).toNat = h.idx := by
  have := h.idx_lt
  unfold N at this
  rw [tw, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem tw_injective : Function.Injective tw := by
  intro h h' e
  apply Name.idx_injective
  rw [← tw_toNat h, ← tw_toNat h', e]

/-- A hash input determines its tweak and its payload. -/
theorem append_inj {n : ℕ} {a a' : BitVec 16} {u u' : BitVec n} (e : a ++ u = a' ++ u') :
    a = a' ∧ u = u' := by
  constructor
  · have := congrArg (fun z => z.extractLsb' n 16) e
    simpa only [BitVec.extractLsb'_append_eq_left] using this
  · have := congrArg (fun z => z.extractLsb' 0 n) e
    simpa only [BitVec.extractLsb'_append_eq_right] using this

/-- Equal hash inputs (of one length) belong to the same hash node and have the same payload. -/
theorem tw_append_inj {n : ℕ} {h h' : Name} {u u' : BitVec n} (e : tw h ++ u = tw h' ++ u') :
    h = h' ∧ u = u' :=
  ⟨tw_injective (append_inj e).1, (append_inj e).2⟩

/-- The number written in the 16 high bits of a query. -/
def tagNat (q : Query) : ℕ := q.2.toNat / 2 ^ (q.1 - 16)

theorem tagNat_append {n : ℕ} (a : BitVec 16) (u : BitVec n) :
    tagNat ⟨16 + n, a ++ u⟩ = a.toNat := by
  unfold tagNat
  simp only [BitVec.toNat_append, Nat.add_sub_cancel_left]
  rw [← Nat.shiftLeft_add_eq_or_of_lt u.isLt, Nat.shiftLeft_eq, Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt u.isLt, Nat.zero_add]

/-- The tweak is read back from a hash input. -/
theorem tagNat_tw_append {n : ℕ} (h : Name) (u : BitVec n) :
    tagNat ⟨16 + n, tw h ++ u⟩ = h.idx := by
  rw [tagNat_append, tw_toNat]

/-- `tagNat` ignores casts. -/
theorem tagNat_cast {n m : ℕ} (e : n = m) (u : BitVec n) :
    tagNat ⟨m, u.cast e⟩ = tagNat ⟨n, u⟩ := by
  subst e; rfl

/-! ## The graph -/

/-- Output lengths, indexed by `Fin N`. -/
def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- Concatenation of three 128-bit values. -/
def cat3 (a b c : BitVec 128) : BitVec 384 := (a ++ b ++ c).cast (by norm_num)

/-- Concatenation of six 128-bit values. -/
def cat6 (a : Fin 6 → BitVec 128) : BitVec 768 :=
  (a 0 ++ a 1 ++ a 2 ++ a 3 ++ a 4 ++ a 5).cast (by norm_num)

/-- The 128-bit truncation. -/
def trunc {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

/-- Assignments of the concrete graph. -/
abbrev Asg := (v : Fin N) → BitVec (lenF v)

/-- The deterministic value of a node, as a function of the assignment (only used for the
deterministic nodes; the function is defined on all names for convenience).  The hash inputs
`ci`, `gc`, `ec`, `rc` start with the tweak of their hash node, in the high bits. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .ci k t => tw (Name.ch k t) ++ trunc (x (Name.prev k t).fin)
  | .cv k t => trunc (x (Name.ch k t).fin)
  | .gc j => tw (Name.gh j) ++ cat3 (trunc (x (Name.cv (Name.chainOf j 0) 13).fin))
      (trunc (x (Name.cv (Name.chainOf j 1) 13).fin)) (trunc (x (Name.cv (Name.chainOf j 2) 13).fin))
  | .gv j => trunc (x (Name.gh j).fin)
  | .ec l => tw (Name.eh l) ++ cat3 (trunc (x (Name.gv (Name.groupOf l 0)).fin))
      (trunc (x (Name.gv (Name.groupOf l 1)).fin)) (trunc (x (Name.gv (Name.groupOf l 2)).fin))
  | .ev l => trunc (x (Name.eh l).fin)
  | .rc => tw Name.rh ++ cat6 fun l => trunc (x (Name.ev l).fin)
  | _ => 0

/-- The value of the parent `p` of a hash node `h` carries the tweak of `h`. -/
theorem tagNat_detVal {p h : Name} (hc : Name.child p = some h) (hh : h.cost ≠ 0) (x : Asg) :
    tagNat ⟨p.len, detVal p x⟩ = h.idx := by
  cases p with
  | ci k t =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_tw_append (n := 128) _ _
  | gc j =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_tw_append (n := 384) _ _
  | ec l =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_tw_append (n := 384) _ _
  | rc =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_tw_append (n := 768) _ _
  | cv k t =>
    simp only [Name.child] at hc
    split_ifs at hc <;>
      (simp only [Option.some.injEq] at hc; subst hc; exact absurd rfl hh)
  | rh => simp only [Name.child, reduceCtorEq] at hc
  | src k => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | ch k t => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | gh j => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | gv j => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | eh l => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | ev l => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh

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
    show tw (Name.ch k t) ++ trunc (x (Name.prev k t).fin) =
      tw (Name.ch k t) ++ trunc (y (Name.prev k t).fin)
    rw [key (Name.prev k t) (by simp [Name.parents])]
  | cv k t =>
    show trunc (x (Name.ch k t).fin) = trunc (y (Name.ch k t).fin)
    rw [key (Name.ch k t) (by simp [Name.parents])]
  | gc j =>
    show tw (Name.gh j) ++ cat3 (trunc (x (Name.cv (Name.chainOf j 0) 13).fin))
        (trunc (x (Name.cv (Name.chainOf j 1) 13).fin))
        (trunc (x (Name.cv (Name.chainOf j 2) 13).fin)) =
      tw (Name.gh j) ++ cat3 (trunc (y (Name.cv (Name.chainOf j 0) 13).fin))
        (trunc (y (Name.cv (Name.chainOf j 1) 13).fin))
        (trunc (y (Name.cv (Name.chainOf j 2) 13).fin))
    rw [key (Name.cv (Name.chainOf j 0) 13) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 1) 13) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 2) 13) (by simp [Name.parents])]
  | gv j =>
    show trunc (x (Name.gh j).fin) = trunc (y (Name.gh j).fin)
    rw [key (Name.gh j) (by simp [Name.parents])]
  | ec l =>
    show tw (Name.eh l) ++ cat3 (trunc (x (Name.gv (Name.groupOf l 0)).fin))
        (trunc (x (Name.gv (Name.groupOf l 1)).fin))
        (trunc (x (Name.gv (Name.groupOf l 2)).fin)) =
      tw (Name.eh l) ++ cat3 (trunc (y (Name.gv (Name.groupOf l 0)).fin))
        (trunc (y (Name.gv (Name.groupOf l 1)).fin))
        (trunc (y (Name.gv (Name.groupOf l 2)).fin))
    rw [key (Name.gv (Name.groupOf l 0)) (by simp [Name.parents]),
      key (Name.gv (Name.groupOf l 1)) (by simp [Name.parents]),
      key (Name.gv (Name.groupOf l 2)) (by simp [Name.parents])]
  | ev l =>
    show trunc (x (Name.eh l).fin) = trunc (y (Name.eh l).fin)
    rw [key (Name.eh l) (by simp [Name.parents])]
  | rc =>
    show tw Name.rh ++ cat6 (fun l => trunc (x (Name.ev l).fin)) =
      tw Name.rh ++ cat6 (fun l => trunc (y (Name.ev l).fin))
    have e : (fun l => trunc (x (Name.ev l).fin)) = fun l => trunc (y (Name.ev l).fin) := by
      funext l
      rw [key (Name.ev l) (Finset.mem_image_of_mem _ (Finset.mem_univ _))]
    rw [e]
  | src _ => rfl
  | ch _ _ => rfl
  | gh _ => rfl
  | eh _ => rfl
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
  | .gc j, h => .det ((Name.parents (.gc j)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.gc j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .gh j, h => .hash (Name.gc j).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .gv j, h => .det ((Name.parents (.gv j)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.gv j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .ec l, h => .det ((Name.parents (.ec l)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.ec l) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .eh l, h => .hash (Name.ec l).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .ev l, h => .det ((Name.parents (.ev l)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.ev l) x).cast (by rw [lenF, h]))
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

theorem graph_isHash_fin (n : Name) :
    (graph.kind n.fin).IsHash ↔ n.cost ≠ 0 := by
  rw [graph_kind_fin]; exact kindOf_isHash _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ k, n = .src k := by
  rw [graph_kind_fin]; exact kindOf_isSource _ _ _

theorem Name.len_prev (k : Fin 54) (t : Fin 14) : (Name.prev k t).len = 128 := by
  unfold Name.prev; split_ifs <;> rfl

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits]

theorem graph_keygenCost : graph.keygenCost = 782 := by
  show ∑ v : Fin N, graph.nodeCost v = 782
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

end Forest

end OptimalOTS
