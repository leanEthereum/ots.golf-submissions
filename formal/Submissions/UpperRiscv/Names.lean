import OptimalOTS.Dag
import Submissions.UpperRiscv.Semantics

/-!
# The mixed-width chain graph

There are 32 chains of 32 hash steps, indexed in execution order. The first 24 chains carry
160-bit states, the last eight 192-bit states. Every hash returns 256 bits; the next state is the
slice starting at bit `truncOff k`, the offset of the chain's state inside its 32-byte answer
buffer: 64 for the thirteen chains that expand their wire value into a separate buffer, and 0,
32, 64 or 96 for the chains hashed in place in the signature. A source is already state-width.

The root input is 7424 bits: the answers of the 32 chains in memory order, all 256 bits of
twenty of them and the high 192 bits of the other twelve (`rootCat`). Every chain's high 192
bits are among them. The three key-generation input lengths 160, 192, and 7424 differ from the
512-bit index input.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace Forest

/-- Width of chain states, indexed in execution order. -/
def chainBits (k : Fin 32) : ℕ := if k.val < 24 then 160 else 192

theorem chainBits_cases (k : Fin 32) : chainBits k = 192 ∨ chainBits k = 160 := by
  unfold chainBits; split_ifs <;> simp

theorem chainBits_ge (k : Fin 32) : 160 ≤ chainBits k := by
  rcases chainBits_cases k with h | h <;> omega

theorem chainBits_le (k : Fin 32) : chainBits k ≤ 192 := by
  rcases chainBits_cases k with h | h <;> omega

/-- Bit offset of a chain's next state inside a 256-bit answer: the answer is written eight
bytes below the state of an expanding chain (0–12), and `j` bytes below the wire value of a chain
hashed in place, `j = 12` (13–19, 21), `4` (20), `0` (22, 24–30) or `8` (23, 31). -/
def truncOff (k : Fin 32) : ℕ :=
  if k.val = 20 then 32 else if k.val = 22 ∨ (24 ≤ k.val ∧ k.val ≤ 30) then 0
  else if 13 ≤ k.val ∧ k.val ≤ 21 then 96 else 64

theorem truncOff_add_le (k : Fin 32) : truncOff k + chainBits k ≤ 256 := by
  unfold truncOff chainBits
  split_ifs <;> omega

theorem truncOff_mod8 (k : Fin 32) : truncOff k % 8 = 0 := by
  unfold truncOff
  split_ifs <;> decide

/-- Node names. -/
inductive Name where
  | src (k : Fin 32)
  | ci (k : Fin 32) (t : Fin 32)
  | ch (k : Fin 32) (t : Fin 32)
  | cv (k : Fin 32) (t : Fin 32)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 3106

namespace Name

/-- Topological index. Chain `k` occupies `97 k, …, 97 k + 96`: its source, then input, hash and
value of each of its 32 levels. -/
def idx : Name → ℕ
  | src k => 97 * k
  | ci k t => 97 * k + 1 + 3 * t
  | ch k t => 97 * k + 2 + 3 * t
  | cv k t => 97 * k + 3 + 3 * t
  | rc => 3104
  | rh => 3105

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src k => chainBits k
  | ci k _ => chainBits k
  | ch _ _ => 256
  | cv _ _ => 256
  | rc => 7424
  | rh => 256

/-- Query cost of a node: one compression for every chain hash, fifteen for the root. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | rh => 15
  | _ => 0

/-- The value node feeding the chain input `ci k t`: the source for `t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 32) (t : Fin 32) : Name :=
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
  if h₁ : v.val < 3104 then
    let k : Fin 32 := ⟨v.val / 97, by omega⟩
    let r := v.val % 97
    if h₂ : r = 0 then .src k
    else
      let t : Fin 32 := ⟨(r - 1) / 3, by omega⟩
      if h₃ : (r - 1) % 3 = 0 then .ci k t
      else if h₃' : (r - 1) % 3 = 1 then .ch k t
      else .cv k t
  else if h₁₀ : v.val < 3105 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Fin.ext_iff,
      reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 3106 := v.isLt
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

abbrev NameSum := Fin 32 ⊕ (Fin 32 × Fin 32) ⊕ (Fin 32 × Fin 32) ⊕ (Fin 32 × Fin 32) ⊕
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

/-! ## The root input -/

/-- The low 192 bits of a top. -/
def lo192 (x : BitVec 256) : BitVec 192 := x.setWidth 192

/-- The low 192 bits of the tops of chains `0 … j`: `lo192 (c j) ‖ ⋯ ‖ lo192 (c 0)`, with
`c 0` in the low bits, as the tops lie in memory. -/
def lowCat (c : ℕ → BitVec 256) : (j : ℕ) → BitVec (192 * (j + 1))
  | 0 => lo192 (c 0)
  | j + 1 => (lo192 (c (j + 1)) ++ lowCat c j).cast (by omega)

/-- The chain tops as a function on naturals. -/
def topFun (c : Fin 32 → BitVec 256) (j : ℕ) : BitVec 256 := if h : j < 32 then c ⟨j, h⟩ else 0

/-- High 192-bit slices in execution order, the first slice in the highest bits. -/
def highCat (c : ℕ → BitVec 256) : (j : ℕ) → BitVec (192 * (j + 1))
  | 0 => (c 0).extractLsb' 64 192
  | j + 1 => (highCat c j ++ (c (j + 1)).extractLsb' 64 192).cast (by omega)

/-- The chains in the memory order of the root input, lowest address first. -/
def rootChain (i : ℕ) : Fin 32 :=
  [31, 24, 13, 25, 14, 26, 15, 27, 16, 28, 17, 29, 18, 30, 19, 12,
    11, 20, 21, 22, 23, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0].getD i 0

/-- The first answer bit of chain `k` kept by the root: the high 24 bytes of the tops of the
stacked expanded chains (0–9), of chain 11 and of the last chain, and all 32 bytes of the others. -/
def rootStart (k : ℕ) : ℕ := if k ≤ 9 ∨ k = 11 ∨ k = 31 then 64 else 0

/-- The number of answer bits of chain `k` kept by the root. -/
def rootWidth (k : ℕ) : ℕ := 256 - rootStart k

/-- Bit offset of the `i`-th piece (in memory order) of the root input. -/
def rootOff : ℕ → ℕ
  | 0 => 0
  | i + 1 => rootOff i + rootWidth (rootChain i)

theorem rootOff_succ (i : ℕ) : rootOff (i + 1) = rootOff i + rootWidth (rootChain i) := rfl

/-- The first `i` pieces of the root input, the first piece in the low bits. -/
def rootPart (c : Fin 32 → BitVec 256) : (i : ℕ) → BitVec (rootOff i)
  | 0 => 0#0
  | i + 1 => ((c (rootChain i)).extractLsb' (rootStart (rootChain i)) (rootWidth (rootChain i)) ++
      rootPart c i).cast (by
        first
        | (show _ = rootOff i + rootWidth (rootChain i); omega)
        | (rw [rootOff_succ]; omega))

theorem rootOff_32 : rootOff 32 = 7424 := by decide +kernel

/-- The root input: the kept part of every chain top, in memory order. -/
def rootCat (c : Fin 32 → BitVec 256) : BitVec 7424 := (rootPart c 32).cast rootOff_32

/-- The memory-order position of chain `k` in the root input (the inverse of `rootChain`). -/
def rootPiece (k : ℕ) : ℕ :=
  [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 16, 15, 2, 4, 6,
    8, 10, 12, 14, 17, 18, 19, 20, 1, 3, 5, 7, 9, 11, 13, 0].getD k 0

theorem rootPiece_spec' : ∀ k : Fin 32, rootPiece k < 32 ∧ rootChain (rootPiece k) = k := by
  decide +kernel

theorem rootStart_le (k : ℕ) : rootStart k ≤ 64 := by
  unfold rootStart
  split_ifs <;> omega

/-- Bit position of the high 192 answer bits of chain `k` in the root input. -/
def rootPos (k : ℕ) : ℕ := rootOff (rootPiece k) + (64 - rootStart k)

/-- Earlier pieces end below later ones. -/
theorem rootOff_le (n : ℕ) : ∀ i, i < n → rootOff i + rootWidth (rootChain i) ≤ rootOff n := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro i hi
    rw [rootOff_succ]
    by_cases hin : i < n
    · have := ih i hin
      omega
    · have e : i = n := by omega
      subst e
      exact le_refl _

/-- Piece `i` of the root input occupies bits `rootOff i, …` of every longer prefix. -/
theorem getLsbD_rootPart (c : Fin 32 → BitVec 256) (n : ℕ) :
    ∀ i, i < n → ∀ t, t < rootWidth (rootChain i) →
      (rootPart c n).getLsbD (rootOff i + t) =
        (c (rootChain i)).getLsbD (rootStart (rootChain i) + t) := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro i hi t ht
    rw [rootPart, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hin : i < n
    · have hle := rootOff_le n i hin
      rw [if_pos (show rootOff i + t < rootOff n by omega)]
      exact ih i hin t ht
    · have e : i = n := by omega
      rw [e] at ht ⊢
      rw [if_neg (show ¬ (rootOff n + t < rootOff n) by omega), Nat.add_sub_cancel_left,
        BitVec.getLsbD_extractLsb']
      simp only [ht, decide_true, Bool.true_and]

/-- The root input determines the high 192 answer bits of every chain top. -/
theorem rootCat_extract (c : Fin 32 → BitVec 256) (k : Fin 32) :
    (rootCat c).extractLsb' (rootPos k) 192 = (c k).extractLsb' 64 192 := by
  obtain ⟨hi, hk⟩ := rootPiece_spec' k
  have hs := rootStart_le k
  apply BitVec.eq_of_getLsbD_eq
  intro u hu
  have ht : 64 - rootStart (rootChain (rootPiece k)) + u < rootWidth (rootChain (rootPiece k)) := by
    rw [hk]
    unfold rootWidth
    omega
  have key := getLsbD_rootPart c 32 (rootPiece k) hi
    (64 - rootStart (rootChain (rootPiece k)) + u) ht
  rw [hk] at key
  have e1 : rootPos k + u = rootOff (rootPiece k) + (64 - rootStart k + u) := by
    unfold rootPos
    omega
  have e2 : rootStart k + (64 - rootStart k + u) = 64 + u := by omega
  rw [e2] at key
  simp only [BitVec.getLsbD_extractLsb', hu, decide_true, Bool.true_and]
  unfold rootCat
  rw [BitVec.getLsbD_cast, e1, key]

/-! ## The graph -/

def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- Retain the state slice starting `truncOff k` bits into a hash output, or the entire
state when the input already has the chain's width. -/
def trunc (k : Fin 32) {w : ℕ} (x : BitVec w) : BitVec (chainBits k) :=
  x.extractLsb' (min (truncOff k) (w - chainBits k)) (chainBits k)

abbrev Asg := (v : Fin N) → BitVec (lenF v)

theorem lenF_ch (k : Fin 32) (t : Fin 32) : lenF (Name.ch k t).fin = (Name.cv k t).len := lenF_fin _

/-- The deterministic value of a node, as a function of the assignment. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .ci k t => trunc k (x (Name.prev k t).fin)
  | .cv k t => (x (Name.ch k t).fin).cast (lenF_ch k t)
  | .rc => rootCat fun k => (x (Name.cv k 31).fin).cast (lenF_fin _)
  | _ => 0

theorem detVal_ci (k : Fin 32) (t : Fin 32) (x : Asg) :
    detVal (.ci k t) x = trunc k (x (Name.prev k t).fin) := rfl

theorem detVal_cv (k : Fin 32) (t : Fin 32) (x : Asg) :
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
    show trunc k (x (Name.prev k t).fin) = trunc k (y (Name.prev k t).fin)
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

theorem Name.len_prev (k : Fin 32) (t : Fin 32) : (Name.prev k t).len = if t.val = 0 then chainBits k else 256 := by
  unfold Name.prev; split_ifs <;> rfl

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits, chainBits]
  split_ifs <;> norm_num

theorem graph_keygenCost : graph.keygenCost = 1039 := by
  show ∑ v : Fin N, graph.nodeCost v = 1039
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

end Forest

end OptimalOTS
