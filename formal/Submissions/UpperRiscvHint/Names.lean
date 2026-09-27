import OptimalOTS.Dag
import Submissions.UpperRiscvHint.Semantics

/-!
# The mixed-width chain graph

There are 33 chains of 32 hash steps, indexed in execution order. Chain 0 is the *free chain*,
which carries the free count; chain `k + 1` carries index digit `k`. Chains 0–12 are *caps* with
192-bit states, chains 13–32 are *normals* with 144-bit states. Every hash returns 256 bits; the
next state starts at bit `truncOff k`: 0 for a cap, 64 for a normal. A source is already
state-width.

Each chain ends in a `top` node read by the root. A cap's top is its final 192-bit state; normals
13–24 commit their whole last answer (256 bits), normals 25–31 their low 192 bits and normal 32
its answer bits `[64,256)`. The root input lists the tops in memory order: normal 32, the free
chain, then normal `13 + j` below cap `1 + j` for `j = 0 … 11`, then normals 25–31, for 7072 bits
(`rootCat`). The key-generation input lengths 144, 192 and 7072 differ from the 512-bit index
input.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace Forest

/-- A chain: chain 0 is the free chain, chain `k + 1` carries index digit `k`. -/
abbrev Chain := Fin 33

/-- Width of chain states: 192 for the caps 0–12, 144 for the normals. -/
def chainBits (k : Chain) : ℕ :=
  if k.val < 13 then 192 else 144

theorem chainBits_cases (k : Chain) :
    chainBits k = 144 ∨ chainBits k = 192 := by
  unfold chainBits; split_ifs <;> simp

theorem chainBits_ge (k : Chain) : 144 ≤ chainBits k := by
  rcases chainBits_cases k with h | h <;> omega

theorem chainBits_le (k : Chain) : chainBits k ≤ 192 := by
  rcases chainBits_cases k with h | h <;> omega

/-- Bit offset of a chain's next state inside a 256-bit answer: a cap keeps answer bytes
`[0, 24)`, a normal answer bytes `[8, 26)`. -/
def truncOff (k : Chain) : ℕ :=
  if k.val = 32 then 112 else if k.val < 13 ∨ k.val = 31 then 0 else 64

theorem truncOff_add_le' : ∀ k : Chain, truncOff k + chainBits k ≤ 256 := by
  decide +kernel

theorem truncOff_add_le (k : Chain) : truncOff k + chainBits k ≤ 256 := truncOff_add_le' k

theorem truncOff_mod8' : ∀ k : Chain, truncOff k % 8 = 0 := by
  decide +kernel

theorem truncOff_mod8 (k : Chain) : truncOff k % 8 = 0 := truncOff_mod8' k

/-- Width of the value the root commits for chain `k`. -/
def topBits (k : Chain) : ℕ :=
  if 31 ≤ k.val then 144 else if (13 ≤ k.val ∧ k.val < 25) ∨ k.val = 30 then 256 else 192

theorem topBits_ge (k : Chain) : 144 ≤ topBits k := by
  unfold topBits; split_ifs <;> omega

theorem topBits_le (k : Chain) : topBits k ≤ 256 := by
  unfold topBits; split_ifs <;> omega

theorem topBits_of_cap {k : Chain} (hk : k.val < 13 ∨ 31 ≤ k.val) : topBits k = chainBits k := by
  unfold topBits chainBits
  split_ifs <;> omega

/-- Bit offset of the committed part of a chain's last answer: 64 for the last chain, whose top
begins at its state, else 0. -/
def topOff (k : Chain) : ℕ := if k.val = 32 then 112 else 0

theorem topOff_cap {k : Chain} (hk : k.val < 13 ∨ 31 ≤ k.val) : topOff k = truncOff k := by
  have := k.isLt
  unfold topOff truncOff
  split_ifs <;> omega

theorem topOff_add_le : ∀ k : Chain, topOff k + topBits k ≤ 256 := by decide +kernel

/-- The committed part of a chain's last answer. -/
def topOf (k : Chain) (w : BitVec 256) : BitVec (topBits k) := w.extractLsb' (topOff k) (topBits k)

/-- Node names. -/
inductive Name where
  | src (k : Chain)
  | ci (k : Chain) (t : Fin 32)
  | ch (k : Chain) (t : Fin 32)
  | cv (k : Chain) (t : Fin 32)
  | top (k : Chain)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 3236

namespace Name

/-- Topological index. Chain `k` occupies `98 k, …, 98 k + 97`: its source, then input, hash and
value of each of its 32 levels, then its top. -/
def idx : Name → ℕ
  | src k => 98 * k
  | ci k t => 98 * k + 1 + 3 * t
  | ch k t => 98 * k + 2 + 3 * t
  | cv k t => 98 * k + 3 + 3 * t
  | top k => 98 * k + 97
  | rc => 3234
  | rh => 3235

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src k => chainBits k
  | ci k _ => chainBits k
  | ch _ _ => 256
  | cv _ _ => 256
  | top k => topBits k
  | rc => 7072
  | rh => 256

/-- Query cost of a node: one compression for every chain hash, fourteen for the root. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | rh => 14
  | _ => 0

/-- The value node feeding the chain input `ci k t`: the source for `t = 0`, else `cv k (t-1)`. -/
def prev (k : Chain) (t : Fin 32) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ci k 0)
  | ci k t => some (ch k t)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 31 then some (top k) else some (ci k ⟨t + 1, by omega⟩)
  | top _ => some rc
  | rc => some rh
  | rh => none

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ci k t => {prev k t}
  | ch k t => {ci k t}
  | cv k t => {ch k t}
  | top k => {cv k 31}
  | rc => Finset.univ.image top
  | rh => {rc}

theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  cases n <;> cases m <;>
    simp only [parents, child, prev, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.notMem_empty, Option.some.injEq,
      reduceCtorEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.top.injEq, Fin.ext_iff,
      Fin.val_zero, iff_true, iff_false, false_iff, or_false, exists_false] <;>
    (try split_ifs) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Name.src.injEq, Name.ci.injEq,
      Name.cv.injEq, Name.top.injEq, Fin.ext_iff, iff_false, false_iff, not_false_eq_true]) <;>
    first | omega | exact ⟨_, rfl⟩ | (constructor <;> intro h <;> first | trivial | omega | (obtain ⟨_, h1, h2⟩ := h; omega) | exact ⟨_, rfl, by omega⟩)

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  rw [mem_parents_iff] at h
  cases m <;> simp only [child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;> subst h <;>
    simp only [idx, Fin.val_zero] <;> omega

end Name

/-- The inverse of `Name.fin`. -/
def ofFin (v : Fin N) : Name :=
  if h₁ : v.val < 3234 then
    let k : Chain := ⟨v.val / 98, by omega⟩
    let r := v.val % 98
    if h₂ : r = 0 then .src k
    else if h₄ : r = 97 then .top k
    else
      let t : Fin 32 := ⟨(r - 1) / 3, by omega⟩
      if h₃ : (r - 1) % 3 = 0 then .ci k t
      else if h₃' : (r - 1) % 3 = 1 then .ch k t
      else .cv k t
  else if h₁₀ : v.val < 3235 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.top.injEq,
      Fin.ext_iff, reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 3236 := v.isLt
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

abbrev NameSum := Chain ⊕ (Chain × Fin 32) ⊕ (Chain × Fin 32) ⊕ (Chain × Fin 32) ⊕
  Chain ⊕ Unit ⊕ Unit

def Name.toSum : Name → NameSum
  | src k => .inl k
  | ci k t => .inr (.inl (k, t))
  | ch k t => .inr (.inr (.inl (k, t)))
  | cv k t => .inr (.inr (.inr (.inl (k, t))))
  | top k => .inr (.inr (.inr (.inr (.inl k))))
  | rc => .inr (.inr (.inr (.inr (.inr (.inl ())))))
  | rh => .inr (.inr (.inr (.inr (.inr (.inr ())))))

def Name.ofSum : NameSum → Name
  | .inl k => src k
  | .inr (.inl (k, t)) => ci k t
  | .inr (.inr (.inl (k, t))) => ch k t
  | .inr (.inr (.inr (.inl (k, t)))) => cv k t
  | .inr (.inr (.inr (.inr (.inl k)))) => top k
  | .inr (.inr (.inr (.inr (.inr (.inl ()))))) => rc
  | .inr (.inr (.inr (.inr (.inr (.inr ()))))) => rh

def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | ⟨k, t⟩ | k | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ci k t)) + (∑ k, ∑ t, f (ch k t)) +
      (∑ k, ∑ t, f (cv k t)) + (∑ k, f (top k)) + f rc + f rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## The root input -/

/-- The chain in root slot `s`: slot 0 holds normal 32, slot 1 the free chain, slot `2 j + 2`
normal `13 + j` and slot `2 j + 3` cap `1 + j` for `j < 12`, slot `s ≥ 26` normal `s - 1`. -/
def slotChain (s : ℕ) : Chain :=
  ⟨(if s = 0 then 32 else if s = 1 then 0 else if s ≤ 25 then
      (if s % 2 = 0 then 13 + (s - 1) / 2 else (s - 1) / 2) else s - 1) % 33,
    Nat.mod_lt _ (by decide)⟩

/-- Total width of root slots `0 … s`. -/
def slotWidth : ℕ → ℕ
  | 0 => topBits (slotChain 0)
  | s + 1 => topBits (slotChain (s + 1)) + slotWidth s

/-- The tops of slots `0 … s`, slot `0` in the low bits, as they lie in memory. -/
def slotCat (c : (k : Chain) → BitVec (topBits k)) : (s : ℕ) → BitVec (slotWidth s)
  | 0 => c (slotChain 0)
  | s + 1 => c (slotChain (s + 1)) ++ slotCat c s

theorem slotWidth_32 : slotWidth 32 = 7072 := by decide

/-- The 884-byte root input, from low to high bits: normal 32's top; the free chain's 24-byte
top; then normal `13 + j`'s 32-byte top and cap `1 + j`'s 24-byte top for `j = 0, …, 11`; then
the low 24 bytes of normals 25–31. -/
def rootCat (c : (k : Chain) → BitVec (topBits k)) : BitVec 7072 :=
  (slotCat c 32).cast slotWidth_32

/-! ## The graph -/

def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- Retain the state slice starting `truncOff k` bits into a hash output, or the entire
state when the input already has the chain's width. -/
def trunc (k : Chain) {w : ℕ} (x : BitVec w) : BitVec (chainBits k) :=
  x.extractLsb' (min (truncOff k) (w - chainBits k)) (chainBits k)

abbrev Asg := (v : Fin N) → BitVec (lenF v)

theorem lenF_ch (k : Chain) (t : Fin 32) : lenF (Name.ch k t).fin = (Name.cv k t).len := lenF_fin _

/-- The deterministic value of a node, as a function of the assignment. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .ci k t => trunc k (x (Name.prev k t).fin)
  | .cv k t => (x (Name.ch k t).fin).cast (lenF_ch k t)
  | .top k => topOf k ((x (Name.cv k 31).fin).cast (lenF_fin _))
  | .rc => rootCat fun k => (x (Name.top k).fin).cast (lenF_fin _)
  | _ => 0

theorem detVal_ci (k : Chain) (t : Fin 32) (x : Asg) :
    detVal (.ci k t) x = trunc k (x (Name.prev k t).fin) := rfl

theorem detVal_cv (k : Chain) (t : Fin 32) (x : Asg) :
    detVal (.cv k t) x = (x (Name.ch k t).fin).cast (lenF_ch k t) := rfl

theorem detVal_top (k : Chain) (x : Asg) :
    detVal (.top k) x = topOf k ((x (Name.cv k 31).fin).cast (lenF_fin _)) := rfl

theorem detVal_rc (x : Asg) :
    detVal .rc x = rootCat fun k => (x (Name.top k).fin).cast (lenF_fin _) := rfl

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
  | top k =>
    show topOf k ((x (Name.cv k 31).fin).cast (lenF_fin _)) =
      topOf k ((y (Name.cv k 31).fin).cast (lenF_fin _))
    rw [key (Name.cv k 31) (by simp [Name.parents])]
  | rc =>
    show rootCat (fun k => (x (Name.top k).fin).cast (lenF_fin _)) =
      rootCat (fun k => (y (Name.top k).fin).cast (lenF_fin _))
    exact congrArg rootCat (funext fun k => by
      rw [key (Name.top k) (Finset.mem_image_of_mem _ (Finset.mem_univ _))])
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
  | .top k, h => .det ((Name.parents (.top k)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.top k) x).cast (by rw [lenF, h]))
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

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits, chainBits]
  split_ifs <;> norm_num

theorem graph_keygenCost : graph.keygenCost = 1070 := by
  show ∑ v : Fin N, graph.nodeCost v = 1070
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

end Forest

end OptimalOTS
