import Submissions.UpperCompressions.ProofBundle00

/-!
# Cost-86 fused shared-DAG geometry

Three identical blocks feed a fifteen-input root.  A block has fourteen
length-18 chains and 35 ternary hash nodes; hubs are shared by several hash
nodes, five nodes are block tops read only by the root, and every hash node has
an exclusive kid in its last input slot.  A cut chooses, per block, the expanded
hash nodes `E` and one disclosure position on each needed chain.

The family count never enumerates the `2^35` subsets of a block.  A top-down
recursion `dfs` over the hash nodes sums a product weight over the valid
shapes; `dfs_eq` identifies it with the sum over all subsets.  The kernel
evaluates `dfs` through `stRun`, a forward pass over weighted states that prunes
unread bits and merges equal states.  The cost generating number `blockGen`
of one block is cubed, which is the three-fold convolution by
`Finset.prod_univ_sum`, and a base-`B` digit of the cube counts the cut triples
of graph cost 86.
-/

open scoped BigOperators

noncomputable section

set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

/-! ## Block structure -/

/-- An input of a block hash node: the top of a chain or another hash value. -/
inductive Kid where
  | c (k : Fin 14)
  | h (j : Fin 35)
  deriving DecidableEq

/-- Fourteen length-18 chains and the searched ternary DAG.
Slot `2` holds the exclusive kid of each hash node. -/
def kid : Fin 35 → Fin 3 → Kid := ![
  ![.c 2, .c 3, .c 8],
  ![.c 4, .c 0, .h 0],
  ![.c 0, .c 2, .c 1],
  ![.c 3, .h 1, .h 2],
  ![.c 3, .c 0, .c 7],
  ![.c 0, .h 1, .c 6],
  ![.c 4, .c 3, .h 5],
  ![.c 2, .h 1, .c 13],
  ![.c 2, .c 0, .h 7],
  ![.c 0, .c 3, .c 9],
  ![.c 3, .c 0, .c 10],
  ![.h 1, .c 3, .h 10],
  ![.c 4, .c 2, .h 11],
  ![.h 6, .c 2, .c 12],
  ![.c 4, .h 1, .h 13],
  ![.c 0, .c 3, .h 14],
  ![.h 6, .h 15, .h 12],
  ![.h 15, .c 3, .h 8],
  ![.c 4, .h 6, .h 17],
  ![.h 16, .h 18, .h 9],
  ![.h 6, .h 1, .h 19],
  ![.h 15, .c 2, .h 20],
  ![.c 0, .c 3, .c 11],
  ![.h 1, .c 2, .h 22],
  ![.h 6, .h 15, .h 4],
  ![.h 18, .h 16, .h 24],
  ![.c 2, .h 1, .h 25],
  ![.h 6, .c 4, .c 5],
  ![.h 15, .c 2, .h 27],
  ![.h 1, .c 0, .h 28],
  ![.h 16, .h 18, .h 29],
  ![.h 15, .h 6, .h 3],
  ![.h 18, .h 16, .h 31],
  ![.h 6, .h 15, .h 23],
  ![.h 18, .h 16, .h 33]]

/-- The five block tops, in root-slot order. -/
def top : Fin 5 → Fin 35 := ![32, 21, 30, 34, 26]

theorem top_injective : Function.Injective top := by
  decide

/-! ## Graph names and static costs -/

/-- Graph names: chain sources and stages, compress/hash/value triples of the
block hash nodes, and the root input and hash. -/
inductive Name where
  | src (b : Fin 3) (k : Fin 14)
  | ci (b : Fin 3) (k : Fin 14) (t : Fin 18)
  | ch (b : Fin 3) (k : Fin 14) (t : Fin 18)
  | cv (b : Fin 3) (k : Fin 14) (t : Fin 18)
  | hc (b : Fin 3) (j : Fin 35)
  | hh (b : Fin 3) (j : Fin 35)
  | hv (b : Fin 3) (j : Fin 35)
  | rc
  | rh
  deriving DecidableEq, Fintype

/-- Number of graph nodes. -/
def nodeCount : ℕ := 2627

namespace Name

/-- A compact topological numbering. -/
def idx : Name → ℕ
  | src b k => 14 * b + k
  | ci b k t => 42 + 126 * t + 14 * b + k
  | ch b k t => 84 + 126 * t + 14 * b + k
  | cv b k t => 126 + 126 * t + 14 * b + k
  | hc b j => 2310 + 105 * b + 3 * j
  | hh b j => 2311 + 105 * b + 3 * j
  | hv b j => 2312 + 105 * b + 3 * j
  | rc => 2625
  | rh => 2626

theorem idx_lt (n : Name) : n.idx < nodeCount := by
  cases n <;> simp only [idx, nodeCount] <;> omega

theorem idx_injective : Function.Injective idx := by
  intro m n h
  cases m <;> cases n <;> simp_all [idx, Fin.ext_iff] <;> omega

def fin (n : Name) : Fin nodeCount := ⟨n.idx, n.idx_lt⟩

theorem fin_injective : Function.Injective fin := by
  intro m n h
  apply idx_injective
  exact congrArg Fin.val h

/-- Bit length of the value stored at a node. -/
def len : Name → ℕ
  | src _ _ => 129
  | ci _ _ _ => 145
  | ch _ _ _ => 256
  | cv _ _ _ => 129
  | hc _ _ => 16 + 129 * 3
  | hh _ _ => 256
  | hv _ _ => 129
  | rc => 16 + 129 * 15
  | rh => 256

/-- SHA-256 compression cost at each hash-output node. -/
def cost : Name → ℕ
  | ch _ _ _ => 1
  | hh _ _ => 1
  | rh => 4
  | _ => 0

end Name

/-- The value node feeding chain stage `t`. -/
def prev (b : Fin 3) (k : Fin 14) (t : Fin 18) : Name :=
  if h : t.val = 0 then .src b k else .cv b k ⟨t.val - 1, by omega⟩

/-- Position zero discloses a source; positive position `p` discloses the
output of chain hash `p-1`. -/
def chainNode (b : Fin 3) (k : Fin 14) (p : Fin 19) : Name :=
  if h : p.val = 0 then .src b k else .cv b k ⟨p.val - 1, by omega⟩

theorem prev_eq_chainNode (b : Fin 3) (k : Fin 14) (t : Fin 18) :
    prev b k t = chainNode b k t.castSucc := by
  unfold prev chainNode
  split_ifs <;> simp_all

@[simp] theorem chainNode_len (b : Fin 3) (k : Fin 14) (p : Fin 19) :
    (chainNode b k p).len = 129 := by
  unfold chainNode
  split_ifs <;> rfl

theorem chainNode_pair_injective {b b' : Fin 3} {k k' : Fin 14} {p p' : Fin 19}
    (h : chainNode b k p = chainNode b' k' p') : b = b' ∧ k = k' ∧ p = p' := by
  unfold chainNode at h
  split_ifs at h with hp hp'
  · obtain ⟨hb, hk⟩ := Name.src.inj h
    exact ⟨hb, hk, Fin.ext (by omega)⟩
  · obtain ⟨hb, hk, ht⟩ := Name.cv.inj h
    have := congrArg Fin.val ht
    simp only at this
    exact ⟨hb, hk, Fin.ext (by omega)⟩

theorem hc_len_ne (b : Fin 3) (j : Fin 35) : (Name.hc b j).len ≠ 129 := by
  simp only [Name.len]
  omega

/-- The root input in slot `r`: top `r % 5` of block `r / 5`. -/
def rootIn (r : Fin 15) : Name :=
  .hv ⟨r.val / 5, by omega⟩ (top ⟨r.val % 5, by omega⟩)

theorem rootIn_mk (b : Fin 3) (s : Fin 5) :
    rootIn ⟨5 * b.val + s.val, by omega⟩ = .hv b (top s) := by
  have h1 : (5 * b.val + s.val) / 5 = b.val := by omega
  have h2 : (5 * b.val + s.val) % 5 = s.val := by omega
  simp only [rootIn, h1, h2]

theorem rootIn_injective : Function.Injective rootIn := by
  intro r r' h
  simp only [rootIn, Name.hv.injEq] at h
  obtain ⟨hb, hs⟩ := h
  have hb' := congrArg Fin.val hb
  have hs' := congrArg Fin.val (top_injective hs)
  simp only at hb' hs'
  exact Fin.ext (by omega)

/-- Static key-generation cost. -/
def keygenCost : ℕ := 3 * (14 * 18 + 35) + 4

theorem keygenCost_eq : keygenCost = 865 := by norm_num [keygenCost]

theorem sum_name_cost : (∑ n : Name, n.cost) = keygenCost := by decide +kernel

/-! ## Needed kids and shapes -/

/-- The graph name holding a kid's 129-bit value in block `b`. -/
def Kid.name (b : Fin 3) : Kid → Name
  | .c k => .cv b k 17
  | .h j => .hv b j

theorem kid_h_lt {j j' : Fin 35} {i : Fin 3} (h : kid j i = .h j') : j' < j := by
  revert j j' i
  decide +kernel

/-- The exclusive kid has exactly one user slot. -/
theorem kid_eq_kid_excl_iff (e j : Fin 35) (i : Fin 3) :
    kid e i = kid j 2 ↔ e = j ∧ i = 2 := by
  revert e j i
  decide +kernel

/-- Block tops are read only by the root. -/
theorem kid_ne_top (j : Fin 35) (i : Fin 3) (s : Fin 5) : kid j i ≠ .h (top s) := by
  revert j i s
  decide +kernel

/-- A kid is needed when it is a block top or an input of an expanded node. -/
def Needed (E : Finset (Fin 35)) (x : Kid) : Prop :=
  (∃ s, x = .h (top s)) ∨ ∃ e ∈ E, ∃ i, kid e i = x

theorem needed_kid {E : Finset (Fin 35)} {e : Fin 35} (he : e ∈ E) (i : Fin 3) :
    Needed E (kid e i) :=
  Or.inr ⟨e, he, i, rfl⟩

/-- Binding rule: the exclusive kid of `j` is needed exactly when `j` is
expanded. -/
theorem needed_kid_excl_iff (E : Finset (Fin 35)) (j : Fin 35) :
    Needed E (kid j 2) ↔ j ∈ E := by
  constructor
  · rintro (⟨s, h⟩ | ⟨e, he, i, hi⟩)
    · exact absurd h (kid_ne_top j 2 s)
    · obtain ⟨rfl, -⟩ := (kid_eq_kid_excl_iff e j i).1 hi
      exact he
  · intro h
    exact needed_kid h _

def topSet : Finset (Fin 35) := {21, 26, 30, 32, 34}

theorem mem_topSet (j : Fin 35) : j ∈ topSet ↔ ∃ s, top s = j := by
  revert j
  decide

/-- Hash kids of each node, as literal finsets for cheap kernel evaluation. -/
def kidsH : Fin 35 → Finset (Fin 35) := ![
  ∅, {0}, ∅, {1, 2}, ∅, {1}, {5}, {1}, {7}, ∅, ∅, {1, 10}, {11}, {6}, {1, 13}, {14}, {6, 12, 15}, {8, 15}, {6, 17}, {9, 16, 18}, {1, 6, 19}, {15, 20}, ∅, {1, 22}, {4, 6, 15}, {16, 18, 24}, {1, 25}, {6}, {15, 27}, {1, 28}, {16, 18, 29}, {3, 6, 15}, {16, 18, 31}, {6, 15, 23}, {16, 18, 33}]

/-- Chain kids of each node. -/
def kidsC : Fin 35 → Finset (Fin 14) := ![
  {2, 3, 8}, {0, 4}, {0, 1, 2}, {3}, {0, 3, 7}, {0, 6}, {3, 4}, {2, 13}, {0, 2}, {0, 3, 9}, {0, 3, 10}, {3}, {2, 4}, {2, 12}, {4}, {0, 3}, ∅, {3}, {4}, ∅, ∅, {2}, {0, 3, 11}, {2}, ∅, ∅, {2}, {4, 5}, {2}, {0}, ∅, ∅, ∅, ∅, ∅]

theorem mem_kidsH (e j : Fin 35) : j ∈ kidsH e ↔ ∃ i, kid e i = .h j := by
  revert e j
  decide +kernel

theorem mem_kidsC (e : Fin 35) (k : Fin 14) : k ∈ kidsC e ↔ ∃ i, kid e i = .c k := by
  revert e k
  decide +kernel

theorem kidsH_lt (e j : Fin 35) (h : j ∈ kidsH e) : j < e := by
  obtain ⟨i, hi⟩ := (mem_kidsH e j).1 h
  exact kid_h_lt hi

def neededH (E : Finset (Fin 35)) : Finset (Fin 35) := topSet ∪ E.biUnion kidsH

def neededC (E : Finset (Fin 35)) : Finset (Fin 14) := E.biUnion kidsC

@[simp] theorem mem_neededH (E : Finset (Fin 35)) (j : Fin 35) :
    j ∈ neededH E ↔ Needed E (.h j) := by
  simp only [neededH, Finset.mem_union, mem_topSet, Finset.mem_biUnion, mem_kidsH, Needed,
    Kid.h.injEq]
  constructor
  · rintro (⟨s, rfl⟩ | h)
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inr h
  · rintro (⟨s, rfl⟩ | h)
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inr h

@[simp] theorem mem_neededC (E : Finset (Fin 35)) (k : Fin 14) :
    k ∈ neededC E ↔ Needed E (.c k) := by
  simp only [neededC, Finset.mem_biUnion, mem_kidsC, Needed, reduceCtorEq, exists_false,
    false_or]

theorem top_mem_neededH (E : Finset (Fin 35)) (s : Fin 5) : top s ∈ neededH E :=
  (mem_neededH E _).2 (Or.inl ⟨s, rfl⟩)

/-- Every expanded node is needed. -/
def ShapeValid (E : Finset (Fin 35)) : Prop := E ⊆ neededH E

instance : DecidablePred ShapeValid := by
  intro E
  unfold ShapeValid
  infer_instance

def validShapes : Finset (Finset (Fin 35)) := Finset.univ.filter ShapeValid

attribute [irreducible] validShapes

theorem mem_validShapes (E : Finset (Fin 35)) : E ∈ validShapes ↔ ShapeValid E := by
  rw [validShapes, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

/-- Disclosed words of a block shape: needed unexpanded hash values plus one
value per needed chain. -/
def shapeWords (E : Finset (Fin 35)) : ℕ := (neededH E \ E).card + (neededC E).card

/-! ## Top-down shape recursion

`dfs a u g n need needC` handles hash nodes `n-1, …, 0`.  A node is needed
when its bit is set in `need`; a needed node is either kept (weight `u`, one
disclosed word) or expanded (weight `a`), which marks its kids as needed.  At
the bottom each needed chain gets weight `g`.  Kids have smaller indices, so a
node's neededness is fixed once the nodes above it are decided. -/

def khMask : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 6
  | 4 => 0
  | 5 => 2
  | 6 => 32
  | 7 => 2
  | 8 => 128
  | 9 => 0
  | 10 => 0
  | 11 => 1026
  | 12 => 2048
  | 13 => 64
  | 14 => 8194
  | 15 => 16384
  | 16 => 36928
  | 17 => 33024
  | 18 => 131136
  | 19 => 328192
  | 20 => 524354
  | 21 => 1081344
  | 22 => 0
  | 23 => 4194306
  | 24 => 32848
  | 25 => 17104896
  | 26 => 33554434
  | 27 => 64
  | 28 => 134250496
  | 29 => 268435458
  | 30 => 537198592
  | 31 => 32840
  | 32 => 2147811328
  | 33 => 8421440
  | 34 => 8590262272
  | _ => 0

def kcMask : ℕ → ℕ
  | 0 => 268
  | 1 => 17
  | 2 => 7
  | 3 => 8
  | 4 => 137
  | 5 => 65
  | 6 => 24
  | 7 => 8196
  | 8 => 5
  | 9 => 521
  | 10 => 1033
  | 11 => 8
  | 12 => 20
  | 13 => 4100
  | 14 => 16
  | 15 => 9
  | 16 => 0
  | 17 => 8
  | 18 => 16
  | 19 => 0
  | 20 => 0
  | 21 => 4
  | 22 => 2057
  | 23 => 4
  | 24 => 0
  | 25 => 0
  | 26 => 4
  | 27 => 48
  | 28 => 4
  | 29 => 1
  | 30 => 0
  | 31 => 0
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | _ => 0

/-- Bit mask of the five block tops. -/
def topMask : ℕ := 22617784320

theorem testBit_khMask (e j : Fin 35) : (khMask e).testBit j = true ↔ j ∈ kidsH e := by
  revert e j
  decide +kernel

theorem testBit_kcMask (e : Fin 35) (k : Fin 14) :
    (kcMask e).testBit k = true ↔ k ∈ kidsC e := by
  revert e k
  decide +kernel

theorem testBit_topMask (j : Fin 35) : topMask.testBit j = true ↔ j ∈ topSet := by
  revert j
  decide +kernel

/-- Chain kids of each node as bit lists, in increasing order. -/
def kcList : ℕ → List (Fin 14)
  | 0 => [2, 3, 8]
  | 1 => [0, 4]
  | 2 => [0, 1, 2]
  | 3 => [3]
  | 4 => [0, 3, 7]
  | 5 => [0, 6]
  | 6 => [3, 4]
  | 7 => [2, 13]
  | 8 => [0, 2]
  | 9 => [0, 3, 9]
  | 10 => [0, 3, 10]
  | 11 => [3]
  | 12 => [2, 4]
  | 13 => [2, 12]
  | 14 => [4]
  | 15 => [0, 3]
  | 16 => []
  | 17 => [3]
  | 18 => [4]
  | 19 => []
  | 20 => []
  | 21 => [2]
  | 22 => [0, 3, 11]
  | 23 => [2]
  | 24 => []
  | 25 => []
  | 26 => [2]
  | 27 => [4, 5]
  | 28 => [2]
  | 29 => [0]
  | 30 => []
  | 31 => []
  | 32 => []
  | 33 => []
  | 34 => []
  | _ => []

theorem kcList_eq (j : Fin 35) :
    kcList j = (List.finRange 14).filter fun k : Fin 14 => (kcMask j).testBit k.val := by
  revert j
  decide +kernel

/-- Weight `g` for each chain kid of node `j` not yet marked in `needC`. -/
def newW (g needC j : ℕ) : ℕ :=
  ((kcList j).map fun k : Fin 14 => if needC.testBit k.val then 1 else g).prod

theorem list_prod_map_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).prod = (l.map fun x => if p x then f x else 1).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      by_cases h : p x = true <;> simp [h, ih]

theorem newW_eq (g needC : ℕ) (j : Fin 35) :
    newW g needC j =
      ∏ k : Fin 14, if k ∈ kidsC j ∧ needC.testBit k = false then g else 1 := by
  rw [newW, kcList_eq, list_prod_map_filter, Fin.prod_univ_def]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  have hk := testBit_kcMask j k
  by_cases h1 : k ∈ kidsC j <;> by_cases h2 : needC.testBit k = true <;>
    simp_all

/-- Top-down sum over expanded sets.  An expansion pays `a` and `g` per newly
needed chain; a kept needed node pays `u`. -/
def dfs (a u g : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, need, needC =>
      if need.testBit n then
        u * dfs a u g n need needC +
          a * newW g needC n * dfs a u g n (need ||| khMask n) (needC ||| kcMask n)
      else dfs a u g n need needC

attribute [irreducible] dfs

/-- Neededness of a hash node under an initial mask and an expanded set. -/
def NdH (need : ℕ) (E : Finset (Fin 35)) (j : Fin 35) : Prop :=
  need.testBit j = true ∨ ∃ e ∈ E, j ∈ kidsH e

def NdC (needC : ℕ) (E : Finset (Fin 35)) (k : Fin 14) : Prop :=
  needC.testBit k = true ∨ ∃ e ∈ E, k ∈ kidsC e

instance (need : ℕ) (E : Finset (Fin 35)) (j : Fin 35) : Decidable (NdH need E j) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (needC : ℕ) (E : Finset (Fin 35)) (k : Fin 14) : Decidable (NdC needC E k) :=
  inferInstanceAs (Decidable (_ ∨ _))

def low (n : ℕ) : Finset (Fin 35) := Finset.univ.filter fun j => j.val < n

/-- Product weight of an expanded set among the nodes below `n`; zero when an
expanded node is not needed. -/
def wt (a u g need needC n : ℕ) (E : Finset (Fin 35)) : ℕ :=
  (∏ j ∈ low n, if j ∈ E then (if NdH need E j then a else 0)
    else (if NdH need E j then u else 1)) *
  ∏ k : Fin 14, if NdC needC E k ∧ needC.testBit k = false then g else 1

theorem dfs_eq (a u g : ℕ) : ∀ n, n ≤ 35 → ∀ need needC,
    dfs a u g n need needC = ∑ E ∈ (low n).powerset, wt a u g need needC n E
  | 0, _, need, needC => by
      have hlow : low 0 = ∅ := by
        ext j
        simp [low]
      rw [hlow, Finset.powerset_empty, Finset.sum_singleton, dfs, wt, hlow,
        Finset.prod_empty, one_mul]
      symm
      refine Finset.prod_eq_one fun k _ => if_neg ?_
      rintro ⟨h | ⟨e, he, _⟩, h'⟩
      · rw [h] at h'
        exact Bool.noConfusion h'
      · exact absurd he (Finset.notMem_empty e)
  | n + 1, hn, need, needC => by
      have ih := dfs_eq a u g n (by omega)
      let jn : Fin 35 := ⟨n, by omega⟩
      have hlow : low (n + 1) = insert jn (low n) := by
        ext j
        simp only [low, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          jn, Fin.ext_iff]
        omega
      have hnot : jn ∉ low n := by simp [low, jn]
      have hbelow : ∀ E ∈ (low n).powerset, ∀ e ∈ E, jn ∉ kidsH e := by
        intro E hE e he hk
        have he' := Finset.mem_powerset.1 hE he
        have h1 := kidsH_lt e jn hk
        simp only [low, Finset.mem_filter, Finset.mem_univ, true_and] at he'
        have h2 : n < e.val := h1
        omega
      have hself : jn ∉ kidsH jn := fun hk => lt_irrefl _ (kidsH_lt jn jn hk)
      have hE1 : ∀ E ∈ (low n).powerset, wt a u g need needC (n + 1) E =
          (if need.testBit n then u else 1) * wt a u g need needC n E := by
        intro E hE
        have hjE : jn ∉ E := fun h => hnot (Finset.mem_powerset.1 hE h)
        have hnd : NdH need E jn ↔ need.testBit n = true := by
          constructor
          · rintro (h | ⟨e, he, hk⟩)
            · exact h
            · exact absurd hk (hbelow E hE e he)
          · exact Or.inl
        unfold wt
        rw [hlow, Finset.prod_insert hnot, if_neg hjE]
        simp only [hnd]
        ring
      have hE2 : ∀ E ∈ (low n).powerset, wt a u g need needC (n + 1) (insert jn E) =
          ((if need.testBit n then a else 0) * newW g needC n) *
            wt a u g (need ||| khMask n) (needC ||| kcMask n) n E := by
        intro E hE
        have hnd : NdH need (insert jn E) jn ↔ need.testBit n = true := by
          constructor
          · rintro (h | ⟨e, he, hk⟩)
            · exact h
            · rcases Finset.mem_insert.1 he with rfl | he
              · exact absurd hk hself
              · exact absurd hk (hbelow E hE e he)
          · exact Or.inl
        have hndj : ∀ j : Fin 35,
            NdH need (insert jn E) j ↔ NdH (need ||| khMask n) E j := by
          intro j
          have hk := testBit_khMask jn j
          simp only [NdH, Finset.mem_insert, exists_eq_or_imp, Nat.testBit_or,
            Bool.or_eq_true]
          change _ ↔ (_ ∨ (khMask jn).testBit j = true) ∨ _
          rw [hk]
          tauto
        have hndc : ∀ k : Fin 14,
            (if NdC needC (insert jn E) k ∧ needC.testBit k = false then g else 1) =
              (if k ∈ kidsC jn ∧ needC.testBit k = false then g else 1) *
              (if NdC (needC ||| kcMask n) E k ∧
                (needC ||| kcMask n).testBit k = false then g else 1) := by
          intro k
          have hk : (kcMask n).testBit k = true ↔ k ∈ kidsC jn := testBit_kcMask jn k
          simp only [NdC, Finset.mem_insert, exists_eq_or_imp, Nat.testBit_or]
          by_cases h1 : needC.testBit k = true <;> by_cases h2 : k ∈ kidsC jn <;>
            by_cases h3 : ∃ e ∈ E, k ∈ kidsC e <;> simp_all
        have hrest : ∀ j ∈ low n,
            (if j ∈ insert jn E then (if NdH need (insert jn E) j then a else 0)
              else (if NdH need (insert jn E) j then u else 1)) =
            (if j ∈ E then (if NdH (need ||| khMask n) E j then a else 0)
              else (if NdH (need ||| khMask n) E j then u else 1)) := by
          intro j hj
          have hne : j ≠ jn := fun h => hnot (h ▸ hj)
          simp only [Finset.mem_insert, hne, false_or, hndj]
        unfold wt
        rw [hlow, Finset.prod_insert hnot, if_pos (Finset.mem_insert_self _ _),
          Finset.prod_congr rfl hrest]
        have hnw : newW g needC n =
            ∏ k : Fin 14, if k ∈ kidsC jn ∧ needC.testBit k = false then g else 1 :=
          newW_eq g needC jn
        rw [Finset.prod_congr rfl fun k _ => hndc k, Finset.prod_mul_distrib, ← hnw]
        simp only [hnd]
        ring
      rw [hlow, Finset.sum_powerset_insert hnot, Finset.sum_congr rfl hE1,
        Finset.sum_congr rfl hE2, ← Finset.mul_sum, ← Finset.mul_sum, ← ih need needC,
        ← ih (need ||| khMask n) (needC ||| kcMask n), dfs]
      by_cases h : need.testBit n = true <;> simp [h]

theorem low_35 : low 35 = Finset.univ := by
  ext j
  simp [low]

theorem wt_top (a u g : ℕ) (E : Finset (Fin 35)) :
    wt a u g topMask 0 35 E = if ShapeValid E then
      a ^ E.card * u ^ (neededH E \ E).card * g ^ (neededC E).card else 0 := by
  have hH : ∀ j, NdH topMask E j ↔ j ∈ neededH E := by
    intro j
    simp only [NdH, testBit_topMask, neededH, Finset.mem_union, Finset.mem_biUnion]
  have hC : ∀ k : Fin 14, (NdC 0 E k ∧ Nat.testBit 0 k = false) ↔ k ∈ neededC E := by
    intro k
    simp [NdC, neededC]
  unfold wt
  simp only [hH, hC, low_35]
  rw [Finset.prod_ite, Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const, Finset.prod_const]
  have hsd : (Finset.univ.filter fun j => j ∉ E) ∩ neededH E = neededH E \ E := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    tauto
  have hE : (Finset.univ.filter fun j => j ∈ E) = E := by
    ext j
    simp
  rw [hsd, hE]
  split_ifs with hv
  · rw [Finset.prod_congr rfl fun j hj => if_pos (hv hj), Finset.prod_const]
  · obtain ⟨j, hj, hjn⟩ := Finset.not_subset.1 hv
    rw [Finset.prod_eq_zero hj (if_neg hjn), zero_mul, zero_mul]

theorem sum_validShapes_eq_dfs (a u g : ℕ) :
    ∑ E ∈ validShapes, a ^ E.card * u ^ (neededH E \ E).card * g ^ (neededC E).card =
      dfs a u g 35 topMask 0 := by
  rw [dfs_eq a u g 35 le_rfl, low_35, Finset.powerset_univ, validShapes, Finset.sum_filter]
  exact Finset.sum_congr rfl fun E _ => (wt_top a u g E).symm

/-! ## Merged-state evaluation of `dfs`

`dfs` depends only on the bits of `need` below the current level and on the
chain bits that nodes below the level can still read (`chainMask n`).  A
forward pass keeps a list of weighted states, prunes those bits, and merges
equal states; the recursion collapses to at most 255 states per
level. -/

/-- Chain bits read by the nodes below level `n`. -/
def chainMask : ℕ → ℕ
  | 0 => 0
  | n + 1 => chainMask n ||| kcMask n

theorem newW_congr (g y y' n : ℕ) (hn : n < 35)
    (h : ∀ k, (kcMask n).testBit k = true → y.testBit k = y'.testBit k) :
    newW g y n = newW g y' n := by
  have e1 : newW g y n = _ := newW_eq g y ⟨n, hn⟩
  have e2 : newW g y' n = _ := newW_eq g y' ⟨n, hn⟩
  rw [e1, e2]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ kidsC ⟨n, hn⟩
  · rw [h k ((testBit_kcMask ⟨n, hn⟩ k).2 hk)]
  · simp [hk]

theorem dfs_congr (a u g : ℕ) : ∀ n, n ≤ 35 → ∀ x x' y y' : ℕ,
    (∀ k < n, x.testBit k = x'.testBit k) →
    (∀ k, (chainMask n).testBit k = true → y.testBit k = y'.testBit k) →
    dfs a u g n x y = dfs a u g n x' y'
  | 0, _, _, _, _, _, _, _ => by rw [dfs, dfs]
  | n + 1, hn, x, x', y, y', hx, hy => by
      have hcm : ∀ k, (chainMask (n + 1)).testBit k =
          ((chainMask n).testBit k || (kcMask n).testBit k) := fun k => by
        rw [chainMask, Nat.testBit_or]
      have hx' : ∀ k < n, x.testBit k = x'.testBit k := fun k hk => hx k (by omega)
      have hy' : ∀ k, (chainMask n).testBit k = true → y.testBit k = y'.testBit k :=
        fun k hk => hy k (by rw [hcm, hk, Bool.true_or])
      have h1 := dfs_congr a u g n (by omega) x x' y y' hx' hy'
      have h2 := dfs_congr a u g n (by omega) (x ||| khMask n) (x' ||| khMask n)
        (y ||| kcMask n) (y' ||| kcMask n)
        (fun k hk => by rw [Nat.testBit_or, Nat.testBit_or, hx' k hk])
        (fun k hk => by rw [Nat.testBit_or, Nat.testBit_or, hy' k hk])
      have h3 := newW_congr g y y' n (by omega)
        (fun k hk => hy k (by rw [hcm, hk, Bool.or_true]))
      rw [dfs, dfs, hx n (by omega), h1, h2, h3]

abbrev DfsState := ℕ × ℕ × ℕ

/-- Weighted value of a state list `(need, needC, weight)` at level `n`. -/
def stVal (a u g n : ℕ) (L : List DfsState) : ℕ :=
  (L.map fun s => s.2.2 * dfs a u g n s.1 s.2.1).sum

theorem stVal_cons (a u g n : ℕ) (s : DfsState) (L : List DfsState) :
    stVal a u g n (s :: L) = s.2.2 * dfs a u g n s.1 s.2.1 + stVal a u g n L := by
  simp [stVal]

def stStep (a u g n : ℕ) : List DfsState → List DfsState
  | [] => []
  | (x, y, w) :: L =>
      if x.testBit n then
        (x, y, w * u) :: (x ||| khMask n, y ||| kcMask n, w * (a * newW g y n)) ::
          stStep a u g n L
      else (x, y, w) :: stStep a u g n L

theorem stVal_step (a u g n : ℕ) (L : List DfsState) :
    stVal a u g (n + 1) L = stVal a u g n (stStep a u g n L) := by
  induction L with
  | nil => rfl
  | cons s L ih =>
      obtain ⟨x, y, w⟩ := s
      rw [stVal_cons, ih, dfs]
      by_cases h : x.testBit n = true
      · simp only [stStep, h, ↓reduceIte, stVal_cons]
        ring
      · simp only [stStep, h, ↓reduceIte, stVal_cons, Bool.false_eq_true]

def stIns (e : DfsState) : List DfsState → List DfsState
  | [] => [e]
  | f :: L => if e.1 = f.1 ∧ e.2.1 = f.2.1 then (f.1, f.2.1, e.2.2 + f.2.2) :: L
      else f :: stIns e L

theorem stVal_ins (a u g n : ℕ) (e : DfsState) (L : List DfsState) :
    stVal a u g n (stIns e L) = e.2.2 * dfs a u g n e.1 e.2.1 + stVal a u g n L := by
  induction L with
  | nil => simp [stIns, stVal]
  | cons f L ih =>
      rw [stIns]
      split_ifs with h
      · obtain ⟨h1, h2⟩ := h
        rw [stVal_cons, stVal_cons, h1, h2]
        dsimp only
        ring
      · rw [stVal_cons, stVal_cons, ih]
        ring

def stMerge : List DfsState → List DfsState
  | [] => []
  | e :: L => stIns e (stMerge L)

theorem stVal_merge (a u g n : ℕ) (L : List DfsState) :
    stVal a u g n (stMerge L) = stVal a u g n L := by
  induction L with
  | nil => rfl
  | cons e L ih => rw [stMerge, stVal_ins, ih, stVal_cons]

def stPrune (n : ℕ) (L : List DfsState) : List DfsState :=
  L.map fun s => (s.1 % 2 ^ n, s.2.1 &&& chainMask n, s.2.2)

theorem stVal_prune (a u g n : ℕ) (hn : n ≤ 35) (L : List DfsState) :
    stVal a u g n (stPrune n L) = stVal a u g n L := by
  simp only [stVal, stPrune, List.map_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [Function.comp_apply]
  rw [dfs_congr a u g n hn (s.1 % 2 ^ n) s.1 (s.2.1 &&& chainMask n) s.2.1
    (fun k hk => by simp [Nat.testBit_mod_two_pow, hk])
    (fun k hk => by simp [Nat.testBit_and, hk])]

def stRun (a u g : ℕ) : ℕ → List DfsState → List DfsState
  | 0, L => L
  | n + 1, L => stRun a u g n (stMerge (stPrune n (stStep a u g n L)))

attribute [irreducible] stRun

theorem stVal_run (a u g : ℕ) : ∀ n, n ≤ 35 → ∀ L : List DfsState,
    stVal a u g n L = stVal a u g 0 (stRun a u g n L)
  | 0, _, _ => by rw [stRun]
  | n + 1, hn, L => by
      rw [stVal_step, stRun, ← stVal_run a u g n (by omega), stVal_merge,
        stVal_prune a u g n (by omega)]

theorem stVal_zero (a u g : ℕ) (L : List DfsState) :
    stVal a u g 0 L = (L.map fun s => s.2.2).sum := by
  induction L with
  | nil => rfl
  | cons s L ih => rw [stVal_cons, ih, dfs, mul_one, List.map_cons, List.sum_cons]

theorem dfs_top_eq_run (a u g : ℕ) :
    dfs a u g 35 topMask 0 = ((stRun a u g 35 [(topMask, 0, 1)]).map fun s => s.2.2).sum := by
  rw [← stVal_zero, ← stVal_run a u g 35 le_rfl, stVal_cons]
  simp [stVal]

/-! ## Word bounds -/

/-- Word generating number of one block in base `2^36 > 2^35`. -/
def wordBase : ℕ := 2 ^ 36

attribute [irreducible] wordBase

theorem sum_wordBase_pow :
    ∑ E ∈ validShapes, wordBase ^ shapeWords E = dfs 1 wordBase wordBase 35 topMask 0 := by
  rw [← sum_validShapes_eq_dfs]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [shapeWords, pow_add, one_pow, one_mul]

set_option maxRecDepth 100000 in
theorem wordGen_eq : dfs 1 wordBase wordBase 35 topMask 0 =
    144952282898879017642119193614117816954462347956927548864030621830297769812344640280348892496403055764114737001788161034479514159018465199420301844554100768768 := by
  rw [dfs_top_eq_run]
  decide +kernel

theorem wordGen_lt : dfs 1 wordBase wordBase 35 topMask 0 < wordBase ^ 15 := by
  rw [wordGen_eq, wordBase]
  norm_num

theorem shapeWords_le : ∀ E ∈ validShapes, shapeWords E ≤ 14 := by
  intro E hE
  have h := Finset.single_le_sum (f := fun E => wordBase ^ shapeWords E)
    (fun _ _ => Nat.zero_le _) hE
  rw [sum_wordBase_pow] at h
  have hlt := lt_of_le_of_lt h wordGen_lt
  have := (Nat.pow_lt_pow_iff_right (by norm_num [wordBase])).1 hlt
  omega

/-! ## Base-`B` digit counting -/

/-- Digit `n` of `∑ B ^ e x` counts the elements with exponent `n`, provided
the finset has fewer than `B` elements. -/
theorem digit_sum_pow {ι : Type*} (T : Finset ι) (e : ι → ℕ) {B : ℕ} (n : ℕ)
    (hB : T.card < B) :
    (∑ x ∈ T, B ^ e x) / B ^ n % B = (T.filter fun x => e x = n).card := by
  have hB0 : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
  let lo : ι → ℕ := fun x => if e x < n then B ^ e x else 0
  let mid : ι → ℕ := fun x => if e x = n then 1 else 0
  let hi : ι → ℕ := fun x => if n < e x then B ^ (e x - n - 1) else 0
  have hpt : ∀ x, B ^ e x = lo x + B ^ n * (mid x + B * hi x) := by
    intro x
    rcases lt_trichotomy (e x) n with h | h | h
    · simp [lo, mid, hi, h, h.ne, not_lt.2 h.le]
    · simp [lo, mid, hi, h]
    · have h1 : ¬ e x < n := by omega
      have h2 : e x ≠ n := by omega
      simp only [lo, mid, hi, h1, h2, h, if_false, if_true, zero_add]
      rw [← mul_assoc, ← pow_succ, ← pow_add]
      congr 1
      omega
  have hsum : ∑ x ∈ T, B ^ e x =
      (∑ x ∈ T, lo x) + B ^ n * ((∑ x ∈ T, mid x) + B * ∑ x ∈ T, hi x) := by
    rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmid : ∑ x ∈ T, mid x = (T.filter fun x => e x = n).card := by
    simp only [mid]
    rw [Finset.sum_boole]
    simp
  have hlo : ∑ x ∈ T, lo x < B ^ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : ∑ x ∈ T, lo x = 0 :=
        Finset.sum_eq_zero fun x _ => by simp [lo]
      rw [this]
      simp
    · have hle : ∀ x ∈ T, lo x ≤ B ^ (n - 1) := by
        intro x _
        simp only [lo]
        split_ifs with h
        · exact Nat.pow_le_pow_right hB0 (by omega)
        · exact Nat.zero_le _
      calc ∑ x ∈ T, lo x ≤ T.card * B ^ (n - 1) := by
            simpa using Finset.sum_le_sum hle
        _ < B * B ^ (n - 1) :=
            Nat.mul_lt_mul_of_pos_right hB (pow_pos hB0 _)
        _ = B ^ n := by
            rw [← pow_succ']
            congr 1
            omega
  have hmidB : (T.filter fun x => e x = n).card < B :=
    lt_of_le_of_lt (Finset.card_filter_le _ _) hB
  rw [hsum, Nat.add_mul_div_left _ _ (pow_pos hB0 _),
    Nat.div_eq_of_lt hlo, zero_add, hmid, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hmidB]

/-- A shape discloses a word: a top when nothing is expanded, else the
exclusive kid of the lowest expanded node. -/
theorem shapeWords_pos : ∀ E ∈ validShapes, 1 ≤ shapeWords E := by
  intro E _
  unfold shapeWords
  rcases E.eq_empty_or_nonempty with rfl | hne
  · have h : (32 : Fin 35) ∈ neededH ∅ \ ∅ := by simp [neededH, topSet]
    have := Finset.card_pos.2 ⟨_, h⟩
    omega
  · have he : E.min' hne ∈ E := E.min'_mem hne
    cases hk : kid (E.min' hne) 2 with
    | c k =>
        have h : k ∈ neededC E := (mem_neededC E k).2 (Or.inr ⟨_, he, 2, hk⟩)
        have := Finset.card_pos.2 ⟨k, h⟩
        omega
    | h j =>
        have hjE : j ∉ E := fun h => absurd (E.min'_le j h) (not_le.2 (kid_h_lt hk))
        have h : j ∈ neededH E \ E :=
          Finset.mem_sdiff.2 ⟨(mem_neededH E j).2 (Or.inr ⟨_, he, 2, hk⟩), hjE⟩
        have := Finset.card_pos.2 ⟨j, h⟩
        omega

/-! ## Per-block and full choices -/

/-- A block choice: expanded hash nodes and one position per local chain. -/
abbrev Local := Finset (Fin 35) × (Fin 14 → Fin 19)

def localWords (v : Local) : ℕ := shapeWords v.1

def localChainCost (v : Local) : ℕ := ∑ k ∈ neededC v.1, (18 - (v.2 k).val)

/-- Block reconstruction cost: one compression per expanded hash node plus
the walked chain suffixes. -/
def localCost (v : Local) : ℕ := v.1.card + localChainCost v

/-- Allowed positions: free on needed chains, fixed to `18` elsewhere. -/
def posSet (E : Finset (Fin 35)) (k : Fin 14) : Finset (Fin 19) :=
  if k ∈ neededC E then Finset.univ else {18}

def localSet : Finset Local :=
  (validShapes.sigma fun E => Fintype.piFinset (posSet E)).map
    (Equiv.sigmaEquivProd _ _).toEmbedding

attribute [irreducible] localSet

theorem mem_localSet (v : Local) : v ∈ localSet ↔
    ShapeValid v.1 ∧ ∀ k, k ∉ neededC v.1 → v.2 k = 18 := by
  rw [localSet]
  constructor
  · intro h
    obtain ⟨⟨E, p⟩, hx, rfl⟩ := Finset.mem_map.1 h
    obtain ⟨hE, hp⟩ := Finset.mem_sigma.1 hx
    refine ⟨(mem_validShapes E).1 hE, fun k hk => ?_⟩
    have := Fintype.mem_piFinset.1 hp k
    have hk' : ¬ Needed E (.c k) := by simpa using hk
    simpa [posSet, hk'] using this
  · rintro ⟨hE, hp⟩
    refine Finset.mem_map.2 ⟨⟨v.1, v.2⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
    · exact (mem_validShapes _).2 hE
    · refine Fintype.mem_piFinset.2 fun k => ?_
      by_cases hk : k ∈ neededC v.1
      · simp [posSet, hk]
      · simp [posSet, hk, hp k hk]

/-- A full choice: one block choice per block. -/
abbrev Choice := Fin 3 → Local

def choiceCost (c : Choice) : ℕ := ∑ b, localCost (c b)

def choiceWords (c : Choice) : ℕ := ∑ b, localWords (c b)

/-- Root cost plus the block costs. -/
def reconstructionCost (c : Choice) : ℕ := 4 + choiceCost c

def choiceTuples : Finset Choice := Fintype.piFinset fun _ : Fin 3 => localSet

theorem mem_choiceTuples (c : Choice) : c ∈ choiceTuples ↔ ∀ b, c b ∈ localSet := by
  rw [choiceTuples, Fintype.mem_piFinset]

/-- The supported layer: valid blocks and graph cost exactly 86. -/
def supportedChoices : Finset Choice :=
  choiceTuples.filter fun c => choiceCost c = 82

attribute [irreducible] supportedChoices

theorem mem_supportedChoices (c : Choice) : c ∈ supportedChoices ↔
    (∀ b, c b ∈ localSet) ∧ choiceCost c = 82 := by
  rw [supportedChoices, Finset.mem_filter, mem_choiceTuples]

theorem shapeValid_of_supported {c : Choice} (hc : c ∈ supportedChoices) (b : Fin 3) :
    ShapeValid (c b).1 :=
  ((mem_localSet _).1 (((mem_supportedChoices c).1 hc).1 b)).1

theorem canonical_of_supported {c : Choice} (hc : c ∈ supportedChoices) (b : Fin 3)
    (k : Fin 14) (hk : k ∉ neededC (c b).1) : (c b).2 k = 18 :=
  ((mem_localSet _).1 (((mem_supportedChoices c).1 hc).1 b)).2 k hk

theorem reconstructionCost_eq {c : Choice} (hc : c ∈ supportedChoices) :
    reconstructionCost c = 86 := by
  rw [reconstructionCost, ((mem_supportedChoices c).1 hc).2]

theorem choiceWords_le {c : Choice} (hc : c ∈ supportedChoices) : choiceWords c ≤ 42 := by
  have h : ∀ b, localWords (c b) ≤ 14 := fun b =>
    shapeWords_le _ ((mem_validShapes _).2 (shapeValid_of_supported hc b))
  calc choiceWords c ≤ ∑ _b : Fin 3, 14 := Finset.sum_le_sum fun b _ => h b
    _ = 42 := by simp

/-! ## Cost generating number -/

/-- Digit base: every digit counts at most `(2^35 * 19^14)^3 < 2^320` tuples. -/
def digitBase : ℕ := 2 ^ 320

attribute [irreducible] digitBase

def blockGen : ℕ := ∑ v ∈ localSet, digitBase ^ localCost v

attribute [irreducible] blockGen

/-- Generating number of one needed chain: positions `18 - t` steps deep. -/
def chainGen : ℕ := ∑ t : Fin 19, digitBase ^ (18 - t.val)

theorem blockGen_eq : blockGen = dfs digitBase 1 chainGen 35 topMask 0 := by
  rw [← sum_validShapes_eq_dfs]
  unfold blockGen localSet
  rw [Finset.sum_map, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun E _ => ?_
  have hfac : ∀ p : Fin 14 → Fin 19,
      digitBase ^ localCost ((Equiv.sigmaEquivProd _ _).toEmbedding ⟨E, p⟩) =
        digitBase ^ E.card *
          ∏ k : Fin 14, (if k ∈ neededC E then digitBase ^ (18 - (p k).val) else 1) := by
    intro p
    simp only [Equiv.toEmbedding_apply, Equiv.sigmaEquivProd_apply, localCost,
      localChainCost]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow_eq_pow_sum, ← pow_add]
  rw [Finset.sum_congr rfl fun p _ => hfac p, ← Finset.mul_sum, one_pow, mul_one]
  congr 1
  refine (Finset.prod_univ_sum (posSet E) fun k (t : Fin 19) =>
    if k ∈ neededC E then digitBase ^ (18 - t.val) else 1).symm.trans ?_
  rw [← Finset.prod_const, show (∏ _k ∈ neededC E, chainGen) =
    ∏ k : Fin 14, (if k ∈ neededC E then chainGen else 1) by
      rw [Finset.prod_ite_mem, Finset.univ_inter]]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ neededC E
  · simp [posSet, hk, chainGen]
  · simp [posSet, hk]

theorem card_localSet_le : localSet.card ≤ 2 ^ 35 * 19 ^ 14 := by
  have h := Finset.card_le_univ localSet
  simpa [Fintype.card_prod, Fintype.card_finset, Fintype.card_fun] using h

theorem card_choiceTuples_lt : choiceTuples.card < digitBase := by
  have h : choiceTuples.card = localSet.card ^ 3 := by
    rw [choiceTuples, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have h2 : (2 ^ 35 * 19 ^ 14) ^ 3 < digitBase := by
    rw [digitBase]
    decide +kernel
  have h3 : localSet.card ^ 3 ≤ (2 ^ 35 * 19 ^ 14) ^ 3 :=
    pow_le_pow_left₀ (Nat.zero_le _) card_localSet_le 3
  rw [h]
  exact lt_of_le_of_lt h3 h2

theorem blockGen_pow :
    blockGen ^ 3 = ∑ c ∈ choiceTuples, digitBase ^ choiceCost c := by
  rw [blockGen, ← Fin.prod_const, Finset.prod_univ_sum, choiceTuples]
  exact Finset.sum_congr rfl fun c _ => Finset.prod_pow_eq_pow_sum _ _ _

theorem card_supportedChoices_eq_digit :
    supportedChoices.card = blockGen ^ 3 / digitBase ^ 82 % digitBase := by
  rw [blockGen_pow, digit_sum_pow _ _ _ card_choiceTuples_lt, supportedChoices]

set_option maxRecDepth 100000 in
theorem blockGen_digit_exact :
    (dfs digitBase 1 chainGen 35 topMask 0) ^ 3 / digitBase ^ 82 % digitBase =
      678547358015097091041046109088624 := by
  rw [dfs_top_eq_run]
  decide +kernel

theorem card_supportedChoices :
    supportedChoices.card = 678547358015097091041046109088624 := by
  rw [card_supportedChoices_eq_digit, blockGen_eq, blockGen_digit_exact]

/-- The record's schedule class count. -/
def K91 : ℕ := 676013856769711926075368867014708

theorem K91_le_card_supportedChoices : K91 ≤ supportedChoices.card := by
  rw [card_supportedChoices, K91]
  norm_num

/-! ## Cut codec -/

/-- Disclosures of one block: needed unexpanded hash values and one value on
each needed chain. -/
def blockCut (b : Fin 3) (v : Local) : Finset Name :=
  (neededH v.1 \ v.1).image (Name.hv b) ∪
    (neededC v.1).image fun k => chainNode b k (v.2 k)

def cutOf (c : Choice) : Finset Name :=
  Finset.univ.biUnion fun b => blockCut b (c b)

theorem mem_cutOf (c : Choice) (n : Name) : n ∈ cutOf c ↔
    (∃ b j, j ∈ neededH (c b).1 ∧ j ∉ (c b).1 ∧ n = .hv b j) ∨
      ∃ b k, k ∈ neededC (c b).1 ∧ n = chainNode b k ((c b).2 k) := by
  simp only [cutOf, blockCut, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨b, ⟨j, ⟨hj, hjE⟩, rfl⟩ | ⟨k, hk, rfl⟩⟩
    · exact Or.inl ⟨b, j, hj, hjE, rfl⟩
    · exact Or.inr ⟨b, k, hk, rfl⟩
  · rintro (⟨b, j, hj, hjE, rfl⟩ | ⟨b, k, hk, rfl⟩)
    · exact ⟨b, Or.inl ⟨j, ⟨hj, hjE⟩, rfl⟩⟩
    · exact ⟨b, Or.inr ⟨k, hk, rfl⟩⟩

theorem hv_ne_chainNode (b b' : Fin 3) (j : Fin 35) (k : Fin 14) (p : Fin 19) :
    Name.hv b j ≠ chainNode b' k p := by
  unfold chainNode
  split_ifs <;> simp

@[simp] theorem hv_mem_cutOf (c : Choice) (b : Fin 3) (j : Fin 35) :
    Name.hv b j ∈ cutOf c ↔ j ∈ neededH (c b).1 ∧ j ∉ (c b).1 := by
  rw [mem_cutOf]
  constructor
  · rintro (⟨b', j', hj, hjE, h⟩ | ⟨b', k, _, h⟩)
    · obtain ⟨rfl, rfl⟩ := Name.hv.inj h
      exact ⟨hj, hjE⟩
    · exact absurd h (hv_ne_chainNode _ _ _ _ _)
  · rintro ⟨hj, hjE⟩
    exact Or.inl ⟨b, j, hj, hjE, rfl⟩

theorem chainNode_mem_cutOf (c : Choice) (b : Fin 3) (k : Fin 14) (p : Fin 19) :
    chainNode b k p ∈ cutOf c ↔ k ∈ neededC (c b).1 ∧ (c b).2 k = p := by
  rw [mem_cutOf]
  constructor
  · rintro (⟨b', j, _, _, h⟩ | ⟨b', k', hk, h⟩)
    · exact absurd h.symm (hv_ne_chainNode _ _ _ _ _)
    · obtain ⟨rfl, rfl, rfl⟩ := chainNode_pair_injective h
      exact ⟨hk, rfl⟩
  · rintro ⟨hk, rfl⟩
    exact Or.inr ⟨b, k, hk, rfl⟩

theorem cutOf_values (c : Choice) : ∀ n ∈ cutOf c, n.len = 129 := by
  intro n hn
  rcases (mem_cutOf c n).1 hn with ⟨b, j, _, _, rfl⟩ | ⟨b, k, _, rfl⟩
  · rfl
  · exact chainNode_len _ _ _

/-- The block of a disclosed value. -/
def Name.blk : Name → Option (Fin 3)
  | src b _ | ci b _ _ | ch b _ _ | cv b _ _ | hc b _ | hh b _ | hv b _ => some b
  | rc | rh => none

theorem blk_of_mem_blockCut {b : Fin 3} {v : Local} {n : Name} (h : n ∈ blockCut b v) :
    n.blk = some b := by
  simp only [blockCut, Finset.mem_union, Finset.mem_image] at h
  rcases h with ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
  · rfl
  · unfold chainNode
    split_ifs <;> rfl

theorem card_blockCut (b : Fin 3) (v : Local) : (blockCut b v).card = localWords v := by
  rw [blockCut, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective]
  · rfl
  · intro k k' h
    exact (chainNode_pair_injective h).2.1
  · intro j j' h
    exact (Name.hv.inj h).2
  · rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨k, _, h⟩ := Finset.mem_image.1 hn'
    exact hv_ne_chainNode _ _ _ _ _ h.symm

theorem card_cutOf (c : Choice) : (cutOf c).card = choiceWords c := by
  rw [cutOf, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun b _ => card_blockCut b (c b)
  · intro b _ b' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    have h := (blk_of_mem_blockCut hn).symm.trans (blk_of_mem_blockCut hn')
    exact hne (Option.some.inj h)

/-! ## Arbitrary class numbering -/

/-- Select the first `M` members of a finite family using only its canonical
finite equivalence. -/
def selectCut {family : Finset (Finset Name)} {M : ℕ} (hM : M ≤ family.card) :
    Fin M → Finset Name := fun i => family.equivFin.symm (Fin.castLE hM i)

theorem selectCut_mem {family : Finset (Finset Name)} {M : ℕ}
    (hM : M ≤ family.card) (i : Fin M) : selectCut hM i ∈ family :=
  (family.equivFin.symm (Fin.castLE hM i)).property

theorem selectCut_injective {family : Finset (Finset Name)} {M : ℕ}
    (hM : M ≤ family.card) : Function.Injective (selectCut hM) := by
  intro i j hij
  have hs : family.equivFin.symm (Fin.castLE hM i) =
      family.equivFin.symm (Fin.castLE hM j) := Subtype.ext hij
  have hf : Fin.castLE hM i = Fin.castLE hM j := family.equivFin.symm.injective hs
  have hv : i.val = j.val := by
    change (Fin.castLE hM i).val = (Fin.castLE hM j).val
    exact congrArg Fin.val hf
  exact Fin.ext hv

end OptimalOTS.WeightedConstruction.LongChain91
