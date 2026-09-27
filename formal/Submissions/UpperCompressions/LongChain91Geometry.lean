import Submissions.UpperCompressions.ProofBundle00

/-!
# Cost-89 fused shared-DAG geometry

Seven identical blocks feed a seven-input root.  A block has eight length-18
chains and eleven ternary hash nodes; hubs are shared by several hash nodes, and
every hash node has an exclusive kid in its last input slot.  A cut chooses, per
block, the expanded hash nodes `E` and one disclosure position on each needed
chain.

The family count never enumerates block tuples.  The generating number
`blockGen = ∑ B ^ code` of one block is raised to the seventh power, which is the
seven-fold convolution by `Finset.prod_univ_sum`; base-`B` digits of the power
then count the cut tuples of each total cost and word count.
-/

open scoped BigOperators

noncomputable section

set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

/-! ## Graph names and static costs -/

/-- Graph names: chain sources and stages, ternary compress/hash/value triples,
and the root input and hash. -/
inductive Name where
  | src (b : Fin 7) (k : Fin 8)
  | ci (b : Fin 7) (k : Fin 8) (t : Fin 18)
  | ch (b : Fin 7) (k : Fin 8) (t : Fin 18)
  | cv (b : Fin 7) (k : Fin 8) (t : Fin 18)
  | hc (b : Fin 7) (j : Fin 11)
  | hh (b : Fin 7) (j : Fin 11)
  | hv (b : Fin 7) (j : Fin 11)
  | rc
  | rh
  deriving DecidableEq, Fintype

/-- Number of graph nodes. -/
def nodeCount : ℕ := 3313

namespace Name

/-- A compact topological numbering. -/
def idx : Name → ℕ
  | src b k => 8 * b + k
  | ci b k t => 56 + 168 * t + 8 * b + k
  | ch b k t => 112 + 168 * t + 8 * b + k
  | cv b k t => 168 + 168 * t + 8 * b + k
  | hc b j => 3080 + 33 * b + 3 * j
  | hh b j => 3081 + 33 * b + 3 * j
  | hv b j => 3082 + 33 * b + 3 * j
  | rc => 3311
  | rh => 3312

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
  | hc _ _ => 403
  | hh _ _ => 256
  | hv _ _ => 129
  | rc => 919
  | rh => 256

/-- SHA-256 compression cost at each hash-output node. -/
def cost : Name → ℕ
  | ch _ _ _ => 1
  | hh _ _ => 1
  | rh => 2
  | _ => 0

end Name

/-- The value node feeding chain stage `t`. -/
def prev (b : Fin 7) (k : Fin 8) (t : Fin 18) : Name :=
  if h : t.val = 0 then .src b k else .cv b k ⟨t.val - 1, by omega⟩

/-- Position zero discloses a source; positive position `p` discloses the
output of chain hash `p-1`. -/
def chainNode (b : Fin 7) (k : Fin 8) (p : Fin 19) : Name :=
  if h : p.val = 0 then .src b k else .cv b k ⟨p.val - 1, by omega⟩

theorem prev_eq_chainNode (b : Fin 7) (k : Fin 8) (t : Fin 18) :
    prev b k t = chainNode b k t.castSucc := by
  unfold prev chainNode
  split_ifs <;> simp_all

@[simp] theorem chainNode_len (b : Fin 7) (k : Fin 8) (p : Fin 19) :
    (chainNode b k p).len = 129 := by
  unfold chainNode
  split_ifs <;> rfl

theorem chainNode_pair_injective {b b' : Fin 7} {k k' : Fin 8} {p p' : Fin 19}
    (h : chainNode b k p = chainNode b' k' p') : b = b' ∧ k = k' ∧ p = p' := by
  unfold chainNode at h
  split_ifs at h with hp hp'
  · obtain ⟨hb, hk⟩ := Name.src.inj h
    exact ⟨hb, hk, Fin.ext (by omega)⟩
  · obtain ⟨hb, hk, ht⟩ := Name.cv.inj h
    have := congrArg Fin.val ht
    simp only at this
    exact ⟨hb, hk, Fin.ext (by omega)⟩

/-- Static key-generation cost. -/
def keygenCost : ℕ := 7 * (8 * 18 + 11) + 2

theorem keygenCost_eq : keygenCost = 1087 := by norm_num [keygenCost]

theorem keygenCost_le : keygenCost ≤ 2 ^ 20 := by norm_num [keygenCost]

theorem card_name : Fintype.card Name = nodeCount := by decide +kernel

theorem sum_name_cost : (∑ n : Name, n.cost) = keygenCost := by decide +kernel

/-! ## Block structure -/

/-- An input of a block hash node: the top of a chain or another hash value. -/
inductive Kid where
  | c (k : Fin 8)
  | h (j : Fin 11)
  deriving DecidableEq

/-- Local chains `0..7` are the design's `c0 c1 c2 c3 c6 c7 c11 c14`; local
hash nodes `0..10` are `h4 h5 h8 h9 h10 h12 h13 h15 h16 h17 h18`, with top
`10`.  Slot `2` holds the exclusive kid of each hash node. -/
def kid : Fin 11 → Fin 3 → Kid :=
  ![![.c 3, .c 0, .c 2],
    ![.c 0, .c 1, .h 0],
    ![.c 3, .c 4, .c 5],
    ![.c 1, .c 0, .h 2],
    ![.c 4, .h 3, .h 1],
    ![.c 4, .c 1, .c 6],
    ![.h 3, .c 3, .h 5],
    ![.h 3, .c 1, .c 7],
    ![.c 4, .c 1, .h 7],
    ![.c 0, .c 3, .h 8],
    ![.h 4, .h 6, .h 9]]

/-- The graph name holding a kid's 129-bit value in block `b`. -/
def Kid.name (b : Fin 7) : Kid → Name
  | .c k => .cv b k 17
  | .h j => .hv b j

theorem kid_h_lt {j j' : Fin 11} {i : Fin 3} (h : kid j i = .h j') : j' < j := by
  revert j j' i
  decide

/-- The exclusive kid has exactly one user, and it is not the root input. -/
theorem kid_eq_kid_two_iff (e j : Fin 11) (i : Fin 3) :
    kid e i = kid j 2 ↔ e = j ∧ i = 2 := by
  revert e j i
  decide

theorem kid_two_ne_top (j : Fin 11) : kid j 2 ≠ .h 10 := by
  revert j
  decide

/-- A kid is needed when it is the block top or an input of an expanded node. -/
def Needed (E : Finset (Fin 11)) (x : Kid) : Prop :=
  x = .h 10 ∨ ∃ e ∈ E, ∃ i, kid e i = x

instance (E : Finset (Fin 11)) : DecidablePred (Needed E) := by
  intro x
  unfold Needed
  infer_instance

theorem needed_kid {E : Finset (Fin 11)} {e : Fin 11} (he : e ∈ E) (i : Fin 3) :
    Needed E (kid e i) :=
  Or.inr ⟨e, he, i, rfl⟩

/-- Binding rule: the exclusive kid of `j` is needed exactly when `j` is
expanded. -/
theorem needed_kid_two_iff (E : Finset (Fin 11)) (j : Fin 11) :
    Needed E (kid j 2) ↔ j ∈ E := by
  constructor
  · rintro (h | ⟨e, he, i, hi⟩)
    · exact absurd h (kid_two_ne_top j)
    · obtain ⟨rfl, -⟩ := (kid_eq_kid_two_iff e j i).1 hi
      exact he
  · intro h
    exact needed_kid h 2

/-- Hash kids of each node, as literal finsets for cheap kernel evaluation. -/
def kidsH : Fin 11 → Finset (Fin 11)
  | 0 => ∅ | 1 => {0} | 2 => ∅ | 3 => {2} | 4 => {3, 1} | 5 => ∅ | 6 => {3, 5}
  | 7 => {3} | 8 => {7} | 9 => {8} | 10 => {4, 6, 9}

/-- Chain kids of each node. -/
def kidsC : Fin 11 → Finset (Fin 8)
  | 0 => {3, 0, 2} | 1 => {0, 1} | 2 => {3, 4, 5} | 3 => {1, 0} | 4 => {4}
  | 5 => {4, 1, 6} | 6 => {3} | 7 => {1, 7} | 8 => {4, 1} | 9 => {0, 3} | 10 => ∅

theorem mem_kidsH (e j : Fin 11) : j ∈ kidsH e ↔ ∃ i, kid e i = .h j := by
  revert e j
  decide

theorem mem_kidsC (e : Fin 11) (k : Fin 8) : k ∈ kidsC e ↔ ∃ i, kid e i = .c k := by
  revert e k
  decide

def neededH (E : Finset (Fin 11)) : Finset (Fin 11) := insert 10 (E.biUnion kidsH)

def neededC (E : Finset (Fin 11)) : Finset (Fin 8) := E.biUnion kidsC

@[simp] theorem mem_neededH (E : Finset (Fin 11)) (j : Fin 11) :
    j ∈ neededH E ↔ Needed E (.h j) := by
  simp only [neededH, Finset.mem_insert, Finset.mem_biUnion, mem_kidsH, Needed,
    Kid.h.injEq]

@[simp] theorem mem_neededC (E : Finset (Fin 11)) (k : Fin 8) :
    k ∈ neededC E ↔ Needed E (.c k) := by
  simp only [neededC, Finset.mem_biUnion, mem_kidsC, Needed, reduceCtorEq, false_or]

theorem top_mem_neededH (E : Finset (Fin 11)) : (10 : Fin 11) ∈ neededH E :=
  (mem_neededH E 10).2 (Or.inl rfl)

/-- Every expanded node is needed. -/
def ShapeValid (E : Finset (Fin 11)) : Prop := E ⊆ neededH E

instance : DecidablePred ShapeValid := by
  intro E
  unfold ShapeValid
  infer_instance

def validShapes : Finset (Finset (Fin 11)) := Finset.univ.filter ShapeValid

theorem card_validShapes : validShapes.card = 139 := by decide +kernel

/-- Disclosed words of a block shape: needed unexpanded hash values plus one
value per needed chain. -/
def shapeWords (E : Finset (Fin 11)) : ℕ := (neededH E \ E).card + (neededC E).card

theorem shapeWords_bad_card :
    (validShapes.filter fun E => ¬ (1 ≤ shapeWords E ∧ shapeWords E ≤ 8)).card = 0 := by
  decide +kernel

theorem shapeWords_bounds {E : Finset (Fin 11)} (hE : E ∈ validShapes) :
    1 ≤ shapeWords E ∧ shapeWords E ≤ 8 := by
  by_contra h
  have hm : E ∈ validShapes.filter fun E => ¬ (1 ≤ shapeWords E ∧ shapeWords E ≤ 8) :=
    Finset.mem_filter.2 ⟨hE, h⟩
  rw [Finset.card_eq_zero.1 shapeWords_bad_card] at hm
  exact Finset.notMem_empty _ hm

theorem shapeWords_le : ∀ E ∈ validShapes, shapeWords E ≤ 8 :=
  fun _ hE => (shapeWords_bounds hE).2

theorem shapeWords_pos : ∀ E ∈ validShapes, 1 ≤ shapeWords E :=
  fun _ hE => (shapeWords_bounds hE).1

attribute [irreducible] validShapes

theorem mem_validShapes (E : Finset (Fin 11)) : E ∈ validShapes ↔ ShapeValid E := by
  rw [validShapes, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

/-! ## Per-block and full choices -/

/-- A block choice: expanded hash nodes and one position per local chain. -/
abbrev Local := Finset (Fin 11) × (Fin 8 → Fin 19)

def localWords (v : Local) : ℕ := shapeWords v.1

def localChainCost (v : Local) : ℕ := ∑ k ∈ neededC v.1, (18 - (v.2 k).val)

/-- Block reconstruction cost: one compression per expanded ternary node plus
the walked chain suffixes. -/
def localCost (v : Local) : ℕ := v.1.card + localChainCost v

/-- Allowed positions: free on needed chains, fixed to `18` elsewhere. -/
def posSet (E : Finset (Fin 11)) (k : Fin 8) : Finset (Fin 19) :=
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
abbrev Choice := Fin 7 → Local

def choiceCost (c : Choice) : ℕ := ∑ b, localCost (c b)

def choiceWords (c : Choice) : ℕ := ∑ b, localWords (c b)

/-- Root cost plus the block costs. -/
def reconstructionCost (c : Choice) : ℕ := 2 + choiceCost c

/-- The supported layer: valid blocks, graph cost exactly 89, at most 42
words. -/
def choiceTuples : Finset Choice := Fintype.piFinset fun _ : Fin 7 => localSet

theorem mem_choiceTuples (c : Choice) : c ∈ choiceTuples ↔ ∀ b, c b ∈ localSet := by
  rw [choiceTuples, Fintype.mem_piFinset]

def supportedChoices : Finset Choice :=
  choiceTuples.filter fun c =>
    choiceCost c = 87 ∧ choiceWords c ≤ 42

attribute [irreducible] supportedChoices

theorem mem_supportedChoices (c : Choice) : c ∈ supportedChoices ↔
    (∀ b, c b ∈ localSet) ∧ choiceCost c = 87 ∧ choiceWords c ≤ 42 := by
  rw [supportedChoices, Finset.mem_filter, mem_choiceTuples]

theorem shapeValid_of_supported {c : Choice} (hc : c ∈ supportedChoices) (b : Fin 7) :
    ShapeValid (c b).1 :=
  ((mem_localSet _).1 (((mem_supportedChoices c).1 hc).1 b)).1

theorem canonical_of_supported {c : Choice} (hc : c ∈ supportedChoices) (b : Fin 7)
    (k : Fin 8) (hk : k ∉ neededC (c b).1) : (c b).2 k = 18 :=
  ((mem_localSet _).1 (((mem_supportedChoices c).1 hc).1 b)).2 k hk

theorem reconstructionCost_eq {c : Choice} (hc : c ∈ supportedChoices) :
    reconstructionCost c = 89 := by
  rw [reconstructionCost, ((mem_supportedChoices c).1 hc).2.1]

theorem choiceWords_le {c : Choice} (hc : c ∈ supportedChoices) : choiceWords c ≤ 42 :=
  ((mem_supportedChoices c).1 hc).2.2

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

/-- Digit base: every digit counts at most `(2^11 * 19^8)^7 < 2^320` tuples. -/
def digitBase : ℕ := 2 ^ 320

attribute [irreducible] digitBase

/-- Cost and words packed into one exponent; block words never exceed 8, so
seven blocks stay below 57. -/
def code (v : Local) : ℕ := localWords v + 57 * localCost v

def blockGen : ℕ := ∑ v ∈ localSet, digitBase ^ code v

attribute [irreducible] blockGen

/-- Generating number of one needed chain: positions `18 - t` steps deep. -/
def chainGen : ℕ := ∑ t : Fin 19, digitBase ^ (57 * (18 - t.val))

/-- `blockGen` as a sum over the 139 shapes only. -/
def blockGenFormula : ℕ :=
  ∑ E ∈ validShapes, digitBase ^ (shapeWords E + 57 * E.card) *
    ∏ k : Fin 8, if k ∈ neededC E then chainGen else 1

attribute [irreducible] chainGen blockGenFormula

theorem blockGen_eq : blockGen = blockGenFormula := by
  unfold blockGen blockGenFormula localSet
  rw [Finset.sum_map, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun E _ => ?_
  have hfac : ∀ p : Fin 8 → Fin 19,
      digitBase ^ code ((Equiv.sigmaEquivProd _ _).toEmbedding ⟨E, p⟩) =
        digitBase ^ (shapeWords E + 57 * E.card) *
          ∏ k : Fin 8, (if k ∈ neededC E then digitBase ^ (57 * (18 - (p k).val)) else 1) := by
    intro p
    simp only [Equiv.toEmbedding_apply, Equiv.sigmaEquivProd_apply, code, localWords,
      localCost, localChainCost]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow_eq_pow_sum, ← pow_add]
    congr 1
    rw [← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl fun p _ => hfac p, ← Finset.mul_sum]
  congr 1
  refine (Finset.prod_univ_sum (posSet E) fun k (t : Fin 19) =>
    if k ∈ neededC E then digitBase ^ (57 * (18 - t.val)) else 1).symm.trans ?_
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ neededC E
  · simp [posSet, hk, chainGen]
  · simp [posSet, hk]

theorem card_localSet_le : localSet.card ≤ 2 ^ 11 * 19 ^ 8 := by
  have h := Finset.card_le_univ localSet
  simpa [Fintype.card_prod, Fintype.card_finset, Fintype.card_fun] using h

theorem card_choiceTuples_lt : choiceTuples.card < digitBase := by
  have h : choiceTuples.card = localSet.card ^ 7 := by
    rw [choiceTuples, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have h2 : (2 ^ 11 * 19 ^ 8) ^ 7 < digitBase := by decide +kernel
  have h3 : localSet.card ^ 7 ≤ (2 ^ 11 * 19 ^ 8) ^ 7 :=
    pow_le_pow_left₀ (Nat.zero_le _) card_localSet_le 7
  rw [h]
  exact lt_of_le_of_lt h3 h2

theorem blockGen_pow :
    blockGen ^ 7 = ∑ c ∈ choiceTuples, digitBase ^ (∑ b, code (c b)) := by
  rw [blockGen, ← Fin.prod_const, Finset.prod_univ_sum, choiceTuples]
  exact Finset.sum_congr rfl fun c _ => Finset.prod_pow_eq_pow_sum _ _ _

theorem card_code_eq (n : ℕ) :
    (choiceTuples.filter fun c => ∑ b, code (c b) = n).card =
      blockGen ^ 7 / digitBase ^ n % digitBase := by
  rw [blockGen_pow, digit_sum_pow _ _ _ card_choiceTuples_lt]

theorem sum_code (c : Choice) :
    ∑ b, code (c b) = choiceWords c + 57 * choiceCost c := by
  simp only [code, Finset.sum_add_distrib, choiceWords, choiceCost, Finset.mul_sum]

theorem choiceWords_le_56 {c : Choice} (hc : c ∈ choiceTuples) : choiceWords c ≤ 56 := by
  have h : ∀ b, localWords (c b) ≤ 8 := fun b => by
    have hv := (mem_choiceTuples c).1 hc b
    exact shapeWords_le _ ((mem_validShapes _).2 ((mem_localSet _).1 hv).1)
  calc choiceWords c ≤ ∑ _b : Fin 7, 8 := Finset.sum_le_sum fun b _ => h b
    _ = 56 := by simp

theorem supportedChoices_eq_biUnion : supportedChoices =
    (Finset.range 43).biUnion fun y =>
      choiceTuples.filter fun c => ∑ b, code (c b) = y + 57 * 87 := by
  ext c
  simp only [supportedChoices, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    sum_code]
  constructor
  · rintro ⟨hc, hcost, hw⟩
    exact ⟨choiceWords c, by omega, hc, by rw [hcost]⟩
  · rintro ⟨y, hy, hc, he⟩
    have := choiceWords_le_56 hc
    exact ⟨hc, by omega, by omega⟩

/-- Sum of the 43 digits for words `0..42` at cost `87` below the root. -/
def classCount : ℕ :=
  ∑ y ∈ Finset.range 43, blockGen ^ 7 / digitBase ^ (y + 57 * 87) % digitBase

attribute [irreducible] classCount

theorem card_supportedChoices_eq_classCount : supportedChoices.card = classCount := by
  rw [supportedChoices_eq_biUnion, Finset.card_biUnion, classCount]
  · exact Finset.sum_congr rfl fun y _ => card_code_eq _
  · intro y _ y' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_filter] at hc hc'
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem classCount_formula_exact :
    ∑ y ∈ Finset.range 43, blockGenFormula ^ 7 / digitBase ^ (y + 57 * 87) % digitBase =
      909152326074156334680488093234770 := by
  decide +kernel

theorem card_supportedChoices :
    supportedChoices.card = 909152326074156334680488093234770 := by
  rw [card_supportedChoices_eq_classCount, classCount, blockGen_eq, classCount_formula_exact]

/-- The record's schedule class count. -/
def K91 : ℕ := 676013856769711926075368867014708

theorem K91_le_card_supportedChoices : K91 ≤ supportedChoices.card := by
  rw [card_supportedChoices, K91]
  norm_num

/-! ## Cut codec -/

/-- Disclosures of one block: needed unexpanded hash values and one value on
each needed chain. -/
def blockCut (b : Fin 7) (v : Local) : Finset Name :=
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

theorem hv_ne_chainNode (b b' : Fin 7) (j : Fin 11) (k : Fin 8) (p : Fin 19) :
    Name.hv b j ≠ chainNode b' k p := by
  unfold chainNode
  split_ifs <;> simp

@[simp] theorem hv_mem_cutOf (c : Choice) (b : Fin 7) (j : Fin 11) :
    Name.hv b j ∈ cutOf c ↔ j ∈ neededH (c b).1 ∧ j ∉ (c b).1 := by
  rw [mem_cutOf]
  constructor
  · rintro (⟨b', j', hj, hjE, h⟩ | ⟨b', k, _, h⟩)
    · obtain ⟨rfl, rfl⟩ := Name.hv.inj h
      exact ⟨hj, hjE⟩
    · exact absurd h (hv_ne_chainNode _ _ _ _ _)
  · rintro ⟨hj, hjE⟩
    exact Or.inl ⟨b, j, hj, hjE, rfl⟩

theorem chainNode_mem_cutOf (c : Choice) (b : Fin 7) (k : Fin 8) (p : Fin 19) :
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
def Name.blk : Name → Option (Fin 7)
  | src b _ | ci b _ _ | ch b _ _ | cv b _ _ | hc b _ | hh b _ | hv b _ => some b
  | rc | rh => none

theorem blk_of_mem_blockCut {b : Fin 7} {v : Local} {n : Name} (h : n ∈ blockCut b v) :
    n.blk = some b := by
  simp only [blockCut, Finset.mem_union, Finset.mem_image] at h
  rcases h with ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
  · rfl
  · unfold chainNode
    split_ifs <;> rfl

theorem card_blockCut (b : Fin 7) (v : Local) : (blockCut b v).card = localWords v := by
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

/-- Every hash-input length differs from the 342-bit index query. -/
theorem hash_input_length_ne_index (n : Name)
    (h : n.len = 145 ∨ n.len = 403 ∨ n.len = 919) : n.len ≠ 342 := by
  omega

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
