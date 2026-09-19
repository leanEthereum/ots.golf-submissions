import Submissions.UpperRiscv.Master
import Submissions.UpperRiscv.Semantics
import Submissions.UpperRiscv.GScheme

/-!
# Key generation under the lazy random oracle

Key generation samples every source and queries every hash node once. The oracle has no labels, so
the queries of different hash nodes are kept apart by the strings themselves: a `Graph.Tagging`
reads, from a query, the hash node it belongs to. Under the lazy random oracle started from the
empty cache, key generation of a tagged graph therefore produces, for a uniformly random record
`ξ : G.Rec`, the assignment `G.evalRec ξ` and the cache `G.keygenCache ξ` holding the keygen point
of every hash node.

* `Graph.Tagging`: a public tag function under which the input of every hash node carries the tag
  of that node;
* `E_run_keygen`: the expectation of any function of the output and the final cache is the
  uniform average over records;
* `costAtMost_keygen_bind`: a budget for `S.keygen >>= k` leaves `B - keygenCost` for the
  continuation at every record.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- A public way to read, from a query, the hash node it belongs to. -/
structure Tagging (G : Graph) where
  tag : Query → Option (Fin G.size)
  /-- The parent of every hash node is a deterministic node whose output always carries the tag
  of that hash node. -/
  tag_parent : ∀ v p hp hl, G.kind v = .hash p hp hl →
    ∃ ps hps f hf, G.kind p = .det ps hps f hf ∧ ∀ x, tag ⟨G.len p, f x⟩ = some v

/-- The keygen point of hash node `v` under the assignment `x`: its input, with its length. -/
def point (x : G.Assignment) (v : Fin G.size) : Option Query :=
  match G.kind v with
  | .hash p _ _ => some ⟨G.len p, x p⟩
  | _ => none

/-- The cache written by key generation for the record `ξ`. -/
def keygenCache (ξ : G.Rec) : Cache :=
  (List.finRange G.size).foldl
    (fun c v => match G.point (G.evalRec ξ) v with
      | some q => c.cacheQuery q (ξ.2 v)
      | none => c) ∅

theorem point_eq_some_iff (x : G.Assignment) (v : Fin G.size) (q : Query) :
    G.point x v = some q ↔
      ∃ p hp hl, G.kind v = .hash p hp hl ∧ q = ⟨G.len p, x p⟩ := by
  unfold point
  rcases hk : G.kind v with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
  · simp
  · simp
  · simp only [Option.some.injEq, NodeKind.hash.injEq]
    constructor
    · rintro rfl
      exact ⟨p, hp, hl, rfl, rfl⟩
    · rintro ⟨p', hp', hl', rfl, rfl⟩
      rfl

/-- The points of the assignment `x` carry the tags of their hash nodes. -/
def TagOK (T : G.Tagging) (x : G.Assignment) : Prop :=
  ∀ v q, G.point x v = some q → T.tag q = some v

/-- Points of different hash nodes differ: they carry different tags. -/
theorem point_inj (T : G.Tagging) {x x' : G.Assignment} (hx : G.TagOK T x) (hx' : G.TagOK T x')
    {v v' : Fin G.size} {q : Query}
    (h : G.point x v = some q) (h' : G.point x' v' = some q) : v = v' :=
  Option.some.inj ((hx v q h).symm.trans (hx' v' q h'))

/-- One step of the cache fold: record the keygen point of `v` under `x` with answer `y v`. -/
def cacheStep (x : G.Assignment) (y : Fin G.size → BitVec hashBits) (c : Cache)
    (v : Fin G.size) : Cache :=
  match G.point x v with
  | some q => c.cacheQuery q (y v)
  | none => c

theorem keygenCache_eq (ξ : G.Rec) :
    G.keygenCache ξ = (List.finRange G.size).foldl (G.cacheStep (G.evalRec ξ) ξ.2) ∅ := rfl

theorem cacheStep_of_eq_some (x : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (c : Cache) {v : Fin G.size} {q : Query} (h : G.point x v = some q) :
    G.cacheStep x y c v = c.cacheQuery q (y v) := by
  simp [cacheStep, h]

theorem cacheStep_of_eq_none (x : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (c : Cache) {v : Fin G.size} (h : G.point x v = none) :
    G.cacheStep x y c v = c := by
  simp [cacheStep, h]

theorem foldl_cacheStep_eq_some_iff (T : G.Tagging) {x : G.Assignment} (hx : G.TagOK T x)
    (y : Fin G.size → BitVec hashBits) (q : Query) (w : BitVec hashBits) :
    ∀ (l : List (Fin G.size)) (c : Cache),
      (l.foldl (G.cacheStep x y) c) q = some w ↔
        (∃ v ∈ l, G.point x v = some q ∧ y v = w) ∨
          (c q = some w ∧ ∀ v ∈ l, G.point x v ≠ some q)
  | [], c => by simp
  | a :: l, c => by
    rw [List.foldl_cons, foldl_cacheStep_eq_some_iff T hx y q w l]
    rcases ha : G.point x a with _ | q'
    · rw [G.cacheStep_of_eq_none x y c ha]
      simp only [List.mem_cons, exists_eq_or_imp, ha, reduceCtorEq, false_and, false_or,
        forall_eq_or_imp, ne_eq, not_false_eq_true, true_and]
    · rw [G.cacheStep_of_eq_some x y c ha]
      by_cases hq : q' = q
      · subst hq
        rw [QueryCache.cacheQuery_self]
        simp only [List.mem_cons, exists_eq_or_imp, ha, true_and, forall_eq_or_imp, ne_eq,
          not_true_eq_false, false_and, and_false, or_false, Option.some.injEq]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact Or.inr h
          · exact Or.inl h
        · rintro (h | ⟨v, hv, hvq, hw⟩)
          · by_cases hl : ∃ v ∈ l, G.point x v = some q' ∧ y v = w
            · exact Or.inl hl
            · refine Or.inr ⟨h, fun v hv hvq => hl ⟨v, hv, hvq, ?_⟩⟩
              rw [G.point_inj T hx hx hvq ha, h]
          · exact Or.inl ⟨v, hv, hvq, hw⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]
        have hne : G.point x a ≠ some q := by rw [ha]; intro h; exact hq (Option.some.inj h)
        simp only [List.mem_cons, exists_eq_or_imp, ha, forall_eq_or_imp, ne_eq]
        constructor
        · rintro (h | ⟨hc, hl⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨hc, fun h => hq (Option.some.inj h), hl⟩
        · rintro ((⟨h, -⟩ | h) | ⟨hc, -, hl⟩)
          · exact absurd h (fun h => hq (Option.some.inj h))
          · exact Or.inl h
          · exact Or.inr ⟨hc, hl⟩

/-- The assignment of a record carries the right tags: the parent of a hash node is a
deterministic node, whose value in `G.evalRec ξ` is its function applied to `G.evalRec ξ`. -/
theorem tagOK_evalRec (T : G.Tagging) (ξ : G.Rec) : G.TagOK T (G.evalRec ξ) := by
  intro v q hq
  obtain ⟨p, hp, hl, hk, rfl⟩ := (G.point_eq_some_iff _ v q).1 hq
  obtain ⟨ps, hps, f, hf, hkp, htag⟩ := T.tag_parent v p hp hl hk
  have hval : G.evalRec ξ p = f (G.evalRec ξ) := by
    have h := G.evalRec_apply ξ p
    rw [hkp] at h
    exact h
  rw [hval]
  exact htag _

theorem keygenCache_apply_iff (T : G.Tagging) (ξ : G.Rec) (q : Query) (w : BitVec hashBits) :
    G.keygenCache ξ q = some w ↔ ∃ v, G.point (G.evalRec ξ) v = some q ∧ ξ.2 v = w := by
  rw [keygenCache_eq, G.foldl_cacheStep_eq_some_iff T (G.tagOK_evalRec T ξ)]
  simp [List.mem_finRange]

/-! ## Node-kind case lemmas -/

theorem point_of_kind_eq_hash (x : G.Assignment) {v p : Fin G.size} {hp : p < v}
    {hl : G.len v = hashBits} (hk : G.kind v = .hash p hp hl) :
    G.point x v = some ⟨G.len p, x p⟩ := by
  simp [point, hk]

theorem point_of_kind_eq_source (x : G.Assignment) {v : Fin G.size} (hk : G.kind v = .source) :
    G.point x v = none := by
  simp [point, hk]

theorem point_of_kind_eq_det (x : G.Assignment) {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) : G.point x v = none := by
  simp [point, hk]

theorem recVal_of_kind_eq_hash (ξ : G.Rec) {v p : Fin G.size} {hp : p < v}
    {hl : G.len v = hashBits} (hk : G.kind v = .hash p hp hl) (x : G.Assignment) :
    G.recVal ξ v x = (ξ.2 v).cast hl.symm := by
  simp [recVal, hk, NodeKind.value]

theorem recVal_of_kind_eq_source (ξ : G.Rec) {v : Fin G.size} (hk : G.kind v = .source)
    (x : G.Assignment) : G.recVal ξ v x = ξ.1 v := by
  simp [recVal, hk, NodeKind.value]

theorem recVal_of_kind_eq_det (ξ : G.Rec) {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) (x : G.Assignment) : G.recVal ξ v x = f x := by
  simp [recVal, hk, NodeKind.value]

theorem evalNode_of_kind_eq_hash (x : G.Assignment) {v p : Fin G.size} {hp : p < v}
    {hl : G.len v = hashBits} (hk : G.kind v = .hash p hp hl)
    (s : OracleComp Spec (BitVec (G.len v))) :
    G.evalNode x v s = (fun y => y.cast hl.symm) <$> hash (x p) := by
  simp [evalNode, hk]

theorem evalNode_of_kind_eq_source (x : G.Assignment) {v : Fin G.size} (hk : G.kind v = .source)
    (s : OracleComp Spec (BitVec (G.len v))) : G.evalNode x v s = s := by
  simp [evalNode, hk]

theorem evalNode_of_kind_eq_det (x : G.Assignment) {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) (s : OracleComp Spec (BitVec (G.len v))) :
    G.evalNode x v s = pure (f x) := by
  simp [evalNode, hk]

theorem nodeCost_of_kind_eq_source {v : Fin G.size} (hk : G.kind v = .source) :
    G.nodeCost v = 0 := by
  simp [nodeCost, hk]

theorem nodeCost_of_kind_eq_det {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) : G.nodeCost v = 0 := by
  simp [nodeCost, hk]

end Dag.Graph

/-! ## Folds of updates -/

theorem foldl_update_apply_of_not_mem {ι : Type} [DecidableEq ι] {β : ι → Type}
    (h : ((i : ι) → β i) → (i : ι) → β i) :
    ∀ (l : List ι) (x : (i : ι) → β i) (w : ι), w ∉ l →
      (l.foldl (fun x v => Function.update x v (h x v)) x) w = x w
  | [], _, _, _ => rfl
  | a :: l, x, w, hw => by
    simp only [List.mem_cons, not_or] at hw
    rw [List.foldl_cons, foldl_update_apply_of_not_mem h l _ w hw.2]
    exact Function.update_of_ne hw.1 _ _

theorem foldl_update_apply_of_mem {ι : Type} [DecidableEq ι] {β : ι → Type}
    (y : (i : ι) → β i) :
    ∀ (l : List ι) (x : (i : ι) → β i) (w : ι), w ∈ l →
      (l.foldl (fun x v => Function.update x v (y v)) x) w = y w
  | [], _, _, hw => by simp at hw
  | a :: l, x, w, hw => by
    rw [List.foldl_cons]
    by_cases hl : w ∈ l
    · exact foldl_update_apply_of_mem y l _ w hl
    · have hwa : w = a := by
        simp only [List.mem_cons] at hw
        exact hw.resolve_right hl
      subst hwa
      rw [foldl_update_apply_of_not_mem (fun _ v => y v) l _ w hl, Function.update_self]

theorem foldl_update_finRange {n : ℕ} {β : Fin n → Type} (y x : (i : Fin n) → β i) :
    (List.finRange n).foldl (fun x v => Function.update x v (y v)) x = y := by
  funext w
  exact foldl_update_apply_of_mem y _ x w (List.mem_finRange w)

theorem foldl_update_of_update_not_mem {ι : Type} [DecidableEq ι] {β : ι → Type}
    (y : (i : ι) → β i) {a : ι} (u' : β a) (l : List ι) (ha : a ∉ l) (x : (i : ι) → β i) :
    l.foldl (fun x v => Function.update x v (Function.update y a u' v)) x =
      l.foldl (fun x v => Function.update x v (y v)) x := by
  refine List.foldl_ext _ _ x fun x v hv => ?_
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  rw [Function.update_of_ne hva]

/-! ## Averaging over one coordinate -/

theorem sum_sum_update_pi {ι : Type} [Fintype ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, Fintype (R i)] (H : ((i : ι) → R i) → ℝ≥0∞) (i : ι) :
    ∑ u : R i, ∑ g : (j : ι) → R j, H (Function.update g i u) =
      Fintype.card (R i) * ∑ g, H g := by
  let φ : ((j : ι) → R j) × R i → ((j : ι) → R j) × R i :=
    fun p => (Function.update p.1 i p.2, p.1 i)
  have hφ : Function.Involutive φ := by
    intro p
    simp [φ]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun g u => H (Function.update g i u))]
  have := Equiv.sum_comp hφ.toPerm (fun p => H p.1)
  simp only [Function.Involutive.coe_toPerm, φ] at this
  rw [this, Fintype.sum_prod_type]
  simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, mul_comm]

theorem sum_inv_card_mul' {α : Type} [Fintype α] [Nonempty α] (a : ℝ≥0∞) :
    ∑ _x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

/-- Averaging a function of a fresh uniform coordinate `u` and a uniform table `y` that does not
read `y i` equals averaging over `y` alone with `u := y i`. -/
theorem sum_avg_update {ι : Type} [Fintype ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)] (i : ι) (Φ : R i → ((j : ι) → R j) → ℝ≥0∞)
    (hΦ : ∀ u u' y, Φ u (Function.update y i u') = Φ u y) :
    ∑ u : R i, (Fintype.card (R i) : ℝ≥0∞)⁻¹ *
        ∑ y : (j : ι) → R j, (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * Φ u y =
      ∑ y : (j : ι) → R j, (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * Φ (y i) y := by
  have key := sum_sum_update_pi (fun y => Φ (y i) y) i
  simp only [Function.update_self, hΦ] at key
  have hn0 : (Fintype.card (R i) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnt : (Fintype.card (R i) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [← Finset.mul_sum]
  rw [key]
  calc (Fintype.card (R i) : ℝ≥0∞)⁻¹ * ((Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ *
        (Fintype.card (R i) * ∑ y, Φ (y i) y))
      = ((Fintype.card (R i) : ℝ≥0∞)⁻¹ * Fintype.card (R i)) *
          ((Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * ∑ y, Φ (y i) y) := by ring
    _ = (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * ∑ y, Φ (y i) y := by
        rw [ENNReal.inv_mul_cancel hn0 hnt, one_mul]

/-! ## Running a single query -/

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem run_query (t : Spec.Domain) (c : Cache) :
    run (liftM (Spec.query t)) c = (oracleImpl t).run c := by
  simp only [run, simulateQ_spec_query]

/-! ## Sampling the sources -/

namespace Dag.Graph

variable (G : Graph)

theorem E_run_sampleFold (g : G.Assignment × Cache → ℝ≥0∞) :
    ∀ (l : List (Fin G.size)), l.Nodup → ∀ (z : G.Assignment) (c : Cache),
      E (run (l.foldlM (fun z v => Function.update z v <$> sampleBits (G.len v)) z) c) g =
        ∑ y : G.Assignment, (Fintype.card G.Assignment : ℝ≥0∞)⁻¹ *
          g (l.foldl (fun z v => Function.update z v (y v)) z, c)
  | [], _, z, c => by
    rw [List.foldlM_nil, run_pure, E_pure]
    simp only [List.foldl_nil, sum_inv_card_mul']
  | a :: l, hnd, z, c => by
    rw [List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    rw [List.foldlM_cons, run_bind, E_bind, sampleBits, run_map, run_liftM]
    simp only [E_map, E_uniform, E_run_sampleFold g l hnd, List.foldl_cons]
    refine sum_avg_update (R := fun v => BitVec (G.len v)) a
      (fun u y => g (l.foldl (fun z v => Function.update z v (y v)) (Function.update z a u), c))
      fun u u' y => ?_
    simp only [foldl_update_of_update_not_mem y u' l ha]

theorem E_run_sampleAssignment (g : G.Assignment × Cache → ℝ≥0∞) (c : Cache) :
    E (run G.sampleAssignment c) g =
      ∑ y : G.Assignment, (Fintype.card G.Assignment : ℝ≥0∞)⁻¹ * g (y, c) := by
  unfold Graph.sampleAssignment
  rw [G.E_run_sampleFold g _ (List.nodup_finRange _)]
  simp only [foldl_update_finRange]

/-! ## Evaluating the nodes -/

/-- The cache `c` holds no query tagged with a node of `l`. -/
def Fresh (T : G.Tagging) (l : List (Fin G.size)) (c : Cache) : Prop :=
  ∀ v ∈ l, ∀ q : Query, T.tag q = some v → c q = none

theorem fresh_empty (T : G.Tagging) (l : List (Fin G.size)) : G.Fresh T l ∅ :=
  fun _ _ _ _ => rfl

theorem Fresh.tail {T : G.Tagging} {a : Fin G.size} {l : List (Fin G.size)} {c : Cache}
    (h : G.Fresh T (a :: l) c) : G.Fresh T l c :=
  fun v hv => h v (List.mem_cons_of_mem a hv)

theorem Fresh.cacheQuery {T : G.Tagging} {a : Fin G.size} {l : List (Fin G.size)} {c : Cache}
    (h : G.Fresh T (a :: l) c) (ha : a ∉ l) {q : Query} (hq : T.tag q = some a)
    (u : BitVec hashBits) : G.Fresh T l (c.cacheQuery q u) := by
  intro v hv q' hq'
  have hne : q' ≠ q := by
    rintro rfl
    have hva : v = a := Option.some.inj (hq'.symm.trans hq)
    exact ha (hva ▸ hv)
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact h v (List.mem_cons_of_mem a hv) q' hq'

/-- Every hash node of `l` whose parent is not in `l` (so has been evaluated already) has, in the
assignment `x`, an input carrying its tag. -/
def Tagged (T : G.Tagging) (l : List (Fin G.size)) (x : G.Assignment) : Prop :=
  ∀ v ∈ l, ∀ p hp hl, G.kind v = .hash p hp hl → p ∉ l → T.tag ⟨G.len p, x p⟩ = some v

theorem tagged_finRange (T : G.Tagging) (x : G.Assignment) :
    G.Tagged T (List.finRange G.size) x :=
  fun _ _ p _ _ _ hp => absurd (List.mem_finRange p) hp

/-- Evaluating the head `a` keeps the invariant, provided a deterministic node gets the value of
its function. A source or a hash node is never the parent of a hash node. -/
theorem Tagged.update {T : G.Tagging} {a : Fin G.size} {l : List (Fin G.size)}
    {x : G.Assignment} (h : G.Tagged T (a :: l) x) (u : BitVec (G.len a))
    (hu : ∀ ps hps f hf, G.kind a = .det ps hps f hf → u = f x) :
    G.Tagged T l (Function.update x a u) := by
  intro v hv p hp hl hk hpl
  obtain ⟨ps, hps, f, hf, hkp, htag⟩ := T.tag_parent v p hp hl hk
  by_cases hpa : p = a
  · subst hpa
    rw [Function.update_self, hu ps hps f hf hkp]
    exact htag x
  · rw [Function.update_of_ne hpa]
    refine h v (List.mem_cons_of_mem a hv) p hp hl hk ?_
    simp only [List.mem_cons, not_or]
    exact ⟨hpa, hpl⟩

theorem foldl_recVal_update_of_not_mem (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    {a : Fin G.size} (u' : BitVec hashBits) (l : List (Fin G.size)) (ha : a ∉ l)
    (x : G.Assignment) :
    l.foldl (fun x v => Function.update x v (G.recVal (z, Function.update y a u') v x)) x =
      l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x)) x := by
  refine List.foldl_ext _ _ x fun x v hv => ?_
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  simp only [recVal, Function.update_of_ne hva]

theorem foldl_cacheStep_update_of_not_mem (Fn : G.Assignment) (y : Fin G.size → BitVec hashBits)
    {a : Fin G.size} (u' : BitVec hashBits) (l : List (Fin G.size)) (ha : a ∉ l)
    (c : Cache) :
    l.foldl (G.cacheStep Fn (Function.update y a u')) c = l.foldl (G.cacheStep Fn y) c := by
  refine List.foldl_ext _ _ c fun c v hv => ?_
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  simp only [cacheStep, Function.update_of_ne hva]

theorem E_run_evalFold (T : G.Tagging) (z : G.Assignment)
    (g : G.Assignment × Cache → ℝ≥0∞) :
    ∀ (l : List (Fin G.size)), l.Pairwise (· < ·) → ∀ (x : G.Assignment) (c : Cache),
      G.Fresh T l c → G.Tagged T l x →
      E (run (l.foldlM (fun x v => Function.update x v <$> G.evalNode x v (pure (z v))) x) c)
          g =
        ∑ y : Fin G.size → BitVec hashBits,
          (Fintype.card (Fin G.size → BitVec hashBits) : ℝ≥0∞)⁻¹ *
            g (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x)) x,
              l.foldl (G.cacheStep
                (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x)) x) y) c)
  | [], _, x, c, _, _ => by
    rw [List.foldlM_nil, run_pure, E_pure]
    simp only [List.foldl_nil, sum_inv_card_mul']
  | a :: l, hpw, x, c, hfresh, htagged => by
    rw [List.pairwise_cons] at hpw
    obtain ⟨hlt, hpw⟩ := hpw
    have ha : a ∉ l := fun h => lt_irrefl a (hlt a h)
    rw [List.foldlM_cons, run_bind, E_bind]
    rcases hk : G.kind a with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
    · rw [G.evalNode_of_kind_eq_source x hk, run_map, run_pure, E_map, E_pure]
      rw [E_run_evalFold T z g l hpw _ c (Fresh.tail G hfresh)
        (Tagged.update G htagged _ fun _ _ _ _ h => by rw [hk] at h; cases h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [List.foldl_cons, G.recVal_of_kind_eq_source _ hk,
        G.cacheStep_of_eq_none _ _ _ (G.point_of_kind_eq_source _ hk)]
    · rw [G.evalNode_of_kind_eq_det x hk, run_map, run_pure, E_map, E_pure]
      rw [E_run_evalFold T z g l hpw _ c (Fresh.tail G hfresh)
        (Tagged.update G htagged _ fun _ _ _ _ h => by
          rw [hk, NodeKind.det.injEq] at h; rw [h.2])]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [List.foldl_cons, G.recVal_of_kind_eq_det _ hk,
        G.cacheStep_of_eq_none _ _ _ (G.point_of_kind_eq_det _ hk)]
    · have hpa : p ∉ a :: l := by
        simp only [List.mem_cons, not_or]
        exact ⟨ne_of_lt hp, fun h => lt_asymm hp (hlt p h)⟩
      -- the input of `a` carries the tag of `a`, so the cache does not hold it
      have htq : T.tag ⟨G.len p, x p⟩ = some a :=
        htagged a (List.mem_cons_self ..) p hp hl hk hpa
      have hcq : c ⟨G.len p, x p⟩ = none := hfresh a (List.mem_cons_self ..) _ htq
      rw [G.evalNode_of_kind_eq_hash x hk, hash, run_map, run_map, run_query,
        oracleImpl_run_inr_none hcq]
      simp only [E_map, E_bind, E_pure, E_uniform]
      have key := sum_avg_update (R := fun _ => BitVec hashBits) a
        (fun u y => g (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x))
            (Function.update x a (u.cast hl.symm)),
          l.foldl (G.cacheStep (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x))
            (Function.update x a (u.cast hl.symm))) y)
            (c.cacheQuery ⟨G.len p, x p⟩ u)))
        (fun u u' y => by
          simp only [G.foldl_recVal_update_of_not_mem z y u' l ha,
            G.foldl_cacheStep_update_of_not_mem _ y u' l ha])
      refine Eq.trans ?_ (key.trans ?_)
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [E_run_evalFold T z g l hpw _ _ (Fresh.cacheQuery G hfresh ha htq u)
          (Tagged.update G htagged _ fun _ _ _ _ h => by rw [hk] at h; cases h)]
      · refine Finset.sum_congr rfl fun y _ => ?_
        have hF : G.point ((a :: l).foldl
            (fun x v => Function.update x v (G.recVal (z, y) v x)) x) a =
            some ⟨G.len p, x p⟩ := by
          rw [G.point_of_kind_eq_hash _ hk,
            foldl_update_apply_of_not_mem (fun x v => G.recVal (z, y) v x) _ x p hpa]
        simp only [List.foldl_cons] at hF ⊢
        rw [G.cacheStep_of_eq_some _ _ _ hF, G.recVal_of_kind_eq_hash _ hk]

theorem E_run_evaluate (T : G.Tagging) (z : G.Assignment)
    (g : G.Assignment × Cache → ℝ≥0∞) :
    E (run (G.evaluate z) ∅) g =
      ∑ y : Fin G.size → BitVec hashBits,
        (Fintype.card (Fin G.size → BitVec hashBits) : ℝ≥0∞)⁻¹ *
          g (G.evalRec (z, y), G.keygenCache (z, y)) := by
  unfold Graph.evaluate
  rw [G.E_run_evalFold T z g _ (List.pairwise_lt_finRange _) _ ∅ (G.fresh_empty T _)
    (G.tagged_finRange T _)]
  rfl

end Dag.Graph

/-- Key generation of a tagged graph is a uniform record. -/
theorem E_run_keygen (S : GScheme) (T : S.graph.Tagging)
    (g : (PublicKey × S.graph.Assignment) × Cache → ℝ≥0∞) :
    E (run S.keygen ∅) g =
      ∑ ξ : S.graph.Rec, (Fintype.card S.graph.Rec : ℝ≥0∞)⁻¹ *
        g ((S.publicKey (S.graph.evalRec ξ), S.graph.evalRec ξ), S.graph.keygenCache ξ) := by
  have hA0 : (Fintype.card S.graph.Assignment : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hAt : (Fintype.card S.graph.Assignment : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold GScheme.keygen Graph.keygen
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  rw [run_bind, E_bind, S.graph.E_run_sampleAssignment]
  simp only [S.graph.E_run_evaluate T]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), mul_assoc]

/-! ## Budgets -/

/-- A lifted `ProbComp` costs nothing: the continuation keeps the whole budget. -/
theorem costAtMost_liftM_bind {α β : Type} (pc : ProbComp α)
    (k : α → OracleComp Spec β) {b : ℕ}
    (h : CostAtMost ((liftM pc : OracleComp Spec α) >>= k) b) :
    ∀ x ∈ support pc, CostAtMost (k x) b := by
  change CostAtMost (liftComp pc Spec >>= k) b at h
  induction pc using OracleComp.inductionOn generalizing b with
  | pure x =>
    intro x' hx'
    rw [support_pure, Set.mem_singleton_iff] at hx'
    subst hx'
    rwa [liftComp_pure, pure_bind] at h
  | query_bind t mx ih =>
    intro x hx
    rw [liftComp_bind] at h
    have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
        (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
      simp [liftComp]; rfl
    rw [hq, bind_assoc, costAtMost_query_bind_iff] at h
    obtain ⟨-, h⟩ := h
    rw [support_bind] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, -, hx⟩ := hx
    have := ih u (h u) x hx
    simpa [queryCost] using this

namespace Dag.Graph

variable (G : Graph)

theorem costAtMost_sampleFold_bind {β : Type} (k : G.Assignment → OracleComp Spec β)
    {b : ℕ} :
    ∀ (l : List (Fin G.size)) (z : G.Assignment),
      CostAtMost
        (l.foldlM (fun z v => Function.update z v <$> sampleBits (G.len v)) z >>= k) b →
      ∀ y : G.Assignment, CostAtMost (k (l.foldl (fun z v => Function.update z v (y v)) z)) b
  | [], z, h, y => by rwa [List.foldlM_nil, pure_bind] at h
  | a :: l, z, h, y => by
    rw [List.foldlM_cons, bind_assoc, sampleBits, bind_map_left] at h
    have := costAtMost_liftM_bind _ _ h (y a) (by simp)
    exact costAtMost_sampleFold_bind k l _ this y

theorem costAtMost_evalFold_bind (z : G.Assignment) {β : Type}
    (k : G.Assignment → OracleComp Spec β) :
    ∀ (l : List (Fin G.size)) (x : G.Assignment) (b : ℕ),
      CostAtMost
        (l.foldlM (fun x v => Function.update x v <$> G.evalNode x v (pure (z v))) x >>= k) b →
      (l.map G.nodeCost).sum ≤ b ∧
        ∀ y : Fin G.size → BitVec hashBits,
          CostAtMost (k (l.foldl (fun x v => Function.update x v (G.recVal (z, y) v x)) x))
            (b - (l.map G.nodeCost).sum)
  | [], x, b, h => by
    refine ⟨by simp, fun y => ?_⟩
    rw [List.foldlM_nil, pure_bind] at h
    simpa using h
  | a :: l, x, b, h => by
    rw [List.foldlM_cons, bind_assoc] at h
    rw [List.map_cons, List.sum_cons]
    rcases hk : G.kind a with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
    · rw [G.evalNode_of_kind_eq_source x hk, map_pure, pure_bind] at h
      obtain ⟨h1, h2⟩ := costAtMost_evalFold_bind z k l _ b h
      rw [G.nodeCost_of_kind_eq_source hk, zero_add]
      refine ⟨h1, fun y => ?_⟩
      simp only [List.foldl_cons, G.recVal_of_kind_eq_source _ hk]
      exact h2 y
    · rw [G.evalNode_of_kind_eq_det x hk, map_pure, pure_bind] at h
      obtain ⟨h1, h2⟩ := costAtMost_evalFold_bind z k l _ b h
      rw [G.nodeCost_of_kind_eq_det hk, zero_add]
      refine ⟨h1, fun y => ?_⟩
      simp only [List.foldl_cons, G.recVal_of_kind_eq_det _ hk]
      exact h2 y
    · rw [G.evalNode_of_kind_eq_hash x hk, hash, bind_map_left, bind_map_left,
        costAtMost_query_bind_iff] at h
      obtain ⟨hc, h⟩ := h
      have hcost : queryCost (.inr ⟨G.len p, x p⟩) = G.nodeCost a := by
        simp [queryCost, nodeCost, hk]
      rw [hcost] at hc h
      refine ⟨?_, fun y => ?_⟩
      · have := (costAtMost_evalFold_bind z k l _ _ (h (0 : BitVec hashBits))).1
        omega
      · have := (costAtMost_evalFold_bind z k l _ _ (h (y a))).2 y
        simp only [List.foldl_cons, G.recVal_of_kind_eq_hash _ hk]
        rw [Nat.sub_add_eq]
        exact this

end Dag.Graph

/-- A budget for `S.keygen >>= k` covers key generation and leaves `B - keygenCost` for the
continuation at every record. -/
theorem costAtMost_keygen_bind (S : GScheme) {β : Type}
    (k : PublicKey × S.graph.Assignment → OracleComp Spec β) {B : ℕ}
    (h : CostAtMost (S.keygen >>= k) B) :
    S.graph.keygenCost ≤ B ∧ ∀ ξ : S.graph.Rec,
      CostAtMost (k (S.publicKey (S.graph.evalRec ξ), S.graph.evalRec ξ))
        (B - S.graph.keygenCost) := by
  have h' : CostAtMost (S.graph.sampleAssignment >>= fun z =>
      S.graph.evaluate z >>= fun x => k (S.publicKey x, x)) B := by
    simpa only [GScheme.keygen, Graph.keygen, bind_assoc, pure_bind] using h
  unfold Graph.sampleAssignment at h'
  have hs := S.graph.costAtMost_sampleFold_bind _ _ _ h'
  simp only [foldl_update_finRange] at hs
  have he : ∀ z : S.graph.Assignment,
      ((List.finRange S.graph.size).map S.graph.nodeCost).sum ≤ B ∧
        ∀ y : Fin S.graph.size → BitVec hashBits,
          CostAtMost (k (S.publicKey (S.graph.evalRec (z, y)), S.graph.evalRec (z, y)))
            (B - ((List.finRange S.graph.size).map S.graph.nodeCost).sum) := fun z =>
    S.graph.costAtMost_evalFold_bind z (fun x => k (S.publicKey x, x)) _ _ B (hs z)
  have hK : S.graph.keygenCost = ((List.finRange S.graph.size).map S.graph.nodeCost).sum := by
    rw [Graph.keygenCost, Fin.sum_univ_def]
  rw [hK]
  exact ⟨(he (fun _ => 0)).1, fun ξ => (he ξ.1).2 ξ.2⟩

end OptimalOTS
