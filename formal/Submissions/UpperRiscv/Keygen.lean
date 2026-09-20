import Submissions.UpperRiscv.Master
import Submissions.UpperRiscv.Semantics
import Submissions.UpperRiscv.GScheme

/-!
# Key generation under the lazy random oracle

Key generation samples every source and queries every hash node once. The oracle has no labels
and the scheme uses none: two hash nodes with equal inputs share one oracle answer. Under the
lazy random oracle started from the empty cache, key generation is the real evaluation
`G.realEval ξ` of a uniformly random record `ξ : G.Rec` (`E_run_keygen_real`), which agrees with
the ideal evaluation `G.evalRec ξ` and the cache `G.keygenCache ξ` whenever the keygen points of
the record are pairwise distinct (`realEval_eq_of_distinct`). Hence the expectation of any
function bounded by one is at most its uniform average over records, up to the probability of a
collision (`E_run_keygen_le`).

* `Graph.Distinct`: the keygen points of an assignment are pairwise distinct;
* `E_run_keygen_real`, `E_run_keygen_le`: key generation as a uniform record;
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

/-- The keygen points of the assignment `x` are pairwise distinct. -/
def Distinct (x : G.Assignment) : Prop :=
  ∀ v v' q, G.point x v = some q → G.point x v' = some q → v = v'

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

theorem foldl_cacheStep_eq_some_iff {x : G.Assignment} (hx : G.Distinct x)
    (y : Fin G.size → BitVec hashBits) (q : Query) (w : BitVec hashBits) :
    ∀ (l : List (Fin G.size)) (c : Cache),
      (l.foldl (G.cacheStep x y) c) q = some w ↔
        (∃ v ∈ l, G.point x v = some q ∧ y v = w) ∨
          (c q = some w ∧ ∀ v ∈ l, G.point x v ≠ some q)
  | [], c => by simp
  | a :: l, c => by
    rw [List.foldl_cons, foldl_cacheStep_eq_some_iff hx y q w l]
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
              rw [hx v a q' hvq ha, h]
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

theorem keygenCache_apply_iff {ξ : G.Rec} (hξ : G.Distinct (G.evalRec ξ)) (q : Query)
    (w : BitVec hashBits) :
    G.keygenCache ξ q = some w ↔ ∃ v, G.point (G.evalRec ξ) v = some q ∧ ξ.2 v = w := by
  rw [keygenCache_eq, G.foldl_cacheStep_eq_some_iff hξ]
  simp [List.mem_finRange]

/-- Every keygen point is present in the keygen cache. -/
theorem keygenCache_isSome_of_point (ξ : G.Rec) (v : Fin G.size) (q : Query)
    (hv : G.point (G.evalRec ξ) v = some q) : (G.keygenCache ξ q).isSome := by
  rw [keygenCache_eq]
  have hmono : ∀ (l : List (Fin G.size)) (c : Cache), (c q).isSome →
      ((l.foldl (G.cacheStep (G.evalRec ξ) ξ.2) c) q).isSome := by
    intro l
    induction l with
    | nil => intro c h; exact h
    | cons a l ih =>
      intro c h
      rw [List.foldl_cons]
      refine ih _ ?_
      rcases ha : G.point (G.evalRec ξ) a with _ | q'
      · rw [G.cacheStep_of_eq_none _ _ _ ha]; exact h
      · rw [G.cacheStep_of_eq_some _ _ _ ha]
        by_cases hq : q' = q
        · subst hq; rw [QueryCache.cacheQuery_self]; rfl
        · rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]; exact h
  suffices key : ∀ (l : List (Fin G.size)) (c : Cache), v ∈ l →
      ((l.foldl (G.cacheStep (G.evalRec ξ) ξ.2) c) q).isSome from
    key _ ∅ (List.mem_finRange v)
  intro l
  induction l with
  | nil => intro c h; exact absurd h List.not_mem_nil
  | cons a l ih =>
    intro c h
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine hmono l _ ?_
      rw [G.cacheStep_of_eq_some _ _ _ hv, QueryCache.cacheQuery_self]
      rfl
    · exact ih _ h

/-- Without injectivity, an entry of the keygen cache is still the point of some hash node. -/
theorem keygenCache_apply_some (ξ : G.Rec) (q : Query) (w : BitVec hashBits)
    (h : G.keygenCache ξ q = some w) : ∃ v, G.point (G.evalRec ξ) v = some q ∧ ξ.2 v = w := by
  rw [keygenCache_eq] at h
  suffices key : ∀ (l : List (Fin G.size)) (c : Cache),
      (l.foldl (G.cacheStep (G.evalRec ξ) ξ.2) c) q = some w →
        (∃ v ∈ l, G.point (G.evalRec ξ) v = some q ∧ ξ.2 v = w) ∨ c q = some w by
    rcases key _ ∅ h with ⟨v, -, hv, hw⟩ | h'
    · exact ⟨v, hv, hw⟩
    · cases h'
  intro l
  induction l with
  | nil => intro c h; exact Or.inr h
  | cons a l ih =>
    intro c h
    rw [List.foldl_cons] at h
    rcases ih _ h with ⟨v, hv, hvq, hw⟩ | h'
    · exact Or.inl ⟨v, List.mem_cons_of_mem a hv, hvq, hw⟩
    · rcases ha : G.point (G.evalRec ξ) a with _ | q'
      · rw [G.cacheStep_of_eq_none _ _ _ ha] at h'
        exact Or.inr h'
      · rw [G.cacheStep_of_eq_some _ _ _ ha] at h'
        by_cases hq : q' = q
        · subst hq
          rw [QueryCache.cacheQuery_self, Option.some.injEq] at h'
          exact Or.inl ⟨a, List.mem_cons_self .., ha, h'⟩
        · rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)] at h'
          exact Or.inr h'

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

/-! ## Evaluating the nodes

The real evaluation mirrors the lazy oracle: a hash node whose input is already cached takes
the cached answer, a fresh input takes the record's coordinate and caches it. -/

/-- One step of the real evaluation with sources `z` and fresh answers `y`. -/
def realStep (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (s : G.Assignment × Cache) (v : Fin G.size) : G.Assignment × Cache :=
  match G.kind v with
  | .hash p _ hl =>
    match s.2 ⟨G.len p, s.1 p⟩ with
    | some w => (Function.update s.1 v (w.cast hl.symm), s.2)
    | none => (Function.update s.1 v ((y v).cast hl.symm),
        s.2.cacheQuery ⟨G.len p, s.1 p⟩ (y v))
  | .source => (Function.update s.1 v (z v), s.2)
  | .det _ _ f _ => (Function.update s.1 v (f s.1), s.2)

theorem realStep_of_kind_eq_source (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (s : G.Assignment × Cache) {v : Fin G.size} (hk : G.kind v = .source) :
    G.realStep z y s v = (Function.update s.1 v (z v), s.2) := by
  simp [realStep, hk]

theorem realStep_of_kind_eq_det (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (s : G.Assignment × Cache) {v : Fin G.size} {ps hps f hf}
    (hk : G.kind v = .det ps hps f hf) :
    G.realStep z y s v = (Function.update s.1 v (f s.1), s.2) := by
  simp [realStep, hk]

theorem realStep_of_kind_eq_hash_some (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (s : G.Assignment × Cache) {v p : Fin G.size} {hp : p < v} {hl : G.len v = hashBits}
    (hk : G.kind v = .hash p hp hl) {w : BitVec hashBits} (hc : s.2 ⟨G.len p, s.1 p⟩ = some w) :
    G.realStep z y s v = (Function.update s.1 v (w.cast hl.symm), s.2) := by
  simp [realStep, hk, hc]

theorem realStep_of_kind_eq_hash_none (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    (s : G.Assignment × Cache) {v p : Fin G.size} {hp : p < v} {hl : G.len v = hashBits}
    (hk : G.kind v = .hash p hp hl) (hc : s.2 ⟨G.len p, s.1 p⟩ = none) :
    G.realStep z y s v = (Function.update s.1 v ((y v).cast hl.symm),
      s.2.cacheQuery ⟨G.len p, s.1 p⟩ (y v)) := by
  simp [realStep, hk, hc]

/-- The real evaluation of the nodes of `l`. -/
def realFold (z : G.Assignment) (y : Fin G.size → BitVec hashBits) (l : List (Fin G.size))
    (s : G.Assignment × Cache) : G.Assignment × Cache :=
  l.foldl (G.realStep z y) s

theorem realStep_update_of_ne (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    {a : Fin G.size} (u' : BitVec hashBits) (s : G.Assignment × Cache) {v : Fin G.size}
    (hva : v ≠ a) : G.realStep z (Function.update y a u') s v = G.realStep z y s v := by
  simp only [realStep, Function.update_of_ne hva]

theorem realFold_update_of_not_mem (z : G.Assignment) (y : Fin G.size → BitVec hashBits)
    {a : Fin G.size} (u' : BitVec hashBits) (l : List (Fin G.size)) (ha : a ∉ l)
    (s : G.Assignment × Cache) :
    G.realFold z (Function.update y a u') l s = G.realFold z y l s := by
  unfold realFold
  refine List.foldl_ext _ _ s fun s v hv => ?_
  exact G.realStep_update_of_ne z y u' s (fun h => ha (h ▸ hv))

theorem E_run_evalFold (z : G.Assignment) (g : G.Assignment × Cache → ℝ≥0∞) :
    ∀ (l : List (Fin G.size)), l.Nodup → ∀ (x : G.Assignment) (c : Cache),
      E (run (l.foldlM (fun x v => Function.update x v <$> G.evalNode x v (pure (z v))) x) c)
          g =
        ∑ y : Fin G.size → BitVec hashBits,
          (Fintype.card (Fin G.size → BitVec hashBits) : ℝ≥0∞)⁻¹ * g (G.realFold z y l (x, c))
  | [], _, x, c => by
    rw [List.foldlM_nil, run_pure, E_pure]
    simp only [realFold, List.foldl_nil, sum_inv_card_mul']
  | a :: l, hnd, x, c => by
    rw [List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    rw [List.foldlM_cons, run_bind, E_bind]
    rcases hk : G.kind a with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
    · rw [G.evalNode_of_kind_eq_source x hk, run_map, run_pure, E_map, E_pure,
        E_run_evalFold z g l hnd _ c]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [realFold, List.foldl_cons, G.realStep_of_kind_eq_source _ _ _ hk]
    · rw [G.evalNode_of_kind_eq_det x hk, run_map, run_pure, E_map, E_pure,
        E_run_evalFold z g l hnd _ c]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [realFold, List.foldl_cons, G.realStep_of_kind_eq_det _ _ _ hk]
    · rw [G.evalNode_of_kind_eq_hash x hk, hash, run_map, run_map, run_query]
      rcases hc : c ⟨G.len p, x p⟩ with _ | w
      · rw [oracleImpl_run_inr_none hc]
        simp only [E_map, E_bind, E_pure, E_uniform]
        have key := sum_avg_update (R := fun _ => BitVec hashBits) a
          (fun u y => g (G.realFold z y l (Function.update x a (u.cast hl.symm),
            c.cacheQuery ⟨G.len p, x p⟩ u)))
          (fun u u' y => by simp only [G.realFold_update_of_not_mem z y u' l ha])
        refine Eq.trans ?_ (key.trans ?_)
        · refine Finset.sum_congr rfl fun u _ => ?_
          rw [E_run_evalFold z g l hnd _ _]
        · refine Finset.sum_congr rfl fun y _ => ?_
          simp only [realFold, List.foldl_cons]
          rw [G.realStep_of_kind_eq_hash_none _ _ _ hk hc]
      · rw [oracleImpl_run_inr_some hc]
        simp only [E_map, E_pure]
        rw [E_run_evalFold z g l hnd _ c]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [realFold, List.foldl_cons]
        rw [G.realStep_of_kind_eq_hash_some _ _ _ hk hc]

/-- The real evaluation and cache of a record. -/
def realRun (ξ : G.Rec) : G.Assignment × Cache :=
  G.realFold ξ.1 ξ.2 (List.finRange G.size) (fun _ => 0, ∅)

theorem E_run_evaluate (z : G.Assignment) (g : G.Assignment × Cache → ℝ≥0∞) :
    E (run (G.evaluate z) ∅) g =
      ∑ y : Fin G.size → BitVec hashBits,
        (Fintype.card (Fin G.size → BitVec hashBits) : ℝ≥0∞)⁻¹ * g (G.realRun (z, y)) := by
  unfold Graph.evaluate
  rw [G.E_run_evalFold z g _ (List.nodup_finRange _) _ ∅]
  rfl

/-! ## Distinct points: the real evaluation is the ideal one -/

/-- Along an increasing, downward-closed list, the real evaluation agrees with the ideal one
and its cache is the keygen cache of the list, provided the keygen points are distinct. -/
theorem realFold_agree (ξ : G.Rec) (hξ : G.Distinct (G.evalRec ξ)) :
    ∀ (l : List (Fin G.size)), l.Pairwise (· < ·) → (∀ v ∈ l, ∀ w, w < v → w ∈ l) →
      (∀ v ∈ l, (G.realFold ξ.1 ξ.2 l (fun _ => 0, ∅)).1 v = G.evalRec ξ v) ∧
        (G.realFold ξ.1 ξ.2 l (fun _ => 0, ∅)).2 =
          l.foldl (G.cacheStep (G.evalRec ξ) ξ.2) ∅ := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ _; exact ⟨fun v hv => absurd hv List.not_mem_nil, rfl⟩
  | append_singleton l a ih =>
    intro hpw hdc
    rw [List.pairwise_append] at hpw
    obtain ⟨hpw, -, hla⟩ := hpw
    have hal : a ∉ l := fun h => lt_irrefl a (hla a h a (List.mem_singleton_self a))
    have hdc' : ∀ v ∈ l, ∀ w, w < v → w ∈ l := by
      intro v hv w hw
      have := hdc v (List.mem_append_left _ hv) w hw
      rw [List.mem_append, List.mem_singleton] at this
      rcases this with h | rfl
      · exact h
      · exact absurd (lt_trans hw (hla v hv w (List.mem_singleton_self _))) (lt_irrefl _)
    obtain ⟨hagree, hcache⟩ := ih hpw hdc'
    have hparents : ∀ w, w < a → w ∈ l := by
      intro w hw
      have := hdc a (List.mem_append_right _ (List.mem_singleton_self a)) w hw
      rw [List.mem_append, List.mem_singleton] at this
      rcases this with h | rfl
      · exact h
      · exact absurd hw (lt_irrefl _)
    simp only [realFold, List.foldl_append, List.foldl_cons, List.foldl_nil] at hagree hcache ⊢
    set s := l.foldl (G.realStep ξ.1 ξ.2) (fun _ => 0, ∅) with hs
    have hx : ∀ w ∈ (G.kind a).parents, s.1 w = G.evalRec ξ w := fun w hw =>
      hagree w (hparents w ((G.kind a).lt_of_mem_parents hw))
    have hval : G.evalRec ξ a = (G.kind a).value (G.evalRec ξ) (ξ.1 a) (ξ.2 a) :=
      G.evalRec_apply ξ a
    -- the new value at `a`
    have hstep : (G.realStep ξ.1 ξ.2 s a).1 a = G.evalRec ξ a ∧
        (G.realStep ξ.1 ξ.2 s a).2 = G.cacheStep (G.evalRec ξ) ξ.2 s.2 a := by
      rcases hk : G.kind a with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
      · rw [G.realStep_of_kind_eq_source _ _ _ hk, G.cacheStep_of_eq_none _ _ _
          (G.point_of_kind_eq_source _ hk)]
        refine ⟨?_, rfl⟩
        show Function.update s.1 a (ξ.1 a) a = _
        rw [Function.update_self, hval, hk]
        rfl
      · rw [G.realStep_of_kind_eq_det _ _ _ hk, G.cacheStep_of_eq_none _ _ _
          (G.point_of_kind_eq_det _ hk)]
        refine ⟨?_, rfl⟩
        show Function.update s.1 a (f s.1) a = _
        rw [Function.update_self, hval, hk]
        show f s.1 = f (G.evalRec ξ)
        refine hf _ _ fun w hw => hx w ?_
        rw [hk]; exact hw
      · have hpp : s.1 p = G.evalRec ξ p := hx p (by rw [hk]; simp [NodeKind.parents])
        have hq : G.point (G.evalRec ξ) a = some ⟨G.len p, s.1 p⟩ := by
          rw [G.point_of_kind_eq_hash _ hk, hpp]
        have hc : s.2 ⟨G.len p, s.1 p⟩ = none := by
          rcases hc : s.2 ⟨G.len p, s.1 p⟩ with _ | w
          · rfl
          · exfalso
            rw [hcache] at hc
            have hfold := (G.foldl_cacheStep_eq_some_iff hξ ξ.2 _ w l ∅).1 hc
            rcases hfold with ⟨v, hv, hvq, -⟩ | ⟨h0, -⟩
            · exact hal (hξ v a _ hvq hq ▸ hv)
            · cases h0
        rw [G.realStep_of_kind_eq_hash_none _ _ _ hk hc, G.cacheStep_of_eq_some _ _ _ hq]
        refine ⟨?_, rfl⟩
        show Function.update s.1 a ((ξ.2 a).cast hl.symm) a = _
        rw [Function.update_self, hval, hk]
        rfl
    refine ⟨fun v hv => ?_, ?_⟩
    · rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · have hva : v ≠ a := fun h => hal (h ▸ hv)
        rw [← hagree v hv]
        rcases hk : G.kind a with _ | ⟨ps, hps, f, hf⟩ | ⟨p, hp, hl⟩
        · rw [G.realStep_of_kind_eq_source _ _ _ hk]; exact Function.update_of_ne hva _ _
        · rw [G.realStep_of_kind_eq_det _ _ _ hk]; exact Function.update_of_ne hva _ _
        · rcases hc : s.2 ⟨G.len p, s.1 p⟩ with _ | w
          · rw [G.realStep_of_kind_eq_hash_none _ _ _ hk hc]; exact Function.update_of_ne hva _ _
          · rw [G.realStep_of_kind_eq_hash_some _ _ _ hk hc]; exact Function.update_of_ne hva _ _
      · exact hstep.1
    · rw [hstep.2, hcache]

theorem finRange_downward_closed (v : Fin G.size) (_ : v ∈ List.finRange G.size) (w : Fin G.size)
    (_ : w < v) : w ∈ List.finRange G.size := List.mem_finRange w

/-- With distinct keygen points, the real run is the ideal record evaluation. -/
theorem realRun_eq_of_distinct (ξ : G.Rec) (hξ : G.Distinct (G.evalRec ξ)) :
    G.realRun ξ = (G.evalRec ξ, G.keygenCache ξ) := by
  obtain ⟨h1, h2⟩ := G.realFold_agree ξ hξ (List.finRange G.size) (List.pairwise_lt_finRange _)
    (G.finRange_downward_closed)
  refine Prod.ext (funext fun v => h1 v (List.mem_finRange v)) ?_
  rw [keygenCache_eq]
  exact h2

end Dag.Graph

/-- Key generation is the real evaluation of a uniform record. -/
theorem E_run_keygen_real (S : GScheme)
    (g : (PublicKey × S.graph.Assignment) × Cache → ℝ≥0∞) :
    E (run S.keygen ∅) g =
      ∑ ξ : S.graph.Rec, (Fintype.card S.graph.Rec : ℝ≥0∞)⁻¹ *
        g ((S.publicKey (S.graph.realRun ξ).1, (S.graph.realRun ξ).1), (S.graph.realRun ξ).2) := by
  have hA0 : (Fintype.card S.graph.Assignment : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hAt : (Fintype.card S.graph.Assignment : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold GScheme.keygen Graph.keygen
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  rw [run_bind, E_bind, S.graph.E_run_sampleAssignment]
  simp only [S.graph.E_run_evaluate]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), mul_assoc]

/-- Key generation as a uniform record, up to the records whose keygen points collide. -/
theorem E_run_keygen_le (S : GScheme)
    (g : (PublicKey × S.graph.Assignment) × Cache → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    E (run S.keygen ∅) g ≤
      ∑ ξ : S.graph.Rec, (Fintype.card S.graph.Rec : ℝ≥0∞)⁻¹ *
        (g ((S.publicKey (S.graph.evalRec ξ), S.graph.evalRec ξ), S.graph.keygenCache ξ) +
          if S.graph.Distinct (S.graph.evalRec ξ) then 0 else 1) := by
  rw [E_run_keygen_real]
  refine Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl ?_
  by_cases hξ : S.graph.Distinct (S.graph.evalRec ξ)
  · rw [if_pos hξ, add_zero, S.graph.realRun_eq_of_distinct ξ hξ]
  · rw [if_neg hξ]
    exact le_add_left (hg _)

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
