import Submissions.UpperLeanIsa.FusionRecords
import Submissions.UpperLeanIsa.IUB

/-!
# Cuts, public data and hidden inputs

A *cut* `d` fixes, for every chain `k`, the first position `d k ≤ len k - 1` whose word is
public. Before signing the cut is at the tops (`beforeSigning`); after signing index `I` it is at
the revealed positions `len k - 1 - digit I k` (`afterSigning`). The chain steps strictly below
the cut are *hidden*; everything else (the steps at or after the cut, and all root calls) is
*exposed*.

* `publicData d ξ` (the seeds and answers visible at the cut) determines every exposed query and
  answer (`exposed_query_eq`, `exposed_answer_eq`) and the exposed cache (`exposedCache_data_eq`);
  exposed and hidden caches partition the record cache (`exposure_partition`,
  `exposure_disjoint`).
* Conditioned on the public data, every hidden word is uniform (`hidden_word_charge`, by
  resampling one coordinate), so a single query hits a hidden input of a record of a public
  fiber with probability at most `2 ^ -128` per query, i.e. `2 ^ -129` per compression
  (`hidden_input_charge`); a query that is not a chain step of any record costs nothing.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion

set_option linter.constructorNameAsVariable false

def recW (P : Params) : ℝ≥0∞ := (Fintype.card (Record P) : ℝ≥0∞)⁻¹

variable {P : Params}

attribute [local irreducible] hashBits

/-! ## Resampling one coordinate -/

theorem sum_resample {R V : Type} [Fintype V] [Nonempty V]
    (get : R → V) (put : R → V → R)
    (hget : ∀ r v, get (put r v) = v)
    (hrestore : ∀ r v, put (put r v) (get r) = r)
    (S : Finset R) (hS : ∀ r ∈ S, ∀ v, put r v ∈ S) (f : R → ℝ≥0∞) :
    ∑ r ∈ S, f r = ∑ r ∈ S, (Fintype.card V : ℝ≥0∞)⁻¹ * ∑ v, f (put r v) := by
  have key : ∑ r ∈ S, ∑ v, f (put r v) = ∑ r ∈ S, ∑ _v : V, f r := by
    calc
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset V), f (put p.1 p.2) :=
        (Finset.sum_product' S Finset.univ (fun r v => f (put r v))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset V), f p.1 := by
        refine Finset.sum_nbij' (fun p => (put p.1 p.2, get p.1))
          (fun p => (put p.1 p.2, get p.1)) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p _
          exact Prod.ext (hrestore _ _) (hget _ _)
        · intro p _
          exact Prod.ext (hrestore _ _) (hget _ _)
        · intro p _
          rfl
      _ = _ := Finset.sum_product' S Finset.univ (fun r _ => f r)
  have hc0 : (Fintype.card V : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card V : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

def Record.putSource (ξ : Record P) (k : Fin numChains) (x : Word) : Record P :=
  (Function.update ξ.1 k x, ξ.2)

def Record.putAnswer (ξ : Record P) (a : Loc P) (x : BitVec hashBits) : Record P :=
  (ξ.1, Function.update ξ.2 a x)

theorem putSource_get (ξ : Record P) (k : Fin numChains) (x : Word) :
    (ξ.putSource k x).1 k = x := Function.update_self _ _ _

theorem putAnswer_get (ξ : Record P) (a : Loc P) (x : BitVec hashBits) :
    (ξ.putAnswer a x).2 a = x := Function.update_self _ _ _

theorem putSource_restore (ξ : Record P) (k : Fin numChains) (x : Word) :
    (ξ.putSource k x).putSource k (ξ.1 k) = ξ := by
  apply Prod.ext
  · funext j
    by_cases h : j = k <;> simp [Record.putSource, h]
  · rfl

theorem putAnswer_restore (ξ : Record P) (a : Loc P) (x : BitVec hashBits) :
    (ξ.putAnswer a x).putAnswer a (ξ.2 a) = ξ := by
  apply Prod.ext
  · rfl
  · funext b
    by_cases h : b = a <;> simp [Record.putAnswer, h]

/-! ## Cuts and public data -/

/-- A cut: the first public position of every chain. -/
abbrev Cut := Fin numChains → ℕ

variable (P) in
/-- Before signing: only the tops are public. -/
def beforeSigning : Cut := fun k => P.codec.len k - 1

variable (P) in
/-- After signing index `I`: the revealed positions. -/
def afterSigning (I : Index) : Cut := fun k => P.codec.len k - 1 - P.codec.digit I k

variable (P) in
/-- A cut is at or below the tops. -/
def ValidCut (d : Cut) : Prop := ∀ k, d k ≤ P.codec.len k - 1

theorem beforeSigning_valid : ValidCut P (beforeSigning P) := fun _ => le_rfl

theorem afterSigning_valid (I : Index) : ValidCut P (afterSigning P I) :=
  fun _ => Nat.sub_le _ _

/-- The hidden locations: chain steps strictly below the cut. -/
def Hidden (d : Cut) : Loc P → Prop
  | .inl a => a.2.val < d a.1
  | .inr _ => False

theorem hidden_inl (d : Cut) (k : Fin numChains) (j : Fin (P.codec.len k - 1)) :
    Hidden d (.inl ⟨k, j⟩) ↔ j.val < d k := Iff.rfl

theorem not_hidden_inr (d : Cut) (r : Fin 3) : ¬ Hidden (P := P) d (.inr r) := fun h => h

variable (P) in
/-- The data visible at a cut. -/
abbrev PublicData := (Fin numChains → Option Word) × (Loc P → Option (BitVec hashBits))

/-- The seeds and answers visible at cut `d`: the seed when the cut is at position `0`, the
answer of every step whose output is at or after the cut, and all root answers. Extra revealed
data only strengthen the adversary. -/
def publicData (d : Cut) (ξ : Record P) : PublicData P :=
  (fun k => if d k = 0 then some (ξ.1 k) else none,
   fun a => match a with
     | .inl b => if d b.1 ≤ b.2.val + 1 then some (ξ.2 (.inl b)) else none
     | .inr r => some (ξ.2 (.inr r)))

def finiteFiber {R V : Type} [Fintype R] (f : R → V) (v : V) : Finset R :=
  @Finset.filter R (fun r => f r = v) (fun _ => Classical.propDecidable _) Finset.univ

theorem mem_finiteFiber {R V : Type} [Fintype R] (f : R → V) (v : V) (r : R) :
    r ∈ finiteFiber f v ↔ f r = v := by
  simp only [finiteFiber, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The records with public data `v` at cut `d`. -/
def publicFiber (d : Cut) (v : PublicData P) : Finset (Record P) :=
  finiteFiber (publicData d) v

theorem mem_publicFiber (d : Cut) (v : PublicData P) (ξ : Record P) :
    ξ ∈ publicFiber d v ↔ publicData d ξ = v :=
  mem_finiteFiber (publicData d) v ξ

theorem publicData_putSource (d : Cut) (ξ : Record P) (k : Fin numChains) (x : Word)
    (hk : 0 < d k) : publicData d (ξ.putSource k x) = publicData d ξ := by
  apply Prod.ext
  · funext j
    by_cases h : j = k
    · subst j
      simp only [publicData, if_neg (Nat.ne_of_gt hk)]
    · simp [publicData, Record.putSource, Function.update_of_ne h]
  · rfl

theorem publicData_putAnswer (d : Cut) (ξ : Record P) (a : ChainLoc P)
    (x : BitVec hashBits) (ha : a.2.val + 1 < d a.1) :
    publicData d (ξ.putAnswer (.inl a) x) = publicData d ξ := by
  apply Prod.ext
  · rfl
  · funext b
    by_cases h : b = .inl a
    · subst b
      simp [publicData, not_le_of_gt ha]
    · cases b with
      | inl b =>
        show (if d b.1 ≤ b.2.val + 1 then some (Function.update ξ.2 (.inl a) x (.inl b))
          else none) = _
        rw [Function.update_of_ne h]
        rfl
      | inr b => simp [publicData, Record.putAnswer]

attribute [local irreducible] publicData finiteFiber

theorem fiber_closed_source (d : Cut) (v : PublicData P) (k : Fin numChains) (hk : 0 < d k) :
    ∀ ξ ∈ publicFiber d v, ∀ x, ξ.putSource k x ∈ publicFiber d v := by
  intro ξ h x
  apply (mem_publicFiber _ _ _).mpr
  rw [publicData_putSource d ξ k x hk]
  exact (mem_publicFiber _ _ _).mp h

theorem fiber_closed_answer (d : Cut) (v : PublicData P) (a : ChainLoc P)
    (ha : a.2.val + 1 < d a.1) :
    ∀ ξ ∈ publicFiber d v, ∀ x, ξ.putAnswer (.inl a) x ∈ publicFiber d v := by
  intro ξ h x
  apply (mem_publicFiber _ _ _).mpr
  rw [publicData_putAnswer d ξ a x ha]
  exact (mem_publicFiber _ _ _).mp h

/-! ## What the public data determine -/

attribute [local semireducible] publicData in
theorem data_source_eq (d : Cut) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) (k : Fin numChains) (hk : d k = 0) :
    ξ.1 k = ζ.1 k := by
  have he := congrArg (fun v : PublicData P => v.1 k) h
  simp only [publicData, hk, if_true, Option.some.injEq] at he
  exact he

attribute [local semireducible] publicData in
theorem data_chain_eq (d : Cut) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) (a : ChainLoc P)
    (ha : d a.1 ≤ a.2.val + 1) : ξ.2 (.inl a) = ζ.2 (.inl a) := by
  have he := congrArg (fun v : PublicData P => v.2 (.inl a)) h
  simp only [publicData, if_pos ha, Option.some.injEq] at he
  exact he

attribute [local semireducible] publicData in
theorem data_root_eq (d : Cut) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) (r : Fin 3) :
    ξ.2 (.inr r) = ζ.2 (.inr r) :=
  Option.some.inj (congrArg (fun v : PublicData P => v.2 (.inr r)) h)

theorem data_word_eq (d : Cut) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) (k : Fin numChains) (j : ℕ)
    (hj : d k ≤ j) : ξ.word k j = ζ.word k j := by
  cases j with
  | zero => exact data_source_eq d ξ ζ h k (by omega)
  | succ j =>
    by_cases hl : j < P.codec.len k - 1
    · rw [Record.word_succ _ k j hl, Record.word_succ _ k j hl,
        data_chain_eq d ξ ζ h ⟨k, ⟨j, hl⟩⟩ (by dsimp only; omega)]
    · simp only [Record.word, dif_neg hl]

theorem data_top_eq {d : Cut} (hd : ValidCut P d) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) : ξ.top = ζ.top :=
  funext fun k => data_word_eq d ξ ζ h k _ (hd k)

theorem data_tops_eq {d : Cut} (hd : ValidCut P d) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) : ξ.tops = ζ.tops := by
  unfold Record.tops
  rw [data_top_eq hd ξ ζ h]

theorem data_rootState_eq {d : Cut} (hd : ValidCut P d) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) (r : ℕ) : ξ.rootState r = ζ.rootState r := by
  cases r with
  | zero => rfl
  | succ r =>
    by_cases hr : r < 3
    · rw [Record.rootState_succ_lt _ r hr, Record.rootState_succ_lt _ r hr,
        data_root_eq d ξ ζ h ⟨r, hr⟩]
    · rw [Record.rootState_succ_ge _ r hr, Record.rootState_succ_ge _ r hr]

theorem data_pk_eq (d : Cut) (ξ ζ : Record P) (h : publicData d ξ = publicData d ζ) :
    ξ.pk = ζ.pk := by
  unfold Record.pk
  rw [data_root_eq d ξ ζ h 2]

theorem exposed_query_eq {d : Cut} (hd : ValidCut P d) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) (a : Loc P) (ha : ¬ Hidden d a) :
    ξ.query a = ζ.query a := by
  cases a with
  | inl a =>
    rcases a with ⟨k, j⟩
    rw [Record.query_inl, Record.query_inl,
      data_word_eq d ξ ζ h k j.val (Nat.le_of_not_gt ha), data_tops_eq hd ξ ζ h]
  | inr r =>
    rw [Record.query_inr, Record.query_inr, data_tops_eq hd ξ ζ h,
      data_rootState_eq hd ξ ζ h]

theorem exposed_answer_eq (d : Cut) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) (a : Loc P) (ha : ¬ Hidden d a) :
    ξ.2 a = ζ.2 a := by
  cases a with
  | inl a =>
    apply data_chain_eq d ξ ζ h a
    have := Nat.le_of_not_gt ha
    omega
  | inr r => exact data_root_eq d ξ ζ h r

/-! ## Hidden and exposed caches -/

attribute [local irreducible] Record.query queryLocation

/-- The programmed points at hidden locations. -/
def hiddenCache (d : Cut) (ξ : Record P) : Cache := fun q =>
  match queryLocation P q with
  | none => none
  | some a => if Hidden d a then ξ.cache q else none

/-- The programmed points at exposed locations. -/
def exposedCache (d : Cut) (ξ : Record P) : Cache := fun q =>
  match queryLocation P q with
  | none => none
  | some a => if Hidden d a then none else ξ.cache q

theorem exposure_partition (d : Cut) (ξ : Record P) :
    Cache.extend (exposedCache d ξ) (hiddenCache d ξ) = ξ.cache := by
  funext q
  cases hl : queryLocation P q with
  | none => simp only [Cache.extend, exposedCache, hiddenCache, Record.cache, hl, Option.or_none]
  | some a =>
    simp only [Cache.extend, exposedCache, hiddenCache, hl]
    split <;> simp

theorem exposure_disjoint (d : Cut) (ξ : Record P) :
    Cache.Disjoint (exposedCache d ξ) (hiddenCache d ξ) := by
  intro q hq
  cases hl : queryLocation P q with
  | none => simp only [hiddenCache, hl, Option.isSome_none, Bool.false_eq_true] at hq
  | some a =>
    by_cases ha : Hidden d a
    · simp only [exposedCache, hl, if_pos ha]
    · simp only [hiddenCache, hl, if_neg ha, Option.isSome_none, Bool.false_eq_true] at hq

theorem hiddenCache_some_iff (hP : P.Hyp) (d : Cut) (ξ : Record P) (q : Query)
    (u : BitVec hashBits) :
    hiddenCache d ξ q = some u ↔ ∃ a, Hidden d a ∧ ξ.query a = q ∧ ξ.2 a = u := by
  constructor
  · intro h
    cases hl : queryLocation P q with
    | none => simp only [hiddenCache, hl, reduceCtorEq] at h
    | some a =>
      by_cases ha : Hidden d a
      · simp only [hiddenCache, hl, if_pos ha] at h
        obtain ⟨b, hb, hu⟩ := (ξ.cache_some_iff hP q u).mp h
        have he : b = a := Option.some.inj ((hb ▸ queryLocation_query hP ξ b).symm.trans hl)
        exact ⟨b, he ▸ ha, hb, hu⟩
      · simp only [hiddenCache, hl, if_neg ha, reduceCtorEq] at h
  · rintro ⟨a, ha, rfl, rfl⟩
    simp only [hiddenCache, queryLocation_query hP, if_pos ha, Record.cache_query hP]

theorem exposedCache_some_iff (hP : P.Hyp) (d : Cut) (ξ : Record P) (q : Query)
    (u : BitVec hashBits) :
    exposedCache d ξ q = some u ↔ ∃ a, ¬ Hidden d a ∧ ξ.query a = q ∧ ξ.2 a = u := by
  constructor
  · intro h
    cases hl : queryLocation P q with
    | none => simp only [exposedCache, hl, reduceCtorEq] at h
    | some a =>
      by_cases ha : Hidden d a
      · simp only [exposedCache, hl, if_pos ha, reduceCtorEq] at h
      · simp only [exposedCache, hl, if_neg ha] at h
        obtain ⟨b, hb, hu⟩ := (ξ.cache_some_iff hP q u).mp h
        have he : b = a := Option.some.inj ((hb ▸ queryLocation_query hP ξ b).symm.trans hl)
        exact ⟨b, he ▸ ha, hb, hu⟩
  · rintro ⟨a, ha, rfl, rfl⟩
    simp only [exposedCache, queryLocation_query hP, if_neg ha, Record.cache_query hP]

theorem hiddenCache_isSome_iff (hP : P.Hyp) (d : Cut) (ξ : Record P) (q : Query) :
    (hiddenCache d ξ q).isSome ↔ ∃ a, Hidden d a ∧ ξ.query a = q := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨a, ha, hq, _⟩ := (hiddenCache_some_iff hP d ξ q u).mp hu
    exact ⟨a, ha, hq⟩
  · rintro ⟨a, ha, hq⟩
    exact ⟨ξ.2 a, (hiddenCache_some_iff hP d ξ q _).mpr ⟨a, ha, hq, rfl⟩⟩

theorem exposedCache_data_eq (hP : P.Hyp) {d : Cut} (hd : ValidCut P d) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) : exposedCache d ξ = exposedCache d ζ := by
  funext q
  apply Option.ext
  intro u
  rw [exposedCache_some_iff hP, exposedCache_some_iff hP]
  constructor
  · rintro ⟨a, ha, hq, hu⟩
    exact ⟨a, ha, (exposed_query_eq hd ξ ζ h a ha).symm.trans hq,
      (exposed_answer_eq d ξ ζ h a ha).symm.trans hu⟩
  · rintro ⟨a, ha, hq, hu⟩
    exact ⟨a, ha, (exposed_query_eq hd ξ ζ h a ha).trans hq,
      (exposed_answer_eq d ξ ζ h a ha).trans hu⟩

/-- The exposed and hidden caches of a record are its programmed points: none at index
queries. -/
theorem hiddenCache_idx (hP : P.Hyp) (d : Cut) (ξ : Record P) (m : Message) (η : Nonce)
    (pk : PublicKey) : hiddenCache d ξ ⟨896, P.codec.idxInput m η pk⟩ = none := by
  rcases h : hiddenCache d ξ ⟨896, P.codec.idxInput m η pk⟩ with _ | u
  · rfl
  · obtain ⟨a, -, ha, -⟩ := (hiddenCache_some_iff hP d ξ _ u).mp h
    exact absurd ha (ξ.query_ne_idx hP a m η pk)

theorem exposedCache_idx (hP : P.Hyp) (d : Cut) (ξ : Record P) (m : Message) (η : Nonce)
    (pk : PublicKey) : exposedCache d ξ ⟨896, P.codec.idxInput m η pk⟩ = none := by
  rcases h : exposedCache d ξ ⟨896, P.codec.idxInput m η pk⟩ with _ | u
  · rfl
  · obtain ⟨a, -, ha, -⟩ := (exposedCache_some_iff hP d ξ _ u).mp h
    exact absurd ha (ξ.query_ne_idx hP a m η pk)

/-! ## Guessing a hidden word -/

/-- The per-query guessing rate: `2 ^ -128` per 896-bit query, `2 ^ -129` per compression. -/
def rate : ℝ≥0∞ := (2 ^ 129)⁻¹

theorem card_filter_low_le (n m : ℕ) (hm : m ≤ n) (a : BitVec m) :
    (Finset.univ.filter fun w : BitVec n => w.setWidth m = a).card ≤ 2 ^ (n - m) := by
  have key : (Finset.univ.filter fun w : BitVec n => w.setWidth m = a).card ≤
      (Finset.univ : Finset (BitVec (n - m))).card := by
    refine Finset.card_le_card_of_injOn (fun w => (w >>> m).setWidth (n - m))
      (fun _ _ => Finset.mem_univ _) ?_
    intro w hw w' hw' e
    rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
    have hlow : ∀ i, i < m → w.getLsbD i = w'.getLsbD i := by
      intro i hi
      have := congrArg (fun x : BitVec m => x.getLsbD i) (hw.2.trans hw'.2.symm)
      simpa [BitVec.getLsbD_setWidth, hi] using this
    have hhigh : ∀ i, m ≤ i → i < n → w.getLsbD i = w'.getLsbD i := by
      intro i hi1 hi2
      have := congrArg (fun x : BitVec (n - m) => x.getLsbD (i - m)) e
      have h1 : i - m < n - m := by omega
      have h2 : m + (i - m) = i := by omega
      simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h1, h2] using this
    apply BitVec.eq_of_getLsbD_eq
    intro i hi2
    by_cases hi : i < m
    · exact hlow i hi
    · exact hhigh i (by omega) hi2
  rw [Finset.card_univ, Fintype.card_bitVec] at key
  exact key

theorem low_eq_setWidth {n : ℕ} (x : BitVec n) : x.extractLsb' 0 128 = x.setWidth 128 := by
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.ushiftRight_zero]

theorem card_low_le (a : Word) :
    (Finset.univ.filter fun w : BitVec hashBits => w.extractLsb' 0 128 = a).card ≤ 2 ^ 128 := by
  have h := card_filter_low_le hashBits 128 (by unfold hashBits; omega) a
  rw [show hashBits - 128 = 128 by unfold hashBits; rfl] at h
  simpa only [low_eq_setWidth] using h

/-- Fixing either half of a 256-bit answer leaves `2 ^ 128` answers. -/
theorem card_half_le (o : ℕ) (ho : o = 0 ∨ o = 128) (a : Word) :
    (Finset.univ.filter fun w : BitVec 256 => w.extractLsb' o 128 = a).card ≤ 2 ^ 128 := by
  have hu : (Finset.univ : Finset (BitVec 128)).card = 2 ^ 128 := by
    rw [Finset.card_univ, Fintype.card_bitVec]
  rw [← hu]
  refine Finset.card_le_card_of_injOn (fun w => w.extractLsb' (128 - o) 128)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
  intro w hw w' hw' h
  rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
  have h' : w.extractLsb' (128 - o) 128 = w'.extractLsb' (128 - o) 128 := h
  have split : ∀ v : BitVec 256, v = v.extractLsb' 128 128 ++ v.extractLsb' 0 128 := fun v => by
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := v) (start₁ := 0)
      (len₁ := 128) (start₂ := 128) (len₂ := 128) rfl]
    exact BitVec.extractLsb'_eq_self.symm
  rw [split w, split w']
  rcases ho with rfl | rfl
  · rw [Nat.sub_zero] at h'
    rw [hw.2, hw'.2, h']
  · rw [Nat.sub_self] at h'
    rw [hw.2, hw'.2, h']

attribute [local semireducible] hashBits in
theorem card_slice_le (k : Fin numChains) (j : ℕ) (a : Word) :
    (Finset.univ.filter fun w : BitVec hashBits => P.codec.slice k j w = a).card ≤ 2 ^ 128 :=
  card_half_le (P.codec.stepOff k j) (by unfold Layer.Params.stepOff; split <;> simp) a

theorem rate_two : rate * 2 = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  unfold rate
  rw [show (2 : ℝ≥0∞) ^ 129 = 2 ^ 128 * 2 by rw [← pow_succ],
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

theorem card_word_inv : (Fintype.card Word : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [Fintype.card_bitVec]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem inv_card_mul_two_pow_128 :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (2 ^ 128 : ℕ) = rate * 2 := by
  rw [rate_two, Fintype.card_bitVec, show hashBits = 256 by unfold hashBits; rfl]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add],
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

theorem word_putSource_zero (ξ : Record P) (k : Fin numChains) (x : Word) :
    (ξ.putSource k x).word k 0 = x := putSource_get ξ k x

theorem word_putAnswer_prev (ξ : Record P) (k : Fin numChains) (j : ℕ) (hj : j < P.codec.len k - 1)
    (x : BitVec hashBits) :
    (ξ.putAnswer (.inl ⟨k, ⟨j, hj⟩⟩) x).word k (j + 1) = P.codec.slice k j x := by
  rw [Record.word_succ _ k j hj]
  exact congrArg (P.codec.slice k j) (putAnswer_get ξ _ x)

/-- Every word strictly before the cut is uniform given the public data of the cut. -/
theorem hidden_word_charge (d : Cut) (hd : ValidCut P d) (v : PublicData P) (k : Fin numChains)
    (j : ℕ) (hj : j < d k) (x : Word) (w : ℝ≥0∞) :
    (∑ ξ ∈ publicFiber d v, if ξ.word k j = x then w else 0) ≤
      (rate * 2) * ∑ _ξ ∈ publicFiber d v, w := by
  rw [Finset.mul_sum]
  cases j with
  | zero =>
    rw [sum_resample (fun ξ : Record P => ξ.1 k) (fun ξ y => ξ.putSource k y)
      (fun ξ y => putSource_get ξ k y) (fun ξ y => putSource_restore ξ k y)
      (publicFiber d v) (fiber_closed_source d v k hj)]
    apply Finset.sum_le_sum
    intro ξ _
    simp only [word_putSource_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ x), card_word_inv, rate_two]
  | succ j =>
    have hl : j < P.codec.len k - 1 := by have := hd k; omega
    rw [sum_resample (fun ξ : Record P => ξ.2 (.inl ⟨k, ⟨j, hl⟩⟩))
      (fun ξ y => ξ.putAnswer (.inl ⟨k, ⟨j, hl⟩⟩) y)
      (fun ξ y => putAnswer_get ξ _ y) (fun ξ y => putAnswer_restore ξ _ y)
      (publicFiber d v) (fiber_closed_answer d v ⟨k, ⟨j, hl⟩⟩ (by dsimp only; omega))]
    apply Finset.sum_le_sum
    intro ξ _
    simp only [word_putAnswer_prev ξ k j hl]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) * w) :=
        mul_le_mul' le_rfl (mul_le_mul' (Nat.cast_le.mpr (card_slice_le k j x)) le_rfl)
      _ = rate * 2 * w := by rw [← mul_assoc, inv_card_mul_two_pow_128]

theorem record_chain_query_current (ξ ζ : Record P) (k : Fin numChains)
    (j : Fin (P.codec.len k - 1))
    (h : ξ.query (.inl ⟨k,j⟩) = ζ.query (.inl ⟨k,j⟩)) : ξ.word k j.val = ζ.word k j.val := by
  rw [Record.query_inl, Record.query_inl] at h
  exact Params.chainInput_current ξ.tops ζ.tops _ _ (query_inj h)

theorem queryCost_896 {q : Query} (h : q.1 = 896) : queryCost (.inr q) = 2 := by
  norm_num [queryCost, blockCost, blockBits, h]

/-- Per-query guessing charge: a query hits a hidden input of the records of a public fiber
with weighted probability at most `rate · queryCost` (two compressions per tagged input). -/
theorem hidden_input_charge (hP : P.Hyp) (d : Cut) (hd : ValidCut P d) (v : PublicData P)
    (q : Query) (w : ℝ≥0∞) :
    (∑ ξ ∈ publicFiber d v, if (hiddenCache d ξ q).isSome then w else 0) ≤
      rate * queryCost (.inr q) * ∑ _ξ ∈ publicFiber d v, w := by
  by_cases hex : ∃ ζ : Record P, ∃ a, Hidden d a ∧ ζ.query a = q
  · obtain ⟨ζ, a, ha, rfl⟩ := hex
    cases a with
    | inr r => exact (not_hidden_inr d r ha).elim
    | inl a =>
      rcases a with ⟨k, j⟩
      have he (ξ : Record P) : (hiddenCache d ξ (ζ.query (.inl ⟨k,j⟩))).isSome →
          ξ.word k j.val = ζ.word k j.val := by
        intro hh
        obtain ⟨b,_,hb⟩ := (hiddenCache_isSome_iff hP d ξ _).mp hh
        have hbe := location_eq_of_query_eq hP ξ ζ b (.inl ⟨k,j⟩) hb
        subst b
        exact record_chain_query_current ξ ζ k j hb
      have hc : queryCost (.inr (ζ.query (.inl ⟨k,j⟩))) = 2 :=
        queryCost_896 (by rw [Record.query_inl])
      rw [hc]
      calc
        _ ≤ ∑ ξ ∈ publicFiber d v, if ξ.word k j.val = ζ.word k j.val then w else 0 := by
          apply Finset.sum_le_sum
          intro ξ _
          by_cases hh : (hiddenCache d ξ (ζ.query (.inl ⟨k,j⟩))).isSome
          · rw [if_pos hh, if_pos (he ξ hh)]
          · rw [if_neg hh]; exact bot_le
        _ ≤ _ := hidden_word_charge d hd v k j.val ha (ζ.word k j.val) w
  · have hn (ξ : Record P) : ¬ (hiddenCache d ξ q).isSome := by
      intro h
      obtain ⟨a, ha, hq⟩ := (hiddenCache_isSome_iff hP d ξ q).mp h
      exact hex ⟨ξ, a, ha, hq⟩
    simp only [if_neg (hn _), Finset.sum_const_zero]
    exact bot_le

/-- A query that is not the input of any record location hits no hidden point. -/
theorem hiddenCache_of_not_loc (hP : P.Hyp) (d : Cut) (ξ : Record P) (q : Query)
    (hq : ∀ (ζ : Record P) (a : Loc P), ζ.query a ≠ q) : hiddenCache d ξ q = none := by
  rcases h : hiddenCache d ξ q with _ | u
  · rfl
  · obtain ⟨a, -, ha, -⟩ := (hiddenCache_some_iff hP d ξ q u).mp h
    exact absurd ha (hq ξ a)

end OptimalOTS.LeanIsaBaseline.Layer.Fusion
