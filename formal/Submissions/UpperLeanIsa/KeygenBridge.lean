import Submissions.UpperLeanIsa.Records
import Submissions.UpperLeanIsa.IUB

/-!
# Key generation is a uniform record

Under the lazy random oracle started from the empty cache, key generation samples the 42 seeds
and then queries every chain step and every root call exactly once, at pairwise distinct
inputs (`location_eq_of_input_eq`). Its output and final cache are those of a uniformly random
record:

```
E[g' | run keygen ∅] = ∑ ξ : Record P, recW P · g' ((ξ.pk, ξ.sk), ξ.cache).
```

Adapted from the record's `KeygenBridge` (after the checked `upper-riscv-687` keygen bridge):
every fresh answer is absorbed into a uniform *full* answer table `y : Loc P → BitVec 256`
(`sum_avg_update`); the caches written along the way are described by `progUpd`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

theorem chainList_succ' {P : Params} (k : Fin numChains) (j n : ℕ) (x : Word) :
    P.chainList k j (n + 1) x = P.chainStep k j x >>= fun y =>
      P.chainList k (j + 1) n y >>= fun ys => pure (x :: ys) := rfl

theorem chainList_zero' {P : Params} (k : Fin numChains) (j : ℕ) (x : Word) :
    P.chainList k j 0 x = pure [x] := rfl

theorem rootFrom_succ' {P : Params} (t : Fin numChains → Word) (r n : ℕ) (st : BitVec 256) :
    P.rootFrom t r (n + 1) st = hash (P.rootInput t r st) >>= fun st' =>
      P.rootFrom t (r + 1) n st' := rfl

theorem rootFrom_zero' {P : Params} (t : Fin numChains → Word) (r : ℕ) (st : BitVec 256) :
    P.rootFrom t r 0 st = pure st := rfl

theorem tabulate_succ' {α : Type} {n : ℕ} (f : Fin (n + 1) → OracleComp Spec α) :
    tabulate f = f 0 >>= fun x => tabulate (fun i => f i.succ) >>= fun xs =>
      pure (Fin.cases x xs) := rfl

theorem tabulate_zero' {α : Type} (f : Fin 0 → OracleComp Spec α) :
    tabulate f = pure Fin.elim0 := rfl

attribute [local irreducible] Params.chainList Params.rootFrom tabulate

/-- The uniform weight of a record. -/
def recW (P : Params) : ℝ≥0∞ := (Fintype.card (Record P) : ℝ≥0∞)⁻¹

/-! ## Averaging over one coordinate (generic) -/

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

theorem sum_fin_cases {α : Type} [Fintype α] {n : ℕ}
    (F : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∑ f, F f = ∑ x : α, ∑ xs : Fin n → α, F (Fin.cases x xs : Fin (n + 1) → α) := by
  rw [← Fintype.sum_prod_type' (fun (x : α) (xs : Fin n → α) =>
    F (Fin.cases x xs : Fin (n + 1) → α))]
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => α)
    (fun p => F (Fin.cases p.1 p.2 : Fin (n + 1) → α)) F fun _ => rfl).symm

/-! ## Full answer tables and one fresh query -/

/-- Full answer tables: one hash output per location. -/
abbrev Tbl (P : Params) := Loc P → BitVec hashBits

variable {P : Params}

/-- A query the cache does not hold gets a fresh uniform answer, which is then cached. -/
theorem run_hash_fresh {n : ℕ} (x : BitVec n) (c : Cache) (hc : c ⟨n, x⟩ = none) :
    run (hash x) c = ($ᵗ BitVec hashBits) >>= fun u => pure (u, c.cacheQuery ⟨n, x⟩ u) := by
  change (simulateQ oracleImpl (liftM (Spec.query (.inr ⟨n, x⟩)))).run c = _
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_none hc

theorem run_sampleBits (m : ℕ) (c : Cache) :
    run (sampleBits m) c = (fun x => (x, c)) <$> ($ᵗ BitVec m) := by
  unfold sampleBits
  exact run_liftM _ c

theorem avg_hash (a : Loc P) (x : Tbl P → BitVec 896) (c : Tbl P → Cache)
    (K : Tbl P → BitVec hashBits × Cache → ℝ≥0∞)
    (hfresh : ∀ y, c y ⟨896, x y⟩ = none)
    (hx : ∀ y u, x (Function.update y a u) = x y)
    (hc : ∀ y u, c (Function.update y a u) = c y)
    (hK : ∀ y u p, K (Function.update y a u) p = K y p) :
    ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ * E (run (hash (x y)) (c y)) (K y) =
      ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
        K y (y a, (c y).cacheQuery ⟨896, x y⟩ (y a)) := by
  have key := sum_avg_update (R := fun _ : Loc P => BitVec hashBits) a
    (fun u y => K y (u, (c y).cacheQuery ⟨896, x y⟩ u))
    (fun u u' y => by rw [hK, hc, hx y u'])
  refine Eq.trans ?_ key
  have h1 : ∀ y : Tbl P, E (run (hash (x y)) (c y)) (K y) =
      ∑ u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        K y (u, (c y).cacheQuery ⟨896, x y⟩ u) := by
    intro y
    rw [run_hash_fresh _ _ (hfresh y), E_bind, E_uniform]
    simp only [E_pure]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_left_comm]

/-! ## Records built from seeds and a table -/

theorem word_update (sk : Fin numChains → Word) (y : Tbl P) (b : Loc P) (u : BitVec hashBits)
    (k : Fin numChains) (j : ℕ)
    (h : ∀ j' : Fin (P.len k - 1), b = .inl ⟨k, j'⟩ → j'.val + 1 ≠ j) :
    Record.word (sk, Function.update y b u) k j = Record.word (sk, y) k j := by
  cases j with
  | zero => rfl
  | succ j =>
    by_cases hj : j < P.len k - 1
    · have hne : (Sum.inl ⟨k, ⟨j, hj⟩⟩ : Loc P) ≠ b := by
        intro hb
        exact h _ hb.symm rfl
      rw [Record.word_succ _ k j hj, Record.word_succ _ k j hj]
      simp only [Function.update_of_ne hne]
    · simp only [Record.word, dif_neg hj]

theorem top_update_inr (sk : Fin numChains → Word) (y : Tbl P) (r : Fin 9) (u : BitVec hashBits) :
    Record.top (sk, Function.update y (.inr r) u) = Record.top (sk, y) := by
  funext k
  exact word_update sk y _ u k _ (fun _ h => absurd h Sum.inr_ne_inl)

theorem table_update_inr (sk : Fin numChains → Word) (y : Tbl P) (r : Fin 9)
    (u : BitVec hashBits) :
    Record.table (sk, Function.update y (.inr r) u) = Record.table (sk, y) := by
  funext k
  unfold Record.table
  exact List.map_congr_left fun j _ =>
    word_update sk y _ u k _ (fun _ h => absurd h Sum.inr_ne_inl)

theorem query_update_inl (sk : Fin numChains → Word) (y : Tbl P) (b : Loc P)
    (u : BitVec hashBits) (k : Fin numChains) (j : Fin (P.len k - 1))
    (h : ∀ j' : Fin (P.len k - 1), b = .inl ⟨k, j'⟩ → j'.val + 1 ≠ j.val) :
    Record.query (sk, Function.update y b u) (.inl ⟨k, j⟩) =
      Record.query (sk, y) (.inl ⟨k, j⟩) := by
  rw [Record.query_inl, Record.query_inl, word_update sk y b u k _ h]

theorem rootState_update (sk : Fin numChains → Word) (y : Tbl P) (r' : Fin 9)
    (u : BitVec hashBits) (r : ℕ) (h : r'.val + 1 ≠ r) :
    Record.rootState (sk, Function.update y (.inr r') u) r = Record.rootState (sk, y) r := by
  cases r with
  | zero =>
    show Params.rootInit (Record.top _) = Params.rootInit (Record.top _)
    rw [top_update_inr]
  | succ r =>
    by_cases hr : r < 9
    · rw [Record.rootState_succ_lt _ r hr, Record.rootState_succ_lt _ r hr]
      have hne : (Sum.inr ⟨r, hr⟩ : Loc P) ≠ .inr r' := by
        intro he
        have := congrArg Fin.val (Sum.inr.inj he)
        simp only at this
        omega
      exact Function.update_of_ne hne u y
    · rw [Record.rootState_succ_ge _ r hr, Record.rootState_succ_ge _ r hr]

theorem rootState_update_inl (sk : Fin numChains → Word) (y : Tbl P) (a : ChainLoc P)
    (u : BitVec hashBits) (r : ℕ) (hr : r ≠ 0) :
    Record.rootState (sk, Function.update y (.inl a) u) r = Record.rootState (sk, y) r := by
  cases r with
  | zero => exact absurd rfl hr
  | succ r =>
    by_cases hr : r < 9
    · rw [Record.rootState_succ_lt _ r hr, Record.rootState_succ_lt _ r hr]
      exact Function.update_of_ne
        (show (Sum.inr ⟨r, hr⟩ : Loc P) ≠ Sum.inl a from Sum.inr_ne_inl) u y
    · rw [Record.rootState_succ_ge _ r hr, Record.rootState_succ_ge _ r hr]

/-! ## Programming a cache with the points of a record -/

/-- `c` overwritten by the programmed points of `ξ` at the locations satisfying `S`. -/
def progUpd (ξ : Record P) (S : Loc P → Prop) (c : Cache) : Cache :=
  fun q => if ∃ a, S a ∧ ξ.query a = q then ξ.cache q else c q

theorem progUpd_apply (ξ : Record P) (S : Loc P → Prop) (c : Cache) (q : Query) :
    progUpd ξ S c q = if ∃ a, S a ∧ ξ.query a = q then ξ.cache q else c q :=
  rfl

theorem progUpd_apply_neg {ξ : Record P} {S : Loc P → Prop} {c : Cache}
    {q : Query} (h : ¬ ∃ a, S a ∧ ξ.query a = q) : progUpd ξ S c q = c q := by
  rw [progUpd_apply, if_neg h]

theorem progUpd_of_false (ξ : Record P) (S : Loc P → Prop) (c : Cache)
    (h : ∀ b, ¬ S b) : progUpd ξ S c = c := by
  funext q
  have hn : ¬ ∃ a, S a ∧ ξ.query a = q := fun ⟨a, ha, _⟩ => h a ha
  rw [progUpd_apply, if_neg hn]

theorem progUpd_congr {ξ : Record P} {S S' : Loc P → Prop} {c : Cache}
    (h : ∀ b, S b ↔ S' b) : progUpd ξ S c = progUpd ξ S' c := by
  have hSS : S = S' := funext fun b => propext (h b)
  rw [hSS]

theorem progUpd_cacheQuery (hP : P.Hyp) (ξ : Record P) (S : Loc P → Prop) (c : Cache)
    (a : Loc P) :
    progUpd ξ S (c.cacheQuery (ξ.query a) (ξ.2 a)) = progUpd ξ (fun b => S b ∨ b = a) c := by
  funext q
  rw [progUpd_apply, progUpd_apply]
  by_cases hq : ξ.query a = q
  · subst hq
    have h1 : ∃ b, (S b ∨ b = a) ∧ ξ.query b = ξ.query a := ⟨a, Or.inr rfl, rfl⟩
    rw [if_pos h1]
    by_cases h : ∃ b, S b ∧ ξ.query b = ξ.query a
    · rw [if_pos h]
    · rw [if_neg h, QueryCache.cacheQuery_self]
      exact (ξ.cache_query hP a).symm
  · by_cases h : ∃ b, S b ∧ ξ.query b = q
    · have h1 : ∃ b, (S b ∨ b = a) ∧ ξ.query b = q := by
        obtain ⟨b, hb, hbq⟩ := h
        exact ⟨b, Or.inl hb, hbq⟩
      rw [if_pos h, if_pos h1]
    · have h1 : ¬ ∃ b, (S b ∨ b = a) ∧ ξ.query b = q := by
        rintro ⟨b, hb | rfl, hbq⟩
        · exact h ⟨b, hb, hbq⟩
        · exact hq hbq
      rw [if_neg h, if_neg h1, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]

theorem progUpd_progUpd (ξ : Record P) (S T : Loc P → Prop) (c : Cache) :
    progUpd ξ S (progUpd ξ T c) = progUpd ξ (fun b => S b ∨ T b) c := by
  funext q
  rw [progUpd_apply, progUpd_apply, progUpd_apply]
  by_cases hS : ∃ b, S b ∧ ξ.query b = q
  · have h1 : ∃ b, (S b ∨ T b) ∧ ξ.query b = q := by
      obtain ⟨b, hb, hbq⟩ := hS
      exact ⟨b, Or.inl hb, hbq⟩
    rw [if_pos hS, if_pos h1]
  · by_cases hT : ∃ b, T b ∧ ξ.query b = q
    · have h1 : ∃ b, (S b ∨ T b) ∧ ξ.query b = q := by
        obtain ⟨b, hb, hbq⟩ := hT
        exact ⟨b, Or.inr hb, hbq⟩
      rw [if_neg hS, if_pos hT, if_pos h1]
    · have h1 : ¬ ∃ b, (S b ∨ T b) ∧ ξ.query b = q := by
        rintro ⟨b, hb | hb, hbq⟩
        · exact hS ⟨b, hb, hbq⟩
        · exact hT ⟨b, hb, hbq⟩
      rw [if_neg hS, if_neg hT, if_neg h1]

theorem progUpd_true_empty (hP : P.Hyp) (ξ : Record P) :
    progUpd ξ (fun _ => True) ∅ = ξ.cache := by
  funext q
  rw [progUpd_apply]
  by_cases h : ∃ a, True ∧ ξ.query a = q
  · rw [if_pos h]
  · rw [if_neg h, QueryCache.empty_apply]
    cases hc : ξ.cache q with
    | none => rfl
    | some v =>
      obtain ⟨a, ha, -⟩ := (ξ.cache_some_iff hP q v).1 hc
      exact (h ⟨a, trivial, ha⟩).elim

theorem progUpd_update (hP : P.Hyp) (sk : Fin numChains → Word) (y : Tbl P) (b : Loc P)
    (u : BitVec hashBits) (S : Loc P → Prop) (c : Cache)
    (hS : ∀ b', S b' → b' ≠ b ∧
      Record.query (sk, Function.update y b u) b' = Record.query (sk, y) b') :
    progUpd (sk, Function.update y b u) S c = progUpd (sk, y) S c := by
  funext q
  rw [progUpd_apply, progUpd_apply]
  have hiff : (∃ b', S b' ∧ Record.query (sk, Function.update y b u) b' = q) ↔
      (∃ b', S b' ∧ Record.query (sk, y) b' = q) :=
    ⟨fun ⟨b', hb', hq⟩ => ⟨b', hb', (hS b' hb').2.symm.trans hq⟩,
      fun ⟨b', hb', hq⟩ => ⟨b', hb', (hS b' hb').2.trans hq⟩⟩
  by_cases h : ∃ b', S b' ∧ Record.query (sk, y) b' = q
  · rw [if_pos (hiff.2 h), if_pos h]
    obtain ⟨b', hb', rfl⟩ := h
    have h1 : Record.cache (sk, Function.update y b u) (Record.query (sk, y) b') =
        some (y b') := by
      rw [← (hS b' hb').2, Record.cache_query hP]
      exact congrArg some (Function.update_of_ne (hS b' hb').1 u y)
    have h2 : Record.cache (sk, y) (Record.query (sk, y) b') = some (y b') :=
      Record.cache_query hP (sk, y) b'
    rw [h1, h2]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

/-! ## Location sets and freshness -/

/-- Positions `j, …, j + n - 1` of chain `k`. -/
def ChainSeg (k : Fin numChains) (j n : ℕ) (b : Loc P) : Prop :=
  ∃ j' : Fin (P.len k - 1), b = .inl ⟨k, j'⟩ ∧ j ≤ j'.val ∧ j'.val < j + n

/-- All positions of the chains `φ t`. -/
def ChainsOf {n : ℕ} (φ : Fin n → Fin numChains) (b : Loc P) : Prop :=
  ∃ (t : Fin n) (j : Fin (P.len (φ t) - 1)), b = .inl ⟨φ t, j⟩

/-- Root calls `r, …, 8`. -/
def RootsFrom (r : ℕ) (b : Loc P) : Prop := ∃ s : Fin 9, b = .inr s ∧ r ≤ s.val

variable (P) in
/-- The cache holds no chain-`k` query at positions `≥ j`. -/
def FreshChain (c : Cache) (k : Fin numChains) (j : ℕ) : Prop :=
  ∀ j' : ℕ, j' + 1 < P.len k → j ≤ j' → ∀ x : Word, c ⟨896, P.chainInput k j' x⟩ = none

variable (P) in
/-- The cache holds no root query at calls `≥ r`. -/
def FreshRoot (c : Cache) (r : ℕ) : Prop :=
  ∀ s : ℕ, s < 9 → r ≤ s → ∀ (t : Fin numChains → Word) (st : BitVec 256),
    c ⟨896, P.rootInput t s st⟩ = none

theorem inl_eq_fst {a b : ChainLoc P} (h : (Sum.inl a : Loc P) = .inl b) : a.1 = b.1 :=
  congrArg Sigma.fst (Sum.inl.inj h)

theorem inl_eq_snd {a b : ChainLoc P} (h : (Sum.inl a : Loc P) = .inl b) : a.2.val = b.2.val :=
  congrArg (fun z : ChainLoc P => z.2.val) (Sum.inl.inj h)

theorem chainSeg_succ (k : Fin numChains) (j n : ℕ) (hj : j < P.len k - 1) (b : Loc P) :
    (ChainSeg k (j + 1) n b ∨ b = .inl ⟨k, ⟨j, hj⟩⟩) ↔ ChainSeg k j (n + 1) b := by
  constructor
  · rintro (⟨j', rfl, h1, h2⟩ | rfl)
    · exact ⟨j', rfl, by omega, by omega⟩
    · exact ⟨⟨j, hj⟩, rfl, le_rfl, show j < j + (n + 1) by omega⟩
  · rintro ⟨j', rfl, h1, h2⟩
    by_cases hjj : j'.val = j
    · exact Or.inr (congrArg (fun z => (Sum.inl ⟨k, z⟩ : Loc P)) (Fin.ext hjj))
    · exact Or.inl ⟨j', rfl, by omega, by omega⟩

theorem chainsOf_succ {n : ℕ} (φ : Fin (n + 1) → Fin numChains) (b : Loc P) :
    (ChainsOf (fun t : Fin n => φ t.succ) b ∨ ChainSeg (φ 0) 0 (P.len (φ 0) - 1) b) ↔
      ChainsOf φ b := by
  constructor
  · rintro (⟨t, j, rfl⟩ | ⟨j, rfl, -, -⟩)
    · exact ⟨t.succ, j, rfl⟩
    · exact ⟨0, j, rfl⟩
  · rintro ⟨t, j, rfl⟩
    rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t, rfl⟩
    · exact Or.inr ⟨j, rfl, Nat.zero_le _, by have := j.isLt; omega⟩
    · exact Or.inl ⟨t, j, rfl⟩

theorem rootsFrom_succ (r : ℕ) (hr : r < 9) (b : Loc P) :
    (RootsFrom (r + 1) b ∨ b = .inr ⟨r, hr⟩) ↔ RootsFrom r b := by
  constructor
  · rintro (⟨s, rfl, hs⟩ | rfl)
    · exact ⟨s, rfl, by omega⟩
    · exact ⟨⟨r, hr⟩, rfl, le_rfl⟩
  · rintro ⟨s, rfl, hs⟩
    by_cases hsr : s.val = r
    · exact Or.inr (congrArg Sum.inr (Fin.ext hsr))
    · exact Or.inl ⟨s, rfl, by omega⟩

/-! ## One chain -/

/-- The words of chain `k` at positions `j, …, j + n`. -/
def wordList (ξ : Record P) (k : Fin numChains) (j n : ℕ) : List Word :=
  (List.range (n + 1)).map fun i => ξ.word k (j + i)

theorem wordList_succ (ξ : Record P) (k : Fin numChains) (j n : ℕ) :
    wordList ξ k j (n + 1) = ξ.word k j :: wordList ξ k (j + 1) n := by
  unfold wordList
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  congr 1
  omega



set_option hygiene false in
local notation "Nt" => ((Fintype.card (Tbl P) : ℝ≥0∞)⁻¹)

/-- Walking chain `k` from position `j` for `n` steps, from a cache fresh on the rest of the
chain, programs positions `j, …, j + n - 1` of the averaged record `(sk, y)`. -/
theorem E_run_chainList_avg (hP : P.Hyp) (sk : Fin numChains → Word) (k : Fin numChains) :
    ∀ (n j : ℕ) (hjn : j + n ≤ P.len k - 1) (G : Tbl P → List Word × Cache → ℝ≥0∞)
      (x : Tbl P → Word) (c : Tbl P → Cache),
      (∀ y, x y = Record.word (sk, y) k j) →
      (∀ y, FreshChain P (c y) k j) →
      (∀ y (j' : Fin (P.len k - 1)) u, j ≤ j'.val →
        c (Function.update y (.inl ⟨k, j'⟩) u) = c y) →
      (∀ y (j' : Fin (P.len k - 1)) u, j ≤ j'.val →
        G (Function.update y (.inl ⟨k, j'⟩) u) = G y) →
      ∑ y : Tbl P, Nt * E (run (P.chainList k j n (x y)) (c y)) (G y) =
        ∑ y : Tbl P, Nt * G y (wordList (sk, y) k j n,
          progUpd (sk, y) (ChainSeg k j n) (c y)) := by
  intro n
  induction n with
  | zero =>
    intro j hjn G x c hx _ _ _
    refine Finset.sum_congr rfl fun y _ => ?_
    have hw : wordList ((sk, y) : Record P) k j 0 = [x y] := by
      rw [hx y]
      simp [wordList]
    rw [chainList_zero', run_pure, E_pure, hw,
      progUpd_of_false (sk, y) (ChainSeg k j 0) (c y) (fun _ ⟨_, _, h1, h2⟩ => by omega)]
  | succ n ih =>
    intro j hjn G x c hx hfr hc hG
    have hj : j < P.len k - 1 := by omega
    have hxu : ∀ y (j' : Fin (P.len k - 1)) u, j ≤ j'.val →
        x (Function.update y (.inl ⟨k, j'⟩) u) = x y := by
      intro y j' u hj'
      rw [hx, hx]
      exact word_update sk y _ u k j (fun j'' h => by
        have := inl_eq_snd h
        simp only at this
        omega)
    have hstep : ∀ y, E (run (P.chainList k j (n + 1) (x y)) (c y)) (G y) =
        E (run (hash (P.chainInput k j (x y))) (c y))
          (fun p => E (run (P.chainList k (j + 1) n (P.slice k j p.1)) p.2)
            (fun p' => G y (x y :: p'.1, p'.2))) := by
      intro y
      rw [chainList_succ', run_bind, Params.chainStep, run_map, E_bind, E_map]
      refine congrArg _ (funext fun p => ?_)
      simp only [Function.comp_apply, run_bind, E_bind, run_pure, E_pure]
    have hfr' : ∀ y, FreshChain P ((c y).cacheQuery ⟨896, P.chainInput k j (x y)⟩
        (y (.inl ⟨k, ⟨j, hj⟩⟩))) k (j + 1) := by
      intro y j' hj' hjj v
      have hne : (⟨896, P.chainInput k j' v⟩ : Query) ≠ ⟨896, P.chainInput k j (x y)⟩ := by
        intro h
        have h2 := ((Params.chainInput_eq_iff hP hj' (by omega) v (x y)).1 (query_inj h)).2.1
        omega
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
      exact hfr y j' hj' (by omega) v
    have hc' : ∀ y (j' : Fin (P.len k - 1)) u, j + 1 ≤ j'.val →
        (c (Function.update y (.inl ⟨k, j'⟩) u)).cacheQuery
            ⟨896, P.chainInput k j (x (Function.update y (.inl ⟨k, j'⟩) u))⟩
            (Function.update y (.inl ⟨k, j'⟩) u (.inl ⟨k, ⟨j, hj⟩⟩)) =
          (c y).cacheQuery ⟨896, P.chainInput k j (x y)⟩ (y (.inl ⟨k, ⟨j, hj⟩⟩)) := by
      intro y j' u hj'
      have hne : (Sum.inl ⟨k, ⟨j, hj⟩⟩ : Loc P) ≠ .inl ⟨k, j'⟩ := by
        intro h
        have := inl_eq_snd h
        simp only at this
        omega
      rw [hc y j' u (by omega), hxu y j' u (by omega), Function.update_of_ne hne]
    have hG' : ∀ y (j' : Fin (P.len k - 1)) u, j + 1 ≤ j'.val →
        (fun p' : List Word × Cache => G (Function.update y (.inl ⟨k, j'⟩) u)
          (x (Function.update y (.inl ⟨k, j'⟩) u) :: p'.1, p'.2)) =
        (fun p' : List Word × Cache => G y (x y :: p'.1, p'.2)) := by
      intro y j' u hj'
      rw [hG y j' u (by omega), hxu y j' u (by omega)]
    have hK : ∀ y u (p : BitVec hashBits × Cache),
        E (run (P.chainList k (j + 1) n (P.slice k j p.1)) p.2)
            (fun p' => G (Function.update y (.inl ⟨k, ⟨j, hj⟩⟩) u)
              (x (Function.update y (.inl ⟨k, ⟨j, hj⟩⟩) u) :: p'.1, p'.2)) =
          E (run (P.chainList k (j + 1) n (P.slice k j p.1)) p.2)
            (fun p' => G y (x y :: p'.1, p'.2)) := by
      intro y u p
      rw [hG y ⟨j, hj⟩ u le_rfl, hxu y ⟨j, hj⟩ u le_rfl]
    calc ∑ y : Tbl P, Nt * E (run (P.chainList k j (n + 1) (x y)) (c y)) (G y)
        = ∑ y : Tbl P, Nt * E (run (hash (P.chainInput k j (x y))) (c y))
            (fun p => E (run (P.chainList k (j + 1) n (P.slice k j p.1)) p.2)
              (fun p' => G y (x y :: p'.1, p'.2))) :=
          Finset.sum_congr rfl fun y _ => by rw [hstep y]
      _ = ∑ y : Tbl P, Nt * E (run (P.chainList k (j + 1) n
              (P.slice k j (y (.inl ⟨k, ⟨j, hj⟩⟩))))
            ((c y).cacheQuery ⟨896, P.chainInput k j (x y)⟩ (y (.inl ⟨k, ⟨j, hj⟩⟩))))
            (fun p' => G y (x y :: p'.1, p'.2)) :=
          avg_hash (.inl ⟨k, ⟨j, hj⟩⟩) (fun y => P.chainInput k j (x y)) c
            (fun y p => E (run (P.chainList k (j + 1) n (P.slice k j p.1)) p.2)
              (fun p' => G y (x y :: p'.1, p'.2)))
            (fun y => hfr y j (by omega) le_rfl (x y))
            (fun y u => congrArg (P.chainInput k j) (hxu y ⟨j, hj⟩ u le_rfl))
            (fun y u => hc y ⟨j, hj⟩ u le_rfl) hK
      _ = ∑ y : Tbl P, Nt * (fun p' : List Word × Cache => G y (x y :: p'.1, p'.2))
            (wordList (sk, y) k (j + 1) n, progUpd (sk, y) (ChainSeg k (j + 1) n)
              ((c y).cacheQuery ⟨896, P.chainInput k j (x y)⟩ (y (.inl ⟨k, ⟨j, hj⟩⟩)))) :=
          ih (j + 1) (by omega) (fun y p' => G y (x y :: p'.1, p'.2))
            (fun y => P.slice k j (y (.inl ⟨k, ⟨j, hj⟩⟩)))
            (fun y => (c y).cacheQuery ⟨896, P.chainInput k j (x y)⟩
              (y (.inl ⟨k, ⟨j, hj⟩⟩)))
            (fun y => (Record.word_succ (sk, y) k j hj).symm) hfr' hc'
            (fun y j' u hj' => hG' y j' u hj')
      _ = ∑ y : Tbl P, Nt * G y (wordList (sk, y) k j (n + 1),
            progUpd (sk, y) (ChainSeg k j (n + 1)) (c y)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have hq : (⟨896, P.chainInput k j (x y)⟩ : Query) =
              Record.query (sk, y) (.inl ⟨k, ⟨j, hj⟩⟩) := by
            rw [hx y]
            rfl
          dsimp only
          rw [wordList_succ, ← hx y, hq, progUpd_cacheQuery hP,
            progUpd_congr (chainSeg_succ k j n hj)]

/-! ## All chains -/



theorem wordList_full (hP : P.Hyp) (ξ : Record P) (k : Fin numChains) :
    wordList ξ k 0 (P.len k - 1) = ξ.table k := by
  unfold wordList Record.table
  rw [Nat.sub_add_cancel (hP.len_pos k)]
  simp only [Nat.zero_add]

/-- Walking the chains `φ 0, φ 1, …` in turn programs all their positions. -/
theorem E_run_tabulate_chains (hP : P.Hyp) (sk : Fin numChains → Word) :
    ∀ (n : ℕ) (φ : Fin n → Fin numChains), Function.Injective φ →
      ∀ (c : Tbl P → Cache) (G : Tbl P → (Fin n → List Word) × Cache → ℝ≥0∞),
      (∀ y t, FreshChain P (c y) (φ t) 0) →
      (∀ y t (j : Fin (P.len (φ t) - 1)) u, c (Function.update y (.inl ⟨φ t, j⟩) u) = c y) →
      (∀ y t (j : Fin (P.len (φ t) - 1)) u, G (Function.update y (.inl ⟨φ t, j⟩) u) = G y) →
      ∑ y : Tbl P, Nt * E (run (tabulate fun t : Fin n =>
          P.chainList (φ t) 0 (P.len (φ t) - 1) (sk (φ t))) (c y)) (G y) =
        ∑ y : Tbl P, Nt * G y (fun t => Record.table (sk, y) (φ t),
          progUpd (sk, y) (ChainsOf φ) (c y)) := by
  intro n
  induction n with
  | zero =>
    intro φ _ c G _ _ _
    refine Finset.sum_congr rfl fun y _ => ?_
    have he : (Fin.elim0 : Fin 0 → List Word) = fun t => Record.table (sk, y) (φ t) :=
      funext fun t => Fin.elim0 t
    rw [tabulate_zero', run_pure, E_pure, he,
      progUpd_of_false (sk, y) (ChainsOf φ) (c y) (fun _ ⟨t, _⟩ => Fin.elim0 t)]
  | succ n ih =>
    intro φ hφ c G hfr hc hG
    have h0 : ∀ t : Fin n, φ t.succ ≠ φ 0 := fun t h => Fin.succ_ne_zero t (hφ h)
    have hφ' : Function.Injective (fun t : Fin n => φ t.succ) :=
      fun a b h => Fin.succ_inj.mp (hφ h)
    have hA : ∀ y, E (run (tabulate fun t : Fin (n + 1) =>
          P.chainList (φ t) 0 (P.len (φ t) - 1) (sk (φ t))) (c y)) (G y) =
        E (run (P.chainList (φ 0) 0 (P.len (φ 0) - 1) (sk (φ 0))) (c y)) (fun p =>
          E (run (tabulate fun t : Fin n =>
              P.chainList (φ t.succ) 0 (P.len (φ t.succ) - 1) (sk (φ t.succ))) p.2)
            (fun p' => G y ((Fin.cases p.1 p'.1 : Fin (n + 1) → List Word), p'.2))) := by
      intro y
      rw [tabulate_succ']
      simp only [run_bind, E_bind, run_pure, E_pure]
    have hG₁ : ∀ y (j : Fin (P.len (φ 0) - 1)) u, 0 ≤ j.val →
        (fun p : List Word × Cache => E (run (tabulate fun t : Fin n =>
            P.chainList (φ t.succ) 0 (P.len (φ t.succ) - 1) (sk (φ t.succ))) p.2)
          (fun p' => G (Function.update y (.inl ⟨φ 0, j⟩) u)
            ((Fin.cases p.1 p'.1 : Fin (n + 1) → List Word), p'.2))) =
        (fun p : List Word × Cache => E (run (tabulate fun t : Fin n =>
            P.chainList (φ t.succ) 0 (P.len (φ t.succ) - 1) (sk (φ t.succ))) p.2)
          (fun p' => G y ((Fin.cases p.1 p'.1 : Fin (n + 1) → List Word), p'.2))) := by
      intro y j u _
      rw [hG y 0 j u]
    have hfr' : ∀ y (t : Fin n),
        FreshChain P (progUpd (sk, y) (ChainSeg (φ 0) 0 (P.len (φ 0) - 1)) (c y))
          (φ t.succ) 0 := by
      intro y t j hj _ v
      have hn : ¬ ∃ b, ChainSeg (φ 0) 0 (P.len (φ 0) - 1) b ∧
          Record.query (sk, y) b = ⟨896, P.chainInput (φ t.succ) j v⟩ := by
        rintro ⟨b, ⟨j', rfl, -, -⟩, hq⟩
        rw [Record.query_inl] at hq
        have := (Params.chainInput_eq_iff hP (by have := j'.isLt; omega) hj _ v).1
          (query_inj hq)
        exact h0 t this.1.symm
      rw [progUpd_apply_neg hn]
      exact hfr y t.succ j hj (Nat.zero_le _) v
    have hc' : ∀ y (t : Fin n) (j : Fin (P.len (φ t.succ) - 1)) u,
        progUpd (sk, Function.update y (.inl ⟨φ t.succ, j⟩) u)
            (ChainSeg (φ 0) 0 (P.len (φ 0) - 1))
            (c (Function.update y (.inl ⟨φ t.succ, j⟩) u)) =
          progUpd (sk, y) (ChainSeg (φ 0) 0 (P.len (φ 0) - 1)) (c y) := by
      intro y t j u
      rw [hc y t.succ j u]
      apply progUpd_update hP
      rintro b ⟨j', rfl, -, -⟩
      refine ⟨fun h => h0 t (inl_eq_fst h).symm, ?_⟩
      exact query_update_inl sk y _ u (φ 0) j'
        (fun _ hb => (h0 t (inl_eq_fst hb)).elim)
    have hG' : ∀ y (t : Fin n) (j : Fin (P.len (φ t.succ) - 1)) u,
        (fun p' : (Fin n → List Word) × Cache =>
          G (Function.update y (.inl ⟨φ t.succ, j⟩) u)
            ((Fin.cases (wordList (sk, Function.update y (.inl ⟨φ t.succ, j⟩) u) (φ 0) 0
              (P.len (φ 0) - 1)) p'.1 : Fin (n + 1) → List Word), p'.2)) =
        (fun p' : (Fin n → List Word) × Cache =>
          G y ((Fin.cases (wordList (sk, y) (φ 0) 0 (P.len (φ 0) - 1)) p'.1 :
            Fin (n + 1) → List Word), p'.2)) := by
      intro y t j u
      have hw : wordList (sk, Function.update y (.inl ⟨φ t.succ, j⟩) u) (φ 0) 0
          (P.len (φ 0) - 1) = wordList (sk, y) (φ 0) 0 (P.len (φ 0) - 1) := by
        unfold wordList
        refine List.map_congr_left fun i _ => ?_
        exact word_update sk y _ u (φ 0) _
          (fun _ hb => (h0 t (inl_eq_fst hb)).elim)
      rw [hw, hG y t.succ j u]
    calc ∑ y : Tbl P, Nt * E (run (tabulate fun t : Fin (n + 1) =>
            P.chainList (φ t) 0 (P.len (φ t) - 1) (sk (φ t))) (c y)) (G y)
        = ∑ y : Tbl P, Nt * E (run (P.chainList (φ 0) 0 (P.len (φ 0) - 1) (sk (φ 0))) (c y))
            (fun p => E (run (tabulate fun t : Fin n =>
                P.chainList (φ t.succ) 0 (P.len (φ t.succ) - 1) (sk (φ t.succ))) p.2)
              (fun p' => G y ((Fin.cases p.1 p'.1 : Fin (n + 1) → List Word), p'.2))) :=
          Finset.sum_congr rfl fun y _ => by rw [hA y]
      _ = ∑ y : Tbl P, Nt * E (run (tabulate fun t : Fin n =>
              P.chainList (φ t.succ) 0 (P.len (φ t.succ) - 1) (sk (φ t.succ)))
            (progUpd (sk, y) (ChainSeg (φ 0) 0 (P.len (φ 0) - 1)) (c y)))
            (fun p' => G y ((Fin.cases (wordList (sk, y) (φ 0) 0 (P.len (φ 0) - 1)) p'.1 :
              Fin (n + 1) → List Word), p'.2)) :=
          by
            let G₀ : Tbl P → List Word × Cache → ℝ≥0∞ := fun y p =>
              E (run (tabulate fun t : Fin n =>
                P.chainList (φ t.succ) 0 (P.len (φ t.succ) - 1) (sk (φ t.succ))) p.2)
                (fun p' => G y ((Fin.cases p.1 p'.1 : Fin (n + 1) → List Word), p'.2))
            have hx0 : ∀ y : Tbl P, (fun _ : Tbl P => sk (φ 0)) y =
                Record.word ((sk, y) : Record P) (φ 0) 0 := fun y => rfl
            have hfr0 : ∀ y : Tbl P, FreshChain P (c y) (φ 0) 0 := fun y => hfr y 0
            have hc0 : ∀ (y : Tbl P) (j : Fin (P.len (φ 0) - 1)) u, 0 ≤ j.val →
                c (Function.update y (.inl ⟨φ 0, j⟩) u) = c y := fun y j u _ => hc y 0 j u
            have hG0 : ∀ (y : Tbl P) (j : Fin (P.len (φ 0) - 1)) u, 0 ≤ j.val →
                G₀ (Function.update y (.inl ⟨φ 0, j⟩) u) = G₀ y := hG₁
            have h := E_run_chainList_avg hP sk (φ 0) (P.len (φ 0) - 1) 0 (Nat.zero_add _).le
              G₀ (fun _ => sk (φ 0)) c hx0 hfr0 hc0 hG0
            exact h
      _ = ∑ y : Tbl P, Nt * G y ((Fin.cases (wordList (sk, y) (φ 0) 0 (P.len (φ 0) - 1))
              (fun t => Record.table (sk, y) (φ t.succ)) : Fin (n + 1) → List Word),
            progUpd (sk, y) (ChainsOf fun t => φ t.succ)
              (progUpd (sk, y) (ChainSeg (φ 0) 0 (P.len (φ 0) - 1)) (c y))) :=
          by
            have h := ih (fun t => φ t.succ) hφ'
              (fun (y : Tbl P) => progUpd ((sk, y) : Record P)
                (ChainSeg (φ 0) 0 (P.len (φ 0) - 1)) (c y))
              (fun (y : Tbl P) (p' : (Fin n → List Word) × Cache) =>
                G y ((Fin.cases (wordList ((sk, y) : Record P) (φ 0) 0 (P.len (φ 0) - 1))
                p'.1 : Fin (n + 1) → List Word), p'.2)) hfr' hc' hG'
            exact h
      _ = ∑ y : Tbl P, Nt * G y (fun t => Record.table (sk, y) (φ t),
            progUpd (sk, y) (ChainsOf φ) (c y)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have hcases : (Fin.cases (wordList (sk, y) (φ 0) 0 (P.len (φ 0) - 1))
              (fun t => Record.table (sk, y) (φ t.succ)) : Fin (n + 1) → List Word) =
              fun t => Record.table (sk, y) (φ t) := by
            funext t
            rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t, rfl⟩
            · exact wordList_full hP _ _
            · rfl
          rw [hcases, progUpd_progUpd, progUpd_congr (chainsOf_succ φ)]

/-! ## The root -/



/-- The root calls `r, …, 8` from the state before call `r` program root locations `r, …, 8` and
end in the final state. -/
theorem E_run_rootFrom_avg (hP : P.Hyp) (sk : Fin numChains → Word)
    (G : Tbl P → BitVec 256 × Cache → ℝ≥0∞) :
    ∀ (m r : ℕ) (hrm : r + m = 9) (st : Tbl P → BitVec 256) (c : Tbl P → Cache),
      (∀ y, st y = Record.rootState (sk, y) r) →
      (∀ y, FreshRoot P (c y) r) →
      (∀ y (s : Fin 9) u, r ≤ s.val → c (Function.update y (.inr s) u) = c y) →
      (∀ y (s : Fin 9) u, r ≤ s.val → G (Function.update y (.inr s) u) = G y) →
      ∑ y : Tbl P, Nt * E (run (P.rootFrom (Record.top (sk, y)) r m (st y)) (c y)) (G y) =
        ∑ y : Tbl P, Nt * G y (Record.rootState (sk, y) 9,
          progUpd (sk, y) (RootsFrom r) (c y)) := by
  intro m
  induction m with
  | zero =>
    intro r hrm st c hst _ _ _
    obtain rfl : r = 9 := by omega
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [rootFrom_zero', run_pure, E_pure, hst y,
      progUpd_of_false (sk, y) (RootsFrom 9) (c y)
        (fun _ ⟨s, _, hs⟩ => by have := s.isLt; omega)]
  | succ m ih =>
    intro r hrm st c hst hfr hc hG
    have hr : r < 9 := by omega
    have hstep : ∀ y : Tbl P,
        E (run (P.rootFrom (Record.top (sk, y)) r (m + 1) (st y)) (c y)) (G y) =
          E (run (hash (P.rootInput (Record.top (sk, y)) r (st y))) (c y))
            (fun p => E (run (P.rootFrom (Record.top (sk, y)) (r + 1) m p.1) p.2) (G y)) := by
      intro y
      rw [rootFrom_succ', run_bind, E_bind]
    have hXu : ∀ y (s : Fin 9) u, r ≤ s.val →
        P.rootInput (Record.top (sk, Function.update y (.inr s) u)) r
            (st (Function.update y (.inr s) u)) =
          P.rootInput (Record.top (sk, y)) r (st y) := by
      intro y s u hs
      rw [hst, hst, rootState_update sk y s u r (by omega), top_update_inr]
    have hK : ∀ y u (p : BitVec hashBits × Cache),
        E (run (P.rootFrom (Record.top (sk, Function.update y (.inr ⟨r, hr⟩) u)) (r + 1) m p.1)
            p.2) (G (Function.update y (.inr ⟨r, hr⟩) u)) =
          E (run (P.rootFrom (Record.top (sk, y)) (r + 1) m p.1) p.2) (G y) := by
      intro y u p
      rw [top_update_inr, hG y ⟨r, hr⟩ u le_rfl]
    have hst' : ∀ y : Tbl P,
        (y (.inr ⟨r, hr⟩) : BitVec 256) = Record.rootState (sk, y) (r + 1) :=
      fun y => (Record.rootState_succ (sk, y) ⟨r, hr⟩).symm
    have hfr' : ∀ y : Tbl P, FreshRoot P ((c y).cacheQuery
        ⟨896, P.rootInput (Record.top (sk, y)) r (st y)⟩ (y (.inr ⟨r, hr⟩))) (r + 1) := by
      intro y s hs hrs t st'
      have hne : (⟨896, P.rootInput t s st'⟩ : Query) ≠
          ⟨896, P.rootInput (Record.top (sk, y)) r (st y)⟩ := by
        intro h
        have h1 := ((Params.rootInput_eq_iff hP hs hr _ _ _ _).1 (query_inj h)).1
        omega
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
      exact hfr y s hs (by omega) t st'
    have hc' : ∀ y (s : Fin 9) u, r + 1 ≤ s.val →
        (c (Function.update y (.inr s) u)).cacheQuery
            ⟨896, P.rootInput (Record.top (sk, Function.update y (.inr s) u)) r
              (st (Function.update y (.inr s) u))⟩
            (Function.update y (.inr s) u (.inr ⟨r, hr⟩)) =
          (c y).cacheQuery ⟨896, P.rootInput (Record.top (sk, y)) r (st y)⟩
            (y (.inr ⟨r, hr⟩)) := by
      intro y s u hs
      have hne : (Sum.inr ⟨r, hr⟩ : Loc P) ≠ .inr s := by
        intro h
        have h2 := congrArg Fin.val (Sum.inr.inj h)
        simp only at h2
        omega
      rw [hc y s u (by omega), hXu y s u (by omega), Function.update_of_ne hne]
    calc ∑ y : Tbl P, Nt * E (run (P.rootFrom (Record.top (sk, y)) r (m + 1) (st y)) (c y)) (G y)
        = ∑ y : Tbl P, Nt * E (run (hash (P.rootInput (Record.top (sk, y)) r (st y))) (c y))
            (fun p => E (run (P.rootFrom (Record.top (sk, y)) (r + 1) m p.1) p.2) (G y)) :=
          Finset.sum_congr rfl fun y _ => by rw [hstep y]
      _ = ∑ y : Tbl P, Nt * E (run (P.rootFrom (Record.top (sk, y)) (r + 1) m
              (y (.inr ⟨r, hr⟩)))
            ((c y).cacheQuery ⟨896, P.rootInput (Record.top (sk, y)) r (st y)⟩
              (y (.inr ⟨r, hr⟩)))) (G y) :=
          avg_hash (.inr ⟨r, hr⟩) (fun y => P.rootInput (Record.top (sk, y)) r (st y)) c
            (fun y p => E (run (P.rootFrom (Record.top (sk, y)) (r + 1) m p.1) p.2) (G y))
            (fun y => hfr y r hr le_rfl _ _) (fun y u => hXu y ⟨r, hr⟩ u le_rfl)
            (fun y u => hc y ⟨r, hr⟩ u le_rfl) hK
      _ = ∑ y : Tbl P, Nt * G y (Record.rootState (sk, y) 9,
            progUpd (sk, y) (RootsFrom (r + 1))
              ((c y).cacheQuery ⟨896, P.rootInput (Record.top (sk, y)) r (st y)⟩
                (y (.inr ⟨r, hr⟩)))) :=
          ih (r + 1) (by omega) (fun y => (y (.inr ⟨r, hr⟩) : BitVec 256))
            (fun y => (c y).cacheQuery ⟨896, P.rootInput (Record.top (sk, y)) r (st y)⟩
              (y (.inr ⟨r, hr⟩)))
            hst' hfr' hc' (fun y s u hs => hG y s u (by omega))
      _ = ∑ y : Tbl P, Nt * G y (Record.rootState (sk, y) 9,
            progUpd (sk, y) (RootsFrom r) (c y)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have hq : (⟨896, P.rootInput (Record.top (sk, y)) r (st y)⟩ : Query) =
              Record.query (sk, y) (.inr ⟨r, hr⟩) := by
            rw [hst y]
            rfl
          rw [hq, progUpd_cacheQuery hP, progUpd_congr (rootsFrom_succ r hr)]

/-! ## Sampling the seeds -/

theorem E_run_tabulate_sample (n : ℕ) :
    ∀ (g : (Fin n → Word) × Cache → ℝ≥0∞) (c : Cache),
      E (run (tabulate fun _ : Fin n => sampleBits 128) c) g =
        ∑ sk : Fin n → Word, (Fintype.card (Fin n → Word) : ℝ≥0∞)⁻¹ * g (sk, c) := by
  induction n with
  | zero =>
    intro g c
    rw [tabulate_zero', run_pure, E_pure]
    symm
    calc ∑ sk : Fin 0 → Word, (Fintype.card (Fin 0 → Word) : ℝ≥0∞)⁻¹ * g (sk, c)
        = ∑ _sk : Fin 0 → Word, (Fintype.card (Fin 0 → Word) : ℝ≥0∞)⁻¹ * g (Fin.elim0, c) :=
          Finset.sum_congr rfl fun sk _ => by
            rw [show sk = Fin.elim0 from funext fun i => Fin.elim0 i]
      _ = g (Fin.elim0, c) := sum_inv_card_mul' _
  | succ n ih =>
    intro g c
    have h0 : (Fintype.card Word : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have ht : (Fintype.card Word : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hcard : (Fintype.card (Fin (n + 1) → Word) : ℝ≥0∞) =
        (Fintype.card Word : ℝ≥0∞) * (Fintype.card (Fin n → Word) : ℝ≥0∞) := by
      rw [← Nat.cast_mul, ← Fintype.card_prod,
        Fintype.card_congr (Fin.consEquiv fun _ : Fin (n + 1) => Word)]
    have hx : ∀ x : Word, E (run (tabulate (fun _ : Fin n => sampleBits 128) >>= fun xs =>
        pure (Fin.cases x xs : Fin (n + 1) → Word)) c) g =
        ∑ xs : Fin n → Word, (Fintype.card (Fin n → Word) : ℝ≥0∞)⁻¹ *
          g ((Fin.cases x xs : Fin (n + 1) → Word), c) := by
      intro x
      rw [run_bind, E_bind, ih]
      refine Finset.sum_congr rfl fun xs _ => ?_
      simp only [run_pure, E_pure]
    calc E (run (tabulate fun _ : Fin (n + 1) => sampleBits 128) c) g
        = E (run (sampleBits 128) c) (fun p => E (run (tabulate (fun _ : Fin n => sampleBits 128)
            >>= fun xs => pure (Fin.cases p.1 xs : Fin (n + 1) → Word)) p.2) g) := by
          rw [tabulate_succ', run_bind, E_bind]
      _ = ∑ x : Word, (Fintype.card Word : ℝ≥0∞)⁻¹ * E (run (tabulate
            (fun _ : Fin n => sampleBits 128) >>= fun xs =>
              pure (Fin.cases x xs : Fin (n + 1) → Word)) c) g := by
          simp only [run_sampleBits, E_map, E_uniform]
      _ = ∑ x : Word, (Fintype.card Word : ℝ≥0∞)⁻¹ * ∑ xs : Fin n → Word,
            (Fintype.card (Fin n → Word) : ℝ≥0∞)⁻¹ *
              g ((Fin.cases x xs : Fin (n + 1) → Word), c) :=
          Finset.sum_congr rfl fun x _ => by rw [hx x]
      _ = ∑ sk : Fin (n + 1) → Word,
            (Fintype.card (Fin (n + 1) → Word) : ℝ≥0∞)⁻¹ * g (sk, c) := by
          rw [sum_fin_cases (fun sk : Fin (n + 1) → Word =>
            (Fintype.card (Fin (n + 1) → Word) : ℝ≥0∞)⁻¹ * g (sk, c))]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun xs _ => ?_
          rw [hcard, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), mul_assoc]

/-! ## Key generation -/

theorem table_getD_top (hP : P.Hyp) (ξ : Record P) (k : Fin numChains) :
    (ξ.table k).getD (P.len k - 1) 0 = ξ.top k := by
  unfold Record.table Record.top
  have h := hP.len_pos k
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- For fixed seeds, the chains and the root are a uniform table. -/
theorem E_run_keygen_sk (hP : P.Hyp) (sk : Fin numChains → Word)
    (g' : (PublicKey × SecretKey) × Cache → ℝ≥0∞) :
    E (run (tabulate (fun k => P.chainList k 0 (P.len k - 1) (sk k)) >>= fun tables =>
        P.root (fun k => (tables k).getD (P.len k - 1) 0) >>= fun pk =>
          pure (pk, (⟨tables, pk⟩ : SecretKey))) ∅) g' =
      ∑ y : Tbl P, Nt * g' ((Record.pk (sk, y), Record.sk (sk, y)), Record.cache (sk, y)) := by
  have hfr0 : ∀ y : Tbl P, FreshRoot P (progUpd (sk, y) (ChainsOf fun t : Fin numChains => t) ∅)
      0 := by
    intro y s hs _ t st
    have hn : ¬ ∃ b, ChainsOf (fun t : Fin numChains => t) b ∧
        Record.query (sk, y) b = ⟨896, P.rootInput t s st⟩ := by
      rintro ⟨b, ⟨t', j', rfl⟩, hq⟩
      rw [Record.query_inl] at hq
      exact Params.chainInput_ne_rootInput hP hs _ _ _ _ _ (query_inj hq)
    rw [progUpd_apply_neg hn, QueryCache.empty_apply]
  have hc0 : ∀ (y : Tbl P) (s : Fin 9) u, 0 ≤ s.val →
      progUpd (sk, Function.update y (.inr s) u) (ChainsOf fun t : Fin numChains => t) ∅ =
        progUpd (sk, y) (ChainsOf fun t : Fin numChains => t) ∅ := by
    intro y s u _
    apply progUpd_update hP
    rintro b ⟨t, j', rfl⟩
    exact ⟨Sum.inl_ne_inr,
      query_update_inl sk y _ u _ j' (fun _ h => absurd h Sum.inr_ne_inl)⟩
  have hall : ∀ b : Loc P,
      (RootsFrom 0 b ∨ ChainsOf (fun t : Fin numChains => t) b) ↔ True := by
    intro b
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rcases b with ⟨k, j⟩ | s
    · exact Or.inr ⟨k, j, rfl⟩
    · exact Or.inl ⟨s, rfl, Nat.zero_le _⟩
  have htops : ∀ y : Tbl P, (fun k => (Record.table (sk, y) k).getD (P.len k - 1) 0) =
      Record.top (sk, y) := fun y => funext fun k => table_getD_top hP _ k
  calc E (run (tabulate (fun k => P.chainList k 0 (P.len k - 1) (sk k)) >>= fun tables =>
          P.root (fun k => (tables k).getD (P.len k - 1) 0) >>= fun pk =>
            pure (pk, (⟨tables, pk⟩ : SecretKey))) ∅) g'
      = ∑ y : Tbl P, Nt * E (run (tabulate (fun k => P.chainList k 0 (P.len k - 1) (sk k))) ∅)
          (fun p => E (run (P.root (fun k => (p.1 k).getD (P.len k - 1) 0) >>= fun pk =>
            pure (pk, (⟨p.1, pk⟩ : SecretKey))) p.2) g') := by
        rw [run_bind, E_bind, sum_inv_card_mul']
    _ = ∑ y : Tbl P, Nt * E (run (P.root (Record.top (sk, y)) >>= fun pk =>
          pure (pk, (⟨Record.table (sk, y), pk⟩ : SecretKey)))
          (progUpd (sk, y) (ChainsOf fun t : Fin numChains => t) ∅)) g' := by
        have h := E_run_tabulate_chains hP sk numChains (fun t => t) (fun _ _ h => h)
          (fun _ => ∅)
          (fun _ p => E (run (P.root (fun k => (p.1 k).getD (P.len k - 1) 0) >>= fun pk =>
            pure (pk, (⟨p.1, pk⟩ : SecretKey))) p.2) g')
          (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        rw [h]
        refine Finset.sum_congr rfl fun y _ => ?_
        dsimp only
        rw [htops y]
    _ = ∑ y : Tbl P, Nt * E (run (P.rootFrom (Record.top (sk, y)) 0 9
            (Params.rootInit (Record.top (sk, y))))
          (progUpd (sk, y) (ChainsOf fun t : Fin numChains => t) ∅))
          (fun p => g' ((p.1.extractLsb' 0 128, (⟨Record.table (sk, y),
            p.1.extractLsb' 0 128⟩ : SecretKey)), p.2)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Params.root]
        simp only [run_bind, E_bind, run_map, E_map, run_pure, E_pure]
    _ = ∑ y : Tbl P, Nt * g' (((Record.rootState (sk, y) 9).extractLsb' 0 128,
          (⟨Record.table (sk, y), (Record.rootState (sk, y) 9).extractLsb' 0 128⟩ : SecretKey)),
          progUpd (sk, y) (RootsFrom 0)
            (progUpd (sk, y) (ChainsOf fun t : Fin numChains => t) ∅)) :=
        E_run_rootFrom_avg hP sk (fun y p => g' ((p.1.extractLsb' 0 128,
            (⟨Record.table (sk, y), p.1.extractLsb' 0 128⟩ : SecretKey)), p.2)) 9 0
          (by omega) (fun y => Params.rootInit (Record.top (sk, y)))
          (fun y => progUpd (sk, y) (ChainsOf fun t : Fin numChains => t) ∅)
          (fun y => rfl) hfr0 hc0 (fun y s u _ => by simp only [table_update_inr])
    _ = ∑ y : Tbl P, Nt * g' ((Record.pk (sk, y), Record.sk (sk, y)), Record.cache (sk, y)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have hpk : ((Record.rootState (sk, y) 9).extractLsb' 0 128 : PublicKey) =
            Record.pk (sk, y) :=
          congrArg (fun v : BitVec 256 => v.extractLsb' 0 128)
            (Record.rootState_succ (sk, y) 8)
        rw [progUpd_progUpd, progUpd_congr hall, progUpd_true_empty hP, hpk]
        rfl

/-- **Key generation is a uniform record.** -/
theorem E_run_keygen (hP : P.Hyp) (g' : (PublicKey × SecretKey) × Cache → ℝ≥0∞) :
    E (run P.keygen ∅) g' = ∑ ξ : Record P, recW P * g' ((ξ.pk, ξ.sk), ξ.cache) := by
  have h0 : (Fintype.card (Fin numChains → Word) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ht : (Fintype.card (Fin numChains → Word) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcard : recW P = (Fintype.card (Fin numChains → Word) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ := by
    rw [recW, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inl h0) (Or.inl ht)]
  calc E (run P.keygen ∅) g'
      = ∑ sk : Fin numChains → Word, (Fintype.card (Fin numChains → Word) : ℝ≥0∞)⁻¹ *
          E (run (tabulate (fun k => P.chainList k 0 (P.len k - 1) (sk k)) >>= fun tables =>
            P.root (fun k => (tables k).getD (P.len k - 1) 0) >>= fun pk =>
              pure (pk, (⟨tables, pk⟩ : SecretKey))) ∅) g' := by
        rw [Params.keygen, run_bind, E_bind, E_run_tabulate_sample]
    _ = ∑ sk : Fin numChains → Word, (Fintype.card (Fin numChains → Word) : ℝ≥0∞)⁻¹ *
          ∑ y : Tbl P, Nt * g' ((Record.pk (sk, y), Record.sk (sk, y)), Record.cache (sk, y)) :=
        Finset.sum_congr rfl fun sk _ => by rw [E_run_keygen_sk hP]
    _ = ∑ sk : Fin numChains → Word, ∑ y : Tbl P, recW P *
          g' ((Record.pk (sk, y), Record.sk (sk, y)), Record.cache (sk, y)) := by
        refine Finset.sum_congr rfl fun sk _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hcard, mul_assoc]
    _ = ∑ ξ : Record P, recW P * g' ((ξ.pk, ξ.sk), ξ.cache) :=
        (Fintype.sum_prod_type (fun ξ : Record P =>
          recW P * g' ((ξ.pk, ξ.sk), ξ.cache))).symm

end OptimalOTS.LeanIsaBaseline.Layer
