import Submissions.UpperLeanIsa.Stages

/-!
# Key generation is a uniform record

Under the lazy random oracle started from the empty cache, key generation samples the 34 secret
words and then queries every chain position and every root position exactly once, at pairwise
distinct inputs. Its output and final cache are therefore those of a uniformly random record:

```
E[g' | run keygen ∅] = ∑ ξ : Record, w · g' ((ξ.publicKey, ξ.1), ξ.cache).
```

Every fresh answer is absorbed into a uniform *full* answer table
`y : HashLocation → BitVec 256` (`sum_avg_update`, after the checked `upper-riscv-687` keygen
bridge), so no sum over a growing tuple is ever split. The caches written along the way are
described by `progUpd`, which overwrites a cache by the programmed points of the record at a set
of locations; at the end all locations are programmed and the cache is `ξ.cache`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/- The programs are only ever unfolded through their equation lemmas; keeping them irreducible
stops the unifier from unrolling `chain … 255 …` or `tabulate` at a literal size. -/
attribute [local irreducible] chain rootFold tabulate

/-! ## Averaging over one coordinate (generic) -/

private theorem sum_sum_update_pi {ι : Type} [Fintype ι] [DecidableEq ι] {R : ι → Type}
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

private theorem sum_inv_card_mul' {α : Type} [Fintype α] [Nonempty α] (a : ℝ≥0∞) :
    ∑ _x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

/-- Averaging a function of a fresh uniform coordinate `u` and a uniform table `y` that does not
read `y i` equals averaging over `y` alone with `u := y i`. -/
private theorem sum_avg_update {ι : Type} [Fintype ι] [DecidableEq ι] {R : ι → Type}
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

/-- Splitting a sum over `(n + 1)`-tuples into the first entry and the rest. -/
private theorem sum_fin_cases {α : Type} [Fintype α] {n : ℕ}
    (F : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∑ f, F f = ∑ x : α, ∑ xs : Fin n → α, F (Fin.cases x xs : Fin (n + 1) → α) := by
  rw [← Fintype.sum_prod_type' (fun (x : α) (xs : Fin n → α) =>
    F (Fin.cases x xs : Fin (n + 1) → α))]
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => α)
    (fun p => F (Fin.cases p.1 p.2 : Fin (n + 1) → α)) F fun _ => rfl).symm

/-! ## Full answer tables and one fresh query -/

/-- Full answer tables: one hash output per chain or root location. -/
private abbrev Tbl := HashLocation → BitVec hashBits

/-- The uniform weight of a full answer table. -/
local notation "Nt" => ((Fintype.card Tbl : ℝ≥0∞)⁻¹)

/-- A query the cache does not hold gets a fresh uniform answer, which is then cached. -/
theorem run_hash_fresh {n : ℕ} (x : BitVec n) (c : Cache) (hc : c ⟨n, x⟩ = none) :
    run (hash x) c = ($ᵗ BitVec hashBits) >>= fun u => pure (u, c.cacheQuery ⟨n, x⟩ u) := by
  change (simulateQ oracleImpl (liftM (Spec.query (.inr ⟨n, x⟩)))).run c = _
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_none hc

private theorem run_sampleBits (m : ℕ) (c : Cache) :
    run (sampleBits m) c = (fun x => (x, c)) <$> ($ᵗ BitVec m) := by
  unfold sampleBits
  exact run_liftM _ c

/-- A fresh answer absorbed into the uniform table: averaging the answer `u` of a fresh query
together with a table `y` that the rest of the computation does not read at `a` is averaging `y`
alone, with `u := y a`. -/
private theorem avg_hash (a : HashLocation) (x : Tbl → BitVec 896) (c : Tbl → Cache)
    (K : Tbl → BitVec hashBits × Cache → ℝ≥0∞)
    (hfresh : ∀ y, c y ⟨896, x y⟩ = none)
    (hx : ∀ y u, x (Function.update y a u) = x y)
    (hc : ∀ y u, c (Function.update y a u) = c y)
    (hK : ∀ y u p, K (Function.update y a u) p = K y p) :
    ∑ y : Tbl, Nt * E (run (hash (x y)) (c y)) (K y) =
      ∑ y : Tbl, Nt * K y (y a, (c y).cacheQuery ⟨896, x y⟩ (y a)) := by
  have key := sum_avg_update (R := fun _ : HashLocation => BitVec hashBits) a
    (fun u y => K y (u, (c y).cacheQuery ⟨896, x y⟩ u))
    (fun u u' y => by
      first
        | (simp only [hx, hc, hK]; done)
        | (simp only [hc, hK]; rw [hx y u'])
        | (rw [hK, hc, hx y u']))
  refine Eq.trans ?_ key
  have h1 : ∀ y : Tbl, E (run (hash (x y)) (c y)) (K y) =
      ∑ u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        K y (u, (c y).cacheQuery ⟨896, x y⟩ u) := by
    intro y
    rw [run_hash_fresh _ _ (hfresh y), E_bind, E_uniform]
    simp only [E_pure]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_left_comm]

/-! ## Records built from a secret-word tuple and a table -/

private theorem query_inj {a b : BitVec 896} (h : (⟨896, a⟩ : Query) = ⟨896, b⟩) : a = b :=
  eq_of_heq (Sigma.mk.inj_iff.mp h).2

private theorem query_inl_eq (sk : Words) (y : Tbl) (i : Fin 34) (k : Fin 255) :
    Record.query (sk, y) (.inl (i, k)) =
      ⟨896, chainInput i.val k.val (Record.word (sk, y) i ⟨k.val, by have := k.isLt; omega⟩)⟩ :=
  rfl

private theorem word_zero (sk : Words) (y : Tbl) (i : Fin 34) :
    Record.word (sk, y) i ⟨0, by omega⟩ = sk i := by
  first
    | exact dif_pos rfl
    | rfl
    | simp only [Record.word, ↓reduceDIte]

private theorem rootState_zero (sk : Words) (y : Tbl) :
    Record.rootState (sk, y) ⟨0, by omega⟩ = 0 := by
  first
    | exact dif_pos rfl
    | rfl
    | simp only [Record.rootState, ↓reduceDIte]

private theorem rootState_34 (sk : Words) (y : Tbl) :
    Record.rootState (sk, y) 34 = y (.inr 33) := by
  first
    | exact Record.rootState_after (sk, y) 33
    | rfl

/-- The word at position `k` of chain `i` reads only the answer at `(i, k - 1)`. -/
private theorem word_update (sk : Words) (y : Tbl) (b : HashLocation) (u : BitVec hashBits)
    (i : Fin 34) (k : Fin 256) (h : ∀ k' : Fin 255, b = .inl (i, k') → k'.val + 1 ≠ k.val) :
    Record.word (sk, Function.update y b u) i k = Record.word (sk, y) i k := by
  by_cases hk : k.val = 0
  · simp only [Record.word, dif_pos hk]
  · have hne : (Sum.inl (i, ⟨k.val - 1, by have := k.isLt; omega⟩) : HashLocation) ≠ b := by
      intro hb
      exact h _ hb.symm (by show k.val - 1 + 1 = k.val; omega)
    simp only [Record.word, dif_neg hk, Function.update_of_ne hne]

private theorem endpoint_update (sk : Words) (y : Tbl) (b : HashLocation) (u : BitVec hashBits)
    (i : Fin 34) (h : ∀ k' : Fin 255, b = .inl (i, k') → k'.val + 1 ≠ 255) :
    Record.endpoint (sk, Function.update y b u) i = Record.endpoint (sk, y) i :=
  word_update sk y b u i 255 h

private theorem query_update_inl (sk : Words) (y : Tbl) (b : HashLocation)
    (u : BitVec hashBits) (i : Fin 34) (k : Fin 255)
    (h : ∀ k' : Fin 255, b = .inl (i, k') → k'.val + 1 ≠ k.val) :
    Record.query (sk, Function.update y b u) (.inl (i, k)) =
      Record.query (sk, y) (.inl (i, k)) := by
  have h': ∀ k' : Fin 255, b = .inl (i, k') →
      k'.val + 1 ≠ (⟨k.val, by have := k.isLt; omega⟩ : Fin 256).val := h
  rw [query_inl_eq, query_inl_eq, word_update sk y b u i _ h']

/-- The root state after `k` absorptions reads only the answer at root position `k - 1`. -/
private theorem rootState_update (sk : Words) (y : Tbl) (b : HashLocation) (u : BitVec hashBits)
    (k : Fin 35) (h : ∀ r' : Fin 34, b = .inr r' → r'.val + 1 ≠ k.val) :
    Record.rootState (sk, Function.update y b u) k = Record.rootState (sk, y) k := by
  by_cases hk : k.val = 0
  · simp only [Record.rootState, dif_pos hk]
  · have hne : (Sum.inr ⟨k.val - 1, by have := k.isLt; omega⟩ : HashLocation) ≠ b := by
      intro hb
      exact h _ hb.symm (by show k.val - 1 + 1 = k.val; omega)
    simp only [Record.rootState, dif_neg hk, Function.update_of_ne hne]

/-! ## Programming a cache with the points of a record -/

/-- `c` overwritten by the programmed points of `ξ` at the locations satisfying `P`. -/
private def progUpd (ξ : Record) (P : HashLocation → Prop) (c : Cache) : Cache :=
  fun q => if ∃ a, P a ∧ ξ.query a = q then ξ.cache q else c q

private theorem progUpd_apply (ξ : Record) (P : HashLocation → Prop) (c : Cache) (q : Query) :
    progUpd ξ P c q = if ∃ a, P a ∧ ξ.query a = q then ξ.cache q else c q :=
  rfl

private theorem progUpd_apply_neg {ξ : Record} {P : HashLocation → Prop} {c : Cache}
    {q : Query} (h : ¬ ∃ a, P a ∧ ξ.query a = q) : progUpd ξ P c q = c q := by
  rw [progUpd_apply, if_neg h]

private theorem progUpd_of_false (ξ : Record) (P : HashLocation → Prop) (c : Cache)
    (h : ∀ b, ¬ P b) : progUpd ξ P c = c := by
  funext q
  have hn : ¬ ∃ a, P a ∧ ξ.query a = q := fun ⟨a, ha, _⟩ => h a ha
  rw [progUpd_apply, if_neg hn]

private theorem progUpd_congr {ξ : Record} {P P' : HashLocation → Prop} {c : Cache}
    (h : ∀ b, P b ↔ P' b) : progUpd ξ P c = progUpd ξ P' c := by
  have hPP : P = P' := funext fun b => propext (h b)
  rw [hPP]

/-- Caching the programmed point of `a` is programming `a` as well. -/
private theorem progUpd_cacheQuery (sk : Words) (y : Tbl) (P : HashLocation → Prop) (c : Cache)
    (a : HashLocation) :
    progUpd (sk, y) P (c.cacheQuery (Record.query (sk, y) a) (y a)) =
      progUpd (sk, y) (fun b => P b ∨ b = a) c := by
  funext q
  rw [progUpd_apply, progUpd_apply]
  by_cases hq : Record.query (sk, y) a = q
  · subst hq
    have h1 : ∃ b, (P b ∨ b = a) ∧ Record.query (sk, y) b = Record.query (sk, y) a :=
      ⟨a, Or.inr rfl, rfl⟩
    rw [if_pos h1]
    by_cases h : ∃ b, P b ∧ Record.query (sk, y) b = Record.query (sk, y) a
    · rw [if_pos h]
    · rw [if_neg h, QueryCache.cacheQuery_self]
      exact (Record.cache_query (sk, y) a).symm
  · by_cases h : ∃ b, P b ∧ Record.query (sk, y) b = q
    · have h1 : ∃ b, (P b ∨ b = a) ∧ Record.query (sk, y) b = q := by
        obtain ⟨b, hb, hbq⟩ := h
        exact ⟨b, Or.inl hb, hbq⟩
      rw [if_pos h, if_pos h1]
    · have h1 : ¬ ∃ b, (P b ∨ b = a) ∧ Record.query (sk, y) b = q := by
        rintro ⟨b, hb | rfl, hbq⟩
        · exact h ⟨b, hb, hbq⟩
        · exact hq hbq
      rw [if_neg h, if_neg h1, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]

private theorem progUpd_progUpd (sk : Words) (y : Tbl) (P Q : HashLocation → Prop) (c : Cache) :
    progUpd (sk, y) P (progUpd (sk, y) Q c) = progUpd (sk, y) (fun b => P b ∨ Q b) c := by
  funext q
  rw [progUpd_apply, progUpd_apply, progUpd_apply]
  by_cases hP : ∃ b, P b ∧ Record.query (sk, y) b = q
  · have h1 : ∃ b, (P b ∨ Q b) ∧ Record.query (sk, y) b = q := by
      obtain ⟨b, hb, hbq⟩ := hP
      exact ⟨b, Or.inl hb, hbq⟩
    rw [if_pos hP, if_pos h1]
  · by_cases hQ : ∃ b, Q b ∧ Record.query (sk, y) b = q
    · have h1 : ∃ b, (P b ∨ Q b) ∧ Record.query (sk, y) b = q := by
        obtain ⟨b, hb, hbq⟩ := hQ
        exact ⟨b, Or.inr hb, hbq⟩
      rw [if_neg hP, if_pos hQ, if_pos h1]
    · have h1 : ¬ ∃ b, (P b ∨ Q b) ∧ Record.query (sk, y) b = q := by
        rintro ⟨b, hb | hb, hbq⟩
        · exact hP ⟨b, hb, hbq⟩
        · exact hQ ⟨b, hb, hbq⟩
      rw [if_neg hP, if_neg hQ, if_neg h1]

/-- Programming every location of the empty cache gives the record's cache. -/
private theorem progUpd_true_empty (ξ : Record) : progUpd ξ (fun _ => True) ∅ = ξ.cache := by
  funext q
  rw [progUpd_apply]
  by_cases h : ∃ a, True ∧ ξ.query a = q
  · rw [if_pos h]
  · rw [if_neg h, QueryCache.empty_apply]
    cases hc : ξ.cache q with
    | none => rfl
    | some v =>
      obtain ⟨a, ha, -⟩ := (ξ.cache_some_iff q v).1 hc
      exact (h ⟨a, trivial, ha⟩).elim

/-- Programming does not read the table at a location `b` that none of the programmed
locations reads. -/
private theorem progUpd_update (sk : Words) (y : Tbl) (b : HashLocation) (u : BitVec hashBits)
    (P : HashLocation → Prop) (c : Cache)
    (hP : ∀ b', P b' → b' ≠ b ∧
      Record.query (sk, Function.update y b u) b' = Record.query (sk, y) b') :
    progUpd (sk, Function.update y b u) P c = progUpd (sk, y) P c := by
  funext q
  rw [progUpd_apply, progUpd_apply]
  have hiff : (∃ b', P b' ∧ Record.query (sk, Function.update y b u) b' = q) ↔
      (∃ b', P b' ∧ Record.query (sk, y) b' = q) :=
    ⟨fun ⟨b', hb', hq⟩ => ⟨b', hb', (hP b' hb').2.symm.trans hq⟩,
      fun ⟨b', hb', hq⟩ => ⟨b', hb', (hP b' hb').2.trans hq⟩⟩
  by_cases h : ∃ b', P b' ∧ Record.query (sk, y) b' = q
  · rw [if_pos (hiff.2 h), if_pos h]
    obtain ⟨b', hb', rfl⟩ := h
    have h1 : Record.cache (sk, Function.update y b u) (Record.query (sk, y) b') = some (y b') := by
      rw [← (hP b' hb').2, Record.cache_query]
      exact congrArg some (Function.update_of_ne (hP b' hb').1 u y)
    have h2 : Record.cache (sk, y) (Record.query (sk, y) b') = some (y b') :=
      Record.cache_query (sk, y) b'
    rw [h1, h2]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

/-! ## Location sets and freshness -/

/-- Positions `j, …, j + n - 1` of chain `i`. -/
private def ChainSeg (i : Fin 34) (j n : ℕ) (b : HashLocation) : Prop :=
  ∃ k : Fin 255, b = .inl (i, k) ∧ j ≤ k.val ∧ k.val < j + n

/-- All positions of the chains `φ t`. -/
private def ChainsOf {n : ℕ} (φ : Fin n → Fin 34) (b : HashLocation) : Prop :=
  ∃ (t : Fin n) (k : Fin 255), b = .inl (φ t, k)

/-- Root positions `r, …, 33`. -/
private def RootsFrom (r : ℕ) (b : HashLocation) : Prop :=
  ∃ k : Fin 34, b = .inr k ∧ r ≤ k.val

/-- The cache holds no chain-`i` query at positions `≥ j`. -/
private def FreshChain (c : Cache) (i : Fin 34) (j : ℕ) : Prop :=
  ∀ k : ℕ, k < 255 → j ≤ k → ∀ x : Word, c ⟨896, chainInput i.val k x⟩ = none

/-- The cache holds no root query at positions `≥ r`. -/
private def FreshRoot (c : Cache) (r : ℕ) : Prop :=
  ∀ k : Fin 34, r ≤ k.val → ∀ (cv : BitVec 256) (x : Word),
    c ⟨896, rootInput (rootTag k) cv x⟩ = none

private theorem chainSeg_succ (i : Fin 34) (j n : ℕ) (hj : j < 255) (b : HashLocation) :
    (ChainSeg i (j + 1) n b ∨ b = .inl (i, ⟨j, hj⟩)) ↔ ChainSeg i j (n + 1) b := by
  constructor
  · rintro (⟨k, rfl, h1, h2⟩ | rfl)
    · exact ⟨k, rfl, by omega, by omega⟩
    · exact ⟨⟨j, hj⟩, rfl, le_rfl, show j < j + (n + 1) by omega⟩
  · rintro ⟨k, rfl, h1, h2⟩
    by_cases hkj : k.val = j
    · exact Or.inr (congrArg (fun k' => (Sum.inl (i, k') : HashLocation)) (Fin.ext hkj))
    · exact Or.inl ⟨k, rfl, by omega, by omega⟩

private theorem chainsOf_succ {n : ℕ} (φ : Fin (n + 1) → Fin 34) (b : HashLocation) :
    (ChainsOf (fun t : Fin n => φ t.succ) b ∨ ChainSeg (φ 0) 0 255 b) ↔ ChainsOf φ b := by
  constructor
  · rintro (⟨t, k, rfl⟩ | ⟨k, rfl, -, -⟩)
    · exact ⟨t.succ, k, rfl⟩
    · exact ⟨0, k, rfl⟩
  · rintro ⟨t, k, rfl⟩
    rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t, rfl⟩
    · exact Or.inr ⟨k, rfl, Nat.zero_le _, by have := k.isLt; omega⟩
    · exact Or.inl ⟨t, k, rfl⟩

private theorem rootsFrom_succ (r : ℕ) (hr : r < 34) (b : HashLocation) :
    (RootsFrom (r + 1) b ∨ b = .inr ⟨r, hr⟩) ↔ RootsFrom r b := by
  constructor
  · rintro (⟨k, rfl, hk⟩ | rfl)
    · exact ⟨k, rfl, by omega⟩
    · exact ⟨⟨r, hr⟩, rfl, le_rfl⟩
  · rintro ⟨k, rfl, hk⟩
    by_cases hkr : k.val = r
    · exact Or.inr (congrArg Sum.inr (Fin.ext hkr))
    · exact Or.inl ⟨k, rfl, by omega⟩

/-! ## One chain -/

/-- Walking chain `i` from position `j` for `n` steps, from a cache fresh on the rest of the
chain, programs positions `j, …, j + n - 1` of the averaged record `(sk, y)`. -/
private theorem E_run_chain_avg (sk : Words) (i : Fin 34) (G : Tbl → Word × Cache → ℝ≥0∞) :
    ∀ (n j : ℕ) (hjn : j + n ≤ 255) (x : Tbl → Word) (c : Tbl → Cache),
      (∀ y, x y = Record.word (sk, y) i ⟨j, by omega⟩) →
      (∀ y, FreshChain (c y) i j) →
      (∀ y (k : Fin 255) u, j ≤ k.val → c (Function.update y (.inl (i, k)) u) = c y) →
      (∀ y (k : Fin 255) u, j ≤ k.val → G (Function.update y (.inl (i, k)) u) = G y) →
      ∑ y : Tbl, Nt * E (run (chain i.val j n (x y)) (c y)) (G y) =
        ∑ y : Tbl, Nt * G y (Record.word (sk, y) i ⟨j + n, by omega⟩,
          progUpd (sk, y) (ChainSeg i j n) (c y)) := by
  intro n
  induction n with
  | zero =>
    intro j hjn x c hx _ _ _
    refine Finset.sum_congr rfl fun y _ => ?_
    have hw : Record.word (sk, y) i ⟨j + 0, by omega⟩ = x y := (hx y).symm
    rw [chain, run_pure, E_pure, hw,
      progUpd_of_false (sk, y) (ChainSeg i j 0) (c y) (fun _ ⟨_, _, h1, h2⟩ => by omega)]
  | succ n ih =>
    intro j hjn x c hx hfr hc hG
    have hj : j < 255 := by omega
    -- the input word of position `j` does not read later positions of the chain
    have hxu : ∀ y (k : Fin 255) u, j ≤ k.val →
        x (Function.update y (.inl (i, k)) u) = x y := by
      intro y k u hk
      have hw : ∀ k' : Fin 255, (Sum.inl (i, k) : HashLocation) = .inl (i, k') →
          k'.val + 1 ≠ (⟨j, by omega⟩ : Fin 256).val := by
        intro k' h
        have h2 : k'.val = k.val := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).2.symm
        show k'.val + 1 ≠ j
        omega
      rw [hx, hx, word_update sk y _ u i _ hw]
    have hK : ∀ y u (p : BitVec hashBits × Cache),
        E (run (chain i.val (j + 1) n (p.1.extractLsb' 0 128)) p.2)
            (G (Function.update y (.inl (i, ⟨j, hj⟩)) u)) =
          E (run (chain i.val (j + 1) n (p.1.extractLsb' 0 128)) p.2) (G y) := by
      intro y u p
      rw [hG y ⟨j, hj⟩ u le_rfl]
    have hstep : ∀ y, E (run (chain i.val j (n + 1) (x y)) (c y)) (G y) =
        E (run (hash (chainInput i.val j (x y))) (c y))
          (fun p => E (run (chain i.val (j + 1) n (p.1.extractLsb' 0 128)) p.2) (G y)) := by
      intro y
      first
        | (simp only [chain, chainStep, run_bind, run_map, E_bind, E_map]; done)
        | (rw [chain, run_bind, chainStep, run_map, E_bind, E_map])
    have hfr' : ∀ y, FreshChain ((c y).cacheQuery ⟨896, chainInput i.val j (x y)⟩
        (y (.inl (i, ⟨j, hj⟩)))) i (j + 1) := by
      intro y k hk hjk v
      have hne : (⟨896, chainInput i.val k v⟩ : Query) ≠ ⟨896, chainInput i.val j (x y)⟩ := by
        intro h
        have h2 := ((chainInput_eq_iff i i ⟨k, hk⟩ ⟨j, hj⟩ v (x y)).1 (query_inj h)).2.1
        have h3 : k = j := Fin.mk.inj_iff.1 h2
        omega
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
      exact hfr y k hk (by omega) v
    have hc' : ∀ y (k : Fin 255) u, j + 1 ≤ k.val →
        (c (Function.update y (.inl (i, k)) u)).cacheQuery
            ⟨896, chainInput i.val j (x (Function.update y (.inl (i, k)) u))⟩
            (Function.update y (.inl (i, k)) u (.inl (i, ⟨j, hj⟩))) =
          (c y).cacheQuery ⟨896, chainInput i.val j (x y)⟩ (y (.inl (i, ⟨j, hj⟩))) := by
      intro y k u hk
      have hne : (Sum.inl (i, ⟨j, hj⟩) : HashLocation) ≠ .inl (i, k) := by
        intro h
        have h2 : j = k.val := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).2
        omega
      rw [hc y k u (by omega), hxu y k u (by omega), Function.update_of_ne hne]
    calc ∑ y : Tbl, Nt * E (run (chain i.val j (n + 1) (x y)) (c y)) (G y)
        = ∑ y : Tbl, Nt * E (run (hash (chainInput i.val j (x y))) (c y))
            (fun p => E (run (chain i.val (j + 1) n (p.1.extractLsb' 0 128)) p.2) (G y)) :=
          Finset.sum_congr rfl fun y _ => by rw [hstep y]
      _ = ∑ y : Tbl, Nt * E (run (chain i.val (j + 1) n
              ((y (.inl (i, ⟨j, hj⟩))).extractLsb' 0 128))
            ((c y).cacheQuery ⟨896, chainInput i.val j (x y)⟩ (y (.inl (i, ⟨j, hj⟩)))))
            (G y) :=
          avg_hash (.inl (i, ⟨j, hj⟩)) (fun y => chainInput i.val j (x y)) c
            (fun y p => E (run (chain i.val (j + 1) n (p.1.extractLsb' 0 128)) p.2) (G y))
            (fun y => hfr y j hj le_rfl (x y))
            (fun y u => congrArg (chainInput i.val j) (hxu y ⟨j, hj⟩ u le_rfl))
            (fun y u => hc y ⟨j, hj⟩ u le_rfl) hK
      _ = ∑ y : Tbl, Nt * G y (Record.word (sk, y) i ⟨j + 1 + n, by omega⟩,
            progUpd (sk, y) (ChainSeg i (j + 1) n)
              ((c y).cacheQuery ⟨896, chainInput i.val j (x y)⟩ (y (.inl (i, ⟨j, hj⟩))))) :=
          ih (j + 1) (by omega) (fun y => (y (.inl (i, ⟨j, hj⟩))).extractLsb' 0 128)
            (fun y => (c y).cacheQuery ⟨896, chainInput i.val j (x y)⟩
              (y (.inl (i, ⟨j, hj⟩))))
            (fun y => (Record.word_next (sk, y) i ⟨j, hj⟩).symm) hfr' hc'
            (fun y k u hk => hG y k u (by omega))
      _ = ∑ y : Tbl, Nt * G y (Record.word (sk, y) i ⟨j + (n + 1), by omega⟩,
            progUpd (sk, y) (ChainSeg i j (n + 1)) (c y)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have hw : Record.word (sk, y) i ⟨j + 1 + n, by omega⟩ =
              Record.word (sk, y) i ⟨j + (n + 1), by omega⟩ :=
            congrArg (Record.word (sk, y) i) (Fin.ext (show j + 1 + n = j + (n + 1) by omega))
          have hq : (⟨896, chainInput i.val j (x y)⟩ : Query) =
              Record.query (sk, y) (.inl (i, ⟨j, hj⟩)) := by
            rw [hx y]
            rfl
          rw [hw, hq, progUpd_cacheQuery, progUpd_congr (chainSeg_succ i j n hj)]

/-! ## All chains -/

/-- Walking the chains `φ 0, φ 1, …` in turn programs all their positions. -/
private theorem E_run_tabulate_chains (sk : Words) :
    ∀ (n : ℕ) (φ : Fin n → Fin 34), Function.Injective φ →
      ∀ (c : Tbl → Cache) (G : Tbl → (Fin n → Word) × Cache → ℝ≥0∞),
      (∀ y t, FreshChain (c y) (φ t) 0) →
      (∀ y t (k : Fin 255) u, c (Function.update y (.inl (φ t, k)) u) = c y) →
      (∀ y t (k : Fin 255) u, G (Function.update y (.inl (φ t, k)) u) = G y) →
      ∑ y : Tbl, Nt * E (run (tabulate fun t : Fin n => chain (φ t).val 0 255 (sk (φ t)))
          (c y)) (G y) =
        ∑ y : Tbl, Nt * G y (fun t => Record.endpoint (sk, y) (φ t),
          progUpd (sk, y) (ChainsOf φ) (c y)) := by
  intro n
  induction n with
  | zero =>
    intro φ _ c G _ _ _
    refine Finset.sum_congr rfl fun y _ => ?_
    have he : (Fin.elim0 : Fin 0 → Word) = fun t => Record.endpoint (sk, y) (φ t) :=
      funext fun t => Fin.elim0 t
    rw [tabulate, run_pure, E_pure, he,
      progUpd_of_false (sk, y) (ChainsOf φ) (c y) (fun _ ⟨t, _⟩ => Fin.elim0 t)]
  | succ n ih =>
    intro φ hφ c G hfr hc hG
    have h0 : ∀ t : Fin n, φ t.succ ≠ φ 0 := fun t h => Fin.succ_ne_zero t (hφ h)
    have hφ' : Function.Injective (fun t : Fin n => φ t.succ) :=
      fun a b h => Fin.succ_inj.mp (hφ h)
    have hA : ∀ y, E (run (tabulate fun t : Fin (n + 1) => chain (φ t).val 0 255 (sk (φ t)))
          (c y)) (G y) =
        E (run (chain (φ 0).val 0 255 (sk (φ 0))) (c y)) (fun p =>
          E (run (tabulate fun t : Fin n => chain (φ t.succ).val 0 255 (sk (φ t.succ))) p.2)
            (fun p' => G y ((Fin.cases p.1 p'.1 : Fin (n + 1) → Word), p'.2))) := by
      intro y
      rw [tabulate]
      simp only [run_bind, E_bind, run_pure, E_pure]
    have hG₁ : ∀ y (k : Fin 255) u, 0 ≤ k.val →
        (fun p : Word × Cache => E (run (tabulate fun t : Fin n =>
            chain (φ t.succ).val 0 255 (sk (φ t.succ))) p.2)
          (fun p' => G (Function.update y (.inl (φ 0, k)) u)
            ((Fin.cases p.1 p'.1 : Fin (n + 1) → Word), p'.2))) =
        (fun p : Word × Cache => E (run (tabulate fun t : Fin n =>
            chain (φ t.succ).val 0 255 (sk (φ t.succ))) p.2)
          (fun p' => G y ((Fin.cases p.1 p'.1 : Fin (n + 1) → Word), p'.2))) := by
      intro y k u _
      rw [hG y 0 k u]
    have hfr' : ∀ y (t : Fin n),
        FreshChain (progUpd (sk, y) (ChainSeg (φ 0) 0 255) (c y)) (φ t.succ) 0 := by
      intro y t k hk _ v
      have hn : ¬ ∃ b, ChainSeg (φ 0) 0 255 b ∧
          Record.query (sk, y) b = ⟨896, chainInput (φ t.succ).val k v⟩ := by
        rintro ⟨b, ⟨k', rfl, -, -⟩, hq⟩
        rw [query_inl_eq] at hq
        have := (chainInput_eq_iff (φ 0) (φ t.succ) k' ⟨k, hk⟩ _ v).1 (query_inj hq)
        exact h0 t this.1.symm
      rw [progUpd_apply_neg hn]
      exact hfr y t.succ k hk (Nat.zero_le _) v
    have hc' : ∀ y (t : Fin n) (k : Fin 255) u,
        progUpd (sk, Function.update y (.inl (φ t.succ, k)) u) (ChainSeg (φ 0) 0 255)
            (c (Function.update y (.inl (φ t.succ, k)) u)) =
          progUpd (sk, y) (ChainSeg (φ 0) 0 255) (c y) := by
      intro y t k u
      rw [hc y t.succ k u]
      apply progUpd_update
      rintro b ⟨k', rfl, -, -⟩
      refine ⟨fun h => h0 t (congrArg Prod.fst (Sum.inl.inj h)).symm, ?_⟩
      exact query_update_inl sk y _ u (φ 0) k'
        (fun _ hb => (h0 t (congrArg Prod.fst (Sum.inl.inj hb))).elim)
    have hG' : ∀ y (t : Fin n) (k : Fin 255) u,
        (fun p' : (Fin n → Word) × Cache =>
          G (Function.update y (.inl (φ t.succ, k)) u)
            ((Fin.cases (Record.word (sk, Function.update y (.inl (φ t.succ, k)) u) (φ 0)
              ⟨0 + 255, by omega⟩) p'.1 : Fin (n + 1) → Word), p'.2)) =
        (fun p' : (Fin n → Word) × Cache =>
          G y ((Fin.cases (Record.word (sk, y) (φ 0) ⟨0 + 255, by omega⟩) p'.1 :
            Fin (n + 1) → Word), p'.2)) := by
      intro y t k u
      have hw := word_update sk y (.inl (φ t.succ, k)) u (φ 0) ⟨0 + 255, by omega⟩
        (fun _ hb => (h0 t (congrArg Prod.fst (Sum.inl.inj hb))).elim)
      exact congrArg₂ (fun (G₀ : (Fin (n + 1) → Word) × Cache → ℝ≥0∞) (z : Word)
          (p' : (Fin n → Word) × Cache) => G₀ ((Fin.cases z p'.1 : Fin (n + 1) → Word), p'.2))
        (hG y t.succ k u) hw
    calc ∑ y : Tbl, Nt * E (run (tabulate fun t : Fin (n + 1) =>
            chain (φ t).val 0 255 (sk (φ t))) (c y)) (G y)
        = ∑ y : Tbl, Nt * E (run (chain (φ 0).val 0 255 (sk (φ 0))) (c y)) (fun p =>
            E (run (tabulate fun t : Fin n => chain (φ t.succ).val 0 255 (sk (φ t.succ))) p.2)
              (fun p' => G y ((Fin.cases p.1 p'.1 : Fin (n + 1) → Word), p'.2))) :=
          Finset.sum_congr rfl fun y _ => by rw [hA y]
      _ = ∑ y : Tbl, Nt * E (run (tabulate fun t : Fin n =>
              chain (φ t.succ).val 0 255 (sk (φ t.succ)))
            (progUpd (sk, y) (ChainSeg (φ 0) 0 255) (c y)))
            (fun p' => G y ((Fin.cases (Record.word (sk, y) (φ 0) ⟨0 + 255, by omega⟩) p'.1 :
              Fin (n + 1) → Word), p'.2)) :=
          by
            have hx0 : ∀ y : Tbl, sk (φ 0) = Record.word (sk, y) (φ 0) ⟨0, by omega⟩ :=
              fun y => (word_zero sk y (φ 0)).symm
            have hfr0 : ∀ y : Tbl, FreshChain (c y) (φ 0) 0 := fun y => hfr y 0
            have hc0 : ∀ y (k : Fin 255) u, 0 ≤ k.val →
                c (Function.update y (.inl (φ 0, k)) u) = c y := fun y k u _ => hc y 0 k u
            have hstep := E_run_chain_avg sk (φ 0) (fun y (p : Word × Cache) =>
                E (run (tabulate fun t : Fin n => chain (φ t.succ).val 0 255 (sk (φ t.succ)))
                  p.2) (fun p' => G y ((Fin.cases p.1 p'.1 : Fin (n + 1) → Word), p'.2)))
              255 0 (by omega) (fun _ => sk (φ 0)) c hx0 hfr0 hc0 hG₁
            first
              | simpa only using hstep
              | exact hstep
      _ = ∑ y : Tbl, Nt * G y ((Fin.cases (Record.word (sk, y) (φ 0) ⟨0 + 255, by omega⟩)
              (fun t => Record.endpoint (sk, y) (φ t.succ)) : Fin (n + 1) → Word),
            progUpd (sk, y) (ChainsOf fun t => φ t.succ)
              (progUpd (sk, y) (ChainSeg (φ 0) 0 255) (c y))) :=
          by
            have hih := ih (fun t => φ t.succ) hφ'
              (fun y => progUpd (sk, y) (ChainSeg (φ 0) 0 255) (c y))
              (fun y p' => G y ((Fin.cases (Record.word (sk, y) (φ 0) ⟨0 + 255, by omega⟩)
                p'.1 : Fin (n + 1) → Word), p'.2)) hfr' hc' hG'
            first
              | simpa only using hih
              | exact hih
      _ = ∑ y : Tbl, Nt * G y (fun t => Record.endpoint (sk, y) (φ t),
            progUpd (sk, y) (ChainsOf φ) (c y)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have hf : (⟨0 + 255, by omega⟩ : Fin 256) = 255 := by
            first
              | rfl
              | decide
              | (apply Fin.ext; simp)
          have hw255 : Record.word (sk, y) (φ 0) ⟨0 + 255, by omega⟩ =
              Record.endpoint (sk, y) (φ 0) := by
            rw [hf]
            rfl
          have hcases : (Fin.cases (Record.word (sk, y) (φ 0) ⟨0 + 255, by omega⟩)
              (fun t => Record.endpoint (sk, y) (φ t.succ)) : Fin (n + 1) → Word) =
              fun t => Record.endpoint (sk, y) (φ t) := by
            funext t
            rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t, rfl⟩
            · first
                | exact hw255
                | exact Eq.trans Fin.cases_zero hw255
            · rfl
          rw [hcases, progUpd_progUpd, progUpd_congr (chainsOf_succ φ)]

/-! ## The root -/

/-- The endpoints of chains `r, …, r + m - 1`, in the order the root absorbs them. -/
private def endList (sk : Words) (y : Tbl) (r m : ℕ) (h : r + m ≤ 34) : List Word :=
  List.ofFn fun t : Fin m => Record.endpoint (sk, y) ⟨r + t.val, by have := t.isLt; omega⟩

private theorem endList_succ (sk : Words) (y : Tbl) (r m : ℕ) (h : r + (m + 1) ≤ 34)
    (h' : r + 1 + m ≤ 34) :
    endList sk y r (m + 1) h =
      Record.endpoint (sk, y) ⟨r, by omega⟩ :: endList sk y (r + 1) m h' := by
  unfold endList
  rw [List.ofFn_succ]
  refine congrArg₂ List.cons ?_ ?_
  · exact congrArg (Record.endpoint (sk, y)) (Fin.ext (Nat.add_zero r))
  · refine congrArg List.ofFn (funext fun t => ?_)
    exact congrArg (Record.endpoint (sk, y))
      (Fin.ext (show r + (t.val + 1) = r + 1 + t.val by omega))

private theorem endList_length (sk : Words) (y : Tbl) (r m : ℕ) (h : r + m ≤ 34) :
    (endList sk y r m h).length = m := by
  unfold endList
  exact List.length_ofFn

private theorem endList_update (sk : Words) (y : Tbl) (k : Fin 34) (u : BitVec hashBits)
    (r m : ℕ) (h : r + m ≤ 34) :
    endList sk (Function.update y (.inr k) u) r m h = endList sk y r m h := by
  unfold endList
  exact congrArg List.ofFn (funext fun t =>
    endpoint_update sk y _ u _ (fun _ hb => absurd hb Sum.inr_ne_inl))

private theorem endList_full (sk : Words) (y : Tbl) (h : 0 + 34 ≤ 34) :
    endList sk y 0 34 h = List.ofFn fun t : Fin 34 => Record.endpoint (sk, y) t := by
  unfold endList
  exact congrArg List.ofFn (funext fun t =>
    congrArg (Record.endpoint (sk, y)) (Fin.ext (Nat.zero_add t.val)))

/-- Absorbing the endpoints of chains `r, …, 33` from the root state after `r` absorptions
programs root positions `r, …, 33` and ends in the final root state. -/
private theorem E_run_rootFold_avg (sk : Words) (G : Tbl → BitVec 256 × Cache → ℝ≥0∞) :
    ∀ (m r : ℕ) (hrm : r + m = 34) (cv : Tbl → BitVec 256) (c : Tbl → Cache),
      (∀ y, cv y = Record.rootState (sk, y) ⟨r, by omega⟩) →
      (∀ y, FreshRoot (c y) r) →
      (∀ y (k : Fin 34) u, r ≤ k.val → c (Function.update y (.inr k) u) = c y) →
      (∀ y (k : Fin 34) u, r ≤ k.val → G (Function.update y (.inr k) u) = G y) →
      ∑ y : Tbl, Nt * E (run (rootFold (endList sk y r m hrm.le) (cv y)) (c y)) (G y) =
        ∑ y : Tbl, Nt * G y (Record.rootState (sk, y) 34,
          progUpd (sk, y) (RootsFrom r) (c y)) := by
  intro m
  induction m with
  | zero =>
    intro r hrm cv c hcv _ _ _
    obtain rfl : r = 34 := by omega
    refine Finset.sum_congr rfl fun y _ => ?_
    have hnil : endList sk y 34 0 hrm.le = [] := by
      unfold endList
      exact List.ofFn_zero
    have h34 : Record.rootState (sk, y) ⟨34, by omega⟩ = Record.rootState (sk, y) 34 := rfl
    rw [hnil, hcv y, h34, rootFold, run_pure, E_pure,
      progUpd_of_false (sk, y) (RootsFrom 34) (c y)
        (fun _ ⟨k, _, hk⟩ => by have := k.isLt; omega)]
  | succ m ih =>
    intro r hrm cv c hcv hfr hc hG
    have hr : r < 34 := by omega
    have hle : r + 1 + m ≤ 34 := by omega
    have hlen : ∀ y : Tbl, (endList sk y (r + 1) m hle).length = (rootTag ⟨r, hr⟩).val := by
      intro y
      rw [endList_length]
      show m = 33 - r
      omega
    have hstep : ∀ y : Tbl,
        E (run (rootFold (endList sk y r (m + 1) hrm.le) (cv y)) (c y)) (G y) =
          E (run (hash (rootInput (rootTag ⟨r, hr⟩) (cv y) (Record.endpoint (sk, y) ⟨r, hr⟩)))
              (c y)) (fun p => E (run (rootFold (endList sk y (r + 1) m hle) p.1) p.2) (G y)) := by
      intro y
      rw [endList_succ sk y r m hrm.le hle, rootFold, run_bind, E_bind, absorb, hlen y]
      rfl
    have hfresh : ∀ y : Tbl, c y ⟨896, rootInput (rootTag ⟨r, hr⟩) (cv y)
        (Record.endpoint (sk, y) ⟨r, hr⟩)⟩ = none :=
      fun y => hfr y ⟨r, hr⟩ le_rfl _ _
    -- the query of root position `r` does not read root positions `≥ r`
    have hXu : ∀ y (k : Fin 34) u, r ≤ k.val →
        rootInput (rootTag ⟨r, hr⟩) (cv (Function.update y (.inr k) u))
            (Record.endpoint (sk, Function.update y (.inr k) u) ⟨r, hr⟩) =
          rootInput (rootTag ⟨r, hr⟩) (cv y) (Record.endpoint (sk, y) ⟨r, hr⟩) := by
      intro y k u hk
      have hrs : ∀ r' : Fin 34, (Sum.inr k : HashLocation) = .inr r' →
          r'.val + 1 ≠ (⟨r, by omega⟩ : Fin 35).val := by
        intro r' h
        have h2 : r'.val = k.val := congrArg Fin.val (Sum.inr.inj h).symm
        show r'.val + 1 ≠ r
        omega
      have hep : ∀ k' : Fin 255, (Sum.inr k : HashLocation) = .inl (⟨r, hr⟩, k') →
          k'.val + 1 ≠ 255 := fun _ h => absurd h Sum.inr_ne_inl
      rw [hcv, hcv, rootState_update sk y _ u _ hrs, endpoint_update sk y _ u _ hep]
    have hK : ∀ y u (p : BitVec hashBits × Cache),
        E (run (rootFold (endList sk (Function.update y (.inr ⟨r, hr⟩) u) (r + 1) m hle) p.1)
            p.2) (G (Function.update y (.inr ⟨r, hr⟩) u)) =
          E (run (rootFold (endList sk y (r + 1) m hle) p.1) p.2) (G y) := by
      intro y u p
      rw [endList_update, hG y ⟨r, hr⟩ u le_rfl]
    have hcv' : ∀ y : Tbl,
        (y (.inr ⟨r, hr⟩) : BitVec 256) = Record.rootState (sk, y) ⟨r + 1, by omega⟩ :=
      fun y => (Record.rootState_after (sk, y) ⟨r, hr⟩).symm
    have hfr' : ∀ y : Tbl, FreshRoot ((c y).cacheQuery ⟨896, rootInput (rootTag ⟨r, hr⟩) (cv y)
        (Record.endpoint (sk, y) ⟨r, hr⟩)⟩ (y (.inr ⟨r, hr⟩))) (r + 1) := by
      intro y k hk cv' v
      have hne : (⟨896, rootInput (rootTag k) cv' v⟩ : Query) ≠
          ⟨896, rootInput (rootTag ⟨r, hr⟩) (cv y) (Record.endpoint (sk, y) ⟨r, hr⟩)⟩ := by
        intro h
        have h1 := ((rootInput_eq_iff _ _ _ _ _ _).1 (query_inj h)).1
        have h2 : k.val = r := congrArg Fin.val (rootTag_injective h1)
        omega
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
      exact hfr y k (by omega) cv' v
    have hc' : ∀ y (k : Fin 34) u, r + 1 ≤ k.val →
        (c (Function.update y (.inr k) u)).cacheQuery
            ⟨896, rootInput (rootTag ⟨r, hr⟩) (cv (Function.update y (.inr k) u))
              (Record.endpoint (sk, Function.update y (.inr k) u) ⟨r, hr⟩)⟩
            (Function.update y (.inr k) u (.inr ⟨r, hr⟩)) =
          (c y).cacheQuery ⟨896, rootInput (rootTag ⟨r, hr⟩) (cv y)
            (Record.endpoint (sk, y) ⟨r, hr⟩)⟩ (y (.inr ⟨r, hr⟩)) := by
      intro y k u hk
      have hne : (Sum.inr ⟨r, hr⟩ : HashLocation) ≠ .inr k := by
        intro h
        have h2 : r = k.val := congrArg Fin.val (Sum.inr.inj h)
        omega
      rw [hc y k u (by omega), hXu y k u (by omega), Function.update_of_ne hne]
    calc ∑ y : Tbl, Nt * E (run (rootFold (endList sk y r (m + 1) hrm.le) (cv y)) (c y)) (G y)
        = ∑ y : Tbl, Nt * E (run (hash (rootInput (rootTag ⟨r, hr⟩) (cv y)
              (Record.endpoint (sk, y) ⟨r, hr⟩))) (c y))
            (fun p => E (run (rootFold (endList sk y (r + 1) m hle) p.1) p.2) (G y)) :=
          Finset.sum_congr rfl fun y _ => by rw [hstep y]
      _ = ∑ y : Tbl, Nt * E (run (rootFold (endList sk y (r + 1) m hle) (y (.inr ⟨r, hr⟩)))
            ((c y).cacheQuery ⟨896, rootInput (rootTag ⟨r, hr⟩) (cv y)
              (Record.endpoint (sk, y) ⟨r, hr⟩)⟩ (y (.inr ⟨r, hr⟩)))) (G y) :=
          avg_hash (.inr ⟨r, hr⟩)
            (fun y => rootInput (rootTag ⟨r, hr⟩) (cv y) (Record.endpoint (sk, y) ⟨r, hr⟩)) c
            (fun y p => E (run (rootFold (endList sk y (r + 1) m hle) p.1) p.2) (G y))
            hfresh (fun y u => hXu y ⟨r, hr⟩ u le_rfl) (fun y u => hc y ⟨r, hr⟩ u le_rfl) hK
      _ = ∑ y : Tbl, Nt * G y (Record.rootState (sk, y) 34,
            progUpd (sk, y) (RootsFrom (r + 1))
              ((c y).cacheQuery ⟨896, rootInput (rootTag ⟨r, hr⟩) (cv y)
                (Record.endpoint (sk, y) ⟨r, hr⟩)⟩ (y (.inr ⟨r, hr⟩)))) :=
          ih (r + 1) (by omega) (fun y => (y (.inr ⟨r, hr⟩) : BitVec 256))
            (fun y => (c y).cacheQuery ⟨896, rootInput (rootTag ⟨r, hr⟩) (cv y)
              (Record.endpoint (sk, y) ⟨r, hr⟩)⟩ (y (.inr ⟨r, hr⟩)))
            hcv' hfr' hc' (fun y k u hk => hG y k u (by omega))
      _ = ∑ y : Tbl, Nt * G y (Record.rootState (sk, y) 34,
            progUpd (sk, y) (RootsFrom r) (c y)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have hq : (⟨896, rootInput (rootTag ⟨r, hr⟩) (cv y)
              (Record.endpoint (sk, y) ⟨r, hr⟩)⟩ : Query) =
              Record.query (sk, y) (.inr ⟨r, hr⟩) := by
            rw [hcv y]
            rfl
          rw [hq, progUpd_cacheQuery, progUpd_congr (rootsFrom_succ r hr)]

/-! ## Sampling the secret words -/

/-- Sampling `n` secret words: a uniform average over all tuples. -/
theorem E_run_tabulate_sample (n : ℕ) :
    ∀ (g : (Fin n → Word) × Cache → ℝ≥0∞) (c : Cache),
      E (run (tabulate fun _ : Fin n => sampleBits 128) c) g =
        ∑ sk : Fin n → Word, (Fintype.card (Fin n → Word) : ℝ≥0∞)⁻¹ * g (sk, c) := by
  induction n with
  | zero =>
    intro g c
    rw [tabulate, run_pure, E_pure]
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
          rw [tabulate, run_bind, E_bind]
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

/-- For fixed secret words, the chains and the root are a uniform table. -/
private theorem E_run_keygen_sk (sk : Words) (g' : (PublicKey × Words) × Cache → ℝ≥0∞) :
    E (run (tabulate (fun i : Fin 34 => chain i.val 0 255 (sk i)) >>= fun e =>
        root e >>= fun pk => pure (pk, sk)) ∅) g' =
      ∑ y : Tbl, Nt * g' ((Record.publicKey (sk, y), sk), Record.cache (sk, y)) := by
  have hfr0 : ∀ y : Tbl, FreshRoot (progUpd (sk, y) (ChainsOf fun t : Fin 34 => t) ∅) 0 := by
    intro y k _ cv v
    have hn : ¬ ∃ b, ChainsOf (fun t : Fin 34 => t) b ∧
        Record.query (sk, y) b = ⟨896, rootInput (rootTag k) cv v⟩ := by
      rintro ⟨b, ⟨t, k', rfl⟩, hq⟩
      rw [query_inl_eq] at hq
      exact chainInput_ne_rootInput _ _ _ _ _ _ (query_inj hq)
    rw [progUpd_apply_neg hn, QueryCache.empty_apply]
  have hc0 : ∀ y (k : Fin 34) u, 0 ≤ k.val →
      progUpd (sk, Function.update y (.inr k) u) (ChainsOf fun t : Fin 34 => t) ∅ =
        progUpd (sk, y) (ChainsOf fun t : Fin 34 => t) ∅ := by
    intro y k u _
    apply progUpd_update
    rintro b ⟨t, k', rfl⟩
    exact ⟨Sum.inl_ne_inr,
      query_update_inl sk y _ u _ k' (fun _ h => absurd h Sum.inr_ne_inl)⟩
  have hall : ∀ b : HashLocation,
      (RootsFrom 0 b ∨ ChainsOf (fun t : Fin 34 => t) b) ↔ True := by
    intro b
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rcases b with ⟨i, k⟩ | k
    · exact Or.inr ⟨i, k, rfl⟩
    · exact Or.inl ⟨k, rfl, Nat.zero_le _⟩
  calc E (run (tabulate (fun i : Fin 34 => chain i.val 0 255 (sk i)) >>= fun e =>
          root e >>= fun pk => pure (pk, sk)) ∅) g'
      = ∑ y : Tbl, Nt * E (run (tabulate (fun i : Fin 34 => chain i.val 0 255 (sk i))) ∅)
          (fun p => E (run (root p.1 >>= fun pk => pure (pk, sk)) p.2) g') := by
        rw [run_bind, E_bind, sum_inv_card_mul']
    _ = ∑ y : Tbl, Nt * E (run (root (fun t => Record.endpoint (sk, y) t) >>= fun pk =>
          pure (pk, sk)) (progUpd (sk, y) (ChainsOf fun t : Fin 34 => t) ∅)) g' :=
        E_run_tabulate_chains sk 34 (fun t => t) (fun _ _ h => h) (fun _ => ∅)
          (fun _ p => E (run (root p.1 >>= fun pk => pure (pk, sk)) p.2) g')
          (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    _ = ∑ y : Tbl, Nt * E (run (rootFold (endList sk y 0 34 (by omega)) 0)
          (progUpd (sk, y) (ChainsOf fun t : Fin 34 => t) ∅))
          (fun p => g' ((p.1.extractLsb' 0 128, sk), p.2)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [root, endList_full]
        simp only [run_bind, E_bind, run_map, E_map, run_pure, E_pure]
    _ = ∑ y : Tbl, Nt * g' (((Record.rootState (sk, y) 34).extractLsb' 0 128, sk),
          progUpd (sk, y) (RootsFrom 0) (progUpd (sk, y) (ChainsOf fun t : Fin 34 => t) ∅)) :=
        E_run_rootFold_avg sk (fun _ p => g' ((p.1.extractLsb' 0 128, sk), p.2)) 34 0
          (by omega) (fun _ => 0) (fun y => progUpd (sk, y) (ChainsOf fun t : Fin 34 => t) ∅)
          (fun y => (rootState_zero sk y).symm) hfr0 hc0 (fun _ _ _ _ => rfl)
    _ = ∑ y : Tbl, Nt * g' ((Record.publicKey (sk, y), sk), Record.cache (sk, y)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have hpk : ((Record.rootState (sk, y) 34).extractLsb' 0 128 : PublicKey) =
            Record.publicKey (sk, y) :=
          congrArg (fun v : BitVec 256 => v.extractLsb' 0 128) (rootState_34 sk y)
        rw [progUpd_progUpd, progUpd_congr hall, progUpd_true_empty, hpk]

/-- **Key generation is a uniform record**, with the explicit uniform weight. -/
theorem E_run_keygen_card (g' : (PublicKey × Words) × Cache → ℝ≥0∞) :
    E (run keygen ∅) g' =
      ∑ ξ : Record, (Fintype.card Record : ℝ≥0∞)⁻¹ * g' ((ξ.publicKey, ξ.1), ξ.cache) := by
  have h0 : (Fintype.card (Fin 34 → Word) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ht : (Fintype.card (Fin 34 → Word) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcard : (Fintype.card Record : ℝ≥0∞)⁻¹ =
      (Fintype.card (Fin 34 → Word) : ℝ≥0∞)⁻¹ * Nt := by
    rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inl h0) (Or.inl ht)]
  calc E (run keygen ∅) g'
      = ∑ sk : Fin 34 → Word, (Fintype.card (Fin 34 → Word) : ℝ≥0∞)⁻¹ *
          E (run (tabulate (fun i : Fin 34 => chain i.val 0 255 (sk i)) >>= fun e =>
            root e >>= fun pk => pure (pk, sk)) ∅) g' := by
        first
          | (simp only [keygen, run_bind, E_bind, E_run_tabulate_sample]; done)
          | (rw [keygen, run_bind, E_bind, E_run_tabulate_sample])
    _ = ∑ sk : Fin 34 → Word, (Fintype.card (Fin 34 → Word) : ℝ≥0∞)⁻¹ *
          ∑ y : Tbl, Nt * g' ((Record.publicKey (sk, y), sk), Record.cache (sk, y)) :=
        Finset.sum_congr rfl fun sk _ => by rw [E_run_keygen_sk]
    _ = ∑ sk : Fin 34 → Word, ∑ y : Tbl, (Fintype.card Record : ℝ≥0∞)⁻¹ *
          g' ((Record.publicKey (sk, y), sk), Record.cache (sk, y)) := by
        refine Finset.sum_congr rfl fun sk _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hcard, mul_assoc]
    _ = ∑ ξ : Record, (Fintype.card Record : ℝ≥0∞)⁻¹ * g' ((ξ.publicKey, ξ.1), ξ.cache) :=
        (Fintype.sum_prod_type (fun ξ : Record =>
          (Fintype.card Record : ℝ≥0∞)⁻¹ * g' ((ξ.publicKey, ξ.1), ξ.cache))).symm

/-- **Key generation is a uniform record**: under the lazy random oracle from the empty cache,
the expectation of any function of the output and the final cache is the `w`-weighted average
over records `ξ` of its value at `((ξ.publicKey, ξ.1), ξ.cache)`. -/
theorem E_run_keygen (g' : (PublicKey × Words) × Cache → ℝ≥0∞) :
    E (run keygen ∅) g' = ∑ ξ : Record, w * g' ((ξ.publicKey, ξ.1), ξ.cache) :=
  E_run_keygen_card g'

end OptimalOTS.LeanIsaBaseline

end
