import Submissions.UpperLeanIsa.LayerScheme
import Submissions.UpperLeanIsa.LayerBits
import Submissions.UpperLeanIsa.TierCodec

/-!
# Signing availability of a layer scheme

Ported from UpperRiscv `Availability.lean` / `SignIdx.lean`.

Key generation leaves at most one index entry: its chain steps carry `chainMd` and its root calls
`r < 9` carry `rootMd r`, all different from `idxMd`; the bound below only uses that the calls
before the last have no index shape (`keepsNoIdxBut_keygen`). The signer makes all its trials at
fresh, distinct nonces and fails exactly when no trial is accepted; every index answer but at most
one is a fresh uniform 256-bit string, and each fresh trial is rejected with probability
`miss = 1 - numValid / 2 ^ 127` (`loop_failure`, `loop_failure_one`). Under a tier schedule
`miss = 1 - A` for the accepted mass `A`, and its condition `avail` gives
`miss ^ (2 ^ 19 - 1) ≤ 2 ^ -128` (`miss_trials_pred_le`) for every message chosen from the public
key (`signingFailure`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Params

variable (P : Params)

/-! ## Key generation makes no index query -/

/-- A cache without index entries. -/
def NoIdx (c : Cache) : Prop := ∀ m η pk, c ⟨896, P.idxInput m η pk⟩ = none

/-- Running `oa` from a cache without index entries reaches only such caches. -/
def KeepsNoIdx {α : Type} (oa : OracleComp Spec α) : Prop :=
  ∀ c, P.NoIdx c → ∀ p ∈ support (run oa c), P.NoIdx p.2

theorem keepsNoIdx_pure {α : Type} (x : α) : P.KeepsNoIdx (pure x) := by
  intro c hc p hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact hc

theorem keepsNoIdx_bind {α β : Type} {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    (ha : P.KeepsNoIdx oa) (hb : ∀ x, P.KeepsNoIdx (ob x)) : P.KeepsNoIdx (oa >>= ob) := by
  intro c hc p hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨q, hq, hp⟩ := hp
  exact hb q.1 q.2 (ha c hc q hq) p hp

theorem keepsNoIdx_map {α β : Type} {oa : OracleComp Spec α} (f : α → β)
    (ha : P.KeepsNoIdx oa) : P.KeepsNoIdx (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact P.keepsNoIdx_bind ha fun x => P.keepsNoIdx_pure _

theorem keepsNoIdx_liftM {α : Type} (pc : ProbComp α) :
    P.KeepsNoIdx (liftM pc : OracleComp Spec α) := by
  intro c hc p hp
  rw [run_liftM, support_map] at hp
  obtain ⟨x, -, rfl⟩ := hp
  exact hc

/-- A hash whose metadata is not `idxMd` keeps the cache free of index entries. -/
theorem keepsNoIdx_hash {cv : BitVec 256} {block : BitVec 512} {md : BitVec 128}
    (hmd : md ≠ P.idxMd) : P.KeepsNoIdx (hash (LeanIsa.hashInput cv block md)) := by
  intro c hc p hp
  have e : hash (LeanIsa.hashInput cv block md) =
      (liftM (Spec.query (.inr ⟨896, LeanIsa.hashInput cv block md⟩)) :
        OracleComp Spec (BitVec hashBits)) >>= pure := by
    rw [bind_pure]; rfl
  rw [e, run_query_bind] at hp
  rcases hq : c ⟨896, LeanIsa.hashInput cv block md⟩ with _ | v
  · rw [oracleImpl_run_inr_none hq, bind_assoc, support_bind] at hp
    simp only [Set.mem_iUnion, pure_bind, run_pure, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨w, -, rfl⟩ := hp
    intro m η pk
    have hne : (⟨896, P.idxInput m η pk⟩ : Query) ≠ ⟨896, LeanIsa.hashInput cv block md⟩ :=
      hashInput_ne_of_md_ne (Ne.symm hmd)
    dsimp only
    rw [QueryCache.cacheQuery_of_ne _ _ hne]
    exact hc m η pk
  · rw [oracleImpl_run_inr_some hq, pure_bind, run_pure, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    exact hc

theorem keepsNoIdx_chainList (hc : P.chainMd ≠ P.idxMd) (k : Fin numChains) :
    ∀ j n x, P.KeepsNoIdx (P.chainList k j n x) := by
  intro j n
  induction n generalizing j with
  | zero => intro x; exact P.keepsNoIdx_pure _
  | succ n ih =>
    intro x
    exact P.keepsNoIdx_bind (P.keepsNoIdx_map _ (P.keepsNoIdx_hash hc))
      fun y => P.keepsNoIdx_bind (ih (j + 1) y) fun _ => P.keepsNoIdx_pure _

theorem keepsNoIdx_rootFrom (hr : ∀ r < 9, P.rootMd r ≠ P.idxMd) (t : Fin numChains → Word) :
    ∀ n r st, r + n ≤ 9 → P.KeepsNoIdx (P.rootFrom t r n st) := by
  intro n
  induction n with
  | zero => intro r st _; exact P.keepsNoIdx_pure _
  | succ n ih =>
    intro r st h
    exact P.keepsNoIdx_bind (P.keepsNoIdx_hash (hr r (by omega)))
      fun st' => ih (r + 1) st' (by omega)

theorem keepsNoIdx_tabulate {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp Spec α), (∀ i, P.KeepsNoIdx (f i)) →
      P.KeepsNoIdx (tabulate f)
  | 0, _, _ => P.keepsNoIdx_pure _
  | n + 1, f, h => by
    exact P.keepsNoIdx_bind (h 0) fun x =>
      P.keepsNoIdx_bind (keepsNoIdx_tabulate (fun i : Fin n => f i.succ) fun i => h i.succ)
        fun _ => P.keepsNoIdx_pure _

/-- A cache with at most one index entry, at the query `q₀`. -/
def NoIdxBut (c : Cache) : Prop :=
  ∃ q₀ : Query, ∀ m η pk, (⟨896, P.idxInput m η pk⟩ : Query) ≠ q₀ →
    c ⟨896, P.idxInput m η pk⟩ = none

/-- Running `oa` from a cache without index entries reaches caches with at most one. -/
def KeepsNoIdxBut {α : Type} (oa : OracleComp Spec α) : Prop :=
  ∀ c, P.NoIdx c → ∀ p ∈ support (run oa c), P.NoIdxBut p.2

theorem keepsNoIdxBut_bind {α β : Type} {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    (ha : P.KeepsNoIdx oa) (hb : ∀ x, P.KeepsNoIdxBut (ob x)) :
    P.KeepsNoIdxBut (oa >>= ob) := by
  intro c hc p hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨q, hq, hp⟩ := hp
  exact hb q.1 q.2 (ha c hc q hq) p hp

theorem keepsNoIdxBut_bind_pure {α β : Type} {oa : OracleComp Spec α} (f : α → β)
    (ha : P.KeepsNoIdxBut oa) : P.KeepsNoIdxBut (oa >>= fun x => pure (f x)) := by
  intro c hc p hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨q, hq, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact ha c hc q hq

theorem keepsNoIdxBut_map {α β : Type} {oa : OracleComp Spec α} (f : α → β)
    (ha : P.KeepsNoIdxBut oa) : P.KeepsNoIdxBut (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact P.keepsNoIdxBut_bind_pure f ha

/-- Any single hash adds at most one index entry. -/
theorem keepsNoIdxBut_hash (x : BitVec 896) : P.KeepsNoIdxBut (hash x) := by
  intro c hc p hp
  refine ⟨⟨896, x⟩, fun m η pk hne => ?_⟩
  have e : hash x = (liftM (Spec.query (.inr ⟨896, x⟩)) :
      OracleComp Spec (BitVec hashBits)) >>= pure := by
    rw [bind_pure]; rfl
  rw [e, run_query_bind] at hp
  rcases hq : c ⟨896, x⟩ with _ | v
  · rw [oracleImpl_run_inr_none hq, bind_assoc, support_bind] at hp
    simp only [Set.mem_iUnion, pure_bind, run_pure, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨w, -, rfl⟩ := hp
    dsimp only
    rw [QueryCache.cacheQuery_of_ne _ _ hne]
    exact hc m η pk
  · rw [oracleImpl_run_inr_some hq, pure_bind, run_pure, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    exact hc m η pk

theorem rootFrom_split' (t : Fin numChains → Word) (st : BitVec 256) :
    P.rootFrom t 0 9 st = P.rootFrom t 0 8 st >>= fun st' =>
      hash (P.rootInput t 8 st') >>= fun y => pure y := by
  have h : ∀ (a r : ℕ) (st : BitVec 256), P.rootFrom t r (a + 1) st =
      P.rootFrom t r a st >>= fun st' => hash (P.rootInput t (r + a) st') >>= fun y => pure y := by
    intro a
    induction a with
    | zero => intro r st; rfl
    | succ a ih =>
      intro r st
      rw [show a + 1 + 1 = (a + 1) + 1 from rfl]
      simp only [rootFrom] at ih ⊢
      simp only [bind_assoc]
      refine bind_congr fun st' => ?_
      rw [ih (r + 1) st', show r + 1 + a = r + (a + 1) by omega]
  exact h 8 0 st

/-- Key generation leaves at most one index entry (at its last root call). -/
theorem keepsNoIdxBut_keygen (hc : P.chainMd ≠ P.idxMd) (hr : ∀ r < 9, P.rootMd r ≠ P.idxMd) :
    P.KeepsNoIdxBut P.keygen := by
  unfold keygen
  refine P.keepsNoIdxBut_bind (P.keepsNoIdx_tabulate _ fun _ => P.keepsNoIdx_liftM _)
    fun seeds => ?_
  refine P.keepsNoIdxBut_bind (P.keepsNoIdx_tabulate _ fun k => P.keepsNoIdx_chainList hc k _ _ _)
    fun tables => ?_
  unfold root
  refine P.keepsNoIdxBut_bind_pure _ ?_
  refine P.keepsNoIdxBut_map _ ?_
  rw [rootFrom_split']
  exact P.keepsNoIdxBut_bind (P.keepsNoIdx_rootFrom hr _ 8 0 _ (by norm_num))
    fun st' => P.keepsNoIdxBut_bind_pure id (P.keepsNoIdxBut_hash _)

theorem noIdx_empty : P.NoIdx ∅ := fun _ _ _ => rfl

/-! ## One trial -/

private theorem append_injective {a b : ℕ} {x x' : BitVec a} {y y' : BitVec b}
    (h : x ++ y = x' ++ y') : x = x' ∧ y = y' := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun z : BitVec (a + b) => z.extractLsb' b a) h
  · simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (a + b) => z.extractLsb' 0 b) h

/-- Index queries at different nonces are different. -/
theorem idxQuery_ne {m : Message} {pk : PublicKey} {η η' : Nonce} (h : η ≠ η') :
    (⟨896, P.idxInput m η pk⟩ : Query) ≠ ⟨896, P.idxInput m η' pk⟩ := by
  intro hq
  have hb := ((hashInput_eq_iff _ _ _ _ _ _).mp (eq_of_heq (Sigma.mk.inj hq).2)).2.1
  have hb' : (pk ++ nonceWord η) ++ m = (pk ++ nonceWord η') ++ m := hb
  exact h (nonceWord_injective (append_injective (append_injective hb').1).2)

/-- The low half of an answer. -/
abbrev lo (w : BitVec hashBits) : Index := indexSlice w

/-- Failure probability of one fresh index query. -/
def miss : ℝ≥0∞ := ((2 ^ 256 - P.numValid * 2 ^ 129 : ℕ) : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹

theorem numValid_le : P.numValid ≤ 2 ^ 127 := by
  unfold numValid
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_bitVec])

theorem append_extract (w : BitVec 256) :
    (w.extractLsb' 128 128 ++ w.extractLsb' 0 128 : BitVec (128 + 128)) = w := by
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := w) (start₁ := 0) (len₁ := 128)
    (start₂ := 128) (len₂ := 128) rfl]
  exact BitVec.extractLsb'_eq_self

/-- The accepted effective indices each have 2^129 full-answer preimages. -/
theorem card_acceptedOut :
    (Finset.univ.filter fun w : BitVec 256 => P.Accepted (indexSlice w)).card =
      P.numValid * 2 ^ 129 := card_indexSlice P.Accepted

attribute [local irreducible] hashBits

private theorem card_filter_not_bitVec {n k : ℕ} (p : BitVec n → Prop) [DecidablePred p]
    (hv : (Finset.univ.filter p).card = k) :
    (Finset.univ.filter fun w => ¬ p w).card = 2 ^ n - k := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BitVec n))) (p := p)
  rw [hv, Finset.card_univ, Fintype.card_bitVec] at h
  omega

attribute [local semireducible] hashBits

/-- One fresh uniform answer fails with probability `miss`. -/
theorem uniform_miss (a : ℝ≥0∞) :
    E ($ᵗ BitVec hashBits) (fun w => if P.Accepted (lo w) then 0 else a) = P.miss * a := by
  have hn : (Finset.univ.filter fun w : BitVec 256 => ¬ P.Accepted (indexSlice w)).card =
      2 ^ 256 - P.numValid * 2 ^ 129 :=
    card_filter_not_bitVec (fun w : BitVec 256 => P.Accepted (indexSlice w))
      P.card_acceptedOut
  change E ($ᵗ BitVec 256) (fun w => if P.Accepted (indexSlice w) then 0 else a) = _
  rw [E_uniform]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, hn,
    Fintype.card_bitVec, miss, mul_assoc]

/-! ## The loop in query normal form -/

/-- The nonce selected by the sample `j`. -/
def nonceOf (tried : Finset Nonce) (hc : 0 < (Finset.univ \ tried).card)
    (j : Fin ((Finset.univ \ tried).card - 1 + 1)) : Nonce :=
  ((Finset.univ \ tried).equivFin.symm (Fin.cast (by omega) j)).1

theorem nonceOf_mem (tried : Finset Nonce) (hc : 0 < (Finset.univ \ tried).card)
    (j : Fin ((Finset.univ \ tried).card - 1 + 1)) :
    nonceOf tried hc j ∈ Finset.univ \ tried :=
  ((Finset.univ \ tried).equivFin.symm (Fin.cast (by omega) j)).2

/-- The continuation after the index answer `w` at nonce `η`. -/
def afterHash (sk : SecretKey) (m : Message) (k : ℕ) (tried : Finset Nonce)
    (β : Option (Nonce × Index)) (η : Nonce) (w : BitVec hashBits) :
    OracleComp Spec (Option (List Bool)) :=
  P.signLoop sk m k (insert η tried) (P.upd β η (lo w))

/-- One trial at nonce `η`: the index query, then the remaining trials. -/
def loopBody (sk : SecretKey) (m : Message) (k : ℕ) (tried : Finset Nonce)
    (β : Option (Nonce × Index)) (η : Nonce) : OracleComp Spec (Option (List Bool)) :=
  (liftM (Spec.query (.inr ⟨896, P.idxInput m η sk.pk⟩)) : OracleComp Spec (BitVec hashBits))
    >>= P.afterHash sk m k tried β η

theorem liftM_uniformFin_eq (n : ℕ) :
    (liftM ($[0..n]) : OracleComp Spec (Fin (n + 1))) = liftM (Spec.query (.inl n)) := by
  change liftComp ($[0..n]) Spec = _
  simp [liftComp, ProbComp.uniformFin]
  rfl

theorem signLoop_succ (sk : SecretKey) (m : Message) (k : ℕ) (tried : Finset Nonce)
    (β : Option (Nonce × Index)) (hc : 0 < (Finset.univ \ tried).card) :
    P.signLoop sk m (k + 1) tried β =
      (liftM (Spec.query (.inl ((Finset.univ \ tried).card - 1))) :
          OracleComp Spec (Fin ((Finset.univ \ tried).card - 1 + 1))) >>= fun j =>
        P.loopBody sk m k tried β (nonceOf tried hc j) := by
  rw [signLoop, dif_pos hc, liftM_uniformFin_eq]
  refine bind_congr fun j => ?_
  simp only [loopBody, afterHash, nonceOf, index, hash, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def]
  rfl

theorem upd_none (η : Nonce) (I : Index) :
    P.upd none η I = if P.Accepted I then some (η, I) else none := by
  unfold upd better
  by_cases h : P.Accepted I <;> simp [h]

theorem upd_isSome (b : Nonce × Index) (η : Nonce) (I : Index) : (P.upd (some b) η I).isSome := by
  unfold upd
  split_ifs <;> rfl

/-- A loop that holds a best trial ends with a signature. -/
theorem signLoop_isSome (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (b : Nonce × Index) (c : Cache),
      ∀ p ∈ support (run (P.signLoop sk m k tried (some b)) c), p.1.isSome := by
  intro k
  induction k with
  | zero =>
    intro tried b c p hp
    rw [signLoop, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl
  | succ k ih =>
    intro tried b c p hp
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signLoop_succ sk m k tried _ hc, run_query_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨j, c₁⟩, -, hp⟩ := hp
      rw [loopBody, run_query_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨w, c₂⟩, -, hp⟩ := hp
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (P.upd_isSome b (nonceOf tried hc j) (lo w))
      unfold afterHash at hp
      rw [hb'] at hp
      exact ih _ _ _ p hp
    · rw [signLoop, dif_neg hc, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      rfl

theorem E_isNone_some (sk : SecretKey) (m : Message) (k : ℕ) (tried : Finset Nonce)
    (b : Nonce × Index) (c : Cache) :
    E (run (P.signLoop sk m k tried (some b)) c) (fun p => if p.1.isNone then 1 else 0) = 0 := by
  refine le_antisymm (expectedValue_le_of_support fun p hp => ?_) bot_le
  have := P.signLoop_isSome sk m k tried b c p hp
  simp [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none.1 this]

/-- The failure indicator after a fresh answer `w`: `0` if its index is accepted. -/
theorem E_afterHash_none (sk : SecretKey) (m : Message) (k : ℕ) (tried : Finset Nonce)
    (η : Nonce) (w : BitVec hashBits) (c : Cache) (a : ℝ≥0∞)
    (hrec : ¬ P.Accepted (lo w) →
      E (run (P.signLoop sk m k (insert η tried) none) c)
        (fun p => if p.1.isNone then 1 else 0) ≤ a) :
    E (run (P.afterHash sk m k tried none η w) c) (fun p => if p.1.isNone then 1 else 0) ≤
      if P.Accepted (lo w) then 0 else a := by
  unfold afterHash
  rw [P.upd_none]
  by_cases hw : P.Accepted (lo w)
  · rw [if_pos hw, if_pos hw, P.E_isNone_some]
  · rw [if_neg hw, if_neg hw]
    exact hrec hw

/-- Failure probability while enough untried nonces remain and their queries are fresh. -/
theorem loop_failure (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (c : Cache),
      tried.card + k ≤ 2 ^ 127 →
      (∀ η ∉ tried, c ⟨896, P.idxInput m η sk.pk⟩ = none) →
      E (run (P.signLoop sk m k tried none) c)
        (fun p => if p.1.isNone then 1 else 0) ≤ P.miss ^ k := by
  intro k
  induction k with
  | zero =>
    intro tried c _ _
    simp [signLoop, sigOf, run_pure]
  | succ k ih =>
    intro tried c hbudget hfresh
    have hc : 0 < (Finset.univ \ tried).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_bitVec]
      omega
    rw [P.signLoop_succ sk m k tried none hc, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, E_bind]
    have hbody : ∀ j,
        E (run (P.loopBody sk m k tried none (nonceOf tried hc j)) c)
          (fun p => if p.1.isNone then 1 else 0) ≤ P.miss ^ (k + 1) := by
      intro j
      set η := nonceOf tried hc j with hηdef
      have hη : η ∉ tried := (Finset.mem_sdiff.mp (nonceOf_mem tried hc j)).2
      rw [loopBody, run_query_bind, oracleImpl_run_inr_none (hfresh η hη)]
      simp only [bind_assoc, pure_bind, E_bind]
      have hkont : ∀ w : BitVec hashBits,
          E (run (P.afterHash sk m k tried none η w)
            (c.cacheQuery ⟨896, P.idxInput m η sk.pk⟩ w))
            (fun p => if p.1.isNone then 1 else 0) ≤
          if P.Accepted (lo w) then 0 else P.miss ^ k := by
        intro w
        refine P.E_afterHash_none sk m k tried η w _ _ fun _ => ih _ _ ?_ ?_
        · rw [Finset.card_insert_of_notMem hη]
          omega
        · intro η' hη'
          have hne : (⟨896, P.idxInput m η' sk.pk⟩ : Query) ≠ ⟨896, P.idxInput m η sk.pk⟩ :=
            P.idxQuery_ne fun he => hη' (he ▸ Finset.mem_insert_self η tried)
          rw [QueryCache.cacheQuery_of_ne _ _ hne]
          exact hfresh η' (fun h => hη' (Finset.mem_insert_of_mem h))
      refine (expectedValue_mono_of_support fun w _ => hkont w).trans
        (le_of_eq ((P.uniform_miss (P.miss ^ k)).trans ?_))
      rw [pow_succ, mul_comm]
    refine (expectedValue_mono_of_support fun j _ => hbody j).trans (le_of_eq ?_)
    exact expectedValue_const (by simp) _

theorem miss_le_one : P.miss ≤ 1 := by
  have h := P.uniform_miss 1
  rw [mul_one] at h
  rw [← h]
  refine E_le_one _ fun w => ?_
  split_ifs <;> simp

/-- Failure probability while enough untried nonces remain and all their queries but one are
fresh: at most `miss ^ (k - 1)`. -/
theorem loop_failure_one (sk : SecretKey) (m : Message) (η₀ : Nonce) :
    ∀ (k : ℕ) (tried : Finset Nonce) (c : Cache),
      tried.card + k ≤ 2 ^ 127 →
      (∀ η ∉ tried, η ≠ η₀ → c ⟨896, P.idxInput m η sk.pk⟩ = none) →
      E (run (P.signLoop sk m k tried none) c)
        (fun p => if p.1.isNone then 1 else 0) ≤ P.miss ^ (k - 1) := by
  intro k
  induction k with
  | zero =>
    intro tried c _ _
    simp [signLoop, sigOf, run_pure]
  | succ k ih =>
    intro tried c hbudget hfresh
    have hc : 0 < (Finset.univ \ tried).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_bitVec]
      omega
    rw [P.signLoop_succ sk m k tried none hc, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, E_bind]
    have hbody : ∀ j,
        E (run (P.loopBody sk m k tried none (nonceOf tried hc j)) c)
          (fun p => if p.1.isNone then 1 else 0) ≤ P.miss ^ (k + 1 - 1) := by
      intro j
      set η := nonceOf tried hc j with hηdef
      have hη : η ∉ tried := (Finset.mem_sdiff.mp (nonceOf_mem tried hc j)).2
      have hbud' : (insert η tried).card + k ≤ 2 ^ 127 := by
        rw [Finset.card_insert_of_notMem hη]
        omega
      have hfresh' : ∀ w : BitVec hashBits, ∀ η' ∉ insert η tried, η' ≠ η₀ →
          (c.cacheQuery ⟨896, P.idxInput m η sk.pk⟩ w) ⟨896, P.idxInput m η' sk.pk⟩ = none := by
        intro w η' hη' hη'0
        have hne : (⟨896, P.idxInput m η' sk.pk⟩ : Query) ≠ ⟨896, P.idxInput m η sk.pk⟩ :=
          P.idxQuery_ne fun he => hη' (he ▸ Finset.mem_insert_self η tried)
        rw [QueryCache.cacheQuery_of_ne _ _ hne]
        exact hfresh η' (fun h => hη' (Finset.mem_insert_of_mem h)) hη'0
      rw [Nat.add_sub_cancel]
      by_cases he : η = η₀
      · -- the one possibly cached nonce: the rest of the loop is fresh
        have hall : ∀ c' : Cache, (∀ η' ∉ insert η tried, η' ≠ η₀ →
            c' ⟨896, P.idxInput m η' sk.pk⟩ = none) →
            ∀ η' ∉ insert η tried, c' ⟨896, P.idxInput m η' sk.pk⟩ = none := by
          intro c' h' η' hη'
          exact h' η' hη' (fun h => hη' (h ▸ he ▸ Finset.mem_insert_self η tried))
        rw [loopBody, run_query_bind]
        rcases hq : c ⟨896, P.idxInput m η sk.pk⟩ with _ | w
        · rw [oracleImpl_run_inr_none hq]
          simp only [bind_assoc, pure_bind, E_bind]
          have hk : ∀ w : BitVec hashBits,
              E (run (P.afterHash sk m k tried none η w)
                (c.cacheQuery ⟨896, P.idxInput m η sk.pk⟩ w))
                (fun p => if p.1.isNone then 1 else 0) ≤
                  if P.Accepted (lo w) then 0 else P.miss ^ k := fun w =>
            P.E_afterHash_none sk m k tried η w _ _ fun _ =>
              P.loop_failure sk m k _ _ hbud' (hall _ (hfresh' w))
          refine (expectedValue_mono_of_support fun w _ => hk w).trans
            ((P.uniform_miss (P.miss ^ k)).le.trans ?_)
          calc P.miss * P.miss ^ k ≤ 1 * P.miss ^ k := mul_le_mul' P.miss_le_one le_rfl
            _ = P.miss ^ k := one_mul _
        · rw [oracleImpl_run_inr_some hq]
          simp only [pure_bind]
          refine (P.E_afterHash_none sk m k tried η w c _ fun _ =>
            P.loop_failure sk m k _ _ hbud' (hall c fun η' hη' hη'0 =>
              hfresh η' (fun h => hη' (Finset.mem_insert_of_mem h)) hη'0)).trans ?_
          split_ifs <;> simp
      · -- a fresh nonce: the one possibly cached nonce remains
        rw [loopBody, run_query_bind, oracleImpl_run_inr_none (hfresh η hη he)]
        simp only [bind_assoc, pure_bind, E_bind]
        have hk : ∀ w : BitVec hashBits,
            E (run (P.afterHash sk m k tried none η w)
              (c.cacheQuery ⟨896, P.idxInput m η sk.pk⟩ w))
              (fun p => if p.1.isNone then 1 else 0) ≤
                if P.Accepted (lo w) then 0 else P.miss ^ (k - 1) := fun w =>
          P.E_afterHash_none sk m k tried η w _ _ fun _ => ih _ _ hbud' (hfresh' w)
        refine (expectedValue_mono_of_support fun w _ => hk w).trans
          ((P.uniform_miss (P.miss ^ (k - 1))).le.trans ?_)
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simpa using P.miss_le_one
        · rw [← pow_succ', Nat.sub_add_cancel hk0]
    refine (expectedValue_mono_of_support fun j _ => hbody j).trans (le_of_eq ?_)
    exact expectedValue_const (by simp) _

/-! ## The numeric bound -/

variable {P} in
/-- The accepted indices number `∑ t, N t * a t`. -/
theorem numValid_eq {S : Tier.Sched} (hS : S.Valid) (hT : P.TierHyp S) :
    P.numValid = ∑ t ∈ Finset.range S.T, S.N t * S.a t := by
  rw [← card_tierI_lt hS hT le_rfl]
  unfold numValid
  exact congrArg Finset.card (Finset.filter_congr fun I _ => (tierI_lt_T hT).symm)

variable {P} in
/-- `2 ^ 19 - 1` trials fail with probability at most `2 ^ -128` (condition `avail`). -/
theorem miss_trials_pred_le {S : Tier.Sched} (hS : S.Valid) (hT : P.TierHyp S) :
    P.miss ^ (trials - 1) ≤ 1 / 2 ^ 128 := by
  have hN := numValid_eq hS hT
  have hX : P.numValid ≤ 2 ^ 127 := P.numValid_le
  have h1 : 2 ^ 256 - P.numValid * 2 ^ 129 = (2 ^ 127 - P.numValid) * 2 ^ 129 := by
    rw [Nat.sub_mul, ← pow_add]
  have hinv : ((2 ^ 129 : ℕ) : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ = ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 129 + 127 from rfl, pow_add,
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
      ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]
  have hmass : ((S.mass S.T : ℚ) : ℝ) = (P.numValid : ℝ) / 2 ^ 127 := by
    unfold Tier.Sched.mass
    rw [hT.K_eq, hN]
    push_cast
    ring
  have hreal : ((2 ^ 127 - P.numValid : ℕ) : ℝ) / 2 ^ 127 = 1 - (S.mass S.T : ℝ) := by
    rw [hmass, Nat.cast_sub hX, Nat.cast_pow, Nat.cast_ofNat, sub_div,
      div_self (show (2 : ℝ) ^ 127 ≠ 0 by positivity)]
  have hmiss : P.miss = ENNReal.ofReal (1 - (S.mass S.T : ℝ)) := by
    rw [miss, h1, Nat.cast_mul, mul_assoc, hinv, ← hreal,
      ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv]
  have hA : (S.mass S.T : ℝ) ≤ 1 := by
    have h' : S.mass S.T ≤ 1 := hS.acc_le.trans (by norm_num)
    exact_mod_cast h'
  have havail : ((1 - S.mass S.T) ^ (2 ^ 19 - 1) : ℚ) ≤ 1 / 2 ^ 128 := hS.avail
  have havail' : (1 - (S.mass S.T : ℝ)) ^ (2 ^ 19 - 1) ≤ 1 / 2 ^ 128 := by
    have h := (Rat.cast_le (K := ℝ)).2 havail
    rw [Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_ofNat] at h
    exact h
  have hlast : ENNReal.ofReal (1 / 2 ^ 128) = 1 / 2 ^ 128 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have e : trials - 1 = 2 ^ 19 - 1 := by unfold trials; rfl
  calc P.miss ^ (trials - 1) = ENNReal.ofReal ((1 - (S.mass S.T : ℝ)) ^ (2 ^ 19 - 1)) := by
        rw [hmiss, ENNReal.ofReal_pow (sub_nonneg.2 hA), e]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 128) := ENNReal.ofReal_le_ofReal havail'
    _ = 1 / 2 ^ 128 := hlast

/-! ## Signing availability -/

theorem probTrue_eq_E_run (oa : OracleComp Spec Bool) :
    probTrue oa = E (run oa ∅) (fun p => if p.1 = true then 1 else 0) := by
  unfold probTrue
  rw [run'_eq, probOutput_map_eq_tsum_ite, E, expectedValue_def]
  refine tsum_congr fun x => ?_
  rcases x with ⟨b, c⟩
  cases b <;> simp

/-- Signing from a cache with at most one index entry fails with probability at most
`miss ^ (trials - 1)`. -/
theorem sign_failure_le (sk : SecretKey) (m : Message) (c : Cache) (hc : P.NoIdxBut c) :
    E (run (P.sign sk m) c) (fun p => if p.1.isNone then 1 else 0) ≤ P.miss ^ (trials - 1) := by
  obtain ⟨q₀, hq₀⟩ := hc
  classical
  let η₀ : Nonce := if h : ∃ η : Nonce, (⟨896, P.idxInput m η sk.pk⟩ : Query) = q₀ then h.choose
    else 0
  have hfresh : ∀ η ∉ (∅ : Finset Nonce), η ≠ η₀ → c ⟨896, P.idxInput m η sk.pk⟩ = none := by
    intro η _ hη
    apply hq₀
    intro he
    have hex : ∃ η : Nonce, (⟨896, P.idxInput m η sk.pk⟩ : Query) = q₀ := ⟨η, he⟩
    have h0 : η₀ = hex.choose := dif_pos hex
    have hspec := hex.choose_spec
    by_contra hne
    have : η = hex.choose := by
      by_contra hne'
      exact P.idxQuery_ne hne' (he.trans hspec.symm)
    exact hη (this.trans h0.symm)
  rw [P.sign_eq sk m]
  exact P.loop_failure_one sk m η₀ trials ∅ c (by norm_num [trials]) hfresh

theorem sign_isNone_le' {S : Tier.Sched} (hS : S.Valid) (hT : P.TierHyp S) (sk : SecretKey)
    (m : Message) (c : Cache) (hc : P.NoIdxBut c) :
    E (run (P.sign sk m >>= fun σ => pure σ.isNone) c) (fun p => if p.1 = true then 1 else 0) ≤
      1 / 2 ^ signingFailureBits := by
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  exact (P.sign_failure_le sk m c hc).trans (miss_trials_pred_le hS hT)

/-- **Signing availability.** For every message chosen from the public key, signing fails with
probability at most `2 ^ -128`, given the metadata separation and the availability condition of a
tier schedule of the scheme. -/
theorem signingFailure (hc : P.chainMd ≠ P.idxMd) (hr : ∀ r < 9, P.rootMd r ≠ P.idxMd)
    {S : Tier.Sched} (hS : S.Valid) (hT : P.TierHyp S) :
    P.scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) := by
  intro message
  rw [probTrue_eq_E_run, run_bind, E_bind]
  refine E_le_of_support _ fun q hq => ?_
  have hno := P.keepsNoIdxBut_keygen hc hr ∅ P.noIdx_empty q hq
  rcases q with ⟨⟨pk, sk⟩, c⟩
  exact P.sign_isNone_le' hS hT sk (message pk) c hno

end Params

end OptimalOTS.LeanIsaBaseline.Layer
