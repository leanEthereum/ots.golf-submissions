import Submissions.UpperLeanIsa.LayerScheme
import Submissions.UpperLeanIsa.LayerBits

/-!
# Signing availability of a layer scheme

Ported from UpperRiscv `Availability.lean` / `SignIdx.lean`.

Key generation leaves at most one index entry: its chain steps carry `chainMd` and its root calls
`r < 7` carry `rootMd r`, all different from `idxMd`; only the last root call, whose metadata is
a state word, can have the index shape (`keepsNoIdxBut_keygen`). The signer then tries fresh,
distinct nonces; every index answer but at most one is a fresh uniform 256-bit string, and each
fresh trial fails with probability exactly `miss = 1 - numValid / 2 ^ 128` (`loop_failure`,
`loop_failure_one`). With `numValid ≥ 188 · 2 ^ 107` the `2 ^ 19` trials fail with probability
at most `miss ^ (2 ^ 19 - 1) ≤ 2 ^ -128` (`miss_trials_pred_le`), for every message chosen from
the public key (`signingFailure`).
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

theorem keepsNoIdx_rootFrom (hr : ∀ r < 7, P.rootMd r ≠ P.idxMd) (t : Fin numChains → Word) :
    ∀ n r st, r + n ≤ 7 → P.KeepsNoIdx (P.rootFrom t r n st) := by
  intro n
  induction n with
  | zero => intro r st _; exact P.keepsNoIdx_pure _
  | succ n ih =>
    intro r st h
    exact P.keepsNoIdx_bind (P.keepsNoIdx_hash (by rw [rootTag_lt (by omega)]; exact hr r (by omega)))
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
    P.rootFrom t 0 8 st = P.rootFrom t 0 7 st >>= fun st' =>
      hash (P.rootInput t 7 st') >>= fun y => pure y := by
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
  exact h 7 0 st

/-- Key generation leaves at most one index entry (its last root call). -/
theorem keepsNoIdxBut_keygen (hc : P.chainMd ≠ P.idxMd) (hr : ∀ r < 7, P.rootMd r ≠ P.idxMd) :
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
  exact P.keepsNoIdxBut_bind (P.keepsNoIdx_rootFrom hr _ 7 0 _ le_rfl)
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
def afterHash (sk : SecretKey) (m : Message) (k : ℕ) (tried : Finset Nonce) (η : Nonce)
    (w : BitVec hashBits) : OracleComp Spec (Option (List Bool)) :=
  if P.Accepted (lo w) then pure (some (encode (P.revealed sk (lo w)) η))
  else P.signLoop sk m k (insert η tried)

/-- One trial at nonce `η`: the index query, then stop or recurse. -/
def loopBody (sk : SecretKey) (m : Message) (k : ℕ) (tried : Finset Nonce) (η : Nonce) :
    OracleComp Spec (Option (List Bool)) :=
  (liftM (Spec.query (.inr ⟨896, P.idxInput m η sk.pk⟩)) : OracleComp Spec (BitVec hashBits))
    >>= P.afterHash sk m k tried η

theorem liftM_uniformFin_eq (n : ℕ) :
    (liftM ($[0..n]) : OracleComp Spec (Fin (n + 1))) = liftM (Spec.query (.inl n)) := by
  change liftComp ($[0..n]) Spec = _
  simp [liftComp, ProbComp.uniformFin]
  rfl

theorem signLoop_succ (sk : SecretKey) (m : Message) (k : ℕ) (tried : Finset Nonce)
    (hc : 0 < (Finset.univ \ tried).card) :
    P.signLoop sk m (k + 1) tried =
      (liftM (Spec.query (.inl ((Finset.univ \ tried).card - 1))) :
          OracleComp Spec (Fin ((Finset.univ \ tried).card - 1 + 1))) >>= fun j =>
        P.loopBody sk m k tried (nonceOf tried hc j) := by
  rw [signLoop, dif_pos hc, liftM_uniformFin_eq]
  refine bind_congr fun j => ?_
  simp only [loopBody, nonceOf, index, hash, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def]
  rfl

/-- Exact failure probability while enough untried nonces remain and their queries are fresh. -/
theorem loop_failure (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (c : Cache),
      tried.card + k ≤ 2 ^ 127 →
      (∀ η ∉ tried, c ⟨896, P.idxInput m η sk.pk⟩ = none) →
      E (run (P.signLoop sk m k tried) c)
        (fun p => if p.1.isNone then 1 else 0) = P.miss ^ k := by
  intro k
  induction k with
  | zero =>
    intro tried c _ _
    simp [signLoop, run_pure]
  | succ k ih =>
    intro tried c hbudget hfresh
    have hc : 0 < (Finset.univ \ tried).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_bitVec]
      omega
    rw [P.signLoop_succ sk m k tried hc, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, E_bind]
    have hbody : ∀ j,
        E (run (P.loopBody sk m k tried (nonceOf tried hc j)) c)
          (fun p => if p.1.isNone then 1 else 0) = P.miss ^ (k + 1) := by
      intro j
      set η := nonceOf tried hc j with hηdef
      have hη : η ∉ tried := (Finset.mem_sdiff.mp (nonceOf_mem tried hc j)).2
      rw [loopBody, run_query_bind, oracleImpl_run_inr_none (hfresh η hη)]
      simp only [bind_assoc, pure_bind, E_bind]
      have hkont : ∀ w : BitVec hashBits,
          E (run (P.afterHash sk m k tried η w)
            (c.cacheQuery ⟨896, P.idxInput m η sk.pk⟩ w))
            (fun p => if p.1.isNone then 1 else 0) =
          if P.Accepted (lo w) then 0 else P.miss ^ k := by
        intro w
        unfold afterHash
        by_cases hw : P.Accepted (lo w)
        · rw [if_pos hw, if_pos hw, run_pure, E_pure]
          rfl
        · rw [if_neg hw, if_neg hw]
          apply ih
          · rw [Finset.card_insert_of_notMem hη]
            omega
          · intro η' hη'
            have hne : (⟨896, P.idxInput m η' sk.pk⟩ : Query) ≠ ⟨896, P.idxInput m η sk.pk⟩ :=
              P.idxQuery_ne fun he => hη' (he ▸ Finset.mem_insert_self η tried)
            rw [QueryCache.cacheQuery_of_ne _ _ hne]
            exact hfresh η' (fun h => hη' (Finset.mem_insert_of_mem h))
      simp only [hkont]
      rw [P.uniform_miss, pow_succ, mul_comm]
    simp_rw [hbody]
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
      E (run (P.signLoop sk m k tried) c)
        (fun p => if p.1.isNone then 1 else 0) ≤ P.miss ^ (k - 1) := by
  intro k
  induction k with
  | zero =>
    intro tried c _ _
    simp [signLoop, run_pure]
  | succ k ih =>
    intro tried c hbudget hfresh
    have hc : 0 < (Finset.univ \ tried).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_bitVec]
      omega
    rw [P.signLoop_succ sk m k tried hc, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, E_bind]
    have hbody : ∀ j,
        E (run (P.loopBody sk m k tried (nonceOf tried hc j)) c)
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
              E (run (P.afterHash sk m k tried η w) (c.cacheQuery ⟨896, P.idxInput m η sk.pk⟩ w))
                (fun p => if p.1.isNone then 1 else 0) = if P.Accepted (lo w) then 0 else P.miss ^ k := by
            intro w
            unfold afterHash
            by_cases hw : P.Accepted (lo w)
            · rw [if_pos hw, if_pos hw, run_pure, E_pure]; rfl
            · rw [if_neg hw, if_neg hw]
              exact P.loop_failure sk m k _ _ hbud' (hall _ (hfresh' w))
          simp only [hk]
          rw [P.uniform_miss]
          calc P.miss * P.miss ^ k ≤ 1 * P.miss ^ k := mul_le_mul' P.miss_le_one le_rfl
            _ = P.miss ^ k := one_mul _
        · rw [oracleImpl_run_inr_some hq]
          simp only [pure_bind]
          unfold afterHash
          by_cases hw : P.Accepted (lo w)
          · rw [if_pos hw, run_pure, E_pure]; simp
          · rw [if_neg hw]
            refine le_of_eq (P.loop_failure sk m k _ _ hbud' (hall c ?_))
            intro η' hη' hη'0
            exact hfresh η' (fun h => hη' (Finset.mem_insert_of_mem h)) hη'0
      · -- a fresh nonce: the one possibly cached nonce remains
        rw [loopBody, run_query_bind, oracleImpl_run_inr_none (hfresh η hη he)]
        simp only [bind_assoc, pure_bind, E_bind]
        have hk : ∀ w : BitVec hashBits,
            E (run (P.afterHash sk m k tried η w) (c.cacheQuery ⟨896, P.idxInput m η sk.pk⟩ w))
              (fun p => if p.1.isNone then 1 else 0) ≤
                if P.Accepted (lo w) then 0 else P.miss ^ (k - 1) := by
          intro w
          unfold afterHash
          by_cases hw : P.Accepted (lo w)
          · rw [if_pos hw, if_pos hw, run_pure, E_pure]; simp
          · rw [if_neg hw, if_neg hw]
            exact ih _ _ hbud' (hfresh' w)
        refine (expectedValue_mono_of_support fun w _ => hk w).trans
          ((P.uniform_miss (P.miss ^ (k - 1))).le.trans ?_)
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simpa using P.miss_le_one
        · rw [← pow_succ', Nat.sub_add_cancel hk0]
    refine (expectedValue_mono_of_support fun j _ => hbody j).trans (le_of_eq ?_)
    exact expectedValue_const (by simp) _

/-! ## The numeric bound -/

/-- At least `188 · 2 ^ 107` accepted indices: one trial fails with probability at most
`1 - 188 / 2 ^ 20`. -/
theorem miss_le (hN : 188 * 2 ^ 107 ≤ P.numValid) : P.miss ≤ 1048388 / 1048576 := by
  have hN' : 188 * 2 ^ 236 ≤ P.numValid * 2 ^ 129 :=
    calc 188 * 2 ^ 236 = (188 * 2 ^ 107) * 2 ^ 129 := by norm_num
      _ ≤ _ := Nat.mul_le_mul_right _ hN
  have ha : 2 ^ 256 - P.numValid * 2 ^ 129 ≤ 1048388 * 2 ^ 236 := by
    have h := Nat.sub_le_sub_left hN' (2 ^ 256)
    have e : 2 ^ 256 - 188 * 2 ^ 236 = 1048388 * 2 ^ 236 := by norm_num
    omega
  calc P.miss = ((2 ^ 256 - P.numValid * 2 ^ 129 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        rw [miss, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((1048388 * 2 ^ 236 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr ha) _
    _ = 1048388 / 1048576 := by
      rw [ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)]
      norm_num

/-- A rational bound on repeated failure; it avoids real exponentials. -/
private theorem bernoulli_reciprocal {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (1 - p) ^ k ≤ 1 / (1 + (k : ℝ) * p) := by
  have hr : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hprod : ∀ n : ℕ, (1 + (n : ℝ) * p) * (1 - p) ^ n ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add_one, pow_succ]
      have hc : (1 + ((n : ℝ) + 1) * p) * (1 - p) ≤ 1 + (n : ℝ) * p := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith [sq_nonneg p]
      have hh := mul_le_mul_of_nonneg_right hc (pow_nonneg hr n)
      nlinarith
  have hd : 0 < 1 + (k : ℝ) * p := by positivity
  rw [le_div_iff₀ hd]
  simpa only [mul_comm] using hprod k

private theorem ofReal_frac (a b : ℕ) (hb : 0 < b) :
    ENNReal.ofReal ((a : ℝ) / b) = (a : ℝ≥0∞) / b := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

/-- `2 ^ 19` trials fail with probability at most `2 ^ -128`: blocks of 512 trials by the
reciprocal bound `(1 - 188 / 2 ^ 20) ^ 512 ≤ 1 / (1 + 512 · 188 / 2 ^ 20) = 512 / 559`, then
`(512 / 559) ^ 32 ≤ 0.061` and `0.061 ^ 32 ≤ 2 ^ -128`. -/
theorem miss_trials_le (hN : 188 * 2 ^ 107 ≤ P.numValid) :
    P.miss ^ trials ≤ 1 / 2 ^ 128 := by
  have hreal : ((1048388 : ℝ) / 1048576) ^ trials ≤ 1 / 2 ^ 128 := by
    have h512 := bernoulli_reciprocal (p := (188 : ℝ) / 1048576) (by norm_num) (by norm_num) 512
    have hbase : (1 : ℝ) - 188 / 1048576 = 1048388 / 1048576 := by norm_num
    have hden : 1 + ((512 : ℕ) : ℝ) * (188 / 1048576) = 1144832 / 1048576 := by norm_num
    rw [hbase, hden, one_div_div] at h512
    have hnn : (0 : ℝ) ≤ ((1048388 : ℝ) / 1048576) ^ 512 := by positivity
    have h32 : ((1048576 : ℝ) / 1144832) ^ 32 ≤ 61 / 1000 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num
    have h61 : ((61 : ℝ) / 1000) ^ 32 ≤ 1 / 2 ^ 128 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num
    calc ((1048388 : ℝ) / 1048576) ^ trials
        = ((((1048388 : ℝ) / 1048576) ^ 512) ^ 32) ^ 32 := by
          rw [← pow_mul, ← pow_mul]; rfl
      _ ≤ (((1048576 : ℝ) / 1144832) ^ 32) ^ 32 := by
          gcongr
      _ ≤ ((61 : ℝ) / 1000) ^ 32 := by gcongr
      _ ≤ 1 / 2 ^ 128 := h61
  refine (pow_le_pow_left' (P.miss_le hN) trials).trans ?_
  have h' := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_pow (by norm_num)] at h'
  have hb : ENNReal.ofReal ((1048388 : ℝ) / 1048576) = (1048388 / 1048576 : ℝ≥0∞) := by
    have := ofReal_frac 1048388 1048576 (by norm_num)
    simpa using this
  have hh : ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) = (1 / 2 ^ 128 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rwa [hb, hh] at h'

/-- The same bound with one trial wasted: `miss ^ (trials - 1) ≤ 2 ^ -128`, since
`(512 / 559) ^ 1023 ≤ 0.061 ^ 32 · 559 / 512`. -/
theorem miss_trials_pred_le (hN : 188 * 2 ^ 107 ≤ P.numValid) :
    P.miss ^ (trials - 1) ≤ 1 / 2 ^ 128 := by
  have hreal : ((1048388 : ℝ) / 1048576) ^ (trials - 1) ≤ 1 / 2 ^ 128 := by
    have h512 := bernoulli_reciprocal (p := (188 : ℝ) / 1048576) (by norm_num) (by norm_num) 512
    have hbase : (1 : ℝ) - 188 / 1048576 = 1048388 / 1048576 := by norm_num
    have hden : 1 + ((512 : ℕ) : ℝ) * (188 / 1048576) = 1144832 / 1048576 := by norm_num
    rw [hbase, hden, one_div_div] at h512
    have h32 : ((1048576 : ℝ) / 1144832) ^ 32 ≤ 61 / 1000 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num
    have h61 : ((61 : ℝ) / 1000) ^ 32 * (1144832 / 1048576) ≤ 1 / 2 ^ 128 := by
      rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num
    have hx0 : (0 : ℝ) ≤ 1048388 / 1048576 := by positivity
    have hx1 : (1048388 : ℝ) / 1048576 ≤ 1 := by norm_num
    have hy0 : (0 : ℝ) ≤ (1048576 : ℝ) / 1144832 := by positivity
    have htr : trials - 1 = 512 * 1023 + 511 := by unfold trials; norm_num
    calc ((1048388 : ℝ) / 1048576) ^ (trials - 1)
        ≤ ((1048388 : ℝ) / 1048576) ^ (512 * 1023) := by
          rw [htr]
          exact pow_le_pow_of_le_one hx0 hx1 (by omega)
      _ = (((1048388 : ℝ) / 1048576) ^ 512) ^ 1023 := by rw [← pow_mul]
      _ ≤ ((1048576 : ℝ) / 1144832) ^ 1023 := by gcongr
      _ = (((1048576 : ℝ) / 1144832) ^ 32) ^ 32 * (1144832 / 1048576) := by
          have hy : (1048576 : ℝ) / 1144832 ≠ 0 := by norm_num
          rw [← pow_mul, show (1144832 : ℝ) / 1048576 = ((1048576 : ℝ) / 1144832)⁻¹ by norm_num,
            show 32 * 32 = 1023 + 1 from rfl, pow_succ ((1048576 : ℝ) / 1144832) 1023, mul_assoc,
            mul_inv_cancel₀ hy, mul_one]
      _ ≤ ((61 : ℝ) / 1000) ^ 32 * (1144832 / 1048576) := by gcongr
      _ ≤ 1 / 2 ^ 128 := h61
  refine (pow_le_pow_left' (P.miss_le hN) (trials - 1)).trans ?_
  have h' := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_pow (by norm_num)] at h'
  have hb : ENNReal.ofReal ((1048388 : ℝ) / 1048576) = (1048388 / 1048576 : ℝ≥0∞) := by
    have := ofReal_frac 1048388 1048576 (by norm_num)
    simpa using this
  have hh : ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) = (1 / 2 ^ 128 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rwa [hb, hh] at h'

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

theorem sign_isNone_le' (hN : 188 * 2 ^ 107 ≤ P.numValid) (sk : SecretKey) (m : Message)
    (c : Cache) (hc : P.NoIdxBut c) :
    E (run (P.sign sk m >>= fun σ => pure σ.isNone) c) (fun p => if p.1 = true then 1 else 0) ≤
      1 / 2 ^ signingFailureBits := by
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  exact (P.sign_failure_le sk m c hc).trans (P.miss_trials_pred_le hN)

/-- Signing from a cache without index entries fails with probability `miss ^ trials`. -/
theorem sign_failure (sk : SecretKey) (m : Message) (c : Cache) (hc : P.NoIdx c) :
    E (run (P.sign sk m) c) (fun p => if p.1.isNone then 1 else 0) = P.miss ^ trials :=
  P.sign_eq sk m ▸ P.loop_failure sk m trials ∅ c (by norm_num [trials]) (fun η _ => hc m η sk.pk)

theorem sign_isNone_le (hN : 188 * 2 ^ 107 ≤ P.numValid) (sk : SecretKey) (m : Message)
    (c : Cache) (hc : P.NoIdx c) :
    E (run (P.sign sk m >>= fun σ => pure σ.isNone) c) (fun p => if p.1 = true then 1 else 0) ≤
      1 / 2 ^ signingFailureBits := by
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  rw [P.sign_failure sk m c hc]
  exact P.miss_trials_le hN

/-- **Signing availability.** For every message chosen from the public key, signing fails with
probability at most `2 ^ -128`, given the metadata separation and `188 · 2 ^ 107` accepted
indices. -/
theorem signingFailure (hc : P.chainMd ≠ P.idxMd) (hr : ∀ r < 7, P.rootMd r ≠ P.idxMd)
    (hN : 188 * 2 ^ 107 ≤ P.numValid) :
    P.scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) := by
  intro message
  rw [probTrue_eq_E_run, run_bind, E_bind]
  refine E_le_of_support _ fun q hq => ?_
  have hno := P.keepsNoIdxBut_keygen hc hr ∅ P.noIdx_empty q hq
  rcases q with ⟨⟨pk, sk⟩, c⟩
  exact P.sign_isNone_le' hN sk (message pk) c hno

end Params

end OptimalOTS.LeanIsaBaseline.Layer
