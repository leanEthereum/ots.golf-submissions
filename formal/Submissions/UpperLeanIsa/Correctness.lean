import Submissions.UpperLeanIsa.LayerAvailability
import Submissions.UpperLeanIsa.Records
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Fixed-table semantics and perfect correctness

For a fixed oracle table `f` every program of the layer scheme has an explicit value:
`chainValue`, `chainListValue`, `idxValue`, `rootFromValue`, `rootValue`, and the exact verifier
decision `verifyValue` on arbitrary raw inputs (`fixed_verify`). Signing under a fixed table only
returns encodings of the revealed words at an accepted index (`fixed_signLoop_support`): its
best trial is always an accepted index of its nonce (`FixedBest`).
Correctness under the shared cached random oracle follows from VCVio's cached-oracle support
characterization (`probTrue_zero_of_fixed`), for every public-key-dependent message choice.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

attribute [local irreducible] trials sigBits

/-- A fixed oracle table. -/
abbrev HashTable := QueryImpl hashSpec Id

namespace Params

variable (P : Params)

/-- One chain step under a fixed table. -/
def stepValue (f : HashTable) (k : Fin numChains) (j : ℕ) (x : Word) : Word :=
  P.slice k j (f ⟨896, P.chainInput k j x⟩)

/-- `n` chain steps from position `j` under a fixed table. -/
def chainValue (f : HashTable) (k : Fin numChains) : ℕ → ℕ → Word → Word
  | _, 0, x => x
  | j, n + 1, x => chainValue f k (j + 1) n (P.stepValue f k j x)

/-- The chain values at positions `j, …, j + n` under a fixed table. -/
def chainListValue (f : HashTable) (k : Fin numChains) : ℕ → ℕ → Word → List Word
  | _, 0, x => [x]
  | j, n + 1, x => x :: chainListValue f k (j + 1) n (P.stepValue f k j x)

/-- The index under a fixed table. -/
def idxValue (f : HashTable) (m : Message) (η : Nonce) (pk : PublicKey) : Index :=
  indexSlice (f ⟨896, P.idxInput m η pk⟩)

/-- Root calls `r, …, r + n - 1` under a fixed table. -/
def rootFromValue (f : HashTable) (t : Fin numChains → Word) :
    ℕ → ℕ → BitVec 256 → BitVec 256
  | _, 0, st => st
  | r, n + 1, st => rootFromValue f t (r + 1) n (f ⟨896, P.rootInput t r st⟩)

/-- The public key of the tops `t` under a fixed table. -/
def rootValue (f : HashTable) (t : Fin numChains → Word) : PublicKey :=
  (P.rootFromValue f t 0 9 (rootInit t)).extractLsb' 0 128

/-- The tops reconstructed by the verifier from the words of `bits` at index `I`. -/
def reconWords (f : HashTable) (I : Index) (bits : List Bool) : Fin numChains → Word :=
  fun k => P.chainValue f k (P.len k - 1 - P.digit I k) (P.digit I k) (decodeWord bits k)

/-- The verifier's decision under a fixed table. -/
def verifyValue (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) : Bool :=
  if bits.length ≠ sigBits then false
  else if ¬ P.Accepted (P.idxValue f m (decodeNonce bits) pk) then false
  else P.rootValue f (P.reconWords f (P.idxValue f m (decodeNonce bits) pk) bits) == pk

/-! ## Algebra of chain values -/

theorem chainValue_add (f : HashTable) (k : Fin numChains) (j a b : ℕ) (x : Word) :
    P.chainValue f k (j + a) b (P.chainValue f k j a x) = P.chainValue f k j (a + b) x := by
  induction a generalizing j x with
  | zero => simp only [chainValue, Nat.add_zero, Nat.zero_add]
  | succ a ih =>
    simp only [Nat.succ_add, chainValue]
    simpa only [Nat.add_assoc, Nat.add_comm 1 a] using ih (j + 1) (P.stepValue f k j x)

theorem chainValue_succ (f : HashTable) (k : Fin numChains) (j n : ℕ) (x : Word) :
    P.chainValue f k j (n + 1) x = P.chainValue f k (j + 1) n (P.stepValue f k j x) := rfl

theorem chainValue_snoc (f : HashTable) (k : Fin numChains) (j n : ℕ) (x : Word) :
    P.chainValue f k j (n + 1) x = P.stepValue f k (j + n) (P.chainValue f k j n x) := by
  rw [← P.chainValue_add f k j n 1 x]
  rfl

theorem chainListValue_getD (f : HashTable) (k : Fin numChains) :
    ∀ (j n : ℕ) (x : Word) (i : ℕ), i ≤ n →
      (P.chainListValue f k j n x).getD i 0 = P.chainValue f k j i x := by
  intro j n
  induction n generalizing j with
  | zero =>
    intro x i hi
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    intro x i hi
    cases i with
    | zero => rfl
    | succ i =>
      rw [chainListValue, List.getD_cons_succ, ih (j + 1) _ i (by omega)]
      rfl

theorem chainListValue_length (f : HashTable) (k : Fin numChains) :
    ∀ (j n : ℕ) (x : Word), (P.chainListValue f k j n x).length = n + 1 := by
  intro j n
  induction n generalizing j with
  | zero => intro x; rfl
  | succ n ih => intro x; simp only [chainListValue, List.length_cons, ih]

/-! ## Fixed-table simulation -/

theorem fixed_hash (f : HashTable) {n : ℕ} (x : BitVec n) :
    simulateQ (unifFwdAnswerImpl f) (hash x) = pure (f ⟨n, x⟩) := by
  rw [hash, simulateQ_spec_query]
  rfl

theorem fixed_chain (f : HashTable) (k : Fin numChains) :
    ∀ (j n : ℕ) (x : Word),
      simulateQ (unifFwdAnswerImpl f) (P.chain k j n x) = pure (P.chainValue f k j n x) := by
  intro j n
  induction n generalizing j with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    simp only [chain, chainStep, simulateQ_bind, simulateQ_map, fixed_hash, map_pure, pure_bind,
      ih]
    rfl

theorem fixed_chainList (f : HashTable) (k : Fin numChains) :
    ∀ (j n : ℕ) (x : Word),
      simulateQ (unifFwdAnswerImpl f) (P.chainList k j n x) =
        pure (P.chainListValue f k j n x) := by
  intro j n
  induction n generalizing j with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    simp only [chainList, chainStep, simulateQ_bind, simulateQ_map, fixed_hash, map_pure,
      pure_bind, ih, simulateQ_pure]
    rfl

theorem fixed_index (f : HashTable) (m : Message) (η : Nonce) (pk : PublicKey) :
    simulateQ (unifFwdAnswerImpl f) (P.index m η pk) = pure (P.idxValue f m η pk) := by
  simp only [index, simulateQ_map, fixed_hash, map_pure]
  rfl

theorem fixed_rootFrom (f : HashTable) (t : Fin numChains → Word) :
    ∀ (r n : ℕ) (st : BitVec 256),
      simulateQ (unifFwdAnswerImpl f) (P.rootFrom t r n st) =
        pure (P.rootFromValue f t r n st) := by
  intro r n
  induction n generalizing r with
  | zero => intro st; rfl
  | succ n ih =>
    intro st
    rw [rootFrom, simulateQ_bind, fixed_hash, pure_bind]
    exact ih (r + 1) _

theorem fixed_root (f : HashTable) (t : Fin numChains → Word) :
    simulateQ (unifFwdAnswerImpl f) (P.root t) = pure (P.rootValue f t) := by
  simp only [root, simulateQ_map, fixed_rootFrom, map_pure]
  rfl

theorem fixed_tabulate (f : HashTable) {α : Type} {n : ℕ}
    (oa : Fin n → OracleComp Spec α) (v : Fin n → α)
    (h : ∀ i, simulateQ (unifFwdAnswerImpl f) (oa i) = pure (v i)) :
    simulateQ (unifFwdAnswerImpl f) (tabulate oa) = pure v := by
  induction n with
  | zero =>
    simp only [tabulate, simulateQ_pure]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [tabulate, simulateQ_bind, simulateQ_pure, h, pure_bind]
    rw [ih (fun i => oa i.succ) (fun i => v i.succ) (fun i => h i.succ), pure_bind]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- The exact fixed-table decision on arbitrary raw inputs, including malformed lengths. -/
theorem fixed_verify (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) :
    simulateQ (unifFwdAnswerImpl f) (P.verify pk m bits) =
      pure (P.verifyValue f pk m bits) := by
  by_cases hl : bits.length = sigBits
  · have ev : P.verify pk m bits = (P.index m (decodeNonce bits) pk >>= fun I =>
        if ¬ P.Accepted I then pure false else
          tabulate (fun k => P.chain k (P.len k - 1 - P.digit I k) (P.digit I k)
            (decodeWord bits k)) >>= fun tops => P.root tops >>= fun r => pure (r == pk)) := by
      simp only [verify, hl, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [ev, simulateQ_bind, fixed_index, pure_bind]
    by_cases ha : P.Accepted (P.idxValue f m (decodeNonce bits) pk)
    · rw [if_neg (not_not.mpr ha), simulateQ_bind,
        fixed_tabulate f _ (P.reconWords f (P.idxValue f m (decodeNonce bits) pk) bits)
          (fun k => P.fixed_chain f k _ _ _), pure_bind, simulateQ_bind, fixed_root, pure_bind,
        simulateQ_pure]
      simp only [verifyValue, hl, ne_eq, not_true_eq_false, ↓reduceIte, ha, not_true_eq_false]
    · rw [if_pos ha, simulateQ_pure]
      simp only [verifyValue, hl, ne_eq, not_true_eq_false, ↓reduceIte, ha, not_false_eq_true]
  · rw [verify_of_length_ne P pk m bits hl, simulateQ_pure]
    simp only [verifyValue, hl, ne_eq, not_false_eq_true, ↓reduceIte]

/-- The keygen value of the seeds under a fixed table. -/
def keygenValue (f : HashTable) (seeds : Fin numChains → Word) : PublicKey × SecretKey :=
  let tables := fun k => P.chainListValue f k 0 (P.len k - 1) (seeds k)
  let pk := P.rootValue f (fun k => (tables k).getD (P.len k - 1) 0)
  (pk, ⟨tables, pk⟩)

theorem fixed_keygen (f : HashTable) :
    simulateQ (unifFwdAnswerImpl f) P.keygen =
      (simulateQ (unifFwdAnswerImpl f) (tabulate (fun _ : Fin numChains => sampleBits 128)) >>=
        fun seeds => pure (P.keygenValue f seeds)) := by
  simp only [keygen, simulateQ_bind, simulateQ_pure]
  apply congrArg
  funext seeds
  rw [fixed_tabulate f _ (fun k => P.chainListValue f k 0 (P.len k - 1) (seeds k))
    (fun k => P.fixed_chainList f k _ _ _), pure_bind, fixed_root, pure_bind]
  rfl

/-- The best trial under a fixed table is an accepted index of its nonce. -/
def FixedBest (f : HashTable) (m : Message) (pk : PublicKey) (β : Option (Nonce × Index)) :
    Prop :=
  ∀ b, β = some b → P.Accepted (P.idxValue f m b.1 pk) ∧ b.2 = P.idxValue f m b.1 pk

theorem fixedBest_upd (f : HashTable) (m : Message) (pk : PublicKey)
    {β : Option (Nonce × Index)} (h : P.FixedBest f m pk β) (η : Nonce) :
    P.FixedBest f m pk (P.upd β η (P.idxValue f m η pk)) := by
  intro b hb
  unfold upd at hb
  split_ifs at hb with hbt
  · obtain rfl := (Option.some.inj hb).symm
    refine ⟨?_, rfl⟩
    cases β with
    | none => simpa [better] using hbt
    | some b' =>
      simp only [better, Bool.and_eq_true, decide_eq_true_eq] at hbt
      exact hbt.1
  · exact h b hb

/-- Under a fixed table, signing only returns encodings of the revealed words at an accepted
index of the nonce. -/
theorem fixed_signLoop_support (f : HashTable) (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (β : Option (Nonce × Index)),
      P.FixedBest f m sk.pk β → ∀ σ : Option (List Bool),
      σ ∈ support (simulateQ (unifFwdAnswerImpl f) (P.signLoop sk m k tried β)) →
      ∀ s, σ = some s → ∃ η : Nonce, P.Accepted (P.idxValue f m η sk.pk) ∧
        s = encode (P.revealed sk (P.idxValue f m η sk.pk)) η := by
  have hbase : ∀ β : Option (Nonce × Index), P.FixedBest f m sk.pk β → ∀ s,
      P.sigOf sk β = some s → ∃ η : Nonce, P.Accepted (P.idxValue f m η sk.pk) ∧
        s = encode (P.revealed sk (P.idxValue f m η sk.pk)) η := by
    intro β hβ s hs
    cases β with
    | none => cases hs
    | some b =>
      obtain ⟨h1, h2⟩ := hβ b rfl
      refine ⟨b.1, h1, ?_⟩
      simp only [sigOf, Option.map_some, Option.some.injEq] at hs
      rw [← hs, ← h2]
  intro k
  induction k with
  | zero =>
    intro tried β hβ σ hσ s hs
    simp only [signLoop, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hσ
    rw [hσ] at hs
    exact hbase β hβ s hs
  | succ k ih =>
    intro tried β hβ σ hσ s hs
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signLoop_succ sk m k tried β hc, simulateQ_bind, support_bind] at hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨j, -, hσ⟩ := hσ
      unfold loopBody at hσ
      have hq : (liftM (Spec.query (.inr ⟨896, P.idxInput m (nonceOf tried hc j) sk.pk⟩)) :
          OracleComp Spec (BitVec hashBits)) = hash (P.idxInput m (nonceOf tried hc j) sk.pk) :=
        rfl
      rw [hq, simulateQ_bind, fixed_hash, pure_bind] at hσ
      unfold afterHash at hσ
      exact ih _ _ (P.fixedBest_upd f m sk.pk hβ (nonceOf tried hc j)) σ hσ s hs
    · rw [signLoop, dif_neg hc, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hσ
      rw [hσ] at hs
      exact hbase β hβ s hs

theorem fixed_sign_support (f : HashTable) (sk : SecretKey) (m : Message) (s : List Bool)
    (hs : some s ∈ support (simulateQ (unifFwdAnswerImpl f) (P.sign sk m))) :
    ∃ η : Nonce, P.Accepted (P.idxValue f m η sk.pk) ∧
      s = encode (P.revealed sk (P.idxValue f m η sk.pk)) η := by
  rw [P.sign_eq] at hs
  exact P.fixed_signLoop_support f sk m trials ∅ none (fun b h => by cases h) _ hs s rfl

/-- The honest signature verifies under the table that produced the key. -/
theorem verifyValue_honest (hP : P.Hyp) (f : HashTable) (seeds : Fin numChains → Word)
    (m : Message) (η : Nonce)
    (ha : P.Accepted (P.idxValue f m η (P.keygenValue f seeds).2.pk)) :
    P.verifyValue f (P.keygenValue f seeds).1 m
      (encode (P.revealed (P.keygenValue f seeds).2
        (P.idxValue f m η (P.keygenValue f seeds).2.pk)) η) = true := by
  set pk := (P.keygenValue f seeds).1 with hpk
  have hpk' : (P.keygenValue f seeds).2.pk = pk := rfl
  rw [hpk'] at ha ⊢
  set I := P.idxValue f m η pk with hI
  unfold verifyValue
  rw [encode_length, decodeNonce_encode]
  simp only [ne_eq, not_true_eq_false, if_false, ← hI, ha, not_true_eq_false, if_false]
  have hrec : P.reconWords f I (encode (P.revealed (P.keygenValue f seeds).2 I) η) =
      fun k => ((P.keygenValue f seeds).2.table k).getD (P.len k - 1) 0 := by
    funext k
    unfold reconWords
    rw [decodeWord_encode]
    unfold revealed keygenValue
    dsimp only
    have hd := hP.digit_lt I k
    rw [P.chainListValue_getD f k 0 (P.len k - 1) _ _ (by omega),
      P.chainListValue_getD f k 0 (P.len k - 1) _ _ le_rfl]
    have h := P.chainValue_add f k 0 (P.len k - 1 - P.digit I k) (P.digit I k) (seeds k)
    rw [Nat.zero_add, show P.len k - 1 - P.digit I k + P.digit I k = P.len k - 1 by omega] at h
    exact h
  rw [hrec]
  simp [pk, keygenValue]

/-- A zero-probability lemma that keeps all repeated hash answers consistent. -/
theorem probTrue_zero_of_fixed (oa : OracleComp Spec Bool)
    (h : ∀ f : HashTable, true ∉ support (simulateQ (unifFwdAnswerImpl f) oa)) :
    probTrue oa = 0 := by
  rw [probTrue, probOutput_eq_zero_iff]
  intro hs
  change true ∈ support (Prod.fst <$> (simulateQ oracleImpl oa).run ∅) at hs
  rw [support_map] at hs
  obtain ⟨⟨b, cache⟩, hs, hb⟩ := hs
  change b = true at hb
  subst b
  obtain ⟨f, _, hf⟩ :=
    (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff oa ∅ true).mpr ⟨cache, hs⟩
  exact h f hf

/-- **Perfect correctness** of a layer scheme. -/
theorem correct (hP : P.Hyp) : P.scheme.Correct := by
  intro message
  apply probTrue_zero_of_fixed
  intro f hmem
  dsimp only [Params.scheme] at hmem
  rw [simulateQ_bind, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨⟨pk, sk⟩, hk, hmem⟩ := hmem
  have hk' : (pk, sk) ∈ support (simulateQ (unifFwdAnswerImpl f) P.keygen) := hk
  rw [fixed_keygen, support_bind] at hk'
  rw [Set.mem_iUnion₂] at hk'
  obtain ⟨seeds, -, hkv⟩ := hk'
  rw [support_pure, Set.mem_singleton_iff] at hkv
  dsimp only at hmem
  rw [simulateQ_bind, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨σ, hσ, hmem⟩ := hmem
  rcases σ with _ | s
  · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
  · have hσ' : some s ∈ support (simulateQ (unifFwdAnswerImpl f) (P.sign sk (message pk))) := hσ
    obtain ⟨η, ha, rfl⟩ := P.fixed_sign_support f _ _ s hσ'
    dsimp only at hmem
    rw [simulateQ_bind, fixed_verify, pure_bind, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    have hpk : pk = (P.keygenValue f seeds).1 := (congrArg Prod.fst hkv)
    have hsk : sk = (P.keygenValue f seeds).2 := (congrArg Prod.snd hkv)
    subst hpk hsk
    rw [P.verifyValue_honest hP f seeds _ η ha] at hmem
    cases hmem

end Params

end OptimalOTS.LeanIsaBaseline.Layer
