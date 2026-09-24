import Submissions.UpperLeanIsa.Targets
import Submissions.UpperLeanIsa.Correctness

/-!
# The experiment in stages, and transcripts of the verifier

The strong-unforgeability experiment is `keygen >>= rest A` (`experiment_eq`), where `rest` runs
the first attacker stage, signing (`rest₂`), the second attacker stage and verification (`stB`).

Support-level descriptions of the runs of the chains, the root, the index query and the
verifier under the lazy random oracle: whatever the answers, the final cache contains every
query made, and the computed values are the fixed-table values of the table read off the final
cache (`table`). `ChainPath` and `RootPath` record that every query of the corresponding
evaluation is cached; both are monotone in the cache (`ChainPath.mono`, `RootPath.mono`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

attribute [local irreducible] trials

namespace Params

variable (P : Params) (A : OracleAlgorithm.Adversary)

/-! ## The experiment in stages -/

/-- Second attacker stage, verification, and the final check. -/
def stB (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option OracleAlgorithm.Signature) :
    OracleComp Spec Bool := do
  let (m₂, σ₂) ← A.forge st σ
  let ok ← P.verify pk m₂ σ₂
  return ok && decide (σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Signing followed by the second stage. -/
def rest₂ (pk : PublicKey) (sk : SecretKey) (y : Message × A.State) : OracleComp Spec Bool :=
  P.sign sk y.1 >>= P.stB A pk y.1 y.2

/-- Everything after key generation. -/
def rest (x : PublicKey × SecretKey) : OracleComp Spec Bool := A.choose x.1 >>= P.rest₂ A x.1 x.2

theorem experiment_eq : OracleAlgorithm.experiment P.scheme A = P.keygen >>= P.rest A := by
  unfold OracleAlgorithm.experiment rest rest₂ stB
  rfl

end Params

/-! ## The table of a cache -/

/-- The fixed oracle table read off a cache; unset points answer `0`. -/
def table (c : Cache) : HashTable := fun q => (c q).getD 0

theorem table_eq_of_some {c : Cache} {q : Query} {u : BitVec hashBits} (h : c q = some u) :
    table c q = u := by
  simp only [table, h, Option.getD_some]

theorem table_of_sub {c c' : Cache} (h : Cache.Sub c c') {q : Query} (hq : (c q).isSome) :
    table c' q = table c q := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hq
  rw [table_eq_of_some hu, table_eq_of_some (h q u hu)]

namespace Params

variable (P : Params)

theorem stepValue_of_sub {c c' : Cache} (h : Cache.Sub c c') {k : Fin numChains} {j : ℕ}
    {x : Word} (hx : (c ⟨896, P.chainInput k j x⟩).isSome) :
    P.stepValue (table c') k j x = P.stepValue (table c) k j x :=
  congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_of_sub h hx)

/-! ## Cached evaluation paths -/

/-- The evaluated chain path from `(j, x)` for `n` steps is cached. -/
def ChainPath (c : Cache) (k : Fin numChains) (j n : ℕ) (x : Word) : Prop :=
  ∀ i, i < n → (c ⟨896, P.chainInput k (j + i) (P.chainValue (table c) k j i x)⟩).isSome

theorem ChainPath.mono {c c' : Cache} (h : Cache.Sub c c') {k : Fin numChains} {j n : ℕ}
    {x : Word} (hp : P.ChainPath c k j n x) :
    P.ChainPath c' k j n x ∧
      P.chainValue (table c') k j n x = P.chainValue (table c) k j n x := by
  have key : ∀ i, i ≤ n → P.chainValue (table c') k j i x = P.chainValue (table c) k j i x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [chainValue_snoc, chainValue_snoc, ih (by omega)]
      exact P.stepValue_of_sub h (hp i (by omega))
  refine ⟨?_, key n le_rfl⟩
  intro i hi
  rw [key i hi.le]
  exact h.isSome (hp i hi)

/-- The query at an absolute position `i` of a cached chain path. -/
theorem ChainPath.cached {c : Cache} {k : Fin numChains} {j n : ℕ} {x : Word}
    (hp : P.ChainPath c k j n x) {i : ℕ} (hji : j ≤ i) (hi : i < j + n) :
    (c ⟨896, P.chainInput k i (P.chainValue (table c) k j (i - j) x)⟩).isSome := by
  have h := hp (i - j) (by omega)
  rwa [Nat.add_sub_of_le hji] at h

/-- The evaluated root calls `r, …, r + n - 1` of the tops `t` from state `st` are cached. -/
def RootPath (c : Cache) (t : Fin numChains → Word) (r n : ℕ) (st : BitVec 256) : Prop :=
  ∀ i, i < n → (c ⟨896, P.rootInput t (r + i) (P.rootFromValue (table c) t r i st)⟩).isSome

theorem rootFromValue_succ (f : HashTable) (t : Fin numChains → Word) (r n : ℕ)
    (st : BitVec 256) :
    P.rootFromValue f t r (n + 1) st = P.rootFromValue f t (r + 1) n (f ⟨896, P.rootInput t r st⟩) :=
  rfl

theorem rootFromValue_snoc (f : HashTable) (t : Fin numChains → Word) :
    ∀ (r n : ℕ) (st : BitVec 256),
      P.rootFromValue f t r (n + 1) st =
        f ⟨896, P.rootInput t (r + n) (P.rootFromValue f t r n st)⟩ := by
  intro r n
  induction n generalizing r with
  | zero => intro st; rfl
  | succ n ih =>
    intro st
    rw [rootFromValue_succ, ih (r + 1), rootFromValue_succ,
      show r + 1 + n = r + (n + 1) by omega]

theorem RootPath.mono {c c' : Cache} (h : Cache.Sub c c') {t : Fin numChains → Word}
    {r n : ℕ} {st : BitVec 256} (hp : P.RootPath c t r n st) :
    P.RootPath c' t r n st ∧
      P.rootFromValue (table c') t r n st = P.rootFromValue (table c) t r n st := by
  have key : ∀ i, i ≤ n →
      P.rootFromValue (table c') t r i st = P.rootFromValue (table c) t r i st := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [rootFromValue_snoc, rootFromValue_snoc, ih (by omega)]
      exact table_of_sub h (hp i (by omega))
  refine ⟨?_, key n le_rfl⟩
  intro i hi
  rw [key i hi.le]
  exact h.isSome (hp i hi)

/-! ## Support of the building blocks -/

theorem run_hash_support {k : ℕ} (u : BitVec k) (c : Cache) :
    ∀ p ∈ support (run (hash u) c), Cache.Sub c p.2 ∧ p.2 ⟨k, u⟩ = some p.1 := by
  intro p hp
  have h : hash u = liftM (Spec.query (.inr ⟨k, u⟩)) >>= pure := (bind_pure _).symm
  rw [h, run_query_bind] at hp
  simp only [run_pure] at hp
  rw [support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨v, c'⟩, hv, hp⟩ := hp
  rw [support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rcases hc : c ⟨k, u⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨w, -, hw⟩ := hv
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨Cache.sub_cacheQuery_of_none hc _, QueryCache.cacheQuery_self ..⟩
  · rw [oracleImpl_run_inr_some hc, support_pure] at hv
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨Cache.Sub.refl _, hc⟩

theorem chainStep_support (k : Fin numChains) (j : ℕ) (x : Word) (c : Cache) :
    ∀ p ∈ support (run (P.chainStep k j x) c), Cache.Sub c p.2 ∧
      (p.2 ⟨896, P.chainInput k j x⟩).isSome ∧ p.1 = P.stepValue (table p.2) k j x := by
  intro p hp
  unfold chainStep at hp
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hsub, hc⟩ := run_hash_support _ c q hq
  refine ⟨hsub, Option.isSome_iff_exists.2 ⟨q.1, hc⟩, ?_⟩
  exact congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_eq_of_some hc).symm

theorem chain_support (k : Fin numChains) :
    ∀ (j n : ℕ) (x : Word) (c : Cache), ∀ p ∈ support (run (P.chain k j n x) c),
      Cache.Sub c p.2 ∧ p.1 = P.chainValue (table p.2) k j n x ∧ P.ChainPath p.2 k j n x := by
  intro j n
  induction n generalizing j with
  | zero =>
    intro x c p hp
    rw [show run (P.chain k j 0 x) c = pure (x, c) from run_pure x c, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro x c p hp
    rw [chain, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q, hq, hp⟩ := hp
    obtain ⟨hsub₁, hcached, hstep⟩ := P.chainStep_support k j x c q hq
    obtain ⟨hsub₂, hval, hpath⟩ := ih (j + 1) q.1 q.2 p hp
    have hst : P.stepValue (table p.2) k j x = q.1 :=
      (P.stepValue_of_sub hsub₂ hcached).trans hstep.symm
    refine ⟨hsub₁.trans hsub₂, ?_, ?_⟩
    · rw [chainValue_succ, hst]
      exact hval
    · intro i hi
      cases i with
      | zero => exact hsub₂.isSome hcached
      | succ i =>
        rw [chainValue_succ, hst, show j + (i + 1) = j + 1 + i by omega]
        exact hpath i (by omega)

theorem rootFrom_support (t : Fin numChains → Word) :
    ∀ (r n : ℕ) (st : BitVec 256) (c : Cache), ∀ p ∈ support (run (P.rootFrom t r n st) c),
      Cache.Sub c p.2 ∧ p.1 = P.rootFromValue (table p.2) t r n st ∧
        P.RootPath p.2 t r n st := by
  intro r n
  induction n generalizing r with
  | zero =>
    intro st c p hp
    rw [show run (P.rootFrom t r 0 st) c = pure (st, c) from run_pure st c, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro st c p hp
    rw [rootFrom, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q, hq, hp⟩ := hp
    obtain ⟨hsub₁, hc₁⟩ := run_hash_support _ c q hq
    obtain ⟨hsub₂, hval, hpath⟩ := ih (r + 1) q.1 q.2 p hp
    have hcached : (q.2 ⟨896, P.rootInput t r st⟩).isSome := Option.isSome_iff_exists.2 ⟨q.1, hc₁⟩
    have ha : table p.2 ⟨896, P.rootInput t r st⟩ = q.1 := table_eq_of_some (hsub₂ _ _ hc₁)
    refine ⟨hsub₁.trans hsub₂, ?_, ?_⟩
    · rw [rootFromValue_succ, ha]
      exact hval
    · intro i hi
      cases i with
      | zero => exact hsub₂.isSome hcached
      | succ i =>
        rw [rootFromValue_succ, ha, show r + (i + 1) = r + 1 + i by omega]
        exact hpath i (by omega)

theorem root_support (t : Fin numChains → Word) (c : Cache) :
    ∀ p ∈ support (run (P.root t) c),
      Cache.Sub c p.2 ∧ p.1 = P.rootValue (table p.2) t ∧ P.RootPath p.2 t 0 10 (rootInit t) := by
  intro p hp
  unfold root at hp
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hsub, hval, hpath⟩ := P.rootFrom_support t 0 10 (rootInit t) c q hq
  exact ⟨hsub, congrArg (fun z : BitVec 256 => z.extractLsb' 0 128) hval, hpath⟩

theorem index_support (m : Message) (η : Nonce) (pk : PublicKey) (c : Cache) :
    ∀ p ∈ support (run (P.index m η pk) c), Cache.Sub c p.2 ∧
      (p.2 ⟨896, P.idxInput m η pk⟩).isSome ∧ p.1 = P.idxValue (table p.2) m η pk := by
  intro p hp
  unfold index at hp
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hsub, hc⟩ := run_hash_support _ c q hq
  refine ⟨hsub, Option.isSome_iff_exists.2 ⟨q.1, hc⟩, ?_⟩
  exact congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_eq_of_some hc).symm

theorem tabulate_support {α : Type} {n : ℕ} (f : Fin n → OracleComp Spec α)
    (Q : Fin n → α → Cache → Prop)
    (hmono : ∀ i x c c', Cache.Sub c c' → Q i x c → Q i x c')
    (hf : ∀ i c, ∀ p ∈ support (run (f i) c), Cache.Sub c p.2 ∧ Q i p.1 p.2) :
    ∀ c, ∀ p ∈ support (run (tabulate f) c), Cache.Sub c p.2 ∧ ∀ i, Q i (p.1 i) p.2 := by
  induction n with
  | zero =>
    intro c p hp
    rw [tabulate, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro c p hp
    rw [tabulate, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q, hq, hp⟩ := hp
    rw [run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨r, hr, hp⟩ := hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    obtain ⟨hsub₁, hQ₁⟩ := hf 0 c q hq
    obtain ⟨hsub₂, hQ₂⟩ := ih (fun i => f i.succ) (fun i => Q i.succ)
      (fun i => hmono i.succ) (fun i => hf i.succ) q.2 r hr
    refine ⟨hsub₁.trans hsub₂, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hmono 0 q.1 q.2 r.2 hsub₂ hQ₁
    · exact hQ₂ i

/-! ## Verification -/

/-- What an accepting run of the verifier witnesses in the final cache `c`. -/
structure Accepts (c : Cache) (pk : PublicKey) (m : Message) (bits : List Bool) : Prop where
  length : bits.length = sigBits
  idx_cached : (c ⟨896, P.idxInput m (decodeNonce bits) pk⟩).isSome
  accepted : P.Accepted (P.idxValue (table c) m (decodeNonce bits) pk)
  chains : ∀ k, P.ChainPath c k
    (P.len k - 1 - P.digit (P.idxValue (table c) m (decodeNonce bits) pk) k)
    (P.digit (P.idxValue (table c) m (decodeNonce bits) pk) k) (decodeWord bits k)
  rootPath : P.RootPath c (P.reconWords (table c) (P.idxValue (table c) m (decodeNonce bits) pk)
    bits) 0 10 (rootInit (P.reconWords (table c)
      (P.idxValue (table c) m (decodeNonce bits) pk) bits))
  root : P.rootValue (table c)
    (P.reconWords (table c) (P.idxValue (table c) m (decodeNonce bits) pk) bits) = pk

theorem verify_support (pk : PublicKey) (m : Message) (bits : List Bool) (c : Cache) :
    ∀ p ∈ support (run (P.verify pk m bits) c), Cache.Sub c p.2 ∧
      (p.1 = true → P.Accepts p.2 pk m bits) := by
  intro p hp
  by_cases hlen : bits.length = sigBits
  · have ev : P.verify pk m bits = (P.index m (decodeNonce bits) pk >>= fun I =>
        if ¬ P.Accepted I then pure false else
          tabulate (fun k => P.chain k (P.len k - 1 - P.digit I k) (P.digit I k)
            (decodeWord bits k)) >>= fun tops => P.root tops >>= fun r => pure (r == pk)) := by
      simp only [verify, hlen, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [ev, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q₀, hq₀, hp⟩ := hp
    obtain ⟨hsub₀, hidx₀, hI₀⟩ := P.index_support m (decodeNonce bits) pk c q₀ hq₀
    by_cases hacc : P.Accepted q₀.1
    · rw [if_neg (not_not.mpr hacc), run_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨q, hq, hp⟩ := hp
      rw [run_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨r, hr, hp⟩ := hp
      rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      obtain ⟨hsub₁, hys⟩ := tabulate_support
        (fun k : Fin numChains => P.chain k (P.len k - 1 - P.digit q₀.1 k) (P.digit q₀.1 k)
          (decodeWord bits k))
        (fun k y c' =>
          y = P.chainValue (table c') k (P.len k - 1 - P.digit q₀.1 k) (P.digit q₀.1 k)
            (decodeWord bits k) ∧
            P.ChainPath c' k (P.len k - 1 - P.digit q₀.1 k) (P.digit q₀.1 k) (decodeWord bits k))
        (fun _ _ _ _ hsub hQ =>
          ⟨hQ.1.trans (ChainPath.mono P hsub hQ.2).2.symm, (ChainPath.mono P hsub hQ.2).1⟩)
        (fun k c' => P.chain_support k _ _ _ c') q₀.2 q hq
      obtain ⟨hsub₂, hr₁, hrpath⟩ := P.root_support q.1 q.2 r hr
      have hIr : P.idxValue (table r.2) m (decodeNonce bits) pk = q₀.1 := by
        rw [hI₀]
        exact congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128)
          (table_of_sub (hsub₁.trans hsub₂) hidx₀)
      have hrec : P.reconWords (table r.2) q₀.1 bits = q.1 :=
        funext fun k => (ChainPath.mono P hsub₂ (hys k).2).2.trans (hys k).1.symm
      refine ⟨hsub₀.trans (hsub₁.trans hsub₂), fun hok => ?_⟩
      have hok' : r.1 = pk := eq_of_beq hok
      refine ⟨hlen, (hsub₁.trans hsub₂).isSome hidx₀, by rw [hIr]; exact hacc, fun k => ?_, ?_, ?_⟩
      · rw [hIr]
        exact (ChainPath.mono P hsub₂ (hys k).2).1
      · rw [hIr, hrec]
        exact hrpath
      · rw [hIr, hrec]
        exact hr₁.symm.trans hok'
    · rw [if_pos hacc, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hsub₀, fun h => by cases h⟩
  · rw [verify_of_length_ne P pk m bits hlen, run_pure, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, fun h => by cases h⟩

variable (A : OracleAlgorithm.Adversary)

/-- An accepting run of the second stage: a fresh pair accepted by the verifier, witnessed in
the final cache. -/
theorem stB_support (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option OracleAlgorithm.Signature) (c : Cache) :
    ∀ p ∈ support (run (P.stB A pk m₁ st σ) c), Cache.Sub c p.2 ∧ (p.1 = true →
      ∃ m₂ σ₂, σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂) ∧ P.Accepts p.2 pk m₂ σ₂) := by
  intro p hp
  unfold stB at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m₂, σ₂⟩, c₁⟩, h₁, hp⟩ := hp
  have hsub₁ := sub_of_mem_support_run _ c _ h₁
  dsimp only at hp hsub₁
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok, c₂⟩, h₂, hp⟩ := hp
  obtain ⟨hsub₂, hver⟩ := P.verify_support pk m₂ σ₂ c₁ ⟨ok, c₂⟩ h₂
  dsimp only at hp hsub₂ hver
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  exact ⟨m₂, σ₂, hne, hver hok⟩

end Params

end OptimalOTS.LeanIsaBaseline.Layer
