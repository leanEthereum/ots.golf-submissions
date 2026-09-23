import Submissions.UpperLeanIsa.Stages

/-!
# Transcripts of the verifier under the lazy random oracle

Support-level descriptions of the runs of `chain`, `rootFold`, `root`, `tabulate`, `verify`
and the second attacker stage `stB`: whatever the oracle answers, the final cache contains the
answer of every query that was made, and the computed values are the fixed-table values
(`chainValue`, `rootValueFold`, `rootValue`) of the table read off the final cache.

`ChainPath c i j n x` and `RootPath c xs cv` record that every query of the corresponding
evaluation (with respect to the table of `c`) is present in `c`. Both are monotone in the cache,
and so are the evaluated values (`ChainPath.mono`, `RootPath.mono`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

-- `hashBits`, `pkBits` stay reducible here: the root fold works on `BitVec 256` states while
-- cache answers are `BitVec hashBits`, and the public key is a `BitVec 128`.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

theorem stepValue_of_sub {c c' : Cache} (h : Cache.Sub c c') {i j : ℕ} {x : Word}
    (hx : (c ⟨896, chainInput i j x⟩).isSome) :
    stepValue (table c') i j x = stepValue (table c) i j x :=
  congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_of_sub h hx)

/-- One step at the front of a chain evaluation. -/
theorem chainValue_cons (f : HashTable) (i j n : ℕ) (x : Word) :
    chainValue f i j (n + 1) x = chainValue f i (j + 1) n (stepValue f i j x) := rfl

/-- One step at the end of a chain evaluation. -/
theorem chainValue_snoc (f : HashTable) (i j k : ℕ) (x : Word) :
    chainValue f i j (k + 1) x = stepValue f i (j + k) (chainValue f i j k x) := by
  first
    | exact (chainValue_add f i j k 1 x).symm
    | (rw [← chainValue_add f i j k 1 x]; simp only [chainValue, stepValue])

/-! ## Cached evaluation paths -/

/-- The evaluated chain path from `(j, x)` for `n` steps is cached. -/
def ChainPath (c : Cache) (i j n : ℕ) (x : Word) : Prop :=
  ∀ k, k < n → (c ⟨896, chainInput i (j + k) (chainValue (table c) i j k x)⟩).isSome

theorem ChainPath.mono {c c' : Cache} (h : Cache.Sub c c') {i j n : ℕ} {x : Word}
    (hp : ChainPath c i j n x) :
    ChainPath c' i j n x ∧ chainValue (table c') i j n x = chainValue (table c) i j n x := by
  have key : ∀ k, k ≤ n → chainValue (table c') i j k x = chainValue (table c) i j k x := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [chainValue_snoc, chainValue_snoc, ih (by omega)]
      exact stepValue_of_sub h (hp k (by omega))
  refine ⟨?_, key n le_rfl⟩
  intro k hk
  rw [key k hk.le]
  exact h.isSome (hp k hk)

/-- The query at an absolute position `k` of a cached chain path. -/
theorem ChainPath.cached {c : Cache} {i j n : ℕ} {x : Word} (hp : ChainPath c i j n x)
    {k : ℕ} (hjk : j ≤ k) (hk : k < j + n) :
    (c ⟨896, chainInput i k (chainValue (table c) i j (k - j) x)⟩).isSome := by
  have h := hp (k - j) (by omega)
  rwa [Nat.add_sub_of_le hjk] at h

/-- The evaluated root fold of `xs` from state `cv` is cached. -/
def RootPath (c : Cache) : List Word → BitVec 256 → Prop
  | [], _ => True
  | x :: xs, cv =>
      (c ⟨896, LeanIsa.hashInput cv (x.setWidth 512) (BitVec.ofNat 128 (2 + xs.length))⟩).isSome ∧
        RootPath c xs (absorbValue (table c) xs.length cv x)

theorem RootPath.mono {c c' : Cache} (h : Cache.Sub c c') :
    ∀ (xs : List Word) (cv : BitVec 256), RootPath c xs cv →
      RootPath c' xs cv ∧ rootValueFold (table c') xs cv = rootValueFold (table c) xs cv := by
  intro xs
  induction xs with
  | nil => intro cv _; exact ⟨trivial, rfl⟩
  | cons x xs ih =>
    intro cv hp
    obtain ⟨hx, hr⟩ := hp
    have ha : absorbValue (table c') xs.length cv x = absorbValue (table c) xs.length cv x :=
      table_of_sub h hx
    obtain ⟨hr', hv⟩ := ih _ hr
    refine ⟨⟨h.isSome hx, ?_⟩, ?_⟩
    · rw [ha]
      exact hr'
    · show rootValueFold (table c') xs (absorbValue (table c') xs.length cv x) =
        rootValueFold (table c) xs (absorbValue (table c) xs.length cv x)
      rw [ha]
      exact hv

/-! ## Support of the building blocks -/

/-- A hash query records its answer in the cache (template: `UpperRiscv.Reconstruct`). -/
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

theorem chainStep_support (i j : ℕ) (x : Word) (c : Cache) :
    ∀ p ∈ support (run (chainStep i j x) c), Cache.Sub c p.2 ∧
      (p.2 ⟨896, chainInput i j x⟩).isSome ∧ p.1 = stepValue (table p.2) i j x := by
  intro p hp
  unfold chainStep at hp
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hsub, hc⟩ := run_hash_support _ c q hq
  refine ⟨hsub, Option.isSome_iff_exists.2 ⟨q.1, hc⟩, ?_⟩
  exact congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_eq_of_some hc).symm

theorem chain_support (i j n : ℕ) (x : Word) (c : Cache) :
    ∀ p ∈ support (run (chain i j n x) c),
      Cache.Sub c p.2 ∧ p.1 = chainValue (table p.2) i j n x ∧ ChainPath p.2 i j n x := by
  induction n generalizing j x c with
  | zero =>
    intro p hp
    rw [show run (chain i j 0 x) c = pure (x, c) from run_pure x c, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl c, rfl, ?_⟩
    intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro p hp
    rw [chain, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q, hq, hp⟩ := hp
    obtain ⟨hsub₁, hcached, hstep⟩ := chainStep_support i j x c q hq
    obtain ⟨hsub₂, hval, hpath⟩ := ih (j + 1) q.1 q.2 p hp
    have hst : stepValue (table p.2) i j x = q.1 :=
      (stepValue_of_sub hsub₂ hcached).trans hstep.symm
    refine ⟨hsub₁.trans hsub₂, ?_, ?_⟩
    · rw [chainValue_cons, hst]
      exact hval
    · intro k hk
      cases k with
      | zero => exact hsub₂.isSome hcached
      | succ k =>
        rw [chainValue_cons, hst, show j + (k + 1) = j + 1 + k by omega]
        exact hpath k (by omega)

theorem rootFold_support (xs : List Word) (cv : BitVec 256) (c : Cache) :
    ∀ p ∈ support (run (rootFold xs cv) c),
      Cache.Sub c p.2 ∧ p.1 = rootValueFold (table p.2) xs cv ∧ RootPath p.2 xs cv := by
  induction xs generalizing cv c with
  | nil =>
    intro p hp
    rw [show run (rootFold [] cv) c = pure (cv, c) from run_pure cv c, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, rfl, trivial⟩
  | cons x xs ih =>
    intro p hp
    rw [rootFold, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q, hq, hp⟩ := hp
    obtain ⟨hsub₁, hc₁⟩ := run_hash_support _ c q hq
    obtain ⟨hsub₂, hval, hpath⟩ := ih q.1 q.2 p hp
    have hcached : (q.2 ⟨896, LeanIsa.hashInput cv (x.setWidth 512)
        (BitVec.ofNat 128 (2 + xs.length))⟩).isSome :=
      Option.isSome_iff_exists.2 ⟨q.1, hc₁⟩
    have ha : absorbValue (table p.2) xs.length cv x = q.1 :=
      table_eq_of_some (hsub₂ _ _ hc₁)
    refine ⟨hsub₁.trans hsub₂, ?_, ?_⟩
    · show p.1 = rootValueFold (table p.2) xs (absorbValue (table p.2) xs.length cv x)
      rw [ha]
      exact hval
    · refine ⟨hsub₂.isSome hcached, ?_⟩
      rw [ha]
      exact hpath

theorem root_support (xs : Words) (c : Cache) :
    ∀ p ∈ support (run (root xs) c),
      Cache.Sub c p.2 ∧ p.1 = rootValue (table p.2) xs ∧ RootPath p.2 (List.ofFn xs) 0 := by
  intro p hp
  unfold root at hp
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hsub, hval, hpath⟩ := rootFold_support (List.ofFn xs) 0 c q hq
  exact ⟨hsub, congrArg (fun z : BitVec 256 => z.extractLsb' 0 128) hval, hpath⟩

theorem tabulate_support {α : Type} {n : ℕ} (f : Fin n → OracleComp Spec α)
    (P : Fin n → α → Cache → Prop)
    (hmono : ∀ i x c c', Cache.Sub c c' → P i x c → P i x c')
    (hf : ∀ i c, ∀ p ∈ support (run (f i) c), Cache.Sub c p.2 ∧ P i p.1 p.2) :
    ∀ c, ∀ p ∈ support (run (tabulate f) c), Cache.Sub c p.2 ∧ ∀ i, P i (p.1 i) p.2 := by
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
    obtain ⟨hsub₁, hP₁⟩ := hf 0 c q hq
    obtain ⟨hsub₂, hP₂⟩ := ih (fun i => f i.succ) (fun i => P i.succ)
      (fun i => hmono i.succ) (fun i => hf i.succ) q.2 r hr
    refine ⟨hsub₁.trans hsub₂, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hmono 0 q.1 q.2 r.2 hsub₂ hP₁
    · exact hP₂ i

/-! ## Verification and the second stage -/

/-- Every accepting run of the verifier is witnessed in the final cache: the signature has the
right length, the reconstructed endpoints (read off the final cache) hash to `pk`, and both the
chain paths and the root fold are cached. -/
theorem verify_support (pk : PublicKey) (m : Message) (bits : List Bool) (c : Cache) :
    ∀ p ∈ support (run (verify pk m bits) c), Cache.Sub c p.2 ∧ (p.1 = true →
      bits.length = 4352 ∧
      rootValue (table p.2) (reconstructedWords (table p.2) m bits) = pk ∧
      (∀ i : Fin 34, ChainPath p.2 i.val (digit m i) (255 - digit m i) (decode bits i)) ∧
      RootPath p.2 (List.ofFn (reconstructedWords (table p.2) m bits)) 0) := by
  intro p hp
  by_cases hlen : bits.length = 4352
  · simp only [verify, hlen, ne_eq, not_true_eq_false, ↓reduceIte] at hp
    rw [run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q, hq, hp⟩ := hp
    rw [run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨r, hr, hp⟩ := hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    obtain ⟨hsub₁, hys⟩ := tabulate_support
      (fun i : Fin 34 => chain i.val (digit m i) (255 - digit m i) (decode bits i))
      (fun i y c' =>
        y = chainValue (table c') i.val (digit m i) (255 - digit m i) (decode bits i) ∧
          ChainPath c' i.val (digit m i) (255 - digit m i) (decode bits i))
      (fun _ _ _ _ hsub hP =>
        ⟨hP.1.trans (ChainPath.mono hsub hP.2).2.symm, (ChainPath.mono hsub hP.2).1⟩)
      (fun i c' => chain_support i.val (digit m i) (255 - digit m i) (decode bits i) c')
      c q hq
    obtain ⟨hsub₂, hr₁, hrpath⟩ := root_support q.1 q.2 r hr
    have hrec : reconstructedWords (table r.2) m bits = q.1 :=
      funext fun i => (ChainPath.mono hsub₂ (hys i).2).2.trans (hys i).1.symm
    refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
    have hok' : r.1 = pk := eq_of_beq hok
    refine ⟨hlen, ?_, fun i => (ChainPath.mono hsub₂ (hys i).2).1, ?_⟩
    · show rootValue (table r.2) (reconstructedWords (table r.2) m bits) = pk
      rw [hrec]
      exact hr₁.symm.trans hok'
    · show RootPath r.2 (List.ofFn (reconstructedWords (table r.2) m bits)) 0
      rw [hrec]
      exact hrpath
  · simp only [verify, hlen, ne_eq, not_false_eq_true, ↓reduceIte] at hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, fun h => by cases h⟩

section StageB

variable (A : OracleAlgorithm.Adversary)

/-- An accepting run of the second stage: a fresh pair accepted by the verifier, witnessed in
the final cache (template: `UpperRiscv.StageB.stB_support`). -/
theorem stB_support (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option OracleAlgorithm.Signature) (c : Cache) :
    ∀ p ∈ support (run (stB A pk m₁ st σ) c), Cache.Sub c p.2 ∧ (p.1 = true →
      ∃ m₂ σ₂, σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂) ∧
        σ₂.length = 4352 ∧
        rootValue (table p.2) (reconstructedWords (table p.2) m₂ σ₂) = pk ∧
        (∀ i : Fin 34, ChainPath p.2 i.val (digit m₂ i) (255 - digit m₂ i) (decode σ₂ i)) ∧
        RootPath p.2 (List.ofFn (reconstructedWords (table p.2) m₂ σ₂)) 0) := by
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
  obtain ⟨hsub₂, hver⟩ := verify_support pk m₂ σ₂ c₁ ⟨ok, c₂⟩ h₂
  dsimp only at hp hsub₂ hver
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  exact ⟨m₂, σ₂, hne, hver hok⟩

end StageB

end OptimalOTS.LeanIsaBaseline

end
