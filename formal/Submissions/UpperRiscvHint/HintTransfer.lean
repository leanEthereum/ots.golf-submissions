import OptimalOTS.Riscv
import OptimalOTS.RiscvHint

/-! Kernel-checked boundary tests for the hinted RISC-V track and derived facts about its
contract, not OTS certificates.

The machine is `RiscvMachine.lean`'s, so `check-riscv.lean` already pins its instruction prices,
its `HASH` query and its `HALT`. What this file pins is what the hinted track adds: the view
loader, the exact points at which each new clause is vacuous, soundness against an
oracle-adaptive prover, and the reading of a deterministic-track submission as a hinted one.

The last is the theorem that licenses the phrase "the hinted track generalises `upper-riscv`":
`Riscv.Submission.hinted_certificate` turns a `Riscv.Submission.Certificate c` into a
`RiscvHint.Submission.Certificate c` for the identity view, given only that the image rejects
views longer than a signature — the one case the deterministic loader never presents. -/

open OptimalOTS OptimalOTS.Riscv OptimalOTS.RiscvHint RiscvZkvm.Rv64 OracleComp

namespace RiscvHintChecks

/-! ## 1. The view budget

The cap is the number the image and the leanISA tables are capped at, in bits, and it is strictly
above the signature cap, so every admissible signature is itself an admissible view. -/

example : maxViewBits = 1048576 := rfl
example : maxSignatureBits < maxViewBits := by decide
example : maxViewBits = 2 ^ 20 := by decide

/-! ## 2. The loader

On a view no longer than a signature the hinted loader *is* the deterministic loader: same
memory, same registers, same length register. The two differ only where the deterministic
loader would truncate. -/

theorem loadView_eq_initialState (image : Image) (pk : PublicKey) (m : Message) (view : View)
    (h : view.length ≤ maxSignatureBits) :
    loadView image pk m view = initialState image pk m view := by
  have hv : view.length ≤ maxViewBits := by
    unfold maxSignatureBits at h; unfold maxViewBits; omega
  have h1 : view.take maxViewBits = view := List.take_of_length_le hv
  have h2 : view.take maxSignatureBits = view := List.take_of_length_le h
  have h3 : min view.length (maxViewBits + 1) = view.length := by omega
  have h4 : min view.length (maxSignatureBits + 1) = view.length := by omega
  simp only [loadView, initialState, h1, h2, h3, h4]

-- The length register of a truncated view is the sentinel, whatever the excess.
example (image : Image) (pk : PublicKey) (m : Message) (view : View)
    (h : maxViewBits < view.length) :
    (loadView image pk m view).getReg .x13 = BitVec.ofNat 64 (maxViewBits + 1) := by
  have : min view.length (maxViewBits + 1) = maxViewBits + 1 := by omega
  simp [loadView, MachineState.getReg, MachineState.setReg, this]

-- The decision of a completed run is its HALT bit; a fault has none.
example (b : Bool) (k : ℕ) : decision (some (b, k)) = some b := rfl
example : decision none = none := rfl

end RiscvHintChecks

/-! ## 3. Derived facts about the contract

Checked here rather than in the protected files, as `check-riscv.lean` and `check-leanisa.lean`
do. -/

namespace OptimalOTS.RiscvHint

/-- What `probTrue … = 0` means in `Sound` and `Faithful`: the event occurs on no path of the
cached random-oracle simulation. This is the support of the **simulated** computation, where a
repeated query returns the cached answer; it is weaker than `true ∉ support oa`, which also
quantifies over incoherent answer paths. -/
theorem probTrue_eq_zero_iff (oa : OracleComp Spec Bool) :
    probTrue oa = 0 ↔ true ∉ support ((simulateQ oracleImpl oa).run' ∅) :=
  probOutput_eq_zero_iff _ _

/-- `CyclesAtMost` is vacuous on its own: an image no view can drive to an accepting HALT
satisfies every bound. `Faithful` together with `Admissible.correct` is what rules such an image
out. -/
theorem Submission.cyclesAtMost_of_never_accepts (S : Submission) (c : ℕ)
    (h : ∀ (pk : PublicKey) (m : Message) (view : View) (n cycles : ℕ),
      some (true, cycles) ∉ support (S.exec n pk m view)) :
    S.CyclesAtMost c :=
  fun pk m view n cycles hmem => absurd hmem (h pk m view n cycles)

/-- `Sound` is equally vacuous on such an image, and for the same reason: with no accepting run
the conjunct `decision outcome = some true` is never `true`. -/
theorem Submission.sound_of_never_accepts (S : Submission)
    (h : ∀ (pk : PublicKey) (m : Message) (view : View) (n : ℕ),
      S.exec n pk m view = pure none) :
    S.Sound := by
  intro pk m view n
  rw [probTrue_eq_zero_iff]
  simp [h pk m view n, decision]

/-! ### Cache weakening

`Sound` quantifies the view and the fuel plainly. `Submission.sound_adaptive` below shows this
is no weaker than quantifying an oracle-adaptive prover, by the same cache-weakening argument
`check-leanisa.lean` makes for committed memories: a path of the cached simulation from a
populated cache is a path from any subcache, because the lazily-sampled oracle is free to sample
exactly the entries the larger cache already held. -/

/-- `c₂` is a subcache of `c₁`: every entry of `c₂` is an entry of `c₁`. Written out rather
than as `≤`, because `QueryCache` is a reducible `Pi` type and the pointwise order is also in
scope for it.

`Subcache`, `subcache_step`, `subcache_run`, `probTrue_eq_zero_iff` and
`mem_support_of_mem_support_run` are copies of the private block of the same names in
`check-leanisa.lean`; the scripts are not modules and cannot import each other. A fix to one
belongs in both. -/
def Subcache (c₂ c₁ : hashSpec.QueryCache) : Prop :=
  ∀ ⦃t : hashSpec.Domain⦄ ⦃u : hashSpec.Range t⦄, c₂ t = some u → c₁ t = some u

theorem Subcache.refl (c : hashSpec.QueryCache) : Subcache c c := fun _ _ h => h

theorem Subcache.empty (c : hashSpec.QueryCache) : Subcache ∅ c :=
  fun _ _ h => absurd h (by simp)

/-- One simulated query is antitone in the starting cache. -/
theorem subcache_step (t : Spec.Domain) (c₁ c₂ : hashSpec.QueryCache)
    (h : Subcache c₂ c₁) (u : Spec.Range t) (c₁' : hashSpec.QueryCache)
    (hmem : (u, c₁') ∈ support ((oracleImpl t).run c₁)) :
    ∃ c₂', Subcache c₂' c₁' ∧ (u, c₂') ∈ support ((oracleImpl t).run c₂) := by
  match t with
  | .inl n =>
      have h₁ : (oracleImpl (.inl n)).run c₁
          = (fun a => (a, c₁)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) :=
        rfl
      have h₂ : (oracleImpl (.inl n)).run c₂
          = (fun a => (a, c₂)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) :=
        rfl
      rw [h₁, support_map] at hmem
      obtain ⟨x, hx, hxe⟩ := hmem
      simp only [Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      exact ⟨c₂, h, by rw [h₂, support_map]; exact ⟨x, hx, rfl⟩⟩
  | .inr q =>
      have h₁ : (oracleImpl (.inr q)).run c₁ = (hashSpec.randomOracle q).run c₁ := rfl
      have h₂ : (oracleImpl (.inr q)).run c₂ = (hashSpec.randomOracle q).run c₂ := rfl
      rw [h₁, randomOracle.run_eq] at hmem
      rw [h₂, randomOracle.run_eq]
      cases hc₁ : c₁ q with
      | some v =>
          rw [hc₁] at hmem
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨hu, hc⟩ := hmem
          subst hu
          subst hc
          cases hc₂ : c₂ q with
          | some w =>
              have hw : c₁' q = some w := h hc₂
              rw [hc₁] at hw
              have huw : u = w := Option.some.inj hw
              refine ⟨c₂, h, ?_⟩
              show (u, c₂) ∈ support (pure (w, c₂) : ProbComp _)
              simp [huw]
          | none =>
              refine ⟨c₂.cacheQuery q u, ?_, ?_⟩
              · intro t' u' ht'
                rcases eq_or_ne t' q with rfl | hne
                · rw [OracleSpec.QueryCache.cacheQuery_self] at ht'
                  exact hc₁.trans (congrArg some (Option.some.inj ht'))
                · rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hne] at ht'
                  exact h ht'
              · show (u, c₂.cacheQuery q u) ∈
                  support (($ᵗ hashSpec.Range q) >>= fun w => pure (w, c₂.cacheQuery q w))
                rw [mem_support_bind_iff]
                exact ⟨u, mem_support_uniformSample _, by simp⟩
      | none =>
          replace hmem : (u, c₁') ∈
              support (($ᵗ hashSpec.Range q) >>= fun w => pure (w, c₁.cacheQuery q w)) := by
            rw [hc₁] at hmem; exact hmem
          rw [mem_support_bind_iff] at hmem
          obtain ⟨x, hx, hxe⟩ := hmem
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hxe
          obtain ⟨hu, hc⟩ := hxe
          subst hu
          subst hc
          have hc₂ : c₂ q = none := by
            rcases hc : c₂ q with _ | w
            · rfl
            · rw [h hc] at hc₁; exact absurd hc₁ (by simp)
          refine ⟨c₂.cacheQuery q u, ?_, ?_⟩
          · intro t' u' ht'
            rcases eq_or_ne t' q with rfl | hne
            · rw [OracleSpec.QueryCache.cacheQuery_self] at ht'
              rw [OracleSpec.QueryCache.cacheQuery_self]
              exact ht'
            · rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hne] at ht'
              rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hne]
              exact h ht'
          · rw [hc₂]
            show (u, c₂.cacheQuery q u) ∈
              support (($ᵗ hashSpec.Range q) >>= fun w => pure (w, c₂.cacheQuery q w))
            rw [mem_support_bind_iff]
            exact ⟨u, mem_support_uniformSample _, by simp⟩

/-- Cache weakening for a whole computation, by induction on the free monad. -/
theorem subcache_run {α : Type} (oa : OracleComp Spec α) :
    ∀ (c₁ c₂ : hashSpec.QueryCache), Subcache c₂ c₁ →
      ∀ (a : α) (c₁' : hashSpec.QueryCache),
        (a, c₁') ∈ support ((simulateQ oracleImpl oa).run c₁) →
        ∃ c₂', Subcache c₂' c₁' ∧ (a, c₂') ∈ support ((simulateQ oracleImpl oa).run c₂) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro c₁ c₂ h a c₁' hmem
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨c₂, h, by simp⟩
  | query_bind t k ih =>
      intro c₁ c₂ h a c₁' hmem
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨u, cmid⟩, hstep, hrest⟩ := hmem
      obtain ⟨cmid₂, hmid₂, hstep₂⟩ := subcache_step t c₁ c₂ h u cmid hstep
      obtain ⟨c₂', hle, hrest₂⟩ := ih u cmid cmid₂ hmid₂ a c₁' hrest
      refine ⟨c₂', hle, ?_⟩
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
      exact ⟨(u, cmid₂), hstep₂, hrest₂⟩

/-- Soundness against an oracle-adaptive prover: a prover that queries the oracle before
choosing its view and its fuel is no stronger than one that chooses first.

A `true` path of the adaptive experiment runs `P` from the empty cache to some `(view, n)` and
some cache, then runs the machine and the verifier from that cache; cache weakening restricts
that tail to a path from the empty cache, which `Sound` at that very view and fuel forbids. The
proof never uses that `P`'s output is reachable, so the theorem holds for every `P`. -/
theorem Submission.sound_adaptive (S : Submission) (sound : S.Sound)
    (pk : PublicKey) (m : Message) (P : OracleComp Spec (View × ℕ)) :
    probTrue (do
      let (view, n) ← P
      let outcome ← S.exec n pk m view
      let accepted ← S.scheme.verify pk m (S.compress view)
      pure (decide (decision outcome = some true) && !accepted)) = 0 := by
  rw [probTrue_eq_zero_iff]
  intro hmem
  rw [StateT.run'_eq, support_map] at hmem
  obtain ⟨⟨b, c⟩, hbc, hb⟩ := hmem
  simp only at hb
  subst hb
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hbc
  obtain ⟨⟨⟨view, n⟩, cmid⟩, hP, hrest⟩ := hbc
  replace hrest : (true, c) ∈ support ((simulateQ oracleImpl (do
      let outcome ← S.exec n pk m view
      let accepted ← S.scheme.verify pk m (S.compress view)
      pure (decide (decision outcome = some true) && !accepted))).run cmid) := hrest
  obtain ⟨c₂', -, hfinal⟩ := subcache_run _ cmid ∅ (Subcache.empty cmid) true c hrest
  exact (probTrue_eq_zero_iff _).mp (sound pk m view n)
    (by rw [StateT.run'_eq, support_map]; exact ⟨(true, c₂'), hfinal, rfl⟩)

/-- Every result the cached simulation can produce is a result the computation can produce:
the cache restricts which answer sequences are coherent, it never adds a path. This is the
bridge from the `probTrue` clauses to the `support` clause. -/
theorem mem_support_of_mem_support_run {α : Type} (oa : OracleComp Spec α) (a : α)
    (c₀ c : hashSpec.QueryCache) (h : (a, c) ∈ support ((simulateQ oracleImpl oa).run c₀)) :
    a ∈ support oa := by
  refine support_simulateQ_run'_subset oracleImpl oa c₀ ?_
  rw [StateT.run'_eq, support_map]
  exact ⟨(a, c), h, rfl⟩

end OptimalOTS.RiscvHint

/-! ## 4. A deterministic-track submission is a hinted one

`upper-riscv`'s single equation `Implements` says more than the two hinted clauses: it fixes the
query sequence and rules out faults on every input. So a deterministic image should read as a
hinted image with the identity view — `compress = id`, `expand = pure` — at the same claim, and
this section proves it. The one hypothesis is about the inputs the deterministic loader never
presents: views longer than a signature, on which the image must halt rejecting.

Three ingredients are proved on the way, and each is a fact a submitter may want.

* **Fuel agreement** (`execute_fuel_agree`): the machine is deterministic given the oracle's
  answers, so a run that halts under one fuel either halts identically under any other or runs
  the other out. Proved once for both path semantics — the uncached `support` and the cached
  simulation — through the three equations they share.
* **Cache growth** (`subcache_run_grow`): the cached simulation only adds entries.
* **Replay** (`replay_deterministic`): a computation with no private randomness, run again from
  any cache that holds every answer of a completed run, returns the same result with no new
  sampling. This is what makes "the machine and the verifier see the same answers" a theorem
  about `verify` run after the machine. -/

namespace OptimalOTS.Riscv

/-- The two readings of a path through an oracle computation, stated by the three equations the
fuel lemma needs. `σ` is the state a path threads: `Unit` for the uncached `support`, the query
cache for the cached simulation. -/
structure PathSemantics (σ : Type) where
  Path : {α : Type} → OracleComp Spec α → α → σ → σ → Prop
  path_pure : ∀ {α : Type} (x a : α) (s s' : σ), Path (pure x) a s s' ↔ a = x ∧ s' = s
  path_bind : ∀ {α β : Type} (oa : OracleComp Spec α) (f : α → OracleComp Spec β) (b : β)
    (s s'' : σ), Path (oa >>= f) b s s'' ↔ ∃ a s', Path oa a s s' ∧ Path (f a) b s' s''
  path_map : ∀ {α β : Type} (g : α → β) (oa : OracleComp Spec α) (b : β) (s s' : σ),
    Path (g <$> oa) b s s' ↔ ∃ a, Path oa a s s' ∧ g a = b

/-- The uncached reading: a value in the `support`, every query answered independently. -/
def supportPaths : PathSemantics Unit where
  Path oa a _ _ := a ∈ support oa
  path_pure := by intros; simp
  path_bind := by intros; simp
  path_map := by intros; simp [support_map]

/-- The cached reading: a value and final cache of the simulation from a starting cache. -/
def cachedPaths : PathSemantics hashSpec.QueryCache where
  Path oa a c c' := (a, c') ∈ support ((simulateQ oracleImpl oa).run c)
  path_pure := by
    intros; simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq]
  path_bind := by
    intro α β oa f b s s''
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    constructor
    · rintro ⟨⟨a, s'⟩, h₁, h₂⟩; exact ⟨a, s', h₁, h₂⟩
    · rintro ⟨a, s', h₁, h₂⟩; exact ⟨(a, s'), h₁, h₂⟩
  path_map := by
    intro α β g oa b s s'
    rw [simulateQ_map, StateT.run_map, support_map]
    constructor
    · rintro ⟨⟨a, sa⟩, h₁, h₂⟩
      simp only [Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨a, h₁, rfl⟩
    · rintro ⟨a, h₁, rfl⟩; exact ⟨(a, s'), h₁, rfl⟩

/-- One step of `execute` at an ordinary instruction. -/
theorem execute_succ_regular (n : ℕ) (s : MachineState) (i : Instr)
    (fetch : s.code s.pc = some i) (admitted : admittedInstruction i = true)
    (ordinary : i ≠ .ECALL) :
    execute (n + 1) s = match step s with
      | none => pure none
      | some next => addCycles 1 <$> execute n next := by
  rw [execute, fetch]
  simp only [admitted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases i <;> rfl

/-- One step of `execute` at a system call. -/
theorem execute_succ_ecall (n : ℕ) (s : MachineState) (fetch : s.code s.pc = some .ECALL) :
    execute (n + 1) s =
      if s.getReg .x5 = 0 then
        if s.getReg .x10 = 0 then pure (some (false, 1)) else
        if s.getReg .x10 = 1 then pure (some (true, 1)) else pure none
      else if s.getReg .x5 = hashCall then
        if hashArgumentsValid s then
          hash (hashInput s).2 >>= fun answer =>
            addCycles (blockCost (hashInput s).1) <$> execute n (writeHash s answer)
        else pure none
      else pure none := by
  rw [execute, fetch]
  simp only [admittedInstruction, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- An unadmitted or unfetchable instruction ends the run without a verdict. -/
theorem execute_succ_fault (n : ℕ) (s : MachineState)
    (h : s.code s.pc = none ∨ ∃ i, s.code s.pc = some i ∧ admittedInstruction i = false) :
    execute (n + 1) s = pure none := by
  rcases h with h | ⟨i, fetch, bad⟩
  · rw [execute, h]
  · rw [execute, fetch]; simp [bad]

/-- The tail of a step: a charged continuation halts under fuel `m` as it did under fuel `n`,
or runs out. -/
theorem tail_agree {σ : Type} (P : PathSemantics σ) (k : ℕ) {n : ℕ} (m : ℕ)
    {s' : MachineState} {r : Bool × ℕ} {st st' : σ}
    (ih : ∀ (n' : ℕ) (s : MachineState) (r : Bool × ℕ) (st st' : σ),
      P.Path (execute n s) (some r) st st' →
      P.Path (execute n' s) (some r) st st' ∨ ∃ st'', P.Path (execute n' s) none st st'')
    (h : P.Path (addCycles k <$> execute n s') (some r) st st') :
    P.Path (addCycles k <$> execute m s') (some r) st st' ∨
      ∃ st'', P.Path (addCycles k <$> execute m s') none st st'' := by
  rw [P.path_map] at h
  obtain ⟨o, ho, hr⟩ := h
  cases o with
  | none => exact absurd hr (by simp [addCycles])
  | some r₀ =>
    rcases ih m s' r₀ st st' ho with hl | ⟨st'', hn⟩
    · exact Or.inl (by rw [P.path_map]; exact ⟨some r₀, hl, hr⟩)
    · exact Or.inr ⟨st'', by rw [P.path_map]; exact ⟨none, hn, rfl⟩⟩

/-- Fuel agreement: a run that halts with `r` under fuel `n` halts with `r` on the same path
under any fuel `n'`, or exhausts `n'` on that path. The machine is deterministic given the
answers, so fuel can only cut a run short, never change it. -/
theorem execute_fuel_agree {σ : Type} (P : PathSemantics σ) (n : ℕ) :
    ∀ (n' : ℕ) (s : MachineState) (r : Bool × ℕ) (st st' : σ),
      P.Path (execute n s) (some r) st st' →
      P.Path (execute n' s) (some r) st st' ∨ ∃ st'', P.Path (execute n' s) none st st'' := by
  induction n with
  | zero =>
    intro n' s r st st' h
    rw [execute, P.path_pure] at h
    exact absurd h.1 (by simp)
  | succ n ih =>
    intro n' s r st st' h
    cases n' with
    | zero => exact Or.inr ⟨st, by rw [execute, P.path_pure]; exact ⟨rfl, rfl⟩⟩
    | succ m =>
      cases hcode : s.code s.pc with
      | none =>
        rw [execute_succ_fault n s (Or.inl hcode), P.path_pure] at h
        exact absurd h.1 (by simp)
      | some i =>
        by_cases hadm : admittedInstruction i = true
        · by_cases hE : i = .ECALL
          · subst hE
            rw [execute_succ_ecall n s hcode] at h
            rw [execute_succ_ecall m s hcode]
            split_ifs at h ⊢
            · exact Or.inl h
            · exact Or.inl h
            · rw [P.path_pure] at h; exact absurd h.1 (by simp)
            · rw [P.path_bind] at h
              obtain ⟨answer, s₁, ha, htail⟩ := h
              rcases tail_agree P _ m ih htail with hl | ⟨st'', hn⟩
              · exact Or.inl (by rw [P.path_bind]; exact ⟨answer, s₁, ha, hl⟩)
              · exact Or.inr ⟨st'', by rw [P.path_bind]; exact ⟨answer, s₁, ha, hn⟩⟩
            · rw [P.path_pure] at h; exact absurd h.1 (by simp)
            · rw [P.path_pure] at h; exact absurd h.1 (by simp)
          · rw [execute_succ_regular n s i hcode hadm hE] at h
            rw [execute_succ_regular m s i hcode hadm hE]
            cases hstep : step s with
            | none =>
              rw [hstep] at h
              change P.Path (pure none) (some r) st st' at h
              rw [P.path_pure] at h
              exact absurd h.1 (by simp)
            | some next =>
              rw [hstep] at h
              change P.Path (addCycles 1 <$> execute n next) (some r) st st' at h
              change P.Path (addCycles 1 <$> execute m next) (some r) st st' ∨
                ∃ st'', P.Path (addCycles 1 <$> execute m next) none st st''
              exact tail_agree P 1 m ih h
        · rw [execute_succ_fault n s (Or.inr ⟨i, hcode, by simpa using hadm⟩), P.path_pure] at h
          exact absurd h.1 (by simp)

/-- Refinement requires termination on every input and every oracle-answer path. -/
theorem Submission.no_fault (S : Submission) (h : S.Implements)
    (pk : PublicKey) (m : Message) (signature : List Bool) :
    none ∉ support (S.run pk m signature) := by
  intro fault
  have mapped : none ∈ support (Option.map Prod.fst <$> S.run pk m signature) := by
    rw [support_map]
    exact ⟨none, fault, rfl⟩
  rw [h.2 pk m signature, support_map] at mapped
  obtain ⟨b, _, impossible⟩ := mapped
  cases impossible

end OptimalOTS.Riscv

namespace OptimalOTS.RiscvHint

/-- One simulated query only adds to the cache. -/
theorem subcache_step_grow (t : Spec.Domain) (c c' : hashSpec.QueryCache) (u : Spec.Range t)
    (h : (u, c') ∈ support ((oracleImpl t).run c)) : Subcache c c' := by
  match t with
  | .inl n =>
    have h₁ : (oracleImpl (.inl n)).run c
        = (fun a => (a, c)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) :=
      rfl
    rw [h₁, support_map] at h
    obtain ⟨x, -, hxe⟩ := h
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨-, rfl⟩ := hxe
    exact Subcache.refl c
  | .inr q =>
    have h₁ : (oracleImpl (.inr q)).run c = (hashSpec.randomOracle q).run c := rfl
    rw [h₁, randomOracle.run_eq] at h
    cases hc : c q with
    | some v =>
      rw [hc] at h
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨-, hcc⟩ := h
      rw [hcc]
      exact Subcache.refl _
    | none =>
      replace h : (u, c') ∈
          support (($ᵗ hashSpec.Range q) >>= fun w => pure (w, c.cacheQuery q w)) := by
        rw [hc] at h; exact h
      rw [mem_support_bind_iff] at h
      obtain ⟨x, -, hxe⟩ := h
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      intro t' u' ht'
      rcases eq_or_ne t' q with rfl | hne
      · rw [hc] at ht'; exact absurd ht' (by simp)
      · rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hne]; exact ht'

/-- After a hash query the answer is in the cache, whether it was a hit or a miss. -/
theorem cache_holds_answer (q : hashSpec.Domain) (c c' : hashSpec.QueryCache)
    (u : hashSpec.Range q) (h : (u, c') ∈ support ((oracleImpl (.inr q)).run c)) :
    c' q = some u := by
  have h₁ : (oracleImpl (.inr q)).run c = (hashSpec.randomOracle q).run c := rfl
  rw [h₁, randomOracle.run_eq] at h
  cases hc : c q with
  | some v =>
    rw [hc] at h
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨huv, hcc⟩ := h
    rw [hcc, huv]
    exact hc
  | none =>
    replace h : (u, c') ∈
        support (($ᵗ hashSpec.Range q) >>= fun w => pure (w, c.cacheQuery q w)) := by
      rw [hc] at h; exact h
    rw [mem_support_bind_iff] at h
    obtain ⟨x, -, hxe⟩ := h
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hxe
    obtain ⟨rfl, rfl⟩ := hxe
    exact OracleSpec.QueryCache.cacheQuery_self _ _ _

/-- The cached simulation only adds entries. -/
theorem subcache_run_grow {α : Type} (oa : OracleComp Spec α) :
    ∀ (c : hashSpec.QueryCache) (a : α) (c' : hashSpec.QueryCache),
      (a, c') ∈ support ((simulateQ oracleImpl oa).run c) → Subcache c c' := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c a c' h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    obtain ⟨-, hcc⟩ := h
    rw [hcc]
    exact Subcache.refl _
  | query_bind t k ih =>
    intro c a c' h
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at h
    obtain ⟨⟨u, cmid⟩, hstep, hrest⟩ := h
    intro t' u' ht'
    exact ih u cmid a c' hrest (subcache_step_grow t c cmid u hstep ht')

/-- Replay: a computation with no private randomness, run from a cache holding every answer of
one of its completed runs, returns that run's result and samples nothing. -/
theorem replay_deterministic {α : Type} (oa : OracleComp Spec α) :
    Deterministic oa →
    ∀ (c c' c'' : hashSpec.QueryCache) (a : α),
      (a, c') ∈ support ((simulateQ oracleImpl oa).run c) → Subcache c' c'' →
      (simulateQ oracleImpl oa).run c'' = pure (a, c'') := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro _ c c' c'' a h _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    intro hdet c c' c'' a h hsub
    unfold Deterministic at hdet
    rw [isQueryBound_query_bind_iff] at hdet
    obtain ⟨ht, hk⟩ := hdet
    match t, ht with
    | .inl n, ht => exact absurd ht (by simp)
    | .inr q, _ =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at h
      obtain ⟨⟨u, cmid⟩, hstep, hrest⟩ := h
      have hcmid : cmid q = some u := cache_holds_answer q c cmid u hstep
      have hgrow : Subcache cmid c' := subcache_run_grow (k u) cmid a c' hrest
      have hc'' : c'' q = some u := hsub (hgrow hcmid)
      rw [simulateQ_query_bind, StateT.run_bind]
      have hrun : (oracleImpl (.inr q)).run c''
          = pure ((u, c'') : Spec.Range (.inr q) × hashSpec.QueryCache) := by
        show (hashSpec.randomOracle q).run c'' = _
        rw [randomOracle.run_eq, hc'']
      change ((oracleImpl (.inr q)).run c'' >>=
        fun p : Spec.Range (.inr q) × hashSpec.QueryCache =>
          (simulateQ oracleImpl (k p.1)).run p.2) = pure (a, c'')
      rw [hrun, pure_bind]
      exact ih u (hk u) cmid c' c'' a hrest hsub

/-- Cached decision agreement does not preserve the number of oracle calls: a deterministic
computation can be replayed from its populated cache without learning new answers. -/
theorem repeated_deterministic_agrees {α : Type} [DecidableEq α]
    (oa : OracleComp Spec α) (hdet : Deterministic oa) :
    probTrue (do
      let first ← oa
      let second ← oa
      pure (decide (first ≠ second))) = 0 := by
  rw [probTrue_eq_zero_iff]
  intro hmem
  rw [StateT.run'_eq, support_map] at hmem
  obtain ⟨⟨b, cend⟩, hbc, hb⟩ := hmem
  simp only at hb
  subst hb
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hbc
  obtain ⟨⟨first, c₁⟩, hfirst, hrest⟩ := hbc
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨second, c₂⟩, hsecond, hpure⟩ := hrest
  have hreplay := replay_deterministic oa hdet ∅ c₁ c₁ first hfirst (Subcache.refl c₁)
  rw [hreplay] at hsecond
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsecond
  rcases hsecond with ⟨rfl, rfl⟩
  simp [simulateQ_pure, StateT.run_pure] at hpure

end OptimalOTS.RiscvHint

namespace OptimalOTS.Riscv

open OptimalOTS.RiscvHint

/-- A deterministic-track submission read as a hinted one: the identity view. -/
def Submission.hinted (S : Submission) : RiscvHint.Submission where
  scheme := S.scheme
  image := S.image
  compress := id
  expand := fun _ _ σ => pure σ
  fuel := S.fuel

/-- On a view no longer than a signature, the hinted run is the deterministic run. -/
theorem Submission.hinted_exec (S : Submission) (n : ℕ) (pk : PublicKey) (m : Message)
    (view : View) (h : view.length ≤ maxSignatureBits) :
    S.hinted.exec n pk m view = execute n (initialState S.image pk m view) := by
  simp only [RiscvHint.Submission.exec, Submission.hinted,
    RiscvHintChecks.loadView_eq_initialState S.image pk m view h]

/-- A deterministic-track certificate is a hinted certificate at the same claim, for the
identity view, provided the image halts rejecting on every view longer than a signature — the
inputs the deterministic loader never presents, because it truncates them and sets the length
sentinel instead. -/
theorem Submission.hinted_certificate (S : Submission) {c : ℕ} (h : S.Certificate c)
    (long : ∀ (pk : PublicKey) (m : Message) (view : View), maxSignatureBits < view.length →
      ∀ o ∈ support (S.hinted.exec (S.fuel pk m view) pk m view), decision o = some false) :
    S.hinted.Certificate c := by
  have himpl := h.implements.2
  have hdet := h.admissible.verifyDeterministic
  -- A `some` outcome of the deterministic run under any fuel, on a short view, is an outcome of
  -- the submission's own run (uncached reading).
  have short_support : ∀ pk m (view : View) n r, view.length ≤ maxSignatureBits →
      some r ∈ support (S.hinted.exec n pk m view) → some r ∈ support (S.run pk m view) := by
    intro pk m view n r hlen hmem
    rw [S.hinted_exec n pk m view hlen] at hmem
    rcases execute_fuel_agree supportPaths n (S.fuel pk m view) _ r () () hmem with hl | ⟨_, hn⟩
    · exact hl
    · exact absurd hn (S.no_fault h.implements pk m view)
  -- On a long view no fuel gives an accepting run.
  have long_reject : ∀ pk m (view : View) n k, maxSignatureBits < view.length →
      some (true, k) ∉ support (S.hinted.exec n pk m view) := by
    intro pk m view n k hlen hmem
    rcases execute_fuel_agree supportPaths n (S.fuel pk m view) _ (true, k) () () hmem
      with hl | ⟨_, hn⟩
    · exact absurd (long pk m view hlen _ hl) (by simp [decision])
    · exact absurd (long pk m view hlen _ hn) (by simp [decision])
  refine ⟨h.admissible, h.secure, h.implements.1, ?_, ?_, ?_, ?_⟩
  · -- Expands
    intro pk m σ view hview
    simp only [Submission.hinted, support_pure, Set.mem_singleton_iff] at hview
    simpa [Submission.hinted] using hview
  · -- Faithful
    intro pk m σ
    rw [probTrue_eq_zero_iff]
    intro hmem
    rw [StateT.run'_eq, support_map] at hmem
    obtain ⟨⟨b, cend⟩, hbc, hb⟩ := hmem
    simp only at hb
    subst hb
    change cachedPaths.Path _ true ∅ cend at hbc
    rw [cachedPaths.path_bind] at hbc
    obtain ⟨d, c₁, hd, hrest⟩ := hbc
    rw [cachedPaths.path_bind] at hrest
    obtain ⟨acc, c₂, hacc, hpure⟩ := hrest
    rw [cachedPaths.path_pure] at hpure
    have hne : d ≠ some acc := by simpa using hpure.1.symm
    have hd' : cachedPaths.Path (decision <$> S.hinted.exec (S.fuel pk m σ) pk m σ) d ∅ c₁ := by
      simpa [RiscvHint.Submission.honestRun, Submission.hinted] using hd
    rw [cachedPaths.path_map] at hd'
    obtain ⟨o, ho, rfl⟩ := hd'
    rcases Nat.lt_or_ge maxSignatureBits σ.length with hlen | hlen
    swap
    · rw [S.hinted_exec _ pk m σ hlen] at ho
      have hmap : cachedPaths.Path (Option.map Prod.fst <$> S.run pk m σ) (decision o) ∅ c₁ := by
        rw [cachedPaths.path_map]; exact ⟨o, ho, rfl⟩
      rw [himpl pk m σ, cachedPaths.path_map] at hmap
      obtain ⟨b, hb, hbo⟩ := hmap
      have hreplay := replay_deterministic _ (hdet pk m σ) ∅ c₁ c₁ b hb (Subcache.refl c₁)
      change (acc, c₂) ∈ support ((simulateQ oracleImpl (S.scheme.verify pk m σ)).run c₁) at hacc
      rw [hreplay] at hacc
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hacc
      exact hne (by rw [← hbo, hacc.1])
    · have hlong := long pk m σ hlen o (mem_support_of_mem_support_run _ _ ∅ c₁ ho)
      have hrej : acc = false := by
        have := h.admissible.rejectsOversized pk m σ hlen
        cases hacc' : acc
        · rfl
        · exact absurd (mem_support_of_mem_support_run _ _ c₁ c₂ (hacc' ▸ hacc)) this
      exact hne (by rw [hlong, hrej])
  · -- Sound
    intro pk m view n
    rw [probTrue_eq_zero_iff]
    intro hmem
    rw [StateT.run'_eq, support_map] at hmem
    obtain ⟨⟨b, cend⟩, hbc, hb⟩ := hmem
    simp only at hb
    subst hb
    change cachedPaths.Path _ true ∅ cend at hbc
    rw [cachedPaths.path_bind] at hbc
    obtain ⟨o, c₁, ho, hrest⟩ := hbc
    rw [cachedPaths.path_bind] at hrest
    obtain ⟨acc, c₂, hacc, hpure⟩ := hrest
    rw [cachedPaths.path_pure] at hpure
    have hb := hpure.1.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
    obtain ⟨hdec, hrej⟩ := hb
    obtain ⟨k, rfl⟩ : ∃ k, o = some (true, k) := by
      cases o with
      | none => cases hdec
      | some r => exact ⟨r.2, by cases r; simp [decision] at hdec; simp [hdec]⟩
    rcases Nat.lt_or_ge maxSignatureBits view.length with hlen | hlen
    swap
    · change cachedPaths.Path (S.hinted.exec n pk m view) _ ∅ c₁ at ho
      rw [S.hinted_exec n pk m view hlen] at ho
      rcases execute_fuel_agree cachedPaths n (S.fuel pk m view) _ (true, k) ∅ c₁ ho
        with hl | ⟨c'', hn⟩
      · have hmap : cachedPaths.Path (Option.map Prod.fst <$> S.run pk m view) (some true) ∅ c₁ := by
          rw [cachedPaths.path_map]; exact ⟨some (true, k), hl, rfl⟩
        rw [himpl pk m view, cachedPaths.path_map] at hmap
        obtain ⟨b, hb, hbo⟩ := hmap
        have hb' : b = true := by simpa using hbo
        subst hb'
        have hreplay := replay_deterministic _ (hdet pk m view) ∅ c₁ c₁ true hb (Subcache.refl c₁)
        change (acc, c₂) ∈ support ((simulateQ oracleImpl (S.scheme.verify pk m (S.hinted.compress view))).run c₁) at hacc
        simp only [Submission.hinted, id] at hacc
        rw [hreplay] at hacc
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hacc
        rw [hacc.1] at hrej
        cases hrej
      · exact S.no_fault h.implements pk m view (mem_support_of_mem_support_run _ _ ∅ c'' hn)
    · exact long_reject pk m view n k hlen (mem_support_of_mem_support_run _ _ ∅ c₁ ho)
  · -- CyclesAtMost
    intro pk m view n cycles hmem
    rcases Nat.lt_or_ge maxSignatureBits view.length with hlen | hlen
    · exact absurd hmem (long_reject pk m view n cycles hlen)
    · exact h.cycles pk m view true cycles (short_support pk m view n (true, cycles) hlen hmem)

end OptimalOTS.Riscv

/-! ## 4. Axiom audit of the derived facts -/

/--
info: 'RiscvHintChecks.loadView_eq_initialState' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms RiscvHintChecks.loadView_eq_initialState

/--
info: 'OptimalOTS.RiscvHint.probTrue_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.RiscvHint.probTrue_eq_zero_iff

/--
info: 'OptimalOTS.RiscvHint.Submission.sound_adaptive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.RiscvHint.Submission.sound_adaptive

/--
info: 'OptimalOTS.RiscvHint.mem_support_of_mem_support_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.RiscvHint.mem_support_of_mem_support_run

/--
info: 'OptimalOTS.Riscv.execute_fuel_agree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Riscv.execute_fuel_agree

/--
info: 'OptimalOTS.RiscvHint.replay_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.RiscvHint.replay_deterministic

/--
info: 'OptimalOTS.Riscv.Submission.hinted_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Riscv.Submission.hinted_certificate

/--
info: 'OptimalOTS.RiscvHint.repeated_deterministic_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.RiscvHint.repeated_deterministic_agrees
