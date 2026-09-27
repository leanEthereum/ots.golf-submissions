import OptimalOTS.Riscv
import OptimalOTS.RiscvHint

/-! Path facts about the hinted RISC-V contract: fuel agreement, cache growth and replay of a
deterministic computation from a populated cache. -/

open OptimalOTS OptimalOTS.Riscv OptimalOTS.RiscvHint RiscvZkvm.Rv64 OracleComp

namespace OptimalOTS.RiscvHint

/-- What `probTrue … = 0` means in `Sound` and `Faithful`: the event occurs on no path of the
cached random-oracle simulation. This is the support of the **simulated** computation, where a
repeated query returns the cached answer; it is weaker than `true ∉ support oa`, which also
quantifies over incoherent answer paths. -/
theorem probTrue_eq_zero_iff (oa : OracleComp Spec Bool) :
    probTrue oa = 0 ↔ true ∉ support ((simulateQ oracleImpl oa).run' ∅) :=
  probOutput_eq_zero_iff _ _

/-- `c₂` is a subcache of `c₁`: every entry of `c₂` is an entry of `c₁`. Written out rather
than as `≤`, because `QueryCache` is a reducible `Pi` type and the pointwise order is also in
scope for it. -/
def Subcache (c₂ c₁ : hashSpec.QueryCache) : Prop :=
  ∀ ⦃t : hashSpec.Domain⦄ ⦃u : hashSpec.Range t⦄, c₂ t = some u → c₁ t = some u

theorem Subcache.refl (c : hashSpec.QueryCache) : Subcache c c := fun _ _ h => h

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

/-- Fuel monotonicity: a run that halts under fuel `n` halts identically, on the same path,
under every larger fuel. -/
theorem execute_fuel_mono {σ : Type} (P : PathSemantics σ) (n : ℕ) :
    ∀ (n' : ℕ) (s : MachineState) (r : Bool × ℕ) (st st' : σ),
      P.Path (execute n s) (some r) st st' → n ≤ n' → P.Path (execute n' s) (some r) st st' := by
  induction n with
  | zero =>
    intro n' s r st st' h _
    rw [execute, P.path_pure] at h
    exact absurd h.1 (by simp)
  | succ n ih =>
    intro n' s r st st' h hle
    obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    have tail : ∀ (k : ℕ) (s' : MachineState) (r : Bool × ℕ) (st st' : σ),
        P.Path (addCycles k <$> execute n s') (some r) st st' →
        P.Path (addCycles k <$> execute m s') (some r) st st' := by
      intro k s' r st st' h
      rw [P.path_map] at h ⊢
      obtain ⟨o, ho, hr⟩ := h
      cases o with
      | none => exact absurd hr (by simp [addCycles])
      | some r₀ => exact ⟨some r₀, ih m s' r₀ st st' ho (by omega), hr⟩
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
          · exact h
          · exact h
          · rw [P.path_pure] at h; exact absurd h.1 (by simp)
          · rw [P.path_bind] at h ⊢
            obtain ⟨answer, s₁, ha, htail⟩ := h
            exact ⟨answer, s₁, ha, tail _ _ _ _ _ htail⟩
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
            change P.Path (addCycles 1 <$> execute m next) (some r) st st'
            exact tail 1 next r st st' h
      · rw [execute_succ_fault n s (Or.inr ⟨i, hcode, by simpa using hadm⟩), P.path_pure] at h
        exact absurd h.1 (by simp)

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

end OptimalOTS.RiscvHint
