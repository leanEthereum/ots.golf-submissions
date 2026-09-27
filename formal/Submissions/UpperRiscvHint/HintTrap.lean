import Submissions.UpperRiscvHint.BlockExecution
import Submissions.UpperRiscvHint.RejectAdapter
import Submissions.UpperRiscvHint.HintTransfer

/-! Views for an image that may trap on invalid input. The honest prover runs the verifier
first: it lays out accepted signatures, by a deterministic oracle computation, and hands every
other signature over in the raw form, which the image rejects before its first possible trap.
Acceptance must still imply the verifier's acceptance on `compress view`, and fuel above the
image's budget changes nothing. The machine may append constant-answer query suffixes to its
specification (`Prunes`), and only accepting runs are charged. -/

noncomputable section

namespace OptimalOTS.HintTrap

open OracleComp OptimalOTS.RiscvHint

variable (S : OracleAlgorithm.Scheme) (image : Riscv.Image)
  (compress : View → OracleAlgorithm.Signature)
  (layout : PublicKey → Message → OracleAlgorithm.Signature → OracleComp Spec View)
  (raw : OracleAlgorithm.Signature → View) (fuel : ℕ)

/-- A path of a computation with appended constant-answer suffixes is a path of the pruned
computation, which stops at a smaller cache. -/
theorem prunes_path {α : Type} {q o : OracleComp Spec α} (h : RejectAdapter.Prunes q o) :
    ∀ (v : α) (c c' : hashSpec.QueryCache), Riscv.cachedPaths.Path o v c c' →
      ∃ c'', Riscv.cachedPaths.Path q v c c'' ∧ Subcache c'' c' := by
  induction h with
  | stop head x =>
    intro v c c' hp
    rw [Riscv.cachedPaths.path_bind] at hp
    obtain ⟨y, cm, hy, hx⟩ := hp
    rw [Riscv.cachedPaths.path_pure] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨c, (Riscv.cachedPaths.path_pure _ _ _ _).2 ⟨rfl, rfl⟩, subcache_run_grow head c y _ hy⟩
  | query t left right _ ih =>
    intro v c c' hp
    rw [Riscv.cachedPaths.path_bind] at hp
    obtain ⟨u, cm, hu, hr⟩ := hp
    obtain ⟨c'', hl, hsub⟩ := ih u v cm c' hr
    exact ⟨c'', (Riscv.cachedPaths.path_bind _ _ _ _ _).2 ⟨u, cm, hu, hl⟩, hsub⟩

def submission : RiscvHint.Submission where
  scheme := S
  image := image
  compress := compress
  expand := fun pk m σ => do
    let ok ← S.verify pk m σ
    if ok then layout pk m σ else pure (raw σ)
  fuel := fun _ _ _ => fuel

theorem certificate (q : PublicKey → Message → View → OracleComp Spec (Option Bool)) (c : ℕ)
    (admissible : S.Admissible) (secure : S.Secure) (valid : image.Valid)
    (prunes : ∀ pk m view n, fuel ≤ n →
      RejectAdapter.Prunes (q pk m view) (Riscv.observe n (loadView image pk m view)))
    (bounded : ∀ pk m view n, fuel ≤ n → ∀ k,
      some (true, k) ∈ support (Riscv.execute n (loadView image pk m view)) → k ≤ c)
    (layout_compress : ∀ pk m σ, true ∈ support (S.verify pk m σ) →
      ∀ view ∈ support (layout pk m σ), compress view = σ)
    (raw_compress : ∀ σ, compress (raw σ) = σ)
    (sound : ∀ pk m view c₀ c₁, Riscv.cachedPaths.Path (q pk m view) (some true) c₀ c₁ →
      Riscv.cachedPaths.Path (S.verify pk m (compress view)) true c₀ c₁)
    (raw_rejects : ∀ pk m σ, ∀ o ∈ support (q pk m (raw σ)), o = some false)
    (accepts : ∀ pk m σ c₀ c₁, Riscv.cachedPaths.Path (S.verify pk m σ) true c₀ c₁ →
      ∀ view c₂, Riscv.cachedPaths.Path (layout pk m σ) view c₁ c₂ →
      ∀ o c₃, Riscv.cachedPaths.Path (q pk m view) o c₂ c₃ → o = some true) :
    (submission S image compress layout raw fuel).Certificate c := by
  have observe_path : ∀ pk m view n o (c c' : hashSpec.QueryCache), fuel ≤ n →
      Riscv.cachedPaths.Path (Riscv.execute n (loadView image pk m view)) o c c' →
      ∃ c'', Riscv.cachedPaths.Path (q pk m view) (decision o) c c'' ∧ Subcache c'' c' := by
    intro pk m view n o c c' hn h
    apply prunes_path (prunes pk m view n hn)
    rw [Riscv.observe, Riscv.cachedPaths.path_map]
    exact ⟨o, h, rfl⟩
  refine ⟨admissible, secure, valid, ?_, ?_, ?_, ?_⟩
  · -- Expands
    intro pk m σ view hview
    change view ∈ support (S.verify pk m σ >>= fun ok =>
      if ok then layout pk m σ else pure (raw σ)) at hview
    rw [mem_support_bind_iff] at hview
    obtain ⟨ok, hok, hview⟩ := hview
    cases ok
    · rw [if_neg (by decide), support_pure, Set.mem_singleton_iff] at hview
      subst hview
      exact raw_compress σ
    · rw [if_pos rfl] at hview
      exact layout_compress pk m σ hok view hview
  · -- Faithful
    intro pk m σ
    rw [probTrue_eq_zero_iff]
    intro hmem
    rw [StateT.run'_eq, support_map] at hmem
    obtain ⟨⟨b, cend⟩, hbc, hb⟩ := hmem
    simp only at hb
    subst hb
    change Riscv.cachedPaths.Path _ true ∅ cend at hbc
    rw [Riscv.cachedPaths.path_bind] at hbc
    obtain ⟨d, c₁, hd, hrest⟩ := hbc
    rw [Riscv.cachedPaths.path_bind] at hrest
    obtain ⟨acc, c₂, hacc, hpure⟩ := hrest
    rw [Riscv.cachedPaths.path_pure] at hpure
    have hne : d ≠ some acc := by simpa using hpure.1.symm
    change Riscv.cachedPaths.Path ((S.verify pk m σ >>= fun ok =>
      if ok then layout pk m σ else pure (raw σ)) >>= fun view =>
        decision <$> Riscv.execute fuel (loadView image pk m view)) d ∅ c₁ at hd
    rw [Riscv.cachedPaths.path_bind] at hd
    obtain ⟨view, cm, hexp, hrun⟩ := hd
    rw [Riscv.cachedPaths.path_bind] at hexp
    obtain ⟨ok, ca, hver, hview⟩ := hexp
    have hlay : Subcache ca cm := by
      cases ok
      · rw [if_neg (by decide), Riscv.cachedPaths.path_pure] at hview
        obtain ⟨-, rfl⟩ := hview
        exact Subcache.refl _
      · rw [if_pos rfl] at hview
        exact subcache_run_grow _ _ _ _ hview
    have hgrow : Subcache ca c₁ := fun _ _ h => subcache_run_grow _ _ _ _ hrun (hlay h)
    have hreplay := replay_deterministic _ (admissible.verifyDeterministic pk m σ) ∅ ca c₁ ok
      hver hgrow
    change (acc, c₂) ∈ support ((simulateQ oracleImpl (S.verify pk m σ)).run c₁) at hacc
    rw [hreplay] at hacc
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hacc
    rw [hacc.1] at hne
    rw [Riscv.cachedPaths.path_map] at hrun
    obtain ⟨o, ho, rfl⟩ := hrun
    obtain ⟨c'', hq, -⟩ := observe_path pk m _ fuel o cm c₁ le_rfl ho
    cases ok
    · rw [if_neg (by decide), Riscv.cachedPaths.path_pure] at hview
      obtain ⟨rfl, -⟩ := hview
      exact hne (raw_rejects pk m σ _ (mem_support_of_mem_support_run _ _ cm c'' hq))
    · rw [if_pos rfl] at hview
      exact hne (accepts pk m σ ∅ ca hver view cm hview _ c'' hq)
  · -- Sound
    intro pk m view n
    rw [probTrue_eq_zero_iff]
    intro hmem
    rw [StateT.run'_eq, support_map] at hmem
    obtain ⟨⟨b, cend⟩, hbc, hb⟩ := hmem
    simp only at hb
    subst hb
    change Riscv.cachedPaths.Path _ true ∅ cend at hbc
    rw [Riscv.cachedPaths.path_bind] at hbc
    obtain ⟨o, c₁, ho, hrest⟩ := hbc
    rw [Riscv.cachedPaths.path_bind] at hrest
    obtain ⟨acc, c₂, hacc, hpure⟩ := hrest
    rw [Riscv.cachedPaths.path_pure] at hpure
    have hb := hpure.1.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
    obtain ⟨hdec, hrej⟩ := hb
    obtain ⟨k, rfl⟩ : ∃ k, o = some (true, k) := by
      cases o with
      | none => cases hdec
      | some r => exact ⟨r.2, by cases r; simp [decision] at hdec; simp [hdec]⟩
    change Riscv.cachedPaths.Path (Riscv.execute n (loadView image pk m view)) _ ∅ c₁ at ho
    have hmono := Riscv.execute_fuel_mono Riscv.cachedPaths n (max n fuel) _ _ _ _ ho
      (le_max_left _ _)
    obtain ⟨c'', hq, hsub⟩ := observe_path pk m view _ _ ∅ c₁ (le_max_right _ _) hmono
    have hver := sound pk m view ∅ c'' hq
    have hreplay := replay_deterministic _ (admissible.verifyDeterministic pk m _) ∅ c'' c₁ true
      hver hsub
    change (acc, c₂) ∈ support ((simulateQ oracleImpl (S.verify pk m (compress view))).run c₁)
      at hacc
    rw [hreplay] at hacc
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hacc
    rw [hacc.1] at hrej
    cases hrej
  · -- CyclesAtMost
    intro pk m view n cycles hmem
    have hmono := Riscv.execute_fuel_mono Riscv.supportPaths n (max n fuel) _ (true, cycles) () ()
      hmem (le_max_left _ _)
    exact bounded pk m view _ (le_max_right _ _) cycles hmono

end OptimalOTS.HintTrap
