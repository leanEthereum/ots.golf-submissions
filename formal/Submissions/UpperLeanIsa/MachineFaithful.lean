import Submissions.UpperLeanIsa.MachineSound
import Submissions.UpperLeanIsa.MachineHonest

/-!
# Soundness and faithfulness of the leanISA machine

* `fixed_sound`: under a fixed table, a completing run on any image walks one forced path
  (`walk_of_sim`, `walk_full`) whose slot relations make the verifier accept (`accept_of_path`).
* `sound`, `faithful`: the two contract clauses. `faithful` is `faithful_clause`
  (`MachineHonest`), fed with the prover's fixed-table image and `fixed_sound`.
-/

namespace OptimalOTS.LeanIsaBaseline.Honest

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Machine

noncomputable section

/-! ## Glue with `MachineRun` -/

theorem crel_of_rel (f : HashTable) {κ : ℕ} (L : MemImage κ) {ci : CInstr} (h : ci.Rel f L) :
    CRel f (Lx L) ci := by
  cases ci with
  | xor a b c => exact h.2.2.2
  | mul a b c => exact h.2.2.2
  | setc a k => exact h.2
  | blake m0 m1 m2 m3 cv out md => exact h.2
  | jump a b c => exact h.2.2.2
  | pad => exact h.elim

/-- Path facts transfer along a pointwise implication of slot predicates. -/
theorem pathFacts_mono {R R' : ℕ → Prop} (hRR : ∀ s, R s → R' s) {D : ℕ → ℕ}
    (h : PathFacts R D) : PathFacts R' D :=
  ⟨fun s hs => hRR _ (h.const s hs), fun k hk i hi => hRR _ (h.leaf k hk i hi),
    fun i hi => hRR _ (h.leafHi i hi), fun k hk j h1 h2 => hRR _ (h.body k hk j h1 h2),
    fun t ht => hRR _ (h.root t ht), hRR _ h.pk⟩

/-! ## Fixed-table soundness -/

/-- **Fixed-table soundness.** If the run on the loaded image completes under the table `f`,
the verifier accepts under `f`. -/
theorem fixed_sound {κ : ℕ} (hκ : 16 ≤ κ) (hκ' : κ ≤ maxLogMem) (f : HashTable)
    (pk : PublicKey) (m : Message) (bits : List Bool) (L : MemImage κ) {n c : ℕ}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program (LeanIsa.loadInput pk m bits L) n Regs.initial))) :
    bits.length = 5504 ∧ rootValue f (reconstructedWords f m bits) = pk := by
  rw [initial_eq] at h
  have hone := one_of_sim hκ' h
  obtain ⟨D, hD, -, -, hP⟩ := walk_full (fun _ hs => holdsNH_of_holds hs) hone
    (walk_of_sim hκ' hone (by norm_num) h)
  exact accept_of_path f pk m bits _ (fun _ hc => Lx_loadInput_pin hκ pk m bits L hc) hD
    (pathFacts_mono (fun s hs => crel_of_rel f _ hs) hP)

set_option linter.constructorNameAsVariable false in
/-- `fixed_sound` on the honest prover's image. Generalizing the step count first keeps
elaboration from unfolding `totalSteps (dig m)`. -/
theorem honest_sound (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) (c : ℕ)
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program (LeanIsa.loadInput pk m bits (imageF f pk m bits))
        (totalSteps (dig m)) Regs.initial))) :
    bits.length = 5504 ∧ rootValue f (reconstructedWords f m bits) = pk := by
  generalize totalSteps (dig m) = n at h
  exact fixed_sound (le_refl 16) (by decide) f pk m bits _ h

/-! ## The contract clauses -/

/-- The machine half of the submission: the baseline scheme, the bytecode, memory `2 ^ 16`, the
honest prover and the honest path's step count `totalSteps (dig m)`. -/
def machineSubmission : LeanIsa.Submission where
  scheme := scheme
  program := program
  memLog := 16
  prover := prover
  steps := fun _ m _ => totalSteps (dig m)

/-- **Sound**: any submission running this bytecode for this scheme is sound. -/
theorem sound (S : LeanIsa.Submission) (hs : S.scheme = scheme) (hp : S.program = program) :
    S.Sound := by
  intro pk m bits κ h16 h32 L n
  apply probTrue_zero_of_fixed
  intro f
  have hexec : S.exec L n pk m bits =
      LeanIsa.runCost program (LeanIsa.loadInput pk m bits L) n Regs.initial := by
    unfold LeanIsa.Submission.exec
    rw [hp]
  have hver : S.scheme.verify pk m bits = verify pk m bits := by
    rw [hs]
    rfl
  rw [hexec, hver]
  simp only [simulateQ_bind, simulateQ_pure, fixed_verify, pure_bind]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨o, ho, hmem⟩ := hmem
  rw [mem_support_pure_iff] at hmem
  cases o with
  | none => simp at hmem
  | some c =>
    obtain ⟨hlen, hroot⟩ := fixed_sound h16 h32 f pk m bits L ho
    rw [if_pos hlen, hroot] at hmem
    simp at hmem

set_option linter.constructorNameAsVariable false in
/-- **Faithful**: the honest prover's run completes exactly when the verifier accepts. -/
theorem faithful : machineSubmission.Faithful := by
  refine ⟨show minLogMem ≤ 16 by decide, show (16 : ℕ) ≤ maxLogMem by decide,
    faithful_clause machineSubmission (fun _ _ _ => rfl) ?_ ?_⟩
  · intro f pk m bits
    show simulateQ _ (prover pk m bits >>= fun L => (fun o : Option ℕ => o.isSome) <$>
      LeanIsa.runCost program (LeanIsa.loadInput pk m bits L) (totalSteps (dig m))
        Regs.initial) = _
    rw [simulateQ_bind, fixed_prover, pure_bind, simulateQ_map]
  · exact honest_sound

end

end OptimalOTS.LeanIsaBaseline.Honest
