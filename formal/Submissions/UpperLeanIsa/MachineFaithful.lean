import Submissions.UpperLeanIsa.MachineHonestPath

/-!
# The HL-GROUP-3 machine submission and its machine clauses

* `machineSubmission P T`: the layer scheme `P.scheme`, the HL bytecode `program T`, memory
  `2 ^ 16`, the honest prover `prover P T` and the step count `207` (every completing run
  executes exactly `207` instructions, `totalSteps_eq`).
* `faithful`: under every fixed table, the honest run completes when the verifier accepts
  (`honest_run`) and only then (`fixed_sound`).
* `machine_sound`, `machine_cycles`, `machine_valid`, `machine_seededRows`: the other machine
  clauses (`sound`, `cycles`, `valid`, `seededRows_lt`).

All of them hold for every table `T` with `T.Hyp` and every scheme `P` with `Compat P T`.
-/

namespace OptimalOTS.HLG3

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

/-- The machine half of the submission. -/
def machineSubmission (P : Params) (T : Tab) : LeanIsa.Submission where
  scheme := P.scheme
  program := program T
  memLog := 16
  prover := prover P T
  steps := fun _ _ _ => 207

variable {P : Params} {T : Tab}

open scoped Classical in
theorem decision_false {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
    (h : ¬ (bits.length = sigBits ∧ P.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk)) :
    (if bits.length = sigBits ∧ P.Accepted (idxValue f P m (decodeNonce bits) pk) then
        rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) == pk
      else false) = false := by
  by_cases hc : bits.length = sigBits ∧ P.Accepted (idxValue f P m (decodeNonce bits) pk)
  · rw [if_pos hc]
    have hne : rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) ≠ pk :=
      fun he => h ⟨hc.1, hc.2, he⟩
    simpa using hne
  · rw [if_neg hc]

set_option linter.constructorNameAsVariable false in
/-- **Faithful**: the honest prover's run completes exactly when the verifier accepts. -/
theorem faithful (hT : T.Hyp) (hC : Compat P T) : (machineSubmission P T).Faithful := by
  refine ⟨show minLogMem ≤ 16 by decide, show (16 : ℕ) ≤ maxLogMem by decide, ?_⟩
  intro pk m bits
  apply probTrue_zero_of_fixed
  intro f
  have hrun : simulateQ (unifFwdAnswerImpl f) ((machineSubmission P T).honestRun pk m bits) =
      (fun o : Option ℕ => o.isSome) <$> simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) 207
          Regs.initial) := by
    show simulateQ _ (prover P T pk m bits >>= fun L => (fun o : Option ℕ => o.isSome) <$>
      LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits L) 207 Regs.initial) = _
    rw [simulateQ_bind, fixed_prover, pure_bind, simulateQ_map]
  have hver : (machineSubmission P T).scheme.verify pk m bits = P.verify pk m bits := rfl
  have hs := fun c (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) 207
        Regs.initial))) =>
    fixed_sound hT hC (le_refl 16) (by norm_num) f pk m bits _ h
  have hh : ∀ (h1 : bits.length = sigBits) (h2 : P.Accepted (idxValue f P m (decodeNonce bits) pk))
      (h3 : rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk),
      simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) 207
          Regs.initial) = pure (some 1089) :=
    fun h1 h2 h3 => honest_run hT hC h1
      (by simpa only [idxValue, indexSlice_effective, IF, idxOf, y0F] using h2)
      (by simpa only [idxValue, indexSlice_effective, IF, idxOf, y0F] using h3)
  rw [simulateQ_bind, hrun, hver]
  generalize simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost (program T)
    (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) 207 Regs.initial) = X at hs hh ⊢
  simp only [simulateQ_bind, simulateQ_pure, fixed_verify, pure_bind]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨b, hb, hmem⟩ := hmem
  rw [mem_support_pure_iff] at hmem
  rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hb
  obtain ⟨o, ho, hb⟩ := hb
  rw [Function.comp_apply, mem_support_pure_iff] at hb
  subst hb
  by_cases hacc : bits.length = sigBits ∧ P.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk
  · rw [hh hacc.1 hacc.2.1 hacc.2.2, mem_support_pure_iff] at ho
    subst ho
    rw [decision_true hacc] at hmem
    simp at hmem
  · cases o with
    | none =>
      rw [decision_false hacc] at hmem
      simp at hmem
    | some c => exact hacc (hs c ho)

/-- **Sound** for the machine submission. -/
theorem machine_sound (hT : T.Hyp) (hC : Compat P T) : (machineSubmission P T).Sound :=
  sound hT hC (machineSubmission P T) rfl rfl

/-- **Cycles** for the machine submission: every completing run costs `1209`. -/
theorem machine_cycles (hT : T.Hyp) : (machineSubmission P T).CyclesAtMost claim :=
  cycles hT (machineSubmission P T) rfl

/-- The claim constant. -/
theorem claim_eq : claim = 1209 := rfl

/-- **Valid** bytecode. -/
theorem machine_valid : LeanIsa.BytecodeValid (machineSubmission P T).program := valid T

/-- The seeded rows: `2 ^ 18 + 2 ^ 16 < 2 ^ 20`. -/
theorem machine_seededRows : (machineSubmission P T).seededRows < LeanIsa.maxSeededRows :=
  seededRows_lt (machineSubmission P T) rfl rfl

end

end OptimalOTS.HLG3

open OptimalOTS.HLG3 in
#print axioms faithful
open OptimalOTS.HLG3 in
#print axioms machine_sound
open OptimalOTS.HLG3 in
#print axioms machine_cycles
open OptimalOTS.HLG3 in
#print axioms machine_valid
open OptimalOTS.HLG3 in
#print axioms machine_seededRows
