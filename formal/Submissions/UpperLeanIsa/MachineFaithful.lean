import Submissions.UpperLeanIsa.MachineHonest

/-!
# The HL-FLAT-A machine submission and its machine clauses

* `machineSubmission`: the FLAT-42 layer scheme (`Flat.scheme`), the HL bytecode (`program`),
  memory `2 ^ 16`, the honest prover (`prover`) and the step count `425` (every completing run
  executes exactly `425` instructions, `totalSteps_eq`).
* `faithful`: under every fixed table, the honest run completes when the verifier accepts
  (`honest_run`) and only then (`fixed_sound`).
* `machine_sound`, `machine_cycles`, `machine_valid`, `machine_seededRows`: the other machine
  clauses for this submission (`sound`, `cycles`, `valid`, `seededRows_lt`).
-/

namespace OptimalOTS.HLFlat

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

/-- The machine half of the submission. -/
def machineSubmission : LeanIsa.Submission where
  scheme := Flat.scheme
  program := program
  memLog := 16
  prover := prover
  steps := fun _ _ _ => 425

open scoped Classical in
theorem decision_false {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
    (h : ¬ (bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk) ∧
      rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) = pk)) :
    (if bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk) then
        rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) == pk
      else false) = false := by
  by_cases hc : bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk)
  · rw [if_pos hc]
    have hne : rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) ≠ pk :=
      fun he => h ⟨hc.1, hc.2, he⟩
    simpa using hne
  · rw [if_neg hc]

set_option linter.constructorNameAsVariable false in
/-- Fixed-table soundness on the honest image. -/
theorem honest_sound (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) {c : ℕ}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program (LeanIsa.loadInput pk m bits (imageF f pk m bits)) 425
        Regs.initial))) :
    bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk) ∧
      rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) = pk := by
  generalize (425 : ℕ) = n at h
  exact fixed_sound (le_refl 16) (by norm_num) f pk m bits _ h

set_option linter.constructorNameAsVariable false in
/-- **Faithful**: the honest prover's run completes exactly when the verifier accepts. -/
theorem faithful : machineSubmission.Faithful := by
  refine ⟨show minLogMem ≤ 16 by decide, show (16 : ℕ) ≤ maxLogMem by decide, ?_⟩
  intro pk m bits
  apply probTrue_zero_of_fixed
  intro f
  have hrun : simulateQ (unifFwdAnswerImpl f) (machineSubmission.honestRun pk m bits) =
      (fun o : Option ℕ => o.isSome) <$> simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost program (LeanIsa.loadInput pk m bits (imageF f pk m bits)) 425
          Regs.initial) := by
    show simulateQ _ (prover pk m bits >>= fun L => (fun o : Option ℕ => o.isSome) <$>
      LeanIsa.runCost program (LeanIsa.loadInput pk m bits L) 425 Regs.initial) = _
    rw [simulateQ_bind, fixed_prover, pure_bind, simulateQ_map]
  have hver : machineSubmission.scheme.verify pk m bits = FP.verify pk m bits := rfl
  have hs := fun c => honest_sound (c := c) f pk m bits
  have hh := fun h1 h2 h3 => honest_run (f := f) (pk := pk) (m := m) (bits := bits) h1 h2 h3
  rw [simulateQ_bind, hrun, hver]
  generalize simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program
    (LeanIsa.loadInput pk m bits (imageF f pk m bits)) 425 Regs.initial) = X at hs hh ⊢
  simp only [simulateQ_bind, simulateQ_pure, fixed_verify, pure_bind]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨b, hb, hmem⟩ := hmem
  rw [mem_support_pure_iff] at hmem
  rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hb
  obtain ⟨o, ho, hb⟩ := hb
  rw [Function.comp_apply, mem_support_pure_iff] at hb
  subst hb
  by_cases hacc : bits.length = sigBits ∧ FP.Accepted (idxValue f FP m (decodeNonce bits) pk) ∧
      rootValue f FP (topsOf f FP (idxValue f FP m (decodeNonce bits) pk) bits) = pk
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
theorem machine_sound : machineSubmission.Sound := sound machineSubmission rfl rfl

/-- **Cycles** for the machine submission: every completing run costs `1598`. -/
theorem machine_cycles : machineSubmission.CyclesAtMost claim := cycles machineSubmission rfl

/-- The claim constant. -/
theorem claim_eq : claim = 1598 := rfl

/-- A cycle bound holds for every larger claim. -/
theorem cyclesAtMost_mono {S : LeanIsa.Submission} {c c' : ℕ} (h : S.CyclesAtMost c)
    (hc : c ≤ c') : S.CyclesAtMost c' :=
  fun pk m σ κ h1 h2 L n cost hmem => le_trans (h pk m σ κ h1 h2 L n cost hmem) hc

/-- The planned HL-FLAT-A claim `1629` holds a fortiori. -/
theorem machine_cycles_1629 : machineSubmission.CyclesAtMost 1629 :=
  cyclesAtMost_mono machine_cycles (by unfold claim; omega)

/-- **Valid** bytecode. -/
theorem machine_valid : LeanIsa.BytecodeValid machineSubmission.program := valid

/-- The seeded rows: `2 ^ 18 + 2 ^ 16 < 2 ^ 20`. -/
theorem machine_seededRows : machineSubmission.seededRows < LeanIsa.maxSeededRows :=
  seededRows_lt machineSubmission rfl rfl

end

end OptimalOTS.HLFlat

open OptimalOTS.HLFlat in
#print axioms faithful
open OptimalOTS.HLFlat in
#print axioms machine_sound
open OptimalOTS.HLFlat in
#print axioms machine_cycles
open OptimalOTS.HLFlat in
#print axioms machine_cycles_1629
open OptimalOTS.HLFlat in
#print axioms machine_valid
open OptimalOTS.HLFlat in
#print axioms machine_seededRows
