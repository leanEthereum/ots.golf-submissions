import Submissions.UpperLeanIsa.AffinePath

/-! Every completing execution of the affine bytecode takes 198 instructions
and costs 990 cycles, plus the contract's 120-cycle public-boundary charge.
`AffineMachine` combines this cycle clause with soundness and honest-prover
equivalence in the complete submission certificate. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
noncomputable section

theorem run_exact {κ : ℕ} {T : Tab} (hT : T.Hyp) (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow 0,1⟩)) :
    n = 198 ∧ c = 990 := by
  obtain ⟨hV,hP,hL,hLayer,hn,hc⟩ := run_full hT h16 hκ M Sm B hHash hd h
  rw [pathSteps_eq hT hV hLayer] at hn
  rw [pathCost_eq hT hV hLayer] at hc
  exact ⟨hn,hc⟩

/-- The contract's universal bound, over all admitted image sizes and all
completing cache-free oracle paths, including adversarial committed images. -/
theorem cycles {T : Tab} (hT : T.Hyp) (S : LeanIsa.Submission) (hS : S.program = program T) :
    S.CyclesAtMost 1110 := by
  intro pk m bits κ h16 hκ M n cost h
  unfold LeanIsa.Submission.exec at h
  rw [hS,initial_eq] at h
  have hc := (run_exact hT h16 hκ (LeanIsa.loadInput pk m bits M) suppSem trueRel
    hashSound_supp (lengthDomain_load h16 pk m bits M) h).2
  rw [boundary_eq,hc]

end
end OptimalOTS.AffineVM
