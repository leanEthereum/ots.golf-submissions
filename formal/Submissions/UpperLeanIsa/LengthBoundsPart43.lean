import Submissions.UpperLeanIsa.LengthBoundsPart42
namespace OptimalOTS.HLG3.LengthGate
open LeanerVM.Parameters LeanerVM.Semantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def block5505 : List (Nat × Nat) := [(5505, 5964272755547696522)]
theorem block5505_good : ∀ p ∈ block5505, Good p := by
  simp only [block5505, List.forall_mem_cons]
  exact ⟨⟨log5505, by decide, by decide⟩, (by simp)⟩
theorem block5505_cover : block5505.map Prod.fst = List.range' 5505 1 := by decide +kernel

end OptimalOTS.HLG3.LengthGate
