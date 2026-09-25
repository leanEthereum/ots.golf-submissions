import Submissions.UpperRiscvHint.MixedContext
import Submissions.UpperRiscvHint.MixedDispatchArith

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag

theorem fine_field_dispatch (answer : BitVec hashBits) (index : RawIdx)
    (hi : index.val = pack answer) (q : Fin 16) :
    fineFld (laneGroup q) (wordOf answer (laneGroup q)).toNat (laneIdx q) =
      digit index.val (2*q.val) := by
  have hq := q.isLt
  have hg : laneGroup q < 4 := by unfold laneGroup; omega
  have hl : laneIdx q < 4 := by unfold laneIdx; omega
  have he : fineChain (laneGroup q) (laneIdx q) = 2*q.val := by
    unfold fineChain laneGroup laneIdx
    omega
  calc
    _ = fieldDigit answer (fineChain (laneGroup q) (laneIdx q)) :=
      fine_word answer _ _ hg hl
    _ = fieldDigit answer (2*q.val) := congrArg (fieldDigit answer) he
    _ = digit (pack answer) (2*q.val) := (digit_pack answer (by omega)).symm
    _ = digit index.val (2*q.val) := congrArg (fun i => digit i (2*q.val)) hi.symm

theorem coarse_field_dispatch (answer : BitVec hashBits) (index : RawIdx)
    (hi : index.val = pack answer) (q : Fin 16) :
    coarseFld (laneGroup q) (wordOf answer (laneGroup q)).toNat (laneIdx q) =
      digit index.val (2*q.val+1) := by
  have hq := q.isLt
  have hg : laneGroup q < 4 := by unfold laneGroup; omega
  have hl : laneIdx q < 4 := by unfold laneIdx; omega
  have he : coarseChain (laneGroup q) (laneIdx q) = 2*q.val+1 := by
    unfold coarseChain laneGroup laneIdx
    omega
  calc
    _ = fieldDigit answer (coarseChain (laneGroup q) (laneIdx q)) :=
      coarse_word answer _ _ hg hl
    _ = fieldDigit answer (2*q.val+1) := congrArg (fieldDigit answer) he
    _ = digit (pack answer) (2*q.val+1) := (digit_pack answer (by omega)).symm
    _ = digit index.val (2*q.val+1) := congrArg (fun i => digit i (2*q.val+1)) hi.symm

theorem word_fields_dispatch (answer : BitVec hashBits) (index : RawIdx)
    (hi : index.val = pack answer) (q : Fin 16) :
    baseLane (4*laneGroup q+laneIdx q) -
      (4*fineFld (laneGroup q) (wordOf answer (laneGroup q)).toNat (laneIdx q) +
       1024*coarseFld (laneGroup q) (wordOf answer (laneGroup q)).toNat (laneIdx q)) =
      baseLane q - dispatch index q := by
  have he : 4*laneGroup q+laneIdx q = q := by unfold laneGroup laneIdx; omega
  have hfields := congrArg₂ (fun a b : ℕ => 4*a+1024*b)
    (fine_field_dispatch answer index hi q) (coarse_field_dispatch answer index hi q)
  exact congrArg₂ Nat.sub (congrArg baseLane he) hfields

end OptimalOTS.RiscvMixedProgram
