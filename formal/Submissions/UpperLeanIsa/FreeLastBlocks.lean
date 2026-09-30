import Submissions.UpperLeanIsa.PartialHintCodec
import Submissions.UpperLeanIsa.FourMachineTable
import Submissions.UpperLeanIsa.FourMachineBlocks

/-! Concrete cell-level straight blocks for the 1088 free-last machine. Each block is
followed by one actual JUMP; the legacy CInstr dispatch weight is deliberately
absent here. Layout, frame guards and whole-run soundness are separate obligations. -/
namespace OptimalOTS.FreeLastBlocks
open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def budget (u : Nat) : Nat := [6,7,7,7,7,5,6,7,6,6,7,5,6].getD u 0
def order : List Nat := [0,2,3,4,5,6,7,8,9,10,11,12,1]
def position (u : Nat) : Nat := if u = 0 then 0 else if u = 1 then 12 else u-1
def nextGroup (u : Nat) : Nat := if u = 0 then 2 else if u = 12 then 1 else u+1
def gp (f : Nat) : Nat := if f = 0 then cCell 1 else gpCell f
def bias (u : Nat) : Nat := if u = 12 then lenCell else if u = 11 then oneCell else cCell (u+1)
def exitCell : Nat := 220

def hinted (u v : Nat) : Bool :=
  if u = 11 then true else if u = 8 then PartialHints.hinted8 v
  else if u = 9 then PartialHints.hinted9 v else false

def label (u v : Nat) : Nat :=
  if u = 8 then (PartialHints.label8Inv (BitVec.ofNat 10 v)).toNat
  else if u = 9 then (PartialHints.label9Inv (BitVec.ofNat 10 v)).toNat else v

def pattern (u v : Nat) : E := LeanIsa.cellOfBits
  (PartialHints.wordPermutation (BitVec.ofNat 128 (label u v * 2^POS u)))

def tie (u v : Nat) : List CInstr :=
  if u = 0 then [.setc (accCell 0) (pattern 0 v)]
  else if hinted u v then [.xor (accCell (u-1)) (hCell (u+1)) (accCell u)]
  else if v = 0 then [copy (accCell (u-1)) (accCell u)]
  else [.setc (tCell u) (pattern u v), .xor (accCell (u-1)) (tCell u) (accCell u)]

def tieCount (u v : Nat) : Nat := if u = 0 ∨ hinted u v ∨ v = 0 then 1 else 2

theorem tie_length (u v : Nat) : (tie u v).length = tieCount u v := by
  unfold tie tieCount
  split_ifs <;> simp_all

theorem tie_cost (u v : Nat) : lcost (tie u v) = tieCount u v := by
  rw [← tie_length]
  unfold tie
  split_ifs <;> rfl

/-- The Z twin checks the last product against ONE instead of a hint cell. -/
def checksum (u v : Nat) (z : Bool) : CInstr :=
  let src := gp (position u)
  let dst := if z then oneCell else gp (position u+1)
  let c := chargedCost fusionTab u v
  if 6 ≤ c then .mul src (cCell (c-6)) dst else .mul dst (cCell (6-c)) src

def pads (u v : Nat) : Nat := budget u - (3 + tieCount u v + copyCount fusionTab u v)

def core (u v : Nat) (z : Bool) : List CInstr :=
  tie u v ++ [checksum u v z] ++ segs fusionTab u v ++ rootIns fusionTab u v false ++
    List.replicate (pads u v) NOP

def normal (u v : Nat) : List CInstr := core u v false ++
  [if u = 1 then .xor (hCell 0) (gp 13) (h1Cell 0)
   else .xor (hCell (nextGroup u+1)) (bias (nextGroup u)) (h1Cell (nextGroup u+1))]

def zero (v : Nat) : List CInstr := core 1 v true ++ [copy (wCell 0) tfCell, NOP]
def free (s : Nat) : List CInstr := chainOps topCell 0 s tfCell

def prologue (a : K) : List CInstr :=
  ((List.range 11).map (fun c => .setc (cCell (c+1)) (ofK (a^(c+1))))) ++
    [.init, copy (stCell 0) pkCell,
     .blake msgLo msgHi nonceCell pkCell (cCell 1) idxCell (cCell 11),
     .xor (hCell 1) (bias 0) (h1Cell 1)]

/-- Check each tuple once, then its alias interval. This avoids repeatedly
searching the entire tuple table for each of the 1024 codes. -/
def partialTupleCopies (u : Nat) (t : List Nat) : Nat :=
  ((List.range (gk u)).map (fun i => if copied u i ∧ t.getD i 0 = 0 then 1 else 0)).sum

def partialEntryBudget (u : Nat) (e : SplitTables.Entry) : Bool :=
  (List.range e.2.2).all fun i =>
    Nat.ble (3 + tieCount u (e.2.1+i) + partialTupleCopies u e.1) 6

def partialBudgetCheck (u : Nat) : Bool :=
  (SplitTables.entries (FourChildCodec.ushape u)).all (partialEntryBudget u)

theorem partial_budget8_checked : partialBudgetCheck 8 = true := by rfl
theorem partial_budget9_checked : partialBudgetCheck 9 = true := by rfl

theorem partial_budget_sound {u v : Nat} (hu : u ≠ 0)
    (hs : FourChildCodec.ushape u < 13)
    (hv : v < FourChildCodec.cutS (FourChildCodec.ushape u))
    (h : partialBudgetCheck u = true) :
    3 + tieCount u v + copyCount fusionTab u v ≤ 6 := by
  obtain ⟨hm,hl,hr⟩ := FourChildCodec.selected_spec hs hv
  have he := List.all_eq_true.mp h _ hm
  have hi : v - FourChildCodec.lead (FourChildCodec.ushape u) v <
      (FourChildCodec.selected (FourChildCodec.ushape u) v).2.2 := by
    change v - FourChildCodec.lead (FourChildCodec.ushape u) v <
      FourChildCodec.multS (FourChildCodec.ushape u) v
    omega
  have hb := List.all_eq_true.mp he _ (List.mem_range.mpr hi)
  have heq : FourChildCodec.lead (FourChildCodec.ushape u) v +
      (v - FourChildCodec.lead (FourChildCodec.ushape u) v) = v := by omega
  have hc : partialTupleCopies u (FourChildCodec.selected (FourChildCodec.ushape u) v).1 =
      copyCount fusionTab u v := by
    unfold partialTupleCopies copyCount fusionTab rawCode FourChildCodec.tup
    rw [if_neg hu]
    simp only [FourChildCodec.tupS,if_pos hv]
  change Nat.ble (3 + tieCount u
      (FourChildCodec.lead (FourChildCodec.ushape u) v +
        (v - FourChildCodec.lead (FourChildCodec.ushape u) v)) +
      partialTupleCopies u (FourChildCodec.selected (FourChildCodec.ushape u) v).1) 6 = true at hb
  rw [heq,hc] at hb
  exact Nat.ble_eq.mp hb

theorem partial_budget8 : ∀ v < 1024,
    3 + tieCount 8 v + copyCount fusionTab 8 v ≤ 6 := by
  intro v hv
  exact partial_budget_sound (by decide) (by decide) hv partial_budget8_checked

theorem partial_budget9 : ∀ v < 1024,
    3 + tieCount 9 v + copyCount fusionTab 9 v ≤ 6 := by
  intro v hv
  exact partial_budget_sound (by decide) (by decide) hv partial_budget9_checked

theorem budget_fit {u v : Nat} (hu : u < 13) (hv : v < VF u) :
    3 + tieCount u v + copyCount fusionTab u v ≤ budget u := by
  by_cases h8 : u = 8
  · subst u; exact partial_budget8 v hv
  by_cases h9 : u = 9
  · subst u; exact partial_budget9 v hv
  have h := fusion_ordinary hu hv
  have ht : tieCount u v = if u ≠ 0 ∧ u ≠ 11 ∧ v ≠ 0 then 2 else 1 := by
    unfold tieCount hinted
    split_ifs <;> simp_all
  have hb : budget u = gcu u - 1 :=
    (show ∀ u < 13, u ≠ 8 → u ≠ 9 → budget u = gcu u - 1 by decide) u hu h8 h9
  rw [ht, hb]
  unfold machineOrdinary at h
  omega

theorem checksum_cost (u v : Nat) (z : Bool) : (checksum u v z).cost = 1 := by
  dsimp only [checksum]
  split_ifs <;> rfl

theorem core_length {u v : Nat} (hu : u < 13) (hv : v < VF u) (z : Bool) :
    (core u v z).length + 2 = budget u + cost fusionTab u v + hm u := by
  have hf := budget_fit hu hv
  unfold core pads
  simp only [List.length_append, List.length_singleton, List.length_replicate, tie_length,
    segs_len, rootIns_len, zexp]
  omega

theorem core_cost {u v : Nat} (hu : u < 13) (hv : v < VF u) (z : Bool) :
    lcost (core u v z) + 2 = budget u + 10*(cost fusionTab u v + hm u) := by
  have hf := budget_fit hu hv
  unfold core pads
  simp only [lcost_append, lcost_cons, lcost_nil, tie_cost, checksum_cost, segs_lcost,
    rootIns_lcost, lcost_replicate, show NOP.cost = 1 from rfl, mul_one, add_zero, zexp]
  omega

/-- Includes the one JUMP following the straight block. -/
theorem normal_length {u v : Nat} (hu : u < 13) (hv : v < VF u) :
    (normal u v).length + 1 = budget u + cost fusionTab u v + hm u := by
  have h := core_length hu hv false
  simpa only [normal, List.length_append, List.length_singleton, Nat.add_assoc] using h

theorem normal_cost {u v : Nat} (hu : u < 13) (hv : v < VF u) :
    lcost (normal u v) + 1 = budget u + 10*(cost fusionTab u v + hm u) := by
  have h := core_cost hu hv false
  have ht : lcost [if u = 1 then CInstr.xor (hCell 0) (gp 13) (h1Cell 0)
      else .xor (hCell (nextGroup u+1)) (bias (nextGroup u)) (h1Cell (nextGroup u+1))] = 1 := by
    split_ifs <;> rfl
  simpa only [normal, lcost_append, ht, Nat.add_assoc] using h

theorem zero_length {v : Nat} (hv : v < VF 1) :
    (zero v).length + 1 = budget 1 + cost fusionTab 1 v + 1 := by
  have h := core_length (by decide : 1 < 13) hv true
  simp only [zero, List.length_append, List.length_cons, List.length_nil]
  change (core 1 v true).length + 2 = budget 1 + cost fusionTab 1 v + 0 at h
  omega

theorem zero_cost {v : Nat} (hv : v < VF 1) :
    lcost (zero v) + 1 = budget 1 + 10*cost fusionTab 1 v + 1 := by
  have h := core_cost (by decide : 1 < 13) hv true
  have ht : lcost [copy (wCell 0) tfCell, NOP] = 2 := rfl
  rw [zero, lcost_append, ht]
  change lcost (core 1 v true) + 2 = budget 1 + 10*(cost fusionTab 1 v+0) at h
  omega

theorem free_length (s : Nat) : (free s).length + 1 = s+1 := by rw [free, chainOps_length]
theorem free_cost (s : Nat) : lcost (free s) + 1 = 10*s+1 := by rw [free, chainOps_lcost]
theorem prologue_length (a : K) : (prologue a).length + 1 = 16 := by simp [prologue]
theorem prologue_cost (a : K) : lcost (prologue a) + 1 = 25 := by rfl
theorem budget_sum : (order.map budget).sum = 82 := by decide
theorem root_sum : (order.map hm).sum = 1 := by decide

end
end OptimalOTS.FreeLastBlocks
