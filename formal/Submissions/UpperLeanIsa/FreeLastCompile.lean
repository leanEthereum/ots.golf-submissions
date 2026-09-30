import Submissions.UpperLeanIsa.FreeLastProgram

/-! Connect the straight-list accounting to the actual pinned ISA opcodes. -/
namespace OptimalOTS.FreeLastBlocks
open LeanerVM.Parameters OptimalOTS.HLFour
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem tie_straight (u v : Nat) {ci : CInstr} (h : ci ∈ tie u v) : ci.straight = true := by
  unfold tie at h
  split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  all_goals first | (subst ci; rfl) | (rcases h with rfl | rfl <;> rfl)

theorem checksum_straight (u v : Nat) (z : Bool) : (checksum u v z).straight = true := by
  dsimp only [checksum]
  split_ifs <;> rfl

theorem core_straight (u v : Nat) (z : Bool) {ci : CInstr} (h : ci ∈ core u v z) :
    ci.straight = true := by
  unfold core at h
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at h
  rcases h with (((h | h) | h) | h) | h
  · exact tie_straight u v h
  · subst ci; exact checksum_straight u v z
  · obtain ⟨i, _, hi⟩ := mem_segs.mp h
    exact seg_straight fusionTab ci hi
  · exact rootIns_straight fusionTab ci h
  · rw [h.2]; rfl

theorem normal_straight (u v : Nat) {ci : CInstr} (h : ci ∈ normal u v) : ci.straight = true := by
  simp only [normal, List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · exact core_straight u v false h
  · subst ci; split_ifs <;> rfl

theorem zero_straight (v : Nat) {ci : CInstr} (h : ci ∈ zero v) : ci.straight = true := by
  simp only [zero, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h
  · exact core_straight 1 v true h
  · subst ci; rfl
  · subst ci; rfl

theorem free_straight (s : Nat) {ci : CInstr} (h : ci ∈ free s) : ci.straight = true := by
  obtain ⟨t, _, rfl⟩ := mem_chainOps.mp h
  exact chainOp_straight ..

theorem prologue_straight (a : K) {ci : CInstr} (h : ci ∈ prologue a) : ci.straight = true := by
  simp only [prologue, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
    rfl
  all_goals subst ci; rfl

end
end OptimalOTS.FreeLastBlocks

namespace OptimalOTS.FreeLastProgram
open LeanerVM.Parameters OptimalOTS.HLFour OptimalOTS.FreeLastLayout OptimalOTS.FreeLastBlocks
noncomputable section

theorem compile_weight (q : K) {ci : CInstr} (h : ci.straight = true) :
    LeanIsa.weight (compile q ci).opcode = ci.cost := by
  cases ci <;> first | rfl | cases h

theorem compile_list_cost (q : K) (cs : List CInstr)
    (h : ∀ ci ∈ cs, ci.straight = true) :
    ((cs.map (compile q)).map (fun i => LeanIsa.weight i.opcode)).sum = lcost cs := by
  unfold lcost
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro ci hci
  exact compile_weight q (h ci hci)

theorem body_straight (r : Row) {ci : CInstr} (h : ci ∈ body r) : ci.straight = true := by
  unfold body at h
  cases hr : r.body with
  | trap => simp [hr] at h
  | free s => rw [hr] at h; exact free_straight s h
  | group u v z =>
    rw [hr] at h
    dsimp only at h
    split_ifs at h
    · exact zero_straight v h
    · exact normal_straight u v h

theorem compiled_body_cost (a : K) (r : Row) :
    (((body r).map (compile (frame a r))).map (fun i => LeanIsa.weight i.opcode)).sum =
      lcost (body r) := compile_list_cost _ _ (fun _ => body_straight r)

theorem jump_weight (q : K) (t f : Nat) : LeanIsa.weight (jump q t f).opcode = 1 := rfl

end
end OptimalOTS.FreeLastProgram
