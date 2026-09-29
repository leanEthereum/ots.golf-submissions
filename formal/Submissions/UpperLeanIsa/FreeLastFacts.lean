import Submissions.UpperLeanIsa.FreeLastPrefix
import Submissions.UpperLeanIsa.FreeLastPathCost
import Submissions.UpperLeanIsa.FreeLastVariant

namespace OptimalOTS.FreeLastVM
open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.FreeLastBase (base)
open OptimalOTS.FreeLastLayout
open OptimalOTS.HLG3 (natV)
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem checksum_embed_one : ofK (1 : K) = 1 := by
  have h := ofK_mul 1 1
  rw [mul_one] at h
  exact (mul_eq_left₀ ofK_one_ne_zero).mp h.symm

theorem checksum_embed_pow (a : K) (n : ℕ) : ofK (a ^ n) = (ofK a) ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using checksum_embed_one
  | succ n ih => rw [pow_succ,ofK_mul,ih,pow_succ]

theorem checksum_embed_ne_zero {a : K} (ha : a ≠ 0) : (ofK a : E) ≠ 0 := by
  intro h
  apply ha
  have hh := congrArg (fun z : E => z.limb 0) h
  simpa only [limb_ofK_zero,limb_zero] using hh

theorem checksum_embed_div (a b : K) (hb : b ≠ 0) :
    ofK (a / b) = ofK a / ofK b := by
  apply (eq_div_iff (checksum_embed_ne_zero hb)).mpr
  rw [← ofK_mul,div_mul_cancel₀ _ hb]

section Prologue
variable {B : BlakeRel} {v : Nat → E} (hp : ∀ ci ∈ prefixCode 16, ci.RelB B v)
include hp
theorem pro_one : v oneCell = oneV := by
  have h := hp _ (prefixCode_mem (i:=12) (by decide : 12 < 16))
  exact h.1

theorem pro_length : v lenCell = natV 5504 := by
  have h := hp _ (prefixCode_mem (i:=12) (by decide : 12 < 16))
  exact h.2

theorem pro_c {c : ℕ} (hc : c ≤ 12) : v (cCell c) = ofK (base ^ c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · simpa only [cCell,ite_true,pow_zero,oneV,oneCell] using pro_one hp
  · have h := hp _ (prefixCode_mem (i:=c-1) (by omega : c-1 < 16))
    simpa only [initialRaw_first (show c-1 < 12 by omega),Nat.sub_add_cancel hc0,CInstr.RelB] using h


def stageBias (u : Nat) : K := if u = 12 then AffineFrames.lengthK else base^(u+1)

theorem pro_bias {u : Nat} (hu : u < 13) : v (FreeLastBlocks.bias u) = ofK (stageBias u) := by
  by_cases he : u = 12
  · subst u
    exact (pro_length hp).trans (OptimalOTS.HLG3.LengthGate128.natV_ofK (by decide))
  · simp only [FreeLastBlocks.bias,stageBias,if_neg he]
    exact pro_c hp (by omega)

end Prologue

def Hint (mem : Nat → E) (u : Nat) : Prop :=
  mem (h1Cell (u+1)) = mem (hCell (u+1)) + ofK (stageBias u)

theorem pro_hint {B : BlakeRel} {mem : Nat → E}
    (hp : ∀ ci ∈ prefixCode 16, ci.RelB B mem) : Hint mem 0 := by
  have hx := hp _ (prefixCode_mem (i:=15) (by decide : 15 < 16))
  change mem (h1Cell 1) = mem (hCell 1)+mem (FreeLastBlocks.bias 0) at hx
  rw [pro_bias hp (by decide)] at hx
  exact hx

def unit (j : Nat) : Nat := if j = 0 then 0 else if j = 12 then 1 else j+1

theorem unit_lt {j : Nat} (hj : j < 13) : unit j < 13 := by
  unfold unit; split_ifs <;> omega

theorem unit_ne_one {j : Nat} (hj : j < 12) : unit j ≠ 1 := by
  unfold unit; split_ifs <;> omega

theorem unit_position {j : Nat} (hj : j < 13) : FreeLastBlocks.position (unit j) = j := by
  interval_cases j <;> rfl

theorem unit_next {j : Nat} (hj : j < 12) : FreeLastBlocks.nextGroup (unit j) = unit (j+1) := by
  interval_cases j <;> rfl

theorem unit_order : (List.range 13).map unit = FreeLastBlocks.order := by decide

def nextTarget (u : Nat) (z : Bool) : Nat :=
  if z then FreeLastBlocks.exitCell else if u = 1 then hCell 0 else hCell (FreeLastBlocks.nextGroup u+1)
def nextFrame (u : Nat) (z : Bool) : Nat :=
  if z then oneCell else if u = 1 then h1Cell 0 else h1Cell (FreeLastBlocks.nextGroup u+1)

def groupBody (u v : Nat) (z : Bool) : List CInstr :=
  if z then FreeLastBlocks.zero v else FreeLastBlocks.normal u v

theorem core_rel {B : BlakeRel} {mem : Nat → E} {u v : Nat} {z : Bool}
    (hz : z = true → u = 1) (h : ∀ ci ∈ groupBody u v z, ci.RelB B mem) :
    ∀ ci ∈ FreeLastBlocks.core u v z, ci.RelB B mem := by
  cases z with
  | false => exact fun ci hi => h ci (List.mem_append_left _ hi)
  | true => have hu := hz rfl; subst u; exact fun ci hi => h ci (List.mem_append_left _ hi)

theorem next_hint {B : BlakeRel} {mem : Nat → E} {u v : Nat}
    (hp : ∀ ci ∈ prefixCode 16, ci.RelB B mem) (hu : u < 13) (hn : u ≠ 1)
    (hb : ∀ ci ∈ FreeLastBlocks.normal u v, ci.RelB B mem) :
    Hint mem (FreeLastBlocks.nextGroup u) := by
  have hh := hb (.xor (hCell (FreeLastBlocks.nextGroup u+1))
      (FreeLastBlocks.bias (FreeLastBlocks.nextGroup u)) (h1Cell (FreeLastBlocks.nextGroup u+1)))
    (by simp only [FreeLastBlocks.normal,if_neg hn,List.mem_append,List.mem_singleton,or_true])
  change mem (h1Cell (FreeLastBlocks.nextGroup u+1)) =
    mem (hCell (FreeLastBlocks.nextGroup u+1))+mem (FreeLastBlocks.bias (FreeLastBlocks.nextGroup u)) at hh
  have hnext : FreeLastBlocks.nextGroup u < 13 := by
    unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
  rwa [pro_bias hp hnext] at hh

theorem hint_incoming {mem : Nat → E} {u : Fin 13} (h : Hint mem u.val)
    {s : Nat} (ht : (mem (hCell (u.val+1))).limb 0 = gpow s) :
    (mem (h1Cell (u.val+1))).limb 0 = FreeLastGuard.incoming (FreeLastGuard.stageFlow u) s := by
  rw [h,limb_add,limb_ofK_zero,ht]
  by_cases hu : u.val < 12
  · simp only [stageBias,show u.val ≠ 12 by omega,if_false,FreeLastGuard.incoming,
      FreeLastGuard.stageFlow,FreeLastSelect.exponent,FreeLastSelect.constant,if_pos hu,zpow_natCast,add_comm]
  · have hu12 : u.val = 12 := by have := u.isLt; omega
    simp only [stageBias,hu12,if_true,FreeLastGuard.incoming,
      FreeLastGuard.stageFlow,FreeLastSelect.exponent,FreeLastSelect.constant,
      show ¬(12 : Nat) < 12 by decide,if_false,zpow_zero]
    exact ((add_comm _ _).trans ((sub_add_cancel _ _).trans (add_comm _ _))).symm

theorem stage_frame {s u v : Nat} {z : Bool} (hu : u < 13)
    (hb : (candidateTree.lookup s).body = .group u v z) (he : (candidateTree.lookup s).entry = s) :
    FreeLastGuard.incoming (FreeLastGuard.stageFlow ⟨u,hu⟩) s =
      FreeLastProgram.frame base (candidateTree.lookup s) := by
  by_cases hp : u < 12
  · simp only [FreeLastGuard.incoming,FreeLastGuard.stageFlow,FreeLastSelect.exponent,
      FreeLastSelect.constant,if_pos hp,zpow_natCast,FreeLastProgram.frame,hb,he,
      show u ≠ 12 by omega,if_false,add_comm]
  · have hu12 : u = 12 := by omega
    subst u
    simp only [FreeLastGuard.incoming,FreeLastGuard.stageFlow,FreeLastSelect.exponent,
      FreeLastSelect.constant,if_neg hp,zpow_zero,FreeLastProgram.frame,hb,he,if_true]
    exact (add_comm _ _).trans ((sub_add_cancel _ _).trans (add_comm _ _))

end
end OptimalOTS.FreeLastVM
