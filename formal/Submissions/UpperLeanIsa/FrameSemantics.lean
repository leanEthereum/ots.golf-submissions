import Submissions.UpperLeanIsa.FreeLastCompile
import Submissions.UpperLeanIsa.PackedSupport

/-! Shared instruction semantics without the obsolete affine machine's layout,
finite guard certificates or whole-program execution proofs. -/
namespace OptimalOTS.AffineFrames
open LeanerVM.Parameters LeanerVM.Semantics
def firstOperand : Instr → K
  | .xor a _ _ => a
  | .mulNative a _ _ => a
  | .setConstant a _ => a
  | .deref a _ _ _ => a
  | .jump a _ _ => a
  | .blake2s m _ _ _ => m 0

theorem execute_none_of_first {κ : ℕ} (M : MemImage κ) (r : Regs K) (i : Instr)
    (h : M.read (r.fp * firstOperand i) = none) :
    LeanIsa.execute M r i = pure none := by
  cases i <;> simp only [firstOperand] at h <;>
    simp [LeanIsa.execute, LeanerVM.Semantics.execute, h]

end OptimalOTS.AffineFrames

namespace OptimalOTS.AffineVM
open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.HLG3 (HashTable fixed_hash)
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def compile (q : K) : CInstr → Instr
  | .init => .deref (gpow lenCell / q) OptimalOTS.HLG3.LengthGate128.scale (gpow lenCell / q) .fp
  | .xor a b c => .xor (gpow a / q) (gpow b / q) (gpow c / q)
  | .mul a b c => .mulNative (gpow a / q) (gpow b / q) (gpow c / q)
  | .setc a v => .setConstant (gpow a / q) v
  | .blake m0 m1 m2 m3 cv out md =>
      .blake2s ![gpow m0 / q,gpow m1 / q,gpow m2 / q,gpow m3 / q]
        (gpow cv / q) (gpow out / q) (gpow md / q)
  | .dispatch f => .jump (gpow oneCell / q) (gpow (hCell f) / q) (gpow (h1Cell f) / q)
  | .exit => .jump (gpow oneCell / q) (gpow (gpCell 13) / q) (gpow oneCell / q)
  | .entry _ => .xor (gpow 0 / q) 0 0
  | .pad => .xor 0 0 0

section Normal

variable {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (M : MemImage κ) (pc q : K) (hq : q ≠ 0)
include h16 hκ hq

theorem read_relative {c : ℕ} (hc : c < 2 ^ 16) :
    M.read (q * (gpow c / q)) = some (Lx M c) := by
  rw [mul_div_cancel₀ _ hq]
  simpa only [one_mul] using read_one h16 hκ M hc

theorem read_relative_g {c : ℕ} (hc : c+1 < 2 ^ 16) :
    M.read (q * (g * (gpow c / q))) = some (Lx M (c+1)) := by
  rw [← mul_div_assoc,g_mul_gpow]
  exact read_relative h16 hκ M q hq hc

theorem exec_xor {a b c : ℕ} (hb : (CInstr.xor a b c).Bounded) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.xor a b c)) =
      pure (if Lx M c = Lx M a + Lx M b then some ⟨g*pc,q⟩ else none) := by
  obtain ⟨ha,hb,hc⟩ := hb
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩
    (.xor (gpow a / q) (gpow b / q) (gpow c / q))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,read_relative h16 hκ M q hq ha,
    read_relative h16 hκ M q hq hb,read_relative h16 hκ M q hq hc,
    Option.bind_eq_bind,Option.bind_some]
  exact guard_some _

theorem exec_mul {a b c : ℕ} (hb : (CInstr.mul a b c).Bounded) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.mul a b c)) =
      pure (if Lx M c = Lx M a * Lx M b then some ⟨g*pc,q⟩ else none) := by
  obtain ⟨ha,hb,hc⟩ := hb
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩
    (.mulNative (gpow a / q) (gpow b / q) (gpow c / q))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,read_relative h16 hκ M q hq ha,
    read_relative h16 hκ M q hq hb,read_relative h16 hκ M q hq hc,
    Option.bind_eq_bind,Option.bind_some]
  exact guard_some _

theorem exec_setc {a : ℕ} {v : E} (hb : (CInstr.setc a v).Bounded) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.setc a v)) =
      pure (if Lx M a = v then some ⟨g*pc,q⟩ else none) := by
  show pure (LeanerVM.Semantics.execute M ⟨pc,q⟩ (.setConstant (gpow a / q) v)) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,read_relative h16 hκ M q hq hb,
    Option.bind_eq_bind,Option.bind_some]
  exact guard_some _

/-- Rebasing preserves the complete oracle query, including both words of each pair. -/
theorem exec_blake {m0 m1 m2 m3 cv out md : ℕ}
    (hb : (CInstr.blake m0 m1 m2 m3 cv out md).Bounded) :
    LeanIsa.execute M ⟨pc,q⟩ (compile q (.blake m0 m1 m2 m3 cv out md)) =
      (hash (LeanIsa.blake2sQuery ![Lx M m0,Lx M m1,Lx M m2,Lx M m3]
        (Lx M cv) (Lx M (cv+1)) (Lx M md))) >>= fun ans =>
        pure (if LeanIsa.OracleCompressCells ![Lx M m0,Lx M m1,Lx M m2,Lx M m3]
          (Lx M cv) (Lx M (cv+1)) (Lx M out) (Lx M (out+1)) (Lx M md) ans
          then some ⟨g*pc,q⟩ else none) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6⟩ := hb
  simp only [compile,LeanIsa.execute,Matrix.cons_val,Fin.isValue,
    read_relative h16 hκ M q hq c0,read_relative h16 hκ M q hq c1,
    read_relative h16 hκ M q hq c2,read_relative h16 hκ M q hq c3,
    read_relative h16 hκ M q hq (show cv < 2 ^ 16 by omega),read_relative_g h16 hκ M q hq c4,
    read_relative h16 hκ M q hq (show out < 2 ^ 16 by omega),read_relative_g h16 hκ M q hq c5,
    read_relative h16 hκ M q hq c6,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
  rfl

end Normal

def HashSound (Sm : Sem) (B : BlakeRel) : Prop :=
  ∀ m cv0 cv1 o0 o1 md ans,
    ans ∈ Sm.S (hash (LeanIsa.blake2sQuery m cv0 cv1 md)) →
    LeanIsa.OracleCompressCells m cv0 cv1 o0 o1 md ans → B m cv0 cv1 o0 o1 md

theorem hashSound_sim (f : HashTable) : HashSound (simSem f) (oracleRel f) := by
  intro m cv0 cv1 o0 o1 md ans ha hr
  change ans ∈ support (simulateQ (unifFwdAnswerImpl f) _) at ha
  rw [fixed_hash,mem_support_pure_iff] at ha
  subst ans
  exact hr

theorem hashSound_supp : HashSound suppSem trueRel := by
  intro m cv0 cv1 o0 o1 md ans ha hr
  trivial

theorem chainOp_ne_init (readTop : ℕ → ℕ) (k d t dst : ℕ) : chainOp readTop k d t dst ≠ .init := by
  unfold chainOp
  split_ifs <;> intro h <;> cases h

theorem init_not_chainOps (readTop : ℕ → ℕ) (k d dst : ℕ) : CInstr.init ∉ chainOps readTop k d dst := by
  intro h
  obtain ⟨t,ht,he⟩ := mem_chainOps.mp h
  exact chainOp_ne_init readTop k d t dst he.symm

theorem init_not_body (T : Tab) (u x : ℕ) (z : Bool) : CInstr.init ∉ body T u x z := by
  intro hi
  unfold body at hi
  simp only [List.mem_append,List.mem_singleton,List.mem_replicate] at hi
  rcases hi with ((((hi | hi) | hi) | hi) | hi) | hi
  · unfold tie at hi
    split_ifs at hi <;> simp [copy] at hi
  · unfold prodOps prodOp at hi
    split_ifs at hi <;> simp [NOP] at hi
  · obtain ⟨i,hi,hseg⟩ := mem_segs.mp hi
    unfold seg at hseg
    split_ifs at hseg
    · simp [copy] at hseg
    · exact init_not_chainOps _ _ _ _ hseg
    · exact init_not_chainOps _ _ _ _ hseg
  · unfold rootIns at hi
    split_ifs at hi <;> simp at hi
  · cases hi.2
  · unfold nextOp at hi
    split_ifs at hi <;> cases hi

end
end OptimalOTS.AffineVM
