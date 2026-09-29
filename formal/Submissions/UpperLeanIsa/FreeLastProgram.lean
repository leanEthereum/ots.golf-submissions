import Submissions.UpperLeanIsa.FreeLastLayoutData

/-! The complete candidate bytecode, parameterized by its field base. The code
image is concrete, but a safe-base construction and complete machine certificate
are still required before claiming 1089 cycles. -/
namespace OptimalOTS.FreeLastProgram
open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.FreeLastLayout OptimalOTS.FreeLastBlocks
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def compile (q : K) : CInstr → Instr
  | .init => .deref (gpow lenCell/q) OptimalOTS.HLG3.LengthGate128.scale (gpow lenCell/q) .fp
  | .xor a b c => .xor (gpow a/q) (gpow b/q) (gpow c/q)
  | .mul a b c => .mulNative (gpow a/q) (gpow b/q) (gpow c/q)
  | .setc a v => .setConstant (gpow a/q) v
  | .blake m0 m1 m2 m3 cv out md =>
      .blake2s ![gpow m0/q,gpow m1/q,gpow m2/q,gpow m3/q]
        (gpow cv/q) (gpow out/q) (gpow md/q)
  | _ => .xor 0 0 0

def jump (q : K) (target frame : Nat) : Instr :=
  .jump (gpow oneCell/q) (gpow target/q) (gpow frame/q)

def body (r : Row) : List CInstr := match r.body with
  | .group u v z => if z then zero v else normal u v
  | .free s => free s
  | .trap => []

def frame (a : K) (r : Row) : K := gpow r.entry + match r.body with
  | .group u _ _ => if u = 12 then BitVec.ofNat 64 5504 else a^(u+1)
  | .free s => (a^s)⁻¹
  | .trap => 0

def control (q : K) (r : Row) : Instr := match r.body with
  | .group u _ z =>
      if z then jump q exitCell oneCell
      else if u = 1 then jump q (hCell 0) (h1Cell 0)
      else jump q (hCell (nextGroup u+1)) (h1Cell (nextGroup u+1))
  | .free _ => jump q exitCell oneCell
  | .trap => .xor 0 0 0

def initial (a : K) (s : Nat) : Instr :=
  if s < (FreeLastBlocks.prologue a).length then
    compile 1 ((FreeLastBlocks.prologue a).getD s .pad)
  else if s = (FreeLastBlocks.prologue a).length then jump 1 (hCell 1) (h1Cell 1)
  else .xor 0 0 0

def instruction (a : K) (s : Nat) : Instr :=
  if s < 27 then initial a s
  else if s < 262143 then
    let r := candidateTree.lookup s
    let i := s-r.entry
    let b := body r
    if i < b.length then compile (frame a r) (b.getD i .pad)
    else if i = b.length then control (frame a r) r
    else .xor 0 0 0
  else .xor 0 0 0

def program (a : K) : Program where
  logSize := 18
  logSize_le := by decide
  code s := instruction a s.val

theorem valid (a : K) : LeanIsa.BytecodeValid (program a) := by
  constructor
  · change 18 ≤ 18; decide
  · change (instruction a 262143).opcode ≠ .jump
    simp only [instruction, show ¬262143 < 27 by decide, if_false,
      show ¬262143 < 262143 by decide]
    decide

theorem seeded_rows (a : K) : 2^(program a).logSize + 2^16 < LeanIsa.maxSeededRows := by
  change 2^18 + 2^16 < LeanIsa.maxSeededRows
  decide

/-- Every straight body and its final JUMP fit inside the certified interval. -/
theorem body_fits {r : Row} (h : Good r) : (body r).length + 1 ≤ r.length := by
  obtain ⟨hl, hb⟩ := h
  cases hr : r.body with
  | trap =>
    simp only [body, hr, List.length_nil, Nat.zero_add]
    omega
  | free s =>
    simp only [hr] at hb
    simp only [body, hr, free_length, hb.2.2.1, le_refl]
  | group u v z =>
    simp only [hr] at hb
    obtain ⟨hu,hv,hz,hfit,_,_⟩ := hb
    have hc : cost fusionTab u v = band u v :=
      (fusion_cost_eq hu (hv.trans_le (VF_le u hu))).trans (fusion_band_eq hu hv)
    cases z with
    | false =>
      simpa only [body, hr, Bool.false_eq_true, if_false, normal_length hu hv, hc,
        Nat.add_zero] using hfit
    | true =>
      have he := hz rfl
      subst u
      simpa only [body, hr, if_true, zero_length hv, hc, show hm 1 = 0 from rfl,
        Nat.add_zero] using hfit

end
end OptimalOTS.FreeLastProgram
