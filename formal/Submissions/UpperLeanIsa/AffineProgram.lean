import Submissions.UpperLeanIsa.AffineCodec
import Submissions.UpperLeanIsa.FourMachineDecode

/-! A fixed affine-frame bytecode candidate. Each block starts with its first
useful instruction; the old entry jump becomes trailing padding. The security
certificate is inherited from `AffineCodec`; the full machine certificate is
not yet assembled. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing fourteen initialized constants, in execution-stage order. -/
def biasCell (f : ℕ) : ℕ := if f = 0 then gCell else cCell f

def stageIndex (f : ℕ) : ℕ := if f = 0 then 13 else f-1

theorem stageIndex_lt {f : ℕ} (hf : f < 14) : stageIndex f < 14 := by
  unfold stageIndex
  split_ifs <;> omega

/-- Replace a hint multiplication by the sum of its destination and stage bias. -/
def rehint : CInstr → CInstr
  | .mul a b c => if b = gCell then .xor a (biasCell (c - h1Cell 0)) c else .mul a b c
  | ci => ci

theorem rehint_cell0 (ci : CInstr) : (rehint ci).cell0 = ci.cell0 := by
  cases ci <;> simp only [rehint, CInstr.cell0]
  split_ifs <;> rfl

theorem rehint_cost (ci : CInstr) : (rehint ci).cost = ci.cost := by
  cases ci <;> simp only [rehint, CInstr.cost]
  split_ifs <;> rfl

theorem rehint_straight (ci : CInstr) : (rehint ci).straight = ci.straight := by
  cases ci <;> simp only [rehint, CInstr.straight]
  split_ifs <;> rfl

inductive Place
  | initial (offset : ℕ)
  | body (stage value offset : ℕ)
  | trap

/-- Slot geometry stays identical to the complete 1124-cycle construction. -/
def place (s : ℕ) : Place :=
  if s < 27 then .initial s
  else if s < gEnd then .body ((dec s).1 + 1) (dec s).2.1 (dec s).2.2
  else if s < baseF then .trap
  else if s < baseF + 4352 then .body 0 ((s-baseF)/68) ((s-baseF)%68)
  else .trap

/-- Cell instructions before relative operand encoding. Only immediate values
depend on `a`, so choosing the base cannot change the layout. -/
def raw (T : Tab) (a : K) : Place → CInstr
  | .trap => .pad
  | .initial s =>
      if s < 13 then .setc (cCell (s+1)) (ofK (a ^ (s+1)))
      else if s = 13 then .init
      else if s = 14 then .setc gCell (ofK (a ^ 14))
      else if s = 15 then .blake msgLo msgHi nonceCell pkCell oneCell idxCell gCell
      else if s = 16 then .xor (hCell 0) gCell (h1Cell 0)
      else if s = 17 then .dispatch 0
      else .pad
  | .body f x i =>
      if f = 0 then
        if i = 0 then .setc (gpCell 0) (ofK (gpow sentinel / a ^ 77 * a ^ x))
        else if i ≤ x then chainOp 0 x (i-1) tfCell
        else if i = x+1 then copy (if x = 0 then wCell 0 else tfCell) tfCell
        else if i = x+2 then .xor (hCell 1) (cCell 1) (h1Cell 1)
        else if i = x+3 then .dispatch 1
        else .pad
      else
        let b := body T (f-1) x false
        if i < b.length then rehint (b.getD i .pad)
        else if i = b.length then ctlOf f x
        else .pad

theorem raw_cell0 (T : Tab) (a b : K) (p : Place) : (raw T a p).cell0 = (raw T b p).cell0 := by
  cases p with
  | trap => rfl
  | initial s =>
    by_cases h : s < 13
    · simp only [raw,if_pos h,CInstr.cell0]
    · by_cases h13 : s = 13
      · simp only [raw,if_neg h,if_pos h13]
      · by_cases h14 : s = 14
        · simp only [raw,if_neg h,if_neg h13,if_pos h14,CInstr.cell0]
        · simp only [raw,if_neg h,if_neg h13,if_neg h14]
  | body f x i =>
    by_cases hf : f = 0
    · by_cases hi : i = 0
      · simp only [raw,if_pos hf,if_pos hi,CInstr.cell0]
      · simp only [raw,if_pos hf,if_neg hi]
    · simp only [raw,if_neg hf]

theorem raw_pad (T : Tab) (a b : K) (p : Place) : raw T a p = .pad ↔ raw T b p = .pad := by
  cases p <;> simp only [raw] <;> split_ifs <;> rfl

def isPad : CInstr → Bool
  | .pad => true
  | _ => false

theorem isPad_eq_true (ci : CInstr) : isPad ci = true ↔ ci = .pad := by
  cases ci <;> simp [isPad]

/-- The first cells and block entries determine the avoidance constraints. -/
def layout (T : Tab) (s : AffineFrames.Slot) : AffineFrames.SlotShape :=
  let p := place s.val
  let ci := raw T 1 p
  if isPad ci then .trap
  else if hc : ci.cell0 < 2 ^ 16 then
    match p with
    | .initial _ => .initial ⟨ci.cell0,hc⟩
    | .body f x _ =>
        if hf : f < 14 then
          if he : ent f x < 2 ^ 18 then
            .body ⟨⟨stageIndex f,stageIndex_lt hf⟩,⟨ent f x,he⟩,⟨ci.cell0,hc⟩⟩
          else .trap
        else .trap
    | .trap => .trap
  else .trap

def base (T : Tab) : K := AffineFrames.safeBase (layout T)

/-- Compile cell operands in frame `q`; dispatch now uses the affine hint as fp. -/
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

theorem compile_first (q : K) {ci : CInstr} (h : ci ≠ .pad) :
    AffineFrames.firstOperand (compile q ci) = gpow ci.cell0 / q := by
  cases ci <;> first | rfl | exact (h rfl).elim

def instrAt (T : Tab) (s : AffineFrames.Slot) : Instr :=
  match layout T s with
  | .trap => .xor 0 0 0
  | .initial _ => compile 1 (raw T (base T) (place s))
  | .body d => compile (AffineFrames.frame (layout T) d.stage d.entry) (raw T (base T) (place s))

def program (T : Tab) : Program where
  logSize := 18
  logSize_le := by decide
  code := instrAt T

def scheme (T : Tab) : OracleAlgorithm.Scheme := (AffineCodec.params (layout T)).scheme

theorem admissible (T : Tab) : (scheme T).Admissible := AffineCodec.admissible (layout T)

theorem secure (T : Tab) : (scheme T).Secure := AffineCodec.secure (layout T)

theorem halt_is_trap (T : Tab) : instrAt T ⟨262143,by decide⟩ = .xor 0 0 0 := by
  have hp : place 262143 = .trap := by norm_num [place,gEnd,baseF]
  simp only [instrAt,layout,hp,raw,isPad,ite_true]

theorem seeded_rows : 2 ^ (18 : ℕ) + 2 ^ (16 : ℕ) < LeanIsa.maxSeededRows := by decide

theorem bytecode_valid (T : Tab) : LeanIsa.BytecodeValid (program T) := by
  refine ⟨by change 18 ≤ 18; decide, ?_⟩
  change (instrAt T ⟨262143,by decide⟩).opcode ≠ .jump
  rw [halt_is_trap]
  decide

end
end OptimalOTS.AffineVM
