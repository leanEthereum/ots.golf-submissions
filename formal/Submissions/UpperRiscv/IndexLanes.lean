import Submissions.UpperRiscv.ChainContext

/-!
# The lane words of the index phase

Each of the eight lane words is one shift, one mask, an accumulation into `x27`, a subtraction
from the broadcast jump base and a store (`laneWord_effect`). Together they leave in `x27` the
sum of the lane words and in memory the dispatch halfwords (`lanesUpTo_effect`).
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64

/-- The address of lane word `j = 2 w + i`. -/
def laneWordAddr (j : ℕ) : ℕ := laneBase + 8 * j

theorem laneOff_eq (w i : ℕ) : laneBase + laneOff w i = laneWordAddr (2 * w + i) := by
  unfold laneOff laneWordAddr; omega

/-- The store offset of lane word `(w, i)` from the message pointer. -/
theorem laneStore_addr (w i : ℕ) (hw : w < 4) (hi : i < 2) :
    W messageAddr + signExtend12 (BitVec.ofInt 12 ((laneBase + laneOff w i : ℤ) - messageAddr)) =
      W (laneWordAddr (2 * w + i)) := by
  have e : BitVec.ofInt 12 ((laneBase + laneOff w i : ℤ) - messageAddr) =
      imm12 ((laneBase + laneOff w i : ℤ) - messageAddr) := rfl
  rw [e, W_add_imm _ _ (by simp only [laneBase, laneOff, messageAddr]; omega)
    (by simp only [laneBase, laneOff, messageAddr]; omega)
    (by simp only [laneBase, laneOff, messageAddr]; omega)
    (by simp only [messageAddr]; omega)]
  congr 1
  simp only [laneBase, laneOff, messageAddr, laneWordAddr]
  omega

theorem srcReg_ne (w : ℕ) : srcReg w ≠ .x26 ∧ srcReg w ≠ .x27 ∧ srcReg w ≠ .x10 := by
  unfold srcReg; split <;> decide

theorem maskReg_ne (w : ℕ) : maskReg w ≠ .x26 ∧ maskReg w ≠ .x27 ∧ maskReg w ≠ .x10 := by
  unfold maskReg; split_ifs <;> decide

structure LaneEffect (a b : MachineState) (w i : ℕ) : Prop where
  acc : b.getReg .x27 = if w = 0 ∧ i = 0 then laneValue (a.getReg (srcReg w)) i (a.getReg (maskReg w))
    else a.getReg .x27 + laneValue (a.getReg (srcReg w)) i (a.getReg (maskReg w))
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = if addr = W (laneWordAddr (2 * w + i)) then
    a.getReg .x3 - laneValue (a.getReg (srcReg w)) i (a.getReg (maskReg w)) else a.getMem addr

/-- Everything of a lane word but its store. -/
def lanePre (w i : ℕ) : Code :=
  let dst : Reg := if w = 0 ∧ i = 0 then .x27 else .x26
  (if i = 0 then [.SLLI dst (srcReg w) 2] else [.SRLI dst (srcReg w) 6]) ++
  [.AND dst dst (maskReg w)] ++ (if w = 0 ∧ i = 0 then [] else [.ADD .x27 .x27 .x26]) ++
  [.SUB .x26 .x3 dst]

theorem laneWord_parts (w i : ℕ) :
    laneWord w i = lanePre w i ++
      [.SD .x10 .x26 (BitVec.ofInt 12 ((laneBase + laneOff w i : ℤ) - messageAddr))] := by
  simp [laneWord, lanePre]

theorem lanePre_ready (a : MachineState) (w i : ℕ) (hw : w < 4) (hi : i < 2) :
    Riscv.LinearReady a (lanePre w i) := by
  interval_cases w <;> interval_cases i <;>
    simp [lanePre, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

/-- The register effect of the lane computation before its store. -/
theorem lanePre_regs (a : MachineState) (w i : ℕ) (hw : w < 4) (hi : i < 2) :
    let b := (lanePre w i).foldl execInstrBr a
    b.getReg .x27 = (if w = 0 ∧ i = 0 then laneValue (a.getReg (srcReg w)) i (a.getReg (maskReg w))
      else a.getReg .x27 + laneValue (a.getReg (srcReg w)) i (a.getReg (maskReg w))) ∧
    b.getReg .x26 = a.getReg .x3 - laneValue (a.getReg (srcReg w)) i (a.getReg (maskReg w)) ∧
    (∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r) ∧
    (∀ addr, b.getMem addr = a.getMem addr) := by
  interval_cases w <;> interval_cases i <;>
    simp [lanePre, execInstrBr, getReg_setReg_ite, laneValue, srcReg, maskReg] <;>
    (try constructor) <;> (try intro r h26 h27) <;> simp_all

theorem laneWord_effect (a : MachineState) (w i : ℕ) (hw : w < 4) (hi : i < 2)
    (h10 : a.getReg .x10 = W messageAddr) :
    LaneEffect a ((laneWord w i).foldl execInstrBr a) w i := by
  obtain ⟨r27, r26, rr, rm⟩ := lanePre_regs a w i hw hi
  rw [laneWord_parts, List.foldl_append]
  generalize hb : (lanePre w i).foldl execInstrBr a = b at r27 r26 rr rm
  have b10 : b.getReg .x10 = W messageAddr := by rw [rr .x10 (by decide) (by decide), h10]
  have st : b.getReg .x10 +
      signExtend12 (BitVec.ofInt 12 ((laneBase + laneOff w i : ℤ) - messageAddr)) =
      W (laneWordAddr (2 * w + i)) := by
    rw [b10, laneStore_addr w i hw hi]
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_store]
    exact r27
  · intro r h26 h27
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_store]
    exact rr r h26 h27
  · intro addr
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getMem_setPC,
      getMem_setMem_ite, st, r26, rm]

theorem laneWord_ready (a : MachineState) (w i : ℕ) (hw : w < 4) (hi : i < 2)
    (h10 : a.getReg .x10 = W messageAddr) :
    Riscv.LinearReady a (laneWord w i) := by
  obtain ⟨-, -, rr, -⟩ := lanePre_regs a w i hw hi
  rw [laneWord_parts]
  refine (lanePre_ready a w i hw hi).append ⟨rfl, ?_, trivial⟩
  show isValidDwordAccess (_ + _) = true
  rw [rr .x10 (by decide) (by decide), h10, laneStore_addr w i hw hi]
  exact dword_ok _ (by unfold laneWordAddr laneBase; omega) (by unfold laneWordAddr laneBase; omega)
    (by unfold laneWordAddr laneBase; omega)

/-! ## All eight lane words -/

/-- Lane word `j` of the state's index words. -/
def laneOf (a : MachineState) (j : ℕ) : Word :=
  laneValue (a.getReg (srcReg (j / 2))) (j % 2) (a.getReg (maskReg (j / 2)))

/-- The running sum of the first `n` lane words. -/
def laneSum (a : MachineState) : ℕ → Word
  | 0 => 0
  | n + 1 => laneSum a n + laneOf a n

/-- The first `n` lane words. -/
def lanesUpTo (n : ℕ) : Code := (List.range n).flatMap fun j => laneWord (j / 2) (j % 2)

theorem lanes_eq : lanes = lanesUpTo 8 := rfl

theorem lanesUpTo_succ (n : ℕ) : lanesUpTo (n + 1) = lanesUpTo n ++ laneWord (n / 2) (n % 2) := by
  simp [lanesUpTo, List.range_succ, List.flatMap_append]

/-- The effect of the first `n` lane words. -/
structure LanesEffect (a b : MachineState) (n : ℕ) : Prop where
  acc : 1 ≤ n → b.getReg .x27 = laneSum a n
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  stored : ∀ j, j < n → b.getMem (W (laneWordAddr j)) = a.getReg .x3 - laneOf a j
  frame : ∀ addr, (∀ j, j < n → addr ≠ W (laneWordAddr j)) → b.getMem addr = a.getMem addr

theorem laneWordAddr_ne (i j : ℕ) (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    W (laneWordAddr i) ≠ W (laneWordAddr j) :=
  W_ne (by unfold laneWordAddr laneBase; omega) (by unfold laneWordAddr laneBase; omega)
    (by unfold laneWordAddr; omega)

theorem lanesUpTo_effect (a : MachineState) (h10 : a.getReg .x10 = W messageAddr) :
    ∀ n, n ≤ 8 → Riscv.LinearReady a (lanesUpTo n) ∧
      LanesEffect a ((lanesUpTo n).foldl execInstrBr a) n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨trivial, ?_⟩
    refine ⟨fun h => absurd h (by norm_num), fun r _ _ => rfl, fun j hj => absurd hj (by omega),
      fun addr _ => rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨ready, eff⟩ := ih (by omega)
    set b := (lanesUpTo n).foldl execInstrBr a with hb
    have b10 : b.getReg .x10 = W messageAddr := by rw [eff.regs .x10 (by decide) (by decide), h10]
    have hw : n / 2 < 4 := by omega
    have hi : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have e := laneWord_effect b (n / 2) (n % 2) hw hi b10
    have ready' := laneWord_ready b (n / 2) (n % 2) hw hi b10
    have hj : 2 * (n / 2) + n % 2 = n := by omega
    have wordEq : b.getReg (srcReg (n / 2)) = a.getReg (srcReg (n / 2)) :=
      eff.regs _ (srcReg_ne _).1 (srcReg_ne _).2.1
    have maskEq : b.getReg (maskReg (n / 2)) = a.getReg (maskReg (n / 2)) :=
      eff.regs _ (maskReg_ne _).1 (maskReg_ne _).2.1
    have baseEq : b.getReg .x3 = a.getReg .x3 := eff.regs _ (by decide) (by decide)
    rw [lanesUpTo_succ, List.foldl_append]
    refine ⟨ready.append ready', ?_⟩
    rw [← hb]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _
      rw [e.acc, wordEq, maskEq]
      show _ = laneSum a n + laneOf a n
      by_cases h0 : n / 2 = 0 ∧ n % 2 = 0
      · rw [if_pos h0]
        have : n = 0 := by omega
        subst this
        simp [laneSum, laneOf]
      · rw [if_neg h0, eff.acc (by omega)]
        rfl
    · intro r h26 h27
      rw [e.regs r h26 h27, eff.regs r h26 h27]
    · intro j hj'
      rw [e.mem]
      rcases Nat.lt_or_ge j n with lt | ge
      · rw [if_neg (by rw [hj]; exact laneWordAddr_ne j n (by omega) (by omega) (by omega)),
          eff.stored j lt]
      · obtain rfl : j = n := by omega
        rw [if_pos (by rw [hj]), wordEq, maskEq, baseEq]
        rfl
    · intro addr hout
      rw [e.mem, if_neg (by rw [hj]; exact hout n (by omega)),
        eff.frame addr (fun j hj' => hout j (by omega))]

end OptimalOTS.Riscv2Program
