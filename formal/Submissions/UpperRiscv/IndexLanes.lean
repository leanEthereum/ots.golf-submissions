import Submissions.UpperRiscv.ChainContext

/-!
# The lane words of the index phase

Each of the eight lane words is one shift, one mask, an accumulation into `x27`, a subtraction
from its broadcast jump base and a store (`laneWord_effect`). Together they leave in `x27` the
sum of the lane words and in memory the dispatch halfwords (`lanes_effect`).
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64

/-- The register holding index word `w`. -/
def wordReg (w : ℕ) : Reg := if w = 0 then .x20 else .x21

/-- The register holding broadcast jump base `w`. -/
def baseReg (w : ℕ) : Reg := if w = 0 then .x24 else .x25

/-- The address of lane word `j`. -/
def laneWordAddr (j : ℕ) : ℕ := dataAddr + 64 + 8 * j

structure LaneEffect (a b : MachineState) (w i : ℕ) : Prop where
  acc : b.getReg .x27 = if w = 0 ∧ i = 0 then laneValue (a.getReg (wordReg w)) i
    else a.getReg .x27 + laneValue (a.getReg (wordReg w)) i
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = if addr = W (laneWordAddr (4 * w + i)) then
    a.getReg (baseReg w) - laneValue (a.getReg (wordReg w)) i else a.getMem addr

/-- Everything of a lane word but its store. -/
def lanePre (w i : ℕ) : Code :=
  let src : Reg := if w = 0 then .x20 else .x21
  let base : Reg := if w = 0 then .x24 else .x25
  let dst : Reg := if w = 0 ∧ i = 0 then .x27 else .x26
  (if i = 0 then [.SLLI dst src 3] else [.SRLI dst src (BitVec.ofNat 6 (4 * i - 3))]) ++
  [.AND dst dst .x22] ++ (if w = 0 ∧ i = 0 then [] else [.ADD .x27 .x27 .x26]) ++
  [.SUB .x26 base dst]

theorem laneWord_parts (w i : ℕ) :
    laneWord w i = lanePre w i ++ [.SD .x12 .x26 (BitVec.ofNat 12 (64 + 8 * (4 * w + i)))] := by
  simp [laneWord, lanePre]

theorem lanePre_ready (a : MachineState) (w i : ℕ) (hw : w < 2) (hi : i < 4) :
    Riscv.LinearReady a (lanePre w i) := by
  interval_cases w <;> interval_cases i <;>
    simp [lanePre, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

/-- The register effect of the lane computation before its store. -/
theorem lanePre_regs (a : MachineState) (w i : ℕ) (hw : w < 2) (hi : i < 4)
    (h22 : a.getReg .x22 = W (broadcast 120)) :
    let b := (lanePre w i).foldl execInstrBr a
    b.getReg .x27 = (if w = 0 ∧ i = 0 then laneValue (a.getReg (wordReg w)) i
      else a.getReg .x27 + laneValue (a.getReg (wordReg w)) i) ∧
    b.getReg .x26 = a.getReg (baseReg w) - laneValue (a.getReg (wordReg w)) i ∧
    (∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r) ∧
    (∀ addr, b.getMem addr = a.getMem addr) := by
  interval_cases w <;> interval_cases i <;>
    simp [lanePre, execInstrBr, getReg_setReg_ite, h22, laneValue, wordReg, baseReg] <;>
    (try constructor) <;> (try intro r h26 h27) <;> simp_all

theorem laneWord_effect (a : MachineState) (w i : ℕ) (hw : w < 2) (hi : i < 4)
    (h12 : a.getReg .x12 = W dataAddr) (h22 : a.getReg .x22 = W (broadcast 120)) :
    LaneEffect a ((laneWord w i).foldl execInstrBr a) w i := by
  obtain ⟨r27, r26, rr, rm⟩ := lanePre_regs a w i hw hi h22
  rw [laneWord_parts, List.foldl_append]
  generalize hb : (lanePre w i).foldl execInstrBr a = b at r27 r26 rr rm
  have b12 : b.getReg .x12 = W dataAddr := by rw [rr .x12 (by decide) (by decide), h12]
  have st : b.getReg .x12 + signExtend12 (BitVec.ofNat 12 (64 + 8 * (4 * w + i))) =
      W (laneWordAddr (4 * w + i)) := by
    rw [b12, signExtend12_nat _ (by omega), W_add]
    unfold laneWordAddr
    congr 1
    omega
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

theorem laneWord_ready (a : MachineState) (w i : ℕ) (hw : w < 2) (hi : i < 4)
    (h12 : a.getReg .x12 = W dataAddr) (h22 : a.getReg .x22 = W (broadcast 120)) :
    Riscv.LinearReady a (laneWord w i) := by
  obtain ⟨-, -, rr, -⟩ := lanePre_regs a w i hw hi h22
  rw [laneWord_parts]
  refine (lanePre_ready a w i hw hi).append ⟨rfl, ?_, trivial⟩
  show isValidDwordAccess (_ + _) = true
  rw [rr .x12 (by decide) (by decide), h12, signExtend12_nat _ (by omega), W_add]
  exact dword_ok _ (by unfold dataAddr; omega) (by unfold dataAddr; omega)
    (by unfold dataAddr; omega)

/-! ## All eight lane words -/

/-- Lane word `j` of the state's index words. -/
def laneOf (a : MachineState) (j : ℕ) : Word := laneValue (a.getReg (wordReg (j / 4))) (j % 4)

/-- The running sum of the first `n` lane words. -/
def laneSum (a : MachineState) : ℕ → Word
  | 0 => 0
  | n + 1 => laneSum a n + laneOf a n

/-- The first `n` lane words. -/
def lanesUpTo (n : ℕ) : Code := (List.range n).flatMap fun j => laneWord (j / 4) (j % 4)

theorem lanes_eq : lanes = lanesUpTo 8 := rfl

theorem lanesUpTo_succ (n : ℕ) : lanesUpTo (n + 1) = lanesUpTo n ++ laneWord (n / 4) (n % 4) := by
  simp [lanesUpTo, List.range_succ, List.flatMap_append]

/-- The effect of the first `n` lane words. -/
structure LanesEffect (a b : MachineState) (n : ℕ) : Prop where
  acc : 1 ≤ n → b.getReg .x27 = laneSum a n
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  stored : ∀ j, j < n → b.getMem (W (laneWordAddr j)) = a.getReg (baseReg (j / 4)) - laneOf a j
  frame : ∀ addr, (∀ j, j < n → addr ≠ W (laneWordAddr j)) → b.getMem addr = a.getMem addr

theorem laneWordAddr_ne (i j : ℕ) (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    W (laneWordAddr i) ≠ W (laneWordAddr j) :=
  W_ne (by unfold laneWordAddr dataAddr; omega) (by unfold laneWordAddr dataAddr; omega)
    (by unfold laneWordAddr; omega)

theorem lanesUpTo_effect (a : MachineState) (h12 : a.getReg .x12 = W dataAddr)
    (h22 : a.getReg .x22 = W (broadcast 120)) :
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
    have b12 : b.getReg .x12 = W dataAddr := by rw [eff.regs .x12 (by decide) (by decide), h12]
    have b22 : b.getReg .x22 = W (broadcast 120) := by
      rw [eff.regs .x22 (by decide) (by decide), h22]
    have hw : n / 4 < 2 := by omega
    have hi : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have e := laneWord_effect b (n / 4) (n % 4) hw hi b12 b22
    have ready' := laneWord_ready b (n / 4) (n % 4) hw hi b12 b22
    have hj : 4 * (n / 4) + n % 4 = n := by omega
    have wordEq : b.getReg (wordReg (n / 4)) = a.getReg (wordReg (n / 4)) := by
      apply eff.regs <;> unfold wordReg <;> split_ifs <;> decide
    have baseEq : b.getReg (baseReg (n / 4)) = a.getReg (baseReg (n / 4)) := by
      apply eff.regs <;> unfold baseReg <;> split_ifs <;> decide
    rw [lanesUpTo_succ, List.foldl_append]
    refine ⟨ready.append ready', ?_⟩
    rw [← hb]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _
      rw [e.acc, wordEq]
      show _ = laneSum a n + laneOf a n
      by_cases h0 : n / 4 = 0 ∧ n % 4 = 0
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
        rw [if_pos (by rw [hj]), wordEq, baseEq]
        rfl
    · intro addr hout
      rw [e.mem, if_neg (by rw [hj]; exact hout n (by omega)),
        eff.frame addr (fun j hj' => hout j (by omega))]

end OptimalOTS.RiscvUpperProgram
