import Submissions.UpperRiscv.ChainContext

/-!
# The lane words of the index phase

Each of the seven lane words is at most one shift, one mask, an accumulation into `x27`, a
subtraction from the broadcast jump base and a store (`laneWord_effect`). Together they leave in
`x27` the sum of the lane words and in memory the dispatch halfwords (`lanesUpTo_effect`).
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64

/-- The address of lane word `g`. -/
def laneWordAddr (g : ℕ) : ℕ := laneBase + laneOff g

/-- The store offset of lane word `g` from the public-key pointer. -/
theorem laneStore_addr (g : ℕ) (hg : g < 7) :
    W hashBase + signExtend12 (BitVec.ofInt 12 ((laneBase + laneOff g : ℤ) - hashBase)) =
      W (laneWordAddr g) := by
  have e : BitVec.ofInt 12 ((laneBase + laneOff g : ℤ) - hashBase) =
      imm12 ((laneBase + laneOff g : ℤ) - hashBase) := rfl
  rw [e, W_add_imm _ _ (by simp only [laneBase, laneOff, hashBase]; omega)
    (by simp only [laneBase, laneOff, hashBase]; omega)
    (by simp only [laneBase, laneOff, hashBase]; omega)
    (by simp only [hashBase]; omega)]
  congr 1
  simp only [laneBase, laneOff, hashBase, laneWordAddr]
  omega

theorem srcReg_ne (g : ℕ) : srcReg g ≠ .x26 ∧ srcReg g ≠ .x27 ∧ srcReg g ≠ .x10 := by
  unfold srcReg wordReg
  split <;> decide

theorem maskReg_ne (g : ℕ) : maskReg g ≠ .x26 ∧ maskReg g ≠ .x27 ∧ maskReg g ≠ .x10 := by
  unfold maskReg
  split_ifs <;> decide

structure LaneEffect (a b : MachineState) (g : ℕ) : Prop where
  acc : b.getReg .x27 = if g = 0 then laneValue (a.getReg (srcReg g)) g (a.getReg (maskReg g))
    else a.getReg .x27 + laneValue (a.getReg (srcReg g)) g (a.getReg (maskReg g))
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = if addr = W (laneWordAddr g) then
    a.getReg .x3 - laneValue (a.getReg (srcReg g)) g (a.getReg (maskReg g)) else a.getMem addr

/-- Everything of a lane word but its store. -/
def lanePre (g : ℕ) : Code :=
  let dst : Reg := if g = 0 then .x27 else .x26
  (if shiftOf g = 0 then [.AND dst (srcReg g) (maskReg g)]
   else [.SRLI dst (srcReg g) (BitVec.ofNat 6 (shiftOf g)), .AND dst dst (maskReg g)]) ++
  (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
  [.SUB .x26 .x3 dst]

theorem laneWord_parts (g : ℕ) :
    laneWord g = lanePre g ++
      [.SD .x10 .x26 (BitVec.ofInt 12 ((laneBase + laneOff g : ℤ) - hashBase))] := by
  simp [laneWord, lanePre]

theorem lanePre_ready (a : MachineState) (g : ℕ) (hg : g < 7) :
    Riscv.LinearReady a (lanePre g) := by
  interval_cases g <;>
    simp [lanePre, shiftOf, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

/-- The register effect of the lane computation before its store. -/
theorem lanePre_regs (a : MachineState) (g : ℕ) (hg : g < 7) :
    let b := (lanePre g).foldl execInstrBr a
    b.getReg .x27 = (if g = 0 then laneValue (a.getReg (srcReg g)) g (a.getReg (maskReg g))
      else a.getReg .x27 + laneValue (a.getReg (srcReg g)) g (a.getReg (maskReg g))) ∧
    b.getReg .x26 = a.getReg .x3 - laneValue (a.getReg (srcReg g)) g (a.getReg (maskReg g)) ∧
    (∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r) ∧
    (∀ addr, b.getMem addr = a.getMem addr) := by
  interval_cases g <;>
    simp [lanePre, shiftOf, execInstrBr, getReg_setReg_ite, laneValue, srcReg, wordReg, wordIdx,
      maskReg] <;>
    (try intro r h26 h27) <;> simp_all

theorem laneWord_effect (a : MachineState) (g : ℕ) (hg : g < 7)
    (h10 : a.getReg .x10 = W hashBase) :
    LaneEffect a ((laneWord g).foldl execInstrBr a) g := by
  obtain ⟨r27, r26, rr, rm⟩ := lanePre_regs a g hg
  rw [laneWord_parts, List.foldl_append]
  generalize hb : (lanePre g).foldl execInstrBr a = b at r27 r26 rr rm
  have b10 : b.getReg .x10 = W hashBase := by rw [rr .x10 (by decide) (by decide), h10]
  have st : b.getReg .x10 +
      signExtend12 (BitVec.ofInt 12 ((laneBase + laneOff g : ℤ) - hashBase)) =
      W (laneWordAddr g) := by
    rw [b10, laneStore_addr g hg]
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

theorem laneWord_ready (a : MachineState) (g : ℕ) (hg : g < 7)
    (h10 : a.getReg .x10 = W hashBase) :
    Riscv.LinearReady a (laneWord g) := by
  obtain ⟨-, -, rr, -⟩ := lanePre_regs a g hg
  rw [laneWord_parts]
  refine (lanePre_ready a g hg).append ⟨rfl, ?_, trivial⟩
  show isValidDwordAccess (_ + _) = true
  rw [rr .x10 (by decide) (by decide), h10, laneStore_addr g hg]
  exact dword_ok _ (by unfold laneWordAddr laneOff laneBase; omega)
    (by unfold laneWordAddr laneOff laneBase; omega)
    (by unfold laneWordAddr laneOff laneBase; omega)

/-! ## All seven lane words -/

/-- Lane word `g` of the state's index words. -/
def laneOf (a : MachineState) (g : ℕ) : Word :=
  laneValue (a.getReg (srcReg g)) g (a.getReg (maskReg g))

/-- The running sum of the first `n` lane words. -/
def laneSum (a : MachineState) : ℕ → Word
  | 0 => 0
  | n + 1 => laneSum a n + laneOf a n

/-- The first `n` lane words. -/
def lanesUpTo (n : ℕ) : Code := (List.range n).flatMap laneWord

theorem lanes_eq : lanes = lanesUpTo 7 := rfl

theorem lanesUpTo_succ (n : ℕ) : lanesUpTo (n + 1) = lanesUpTo n ++ laneWord n := by
  simp [lanesUpTo, List.range_succ, List.flatMap_append]

/-- The effect of the first `n` lane words. -/
structure LanesEffect (a b : MachineState) (n : ℕ) : Prop where
  acc : 1 ≤ n → b.getReg .x27 = laneSum a n
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  stored : ∀ g, g < n → b.getMem (W (laneWordAddr g)) = a.getReg .x3 - laneOf a g
  frame : ∀ addr, (∀ g, g < n → addr ≠ W (laneWordAddr g)) → b.getMem addr = a.getMem addr

theorem laneWordAddr_ne (i j : ℕ) (hi : i < 7) (hj : j < 7) (h : i ≠ j) :
    W (laneWordAddr i) ≠ W (laneWordAddr j) :=
  W_ne (by unfold laneWordAddr laneOff laneBase; omega)
    (by unfold laneWordAddr laneOff laneBase; omega) (by unfold laneWordAddr laneOff; omega)

theorem lanesUpTo_effect (a : MachineState) (h10 : a.getReg .x10 = W hashBase) :
    ∀ n, n ≤ 7 → Riscv.LinearReady a (lanesUpTo n) ∧
      LanesEffect a ((lanesUpTo n).foldl execInstrBr a) n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨trivial, ?_⟩
    refine ⟨fun h => absurd h (by norm_num), fun r _ _ => rfl, fun g hg => absurd hg (by omega),
      fun addr _ => rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨ready, eff⟩ := ih (by omega)
    set b := (lanesUpTo n).foldl execInstrBr a with hb
    have b10 : b.getReg .x10 = W hashBase := by rw [eff.regs .x10 (by decide) (by decide), h10]
    have hg : n < 7 := by omega
    have e := laneWord_effect b n hg b10
    have ready' := laneWord_ready b n hg b10
    have wordEq : b.getReg (srcReg n) = a.getReg (srcReg n) :=
      eff.regs _ (srcReg_ne _).1 (srcReg_ne _).2.1
    have maskEq : b.getReg (maskReg n) = a.getReg (maskReg n) :=
      eff.regs _ (maskReg_ne _).1 (maskReg_ne _).2.1
    have baseEq : b.getReg .x3 = a.getReg .x3 := eff.regs _ (by decide) (by decide)
    rw [lanesUpTo_succ, List.foldl_append]
    refine ⟨ready.append ready', ?_⟩
    rw [← hb]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _
      rw [e.acc, wordEq, maskEq]
      show _ = laneSum a n + laneOf a n
      by_cases h0 : n = 0
      · rw [if_pos h0]
        subst h0
        simp [laneSum, laneOf]
      · rw [if_neg h0, eff.acc (by omega)]
        rfl
    · intro r h26 h27
      rw [e.regs r h26 h27, eff.regs r h26 h27]
    · intro g hg'
      rw [e.mem]
      rcases Nat.lt_or_ge g n with lt | ge
      · rw [if_neg (laneWordAddr_ne g n (by omega) (by omega) (by omega)), eff.stored g lt]
      · obtain rfl : g = n := by omega
        rw [if_pos rfl, wordEq, maskEq, baseEq]
        rfl
    · intro addr hout
      rw [e.mem, if_neg (hout n (by omega)), eff.frame addr (fun g hg' => hout g (by omega))]

end OptimalOTS.Riscv2Program
