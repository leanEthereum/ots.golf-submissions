import Submissions.UpperRiscv.ChainContext

/-!
# The lane words and the fold of the index phase

Each of the four lane words is one mask, an accumulation into `x27`, a subtraction from its
broadcast jump base and a store (`laneWord_effect`). Together they leave in `x27` the sum of the
masked words and in memory the dispatch halfwords (`lanesUpTo_effect`). The fold then adds the
coarse fields onto the fine ones (`fold_effect`).
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64

/-- The store offset of lane word `g` from the public-key pointer. -/
theorem laneStore_addr (g : ℕ) (hg : g < 4) :
    W hashBase + signExtend12 (imm12 ((laneWordAddr g : ℤ) - hashBase)) = W (laneWordAddr g) := by
  rw [W_add_imm _ _ (by simp only [laneWordAddr, laneBase, hashBase]; omega)
    (by simp only [laneWordAddr, laneBase, hashBase]; omega)
    (by simp only [laneWordAddr, laneBase, hashBase]; omega)
    (by simp only [hashBase]; omega)]
  congr 1
  simp only [laneWordAddr, laneBase, hashBase]
  omega

theorem wordReg_ne (g : ℕ) : wordReg g ≠ .x26 ∧ wordReg g ≠ .x27 ∧ wordReg g ≠ .x10 := by
  unfold wordReg; split <;> decide

theorem maskReg_ne (g : ℕ) : maskReg g ≠ .x26 ∧ maskReg g ≠ .x27 ∧ maskReg g ≠ .x10 := by
  unfold maskReg; split_ifs <;> decide

theorem baseReg_ne (g : ℕ) : baseReg g ≠ .x26 ∧ baseReg g ≠ .x27 ∧ baseReg g ≠ .x10 := by
  unfold baseReg; split <;> decide

structure LaneEffect (a b : MachineState) (g : ℕ) : Prop where
  acc : b.getReg .x27 = if g = 0 then laneValue (a.getReg (wordReg g)) (a.getReg (maskReg g))
    else a.getReg .x27 + laneValue (a.getReg (wordReg g)) (a.getReg (maskReg g))
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = if addr = W (laneWordAddr g) then
    a.getReg (baseReg g) - laneValue (a.getReg (wordReg g)) (a.getReg (maskReg g))
    else a.getMem addr

/-- Everything of a lane word but its store. -/
def lanePre (g : ℕ) : Code :=
  let dst : Reg := if g = 0 then .x27 else .x26
  [.AND dst (wordReg g) (maskReg g)] ++ (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
  [.SUB .x26 (baseReg g) dst]

theorem laneWord_parts (g : ℕ) :
    laneWord g = lanePre g ++ [.SD .x10 .x26 (imm12 ((laneWordAddr g : ℤ) - hashBase))] := by
  simp [laneWord, lanePre]

theorem lanePre_ready (a : MachineState) (g : ℕ) (hg : g < 4) :
    Riscv.LinearReady a (lanePre g) := by
  interval_cases g <;>
    simp [lanePre, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

/-- The register effect of the lane computation before its store. -/
theorem lanePre_regs (a : MachineState) (g : ℕ) (hg : g < 4) :
    let b := (lanePre g).foldl execInstrBr a
    b.getReg .x27 = (if g = 0 then laneValue (a.getReg (wordReg g)) (a.getReg (maskReg g))
      else a.getReg .x27 + laneValue (a.getReg (wordReg g)) (a.getReg (maskReg g))) ∧
    b.getReg .x26 = a.getReg (baseReg g) - laneValue (a.getReg (wordReg g)) (a.getReg (maskReg g)) ∧
    (∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r) ∧
    (∀ addr, b.getMem addr = a.getMem addr) := by
  interval_cases g <;>
    simp [lanePre, execInstrBr, getReg_setReg_ite, laneValue, wordReg, maskReg, baseReg] <;>
    (try intro r h26 h27) <;> simp_all

theorem laneWord_effect (a : MachineState) (g : ℕ) (hg : g < 4)
    (h10 : a.getReg .x10 = W hashBase) :
    LaneEffect a ((laneWord g).foldl execInstrBr a) g := by
  obtain ⟨r27, r26, rr, rm⟩ := lanePre_regs a g hg
  rw [laneWord_parts, List.foldl_append]
  generalize hb : (lanePre g).foldl execInstrBr a = b at r27 r26 rr rm
  have b10 : b.getReg .x10 = W hashBase := by rw [rr .x10 (by decide) (by decide), h10]
  have st : b.getReg .x10 + signExtend12 (imm12 ((laneWordAddr g : ℤ) - hashBase)) =
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

theorem laneWord_ready (a : MachineState) (g : ℕ) (hg : g < 4)
    (h10 : a.getReg .x10 = W hashBase) :
    Riscv.LinearReady a (laneWord g) := by
  obtain ⟨-, -, rr, -⟩ := lanePre_regs a g hg
  rw [laneWord_parts]
  refine (lanePre_ready a g hg).append ⟨rfl, ?_, trivial⟩
  show isValidDwordAccess (_ + _) = true
  rw [rr .x10 (by decide) (by decide), h10, laneStore_addr g hg]
  exact dword_ok _ (by unfold laneWordAddr laneBase; omega)
    (by unfold laneWordAddr laneBase; omega) (by unfold laneWordAddr laneBase; omega)

/-! ## All four lane words -/

/-- Lane word `g` of the state's index words. -/
def laneOf (a : MachineState) (g : ℕ) : Word :=
  laneValue (a.getReg (wordReg g)) (a.getReg (maskReg g))

/-- The running sum of the first `n` lane words. -/
def laneSum (a : MachineState) : ℕ → Word
  | 0 => 0
  | n + 1 => laneSum a n + laneOf a n

/-- The first `n` lane words. -/
def lanesUpTo (n : ℕ) : Code := (List.range n).flatMap laneWord

theorem lanes_eq : lanes = lanesUpTo 4 := rfl

theorem lanesUpTo_succ (n : ℕ) : lanesUpTo (n + 1) = lanesUpTo n ++ laneWord n := by
  simp [lanesUpTo, List.range_succ, List.flatMap_append]

/-- The effect of the first `n` lane words. -/
structure LanesEffect (a b : MachineState) (n : ℕ) : Prop where
  acc : 1 ≤ n → b.getReg .x27 = laneSum a n
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  stored : ∀ g, g < n → b.getMem (W (laneWordAddr g)) = a.getReg (baseReg g) - laneOf a g
  frame : ∀ addr, (∀ g, g < n → addr ≠ W (laneWordAddr g)) → b.getMem addr = a.getMem addr

theorem laneWordAddr_ne (i j : ℕ) (hi : i < 4) (hj : j < 4) (h : i ≠ j) :
    W (laneWordAddr i) ≠ W (laneWordAddr j) :=
  W_ne (by unfold laneWordAddr laneBase; omega) (by unfold laneWordAddr laneBase; omega)
    (by unfold laneWordAddr; omega)

theorem lanesUpTo_effect (a : MachineState) (h10 : a.getReg .x10 = W hashBase) :
    ∀ n, n ≤ 4 → Riscv.LinearReady a (lanesUpTo n) ∧
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
    have hg : n < 4 := by omega
    have e := laneWord_effect b n hg b10
    have ready' := laneWord_ready b n hg b10
    have wordEq : b.getReg (wordReg n) = a.getReg (wordReg n) :=
      eff.regs _ (wordReg_ne _).1 (wordReg_ne _).2.1
    have maskEq : b.getReg (maskReg n) = a.getReg (maskReg n) :=
      eff.regs _ (maskReg_ne _).1 (maskReg_ne _).2.1
    have baseEq : b.getReg (baseReg n) = a.getReg (baseReg n) :=
      eff.regs _ (baseReg_ne _).1 (baseReg_ne _).2.1
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

/-! ## The fold -/

/-- The machine's fold of the lane sum with the fold mask `m`. -/
def foldValue (x m : Word) : Word := (x + (x >>> 8)) &&& m

structure FoldEffect (a b : MachineState) : Prop where
  acc : b.getReg .x27 = foldValue (a.getReg .x27) (a.getReg .x1)
  regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = a.getMem addr

theorem fold_ready (a : MachineState) : Riscv.LinearReady a fold := by
  simp [fold, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem fold_effect (a : MachineState) : FoldEffect a (fold.foldl execInstrBr a) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [fold, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite, foldValue]
    simp
  · intro r h26 h27
    simp only [fold, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp [h26, h27]
  · intro addr
    simp [fold, execInstrBr]

end OptimalOTS.Riscv2Program
