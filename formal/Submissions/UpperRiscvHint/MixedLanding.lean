import Submissions.UpperRiscvHint.MixedDispatch

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

def leftChain (q : Fin 16) : Chain := ⟨2*q.val+1, by have := q.isLt; omega⟩
def rightChain (q : Fin 16) : Chain := ⟨2*q.val+2, by have := q.isLt; omega⟩
def lengthSetup (_q : ℕ) : Code := []

theorem hashRow_length (q d : ℕ) : (hashRow q d).length = 2^fineWidth q := by
  simp [hashRow]

set_option maxRecDepth 100000 in
theorem hashRow_drop : ∀ q a d : Fin 16, mappedPair q a (15-d.val) = (a.val,15-d.val) →
    (hashRow q d).drop (15-a.val+lead q) = List.replicate (a.val+1-lead q) Instr.ECALL := by
  decide +kernel

theorem prologue_parts (q : Fin 16) :
    prologue q = lengthSetup q ++ dispatchCode q (prevInput (2*q.val+1)) := by
  unfold prologue lengthSetup dispatchCode dispatchFront prevInput laneAddr
  simp only [show 2*q.val+1 ≠ 0 by omega, if_false, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, List.append_assoc, List.cons_append, List.nil_append]

theorem skipPrologue_parts (q : Fin 16) :
    skipPrologue q = lengthSetup q ++ dispatchCode q (work (2*q.val-1)) := by
  unfold skipPrologue lengthSetup dispatchCode dispatchFront laneAddr
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, List.append_assoc, List.cons_append,
    List.nil_append]

theorem right_previous (q : Fin 16) : prevInput (rightChain q) = work (leftChain q) := by
  unfold prevInput leftChain rightChain
  rw [if_neg (by omega : 2*q.val+2 ≠ 0)]
  congr 1

theorem remaining_left (index : ChainIndex) (q : Fin 16) :
    remaining index (leftChain q) = (PairCode.recode q (rawPair index.val q)).1 + 1 - lead q := by
  rw [steps_eq_digit, ← lead_left q.val]
  simp only [leftChain, Nat.add_zero, chainDigit_succ, stepDigit_even]
  rfl

theorem remaining_right (index : ChainIndex) (q : Fin 16) :
    remaining index (rightChain q) = (PairCode.recode q (rawPair index.val q)).2 + 1 - tailLead q := by
  rw [steps_eq_digit, ← lead_right q.val]
  simp only [rightChain, show 2*q.val+2 = (2*q.val+1)+1 by omega, chainDigit_succ, stepDigit_odd]

def pairCorrection (index : ChainIndex) (q : ℕ) : ℕ :=
  correction q (digit index.val (2*q)) (15-digit index.val (2*q+1))
    (PairCode.recode q (rawPair index.val q)).1 (PairCode.recode q (rawPair index.val q)).2

def pairFee (index : ChainIndex) (q : ℕ) : ℕ := 2*PairCode.helper q (rawPair index.val q)

theorem mapping_agrees : ∀ q a d : Fin 16,
    mappedPair q a (15-d.val) = PairCode.recode q (a,d) := by decide +kernel

theorem mappedPair_rawPair (index : ChainIndex) (q : Fin 16) :
    mappedPair q (digit index.val (2*q.val)) (15-coarseDigit index q) =
      PairCode.recode q (rawPair index.val q) :=
  mapping_agrees q (rawPair index.val q).1 (rawPair index.val q).2

/-- An unredirected pair pays no fee; its correction is the skip row's single unit. -/
theorem fixed_fee_correction : ∀ q a d : Fin 16,
    mappedPair q a (15-d.val) = (a.val,15-d.val) →
    PairCode.helper q (a,d) = 0 ∧ correction q a (15-d.val)
      (PairCode.recode q (a,d)).1 (PairCode.recode q (a,d)).2 = 4 * PairCode.skip q (a,d) := by
  decide +kernel

theorem redirected_fee : ∀ q a d : Fin 16,
    mappedPair q a (15-d.val) ≠ (a.val,15-d.val) → PairCode.helper q (a,d) = 1 := by decide +kernel

/-- Pair `q`'s right chain hashes zero times and its pointer pair is skipped. -/
def skipFlag (index : ChainIndex) (q : ℕ) : Bool := isSkip q (PairCode.recode q (rawPair index.val q)).2

theorem skipFlag_iff' : ∀ q : Fin 16, ∀ p : PairCode.Pair,
    isSkip q (PairCode.recode q p).2 = true ↔ PairCode.skip q p = 1 := by decide +kernel

theorem skipFlag_iff (index : ChainIndex) (q : Fin 16) :
    skipFlag index q = true ↔ PairCode.skip q (rawPair index.val q) = 1 :=
  skipFlag_iff' q (rawPair index.val q)

theorem skipFlag_cap (index : ChainIndex) (q : Fin 16) (h : skipFlag index q = true) : q.val < 6 := by
  unfold skipFlag isSkip capPair WeightedPairs.capPos at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem skipFlag_right (index : ChainIndex) (q : Fin 16) (h : skipFlag index q = true) :
    remaining index (rightChain q) = 0 := by
  have hc := skipFlag_cap index q h
  unfold skipFlag isSkip at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [remaining_right, h.2]
  unfold tailLead; rw [if_pos (Or.inl hc)]

/-- What follows the left chain's hashes: the right chain's pointer pair, hashes and the next
prologue; or, after a skip, the rebased prologue (preceded by the skip row's checksum unit when
the pair was not redirected). -/
def afterLeft (index : ChainIndex) (q : Fin 16) : Code :=
  if skipFlag index q then
    (if PairCode.helper q (rawPair index.val q) = 0 then [.ADDI .x27 .x27 (imm12 4)] else []) ++
      skipNext q
  else between q ++
    List.replicate (remaining index (rightChain q)) .ECALL ++ nextCode q

/-- The correction added before the left chain (by a redirect), and after it (by a skip row). -/
def landCorrection (index : ChainIndex) (q : ℕ) : ℕ :=
  if PairCode.helper q (rawPair index.val q) = 0 then 0 else pairCorrection index q
def lateCorrection (index : ChainIndex) (q : ℕ) : ℕ :=
  if skipFlag index q = true ∧ PairCode.helper q (rawPair index.val q) = 0 then 4 else 0

/-- Code reached by the packed two-digit jump, including the second chain and next prologue. -/
theorem landing_located (index : ChainIndex) (s : MachineState)
    (global : Riscv.CodeAt s (W 4096) verifier) (q : Fin 16)
    (good : mappedPair q (digit index.val (2*q.val)) (15-coarseDigit index q) =
      (digit index.val (2*q.val),15-coarseDigit index q)) :
    Riscv.CodeAt s (W (landing0 q+4*lead q-dispatch index q))
      (List.replicate (remaining index (leftChain q)) Instr.ECALL ++ afterLeft index q) := by
  let d := coarseDigit index q
  have hd : d < copies q := coarseDigit_lt_copies index q q.isLt
  have ha := fineDigit_lt index q q.isLt
  have hl := lead_le q
  let off := 2^fineWidth q-1-digit index.val (2*q.val)+lead q
  have hOff : off ≤ 2^fineWidth q := by
    have : digit index.val (2*q.val) < 16 := by simpa [fineWidth] using ha
    dsimp only [off, fineWidth]
    omega
  have mapped : PairCode.recode q (rawPair index.val q) =
      (digit index.val (2*q.val),15-coarseDigit index q) := (mappedPair_rawPair index q).symm.trans good
  have hRemain : digit index.val (2*q.val)+1-lead q = remaining index (leftChain q) := by
    rw [remaining_left, mapped]
  have hSecond : 15-d+1-tailLead q = remaining index (rightChain q) := by
    rw [remaining_right, mapped]
  have located := copy_located s global q ⟨d,hd⟩
  have h := CodeAt.drop located off
  change Riscv.CodeAt s (W (copyStart q d)+W (4*off)) ((copyCode q d).drop off) at h
  unfold copyCode at h
  have hdrop : (hashRow q d).drop off = List.replicate (remaining index (leftChain q)) Instr.ECALL := by
    have hf : digit index.val (2*q.val) < 16 := by simpa [fineWidth] using ha
    have hc : d < 16 := by simpa [copies] using hd
    have ht := hashRow_drop q ⟨digit index.val (2*q.val),hf⟩ ⟨d,hc⟩ good
    rw [← hRemain]
    simpa [fineWidth, off] using ht
  rw [List.drop_append_of_le_length (by rw [hashRow_length]; exact hOff),
    hdrop, W_add] at h
  have addr : copyStart q d+4*off = landing0 q+4*lead q-dispatch index q :=
    (pair_landing index q q.isLt).symm
  rw [addr] at h
  have hflag : skipFlag index q = isSkip q (15-d) := by
    unfold skipFlag; rw [mapped]
  have hfee : PairCode.helper q.val (rawPair index.val q) = 0 := by
    have e := (fixed_fee_correction q (rawPair index.val q).1 (rawPair index.val q).2 good).1
    exact e
  unfold afterLeft
  rw [hflag, hfee, if_pos rfl]
  by_cases hs : isSkip q (15-d) = true
  · rw [if_pos hs] at h ⊢
    simpa only [List.nil_append, List.singleton_append, List.cons_append] using h
  · rw [if_neg hs] at h ⊢
    rw [← hSecond]
    simpa only [nextCode, rightChain, leftChain, List.append_assoc] using h

end OptimalOTS.RiscvMixedProgram
