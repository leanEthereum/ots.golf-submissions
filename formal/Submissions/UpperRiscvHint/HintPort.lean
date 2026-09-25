import Submissions.UpperRiscvHint.Candidate
import Submissions.UpperRiscvHint.HintTransfer

/-! Identity views preserve the current deterministic verifier. Its length check also rejects
all oversized views presented by the hinted loader. -/
namespace OptimalOTS.RiscvMixedProgram
open Riscv2Program RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] verifier validSet

private theorem view_data_len (pk : PublicKey) (m : Message) (bits : List Bool) :
    (RiscvHint.loadView image pk m bits).getMem (W (dataAddr + 72)) = W 5504 := by
  have old := initial_data_len pk m bits
  have newEq : (RiscvHint.loadView image pk m bits).getMem (W (dataAddr + 72)) =
      (loaderMessage image pk m).getMem (W (dataAddr + 72)) := by
    change ((loaderMessage image pk m).writeBytesAsWords Riscv.signatureBase
      (Riscv.bytesOfBits (bits.take RiscvHint.maxViewBits))).getMem _ = _
    apply getMem_load_outside
    · simp [RiscvHint.maxViewBits, Riscv.bytesOfBits]; omega
    · left; decide
  rw [initialState_getMem, getMem_load_outside] at old
  · exact newEq.trans old
  · simp [Riscv.bytesOfBits]; omega
  · left; decide

private theorem prefix_reject (s : MachineState) (tail : Code)
    (located : Riscv.CodeAt s s.pc (indexPrefix ++ [.ECALL] ++ lenBlock ++
      ([.BEQ .x13 .x6 16] ++ reject ++ tail)))
    (r10 : s.getReg .x10 = W 0x400000)
    (r13 : s.getReg .x13 ≠ W 5504)
    (mem : s.getMem (W (dataAddr + 72)) = W 5504) :
    ∃ q : OracleComp Spec (Option Bool),
      Riscv.Refines 1337 s q 11 ∧ ∀ v ∈ support q, v = some false := by
  let p := indexPrefix.foldl execInstrBr s
  have ready : Riscv.LinearReady s indexPrefix := by
    simp [indexPrefix, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
      execInstrBr, getReg_setReg_ite, r10, signExtend12, MEM_START, MEM_END]
  have px10 : p.getReg .x10 = W 0x400000 := by
    simp [p, indexPrefix, execInstrBr, getReg_setReg_ite, r10]
  have px11 : p.getReg .x11 = 512 := by
    simp [p, indexPrefix, execInstrBr, getReg_setReg_ite, getReg_x0', signExtend12]
  have px12 : p.getReg .x12 = W dataAddr := by
    simp [p, indexPrefix, execInstrBr, getReg_setReg_ite, getReg_x0']; rfl
  have px5 : p.getReg .x5 = 1 := by
    simp [p, indexPrefix, execInstrBr, getReg_setReg_ite, getReg_x0', signExtend12]
  have px13 : p.getReg .x13 ≠ W 5504 := by
    simpa [p, indexPrefix, execInstrBr, getReg_setReg_ite] using r13
  have pmem : ∀ a, p.getMem a = s.getMem a := by
    intro a; simp [p, indexPrefix, execInstrBr]
  have valid : Riscv.hashArgumentsValid p = true := by
    unfold Riscv.hashArgumentsValid
    rw [px10, px11, px12]
    decide
  have loc : Riscv.CodeAt p p.pc ([.ECALL] ++ (lenBlock ++
      ([.BEQ .x13 .x6 16] ++ reject ++ tail))) := by
    have h : Riscv.CodeAt s s.pc (indexPrefix ++ ([.ECALL] ++ (lenBlock ++
      ([.BEQ .x13 .x6 16] ++ reject ++ tail)))) := by simpa [List.append_assoc] using located
    rw [show p.pc = s.pc + BitVec.ofNat 64 (4 * indexPrefix.length) from Riscv.linear_fold_pc _ _ ready]
    exact h.append_right.code_eq (Riscv.fold_code _ _)
  let q : OracleComp Spec (Option Bool) := hash (Riscv.hashInput p).2 >>= fun _ => pure (some false)
  refine ⟨q, ?_, ?_⟩
  · have hashRef := Riscv.Refines.hash (fuel := 1331) loc.head px5 valid
      (c := 5) (k := fun _ => pure (some false)) ?_
    · have cost : blockCost (Riscv.hashInput p).1 = 1 := by
        change blockCost (p.getReg .x11).toNat = 1
        rw [px11]; decide
      rw [cost] at hashRef
      exact Riscv.Refines.linear indexPrefix (located.append_left.append_left.append_left) ready hashRef
    intro answer
    let t := Riscv.writeHash p answer
    have tx12 : t.getReg .x12 = W dataAddr := by simpa [t, Riscv.writeHash] using px12
    have tx13 : t.getReg .x13 ≠ W 5504 := by simpa [t, Riscv.writeHash] using px13
    have tmem : t.getMem (W (dataAddr + 72)) = W 5504 := by
      rw [show t.getMem (W (dataAddr + 72)) = p.getMem (W (dataAddr + 72)) from
        writeHash_frame p answer _ (by
          rw [px12]
          intro j hj eq
          rw [W_add] at eq
          have := congrArg BitVec.toNat eq
          simp only [W, BitVec.toNat_ofNat] at this
          norm_num [dataAddr, Nat.mod_eq_of_lt (show dataAddr + 8 * j < 2 ^ 64 by unfold dataAddr; omega)] at this
          omega), pmem, mem]
    have tcode : Riscv.CodeAt t t.pc (lenBlock ++ ([.BEQ .x13 .x6 16] ++ reject ++ tail)) :=
      loc.tail.code_eq (by simp [t, Riscv.writeHash])
    have lready : Riscv.LinearReady t lenBlock := by
      simp only [lenBlock, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, true_and, and_true]
      rw [tx12, signExtend12_nat 72 (by norm_num), W_add]
      decide
    let u := lenBlock.foldl execInstrBr t
    have ux6 : u.getReg .x6 = W 5504 := by
      simp [u, lenBlock, execInstrBr, getReg_setReg_ite, tx12,
        signExtend12_nat 72 (by norm_num), W_add, tmem]
    have ux13 : u.getReg .x13 ≠ W 5504 := by
      simpa [u, lenBlock, execInstrBr, getReg_setReg_ite] using tx13
    have ucode : Riscv.CodeAt u u.pc ([.BEQ .x13 .x6 16] ++ reject ++ tail) := by
      rw [show u.pc = t.pc + BitVec.ofNat 64 (4 * lenBlock.length) from Riscv.linear_fold_pc _ _ lready]
      exact tcode.append_right.code_eq (Riscv.fold_code _ _)
    have bref := beq_refines u .x13 .x6 1330 tail ucode (by omega)
      (q := pure (some false)) (c := 3) (by omega) (by intro h; exact False.elim (ux13 (h.trans ux6)))
    rw [if_neg (fun h => ux13 (h.trans ux6))] at bref
    exact Riscv.Refines.linear lenBlock tcode.append_left lready bref
  · intro v hv
    simp [q] at hv
    exact hv.2.symm

/-- The unchanged image rejects every view exceeding the signature-size cap. -/
theorem long_view_rejects (pk : PublicKey) (m : Message) (view : List Bool)
    (hlen : maxSignatureBits < view.length) :
    ∀ o ∈ support (RiscvUpperForest.submission.hinted.exec 1337 pk m view),
      RiscvHint.decision o = some false := by
  let s := RiscvHint.loadView image pk m view
  have located : Riscv.CodeAt s s.pc verifier := by
    have h := Riscv.CodeAt.initial image pk m view image_valid
    rw [image_code] at h
    rw [show s.pc = Riscv.codeBase by simp [s, RiscvHint.loadView]]
    exact h.code_eq (t := s) (by simp [s, RiscvHint.loadView, Riscv.initialState]; rfl)
  have parts : verifier = indexPrefix ++ [.ECALL] ++ lenBlock ++
      ([.BEQ .x13 .x6 16] ++ reject ++ (mainBlock ++ ([.BEQ .x27 .x0 16] ++ reject ++
        (setup ++ (prologue 0 ++ List.replicate 5 nop ++ tables))))) := by
    rw [show verifier = indexPhase ++ (prologue 0 ++ List.replicate 5 nop ++ tables) by simp only [verifier, List.append_assoc],
      indexPhase_parts]
    simp only [List.append_assoc]
  rw [parts] at located
  have wrong : s.getReg .x13 ≠ W 5504 := by
    change BitVec.ofNat 64 (min view.length 1048577) ≠ W 5504
    apply W_ne
    · omega
    · norm_num
    · change 5504 < view.length at hlen
      omega
  obtain ⟨q, hq, reject⟩ := prefix_reject s _ located rfl wrong (view_data_len pk m view)
  intro o ho
  apply reject
  rw [← hq.1, Riscv.observe, support_map]
  exact ⟨o, ho, rfl⟩

end OptimalOTS.RiscvMixedProgram
