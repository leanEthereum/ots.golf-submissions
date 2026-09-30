import Submissions.UpperRiscvHint.MixedLanding

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program
variable {credit : Word}

/-- A helper changes only the running checksum, preserving the chain context. -/
theorem Ctx.recredit {s t : MachineState} {index : ChainIndex} {view : List Bool} {pk : PublicKey}
    (ctx : Ctx (credit := credit) s index view pk) (next : Word)
    (regs : ∀ r, r ≠ .x27 → t.getReg r = s.getReg r)
    (mem : t.mem = s.mem) (code : t.code = s.code) (sum : t.getReg .x27 = next) :
    Ctx (credit := next) t index view pk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [code]; exact ctx.null,
    ctx.code.code_eq code, ?_, sum⟩
  · rw [regs .x30 (by decide)]; exact ctx.pk0
  · rw [regs .x31 (by decide)]; exact ctx.pk1
  · rw [regs .x5 (by decide)]; exact ctx.call
  · intro q
    simpa only [MachineState.getHalfword, MachineState.getMem, mem] using ctx.lanes q
  · intro q h
    rw [regs .x10 (by decide), regs .x12 (by decide)] at h
    rw [regs .x28 (by decide)]
    exact ctx.row q h
  · intro k hk hk' h
    rw [regs .x12 (by decide)] at h
    rw [regs .x1 (by decide)]; exact ctx.base k hk hk' h
  · rw [regs .x2 (by decide)]; exact ctx.modulus

theorem Prepared.recredit {s t : MachineState} {index : ChainIndex} {view : List Bool}
    {pk : PublicKey} {x : graph.Assignment} {k : Chain}
    (prep : Prepared (credit := credit) index view pk s x k) (next : Word)
    (regs : ∀ r, r ≠ .x27 → t.getReg r = s.getReg r)
    (mem : t.mem = s.mem) (code : t.code = s.code) (sum : t.getReg .x27 = next) :
    Prepared (credit := next) index view pk t x k := by
  refine ⟨⟨prep.inv.ctx.recredit next regs mem code sum, ?_, prep.inv.inputRange,
    ?_, ?_, ?_, ?_⟩, memBits_of_mem_eq mem prep.ready⟩
  · rw [regs .x10 (by decide)]; exact prep.inv.input
  · rw [regs .x11 (by decide)]; exact prep.inv.length
  · rw [regs .x12 (by decide)]; exact prep.inv.out
  · intro j hj; exact memBits_of_mem_eq mem (prep.inv.payload j hj)
  · intro j hj; exact memBits_of_mem_eq mem (prep.inv.done j hj)

def helperEntry (q a d : ℕ) : ℕ :=
  copiesIndex + groupOffset (group q) + 256*(15-d) + slotOffset q + (15-a+lead q)
def helperJump (q a d : ℕ) : Instr := .JAL .x0
  (BitVec.ofInt 21 (4*((helperStart q a (15-d) : ℤ)-helperEntry q a d)))

theorem redirected_facts : ∀ q a d : Fin 16,
    mappedPair q a (15-d.val) ≠ (a.val,15-d.val) →
    (15-a.val+lead q < (hashRow q d).length) ∧
    rowInstr q d (15-a.val+lead q) = helperJump q a d ∧
    ((a.val,15-d.val),mappedPair q a (15-d.val)) ∈ WeightedPairs.swapsOf (capPair q) ∧
    copiesIndex ≤ helperStart q a (15-d.val) ∧
    Riscv.admittedInstruction (helperJump q a d) = true ∧
    W (4096+4*helperEntry q a d) +
      signExtend21 (BitVec.ofInt 21 (4*((helperStart q a (15-d.val) : ℤ)-helperEntry q a d))) =
        W (4096+4*helperStart q a (15-d.val)) := by decide +kernel

theorem correction_lt : ∀ q a d : Fin 16,
    correction q a (15-d.val) (PairCode.recode q (a,d)).1 (PairCode.recode q (a,d)).2 < 2048 := by
  decide +kernel

/-- A redirect's continuation is its right-chain code, which is `afterLeft`. -/
theorem afterLeft_redirected (index : ChainIndex) (q : Fin 16)
    (h : PairCode.helper q.val (rawPair index.val q) = 1) :
    afterLeft index q = rightCode q (PairCode.recode q (rawPair index.val q)).2 := by
  unfold afterLeft rightCode
  rw [h]
  simp only [one_ne_zero, if_false, List.nil_append]
  have hs : skipFlag index q = isSkip q (PairCode.recode q (rawPair index.val q)).2 := rfl
  rw [hs]
  split_ifs
  · rfl
  · rw [remaining_right, right_previous]; rfl

/-- Both entry forms reach the same recoded hash block. Redirects execute exactly JAL + ADDI. -/
theorem landing_refines (index : ChainIndex) (view : List Bool) (pk : PublicKey) (q : Fin 16)
    (K : OracleComp Spec (Option Bool)) (c rest : ℕ)
    (continuation : ∀ (u : MachineState),
      Prepared (credit := credit + W (landCorrection index q)) index view pk u x (leftChain q) →
      Riscv.CodeAt u u.pc
        (List.replicate (remaining index (leftChain q)) .ECALL ++ afterLeft index q) →
      ∀ left, rest ≤ left → Riscv.Refines left u K c)
    (s : MachineState) (prep : Prepared (credit := credit) index view pk s x (leftChain q))
    (pc : s.pc = W (landing0 q+4*lead q-dispatch index q))
    (fuel : ℕ) (bound : pairFee index q + rest ≤ fuel) :
    Riscv.Refines fuel s K (pairFee index q + c) := by
  let a : Fin 16 := (rawPair index.val q).1
  let d : Fin 16 := (rawPair index.val q).2
  have rawA : a.val = digit index.val (2*q.val) := rfl
  have rawD : d.val = coarseDigit index q := rfl
  by_cases fixed : mappedPair q a (15-d.val) = (a.val,15-d.val)
  · obtain ⟨fee, -⟩ := fixed_fee_correction q a d fixed
    have fee0 : pairFee index q = 0 := by unfold pairFee; rw [fee]
    have corr0 : landCorrection index q = 0 := by unfold landCorrection; rw [if_pos fee]
    rw [fee0, Nat.zero_add] at bound ⊢
    apply continuation s
    · rw [corr0, show credit + W 0 = credit from BitVec.add_zero credit]
      exact prep
    · rw [pc]
      exact landing_located index s prep.inv.ctx.code q fixed
    · exact bound
  · have fee2 : pairFee index q = 2 := by
      unfold pairFee
      rw [redirected_fee q a d fixed]
    rw [fee2] at bound ⊢
    have fee1 : PairCode.helper q.val (rawPair index.val q) = 1 := redirected_fee q a d fixed
    obtain ⟨hlen,hrow,hmem,hbase,hadmit,htarget⟩ := redirected_facts q a d fixed
    have loc := copy_located s prep.inv.ctx.code q ⟨d.val, by simpa [copies] using d.isLt⟩
    have fetch := loc (15-a.val+lead q) (by simp only [copyCode, List.length_append]; omega)
    have head : (copyCode q d)[15-a.val+lead q]? = some (rowInstr q d (15-a.val+lead q)) := by
      simp only [copyCode, List.append_assoc, List.getElem?_append, hlen, ↓reduceIte]
      simp only [hashRow, List.getElem?_map, List.getElem?_range,
        show 15-a.val+lead q < 2^fineWidth q by simpa [hashRow] using hlen,
        ↓reduceIte, Option.map_some]
    have addr : copyStart q d+4*(15-a.val+lead q) = landing0 q+4*lead q-dispatch index q := by
      simpa [fineWidth, rawA, rawD] using (pair_landing index q q.isLt).symm
    have ipc : 4096+4*helperEntry q a d = landing0 q+4*lead q-dispatch index q := by
      rw [← addr]
      simp only [helperEntry, copyStart, copiesStart, copiesIndex, copies]
      omega
    rw [head,hrow,W_add,addr,← pc] at fetch
    let t := s.setPC (W (4096+4*helperStart q a (15-d.val)))
    have transition : step s = some t := by
      rw [RiscvZkvm.Rv64.step, fetch]
      simp only [helperJump, execInstrBr, MachineState.setReg]
      rw [pc,← ipc,htarget]
    have mapped := mapping_agrees q a d
    rw [mapped] at hmem
    have locHelp := helper_located s prep.inv.ctx.code q a (15-d.val)
      (PairCode.recode q (a,d)).1 (PairCode.recode q (a,d)).2 hmem hbase
    have locT : Riscv.CodeAt t t.pc
        (helperCode q a (15-d.val) (PairCode.recode q (a,d)).1 (PairCode.recode q (a,d)).2) :=
      locHelp.code_eq rfl
    have land : landCorrection index q = pairCorrection index q := by
      unfold landCorrection; rw [if_neg (by rw [fee1]; decide)]
    let delta := pairCorrection index q
    let lin : Code := [.ADDI .x27 .x27 (imm12 delta)]
    let u := lin.foldl execInstrBr t
    have locLin : Riscv.CodeAt t t.pc (lin ++
        (List.replicate (remaining index (leftChain q)) .ECALL ++ afterLeft index q)) := by
      rw [afterLeft_redirected index q fee1, remaining_left]
      exact locT
    have ready : Riscv.LinearReady t lin := by
      simp [lin,Riscv.LinearReady,Riscv.linearInstruction,Riscv.memoryReady]
    have regs : ∀ r, r ≠ .x27 → u.getReg r = s.getReg r := by
      intro r hr
      simp [u,lin,t,execInstrBr,getReg_setReg_ite,hr]
    have mem : u.mem = s.mem := rfl
    have code : u.code = s.code := by simp [u,lin,t,execInstrBr]
    have sum : u.getReg .x27 = credit + W delta := by
      have hd := correction_lt q a d
      have imm : signExtend12 (imm12 delta) = W delta := by
        exact signExtend12_nat delta hd
      simp [u,lin,t,execInstrBr,getReg_setReg_ite,imm,prep.inv.ctx.checksum]
    have locU : Riscv.CodeAt u u.pc
        (List.replicate (remaining index (leftChain q)) .ECALL ++ afterLeft index q) := by
      rw [show u.pc=t.pc+W (4*lin.length) from Riscv.linear_fold_pc _ _ ready]
      exact locLin.append_right.code_eq (Riscv.fold_code _ _)
    have finish := continuation u (by rw [land]; exact prep.recredit _ regs mem code sum) locU
      (fuel-2) (by omega)
    have linear := Riscv.Refines.linear (fuel := fuel-2) (c := c) lin locLin.append_left ready finish
    have linLength : lin.length = 1 := rfl
    rw [linLength] at linear
    rw [show fuel = (1+(fuel-2))+1 by omega,show 2+c=(1+c)+1 by omega]
    exact Riscv.Refines.branch fetch hadmit (fun h => nomatch h) transition linear

end OptimalOTS.RiscvMixedProgram
