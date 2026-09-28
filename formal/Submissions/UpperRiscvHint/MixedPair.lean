import Submissions.UpperRiscvHint.MixedLanding

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

def landingIP (q a d : ℕ) : ℕ :=
  copiesIndex + groupOffset (group q) + 256*(15-d) + slotOffset q + (15-a+lead q)

set_option maxRecDepth 100000 in
theorem rejecting_landing_facts : ∀ q a d : Fin 16, pairCap q < a.val+d.val →
    (15-a.val+lead q < (hashRow q d).length) ∧
    rowInstr q d (15-a.val+lead q) = rejectJump (landingIP q a d) ∧
    stubFor (landingIP q a d) ∈ rejectStubs ∧
    Riscv.admittedInstruction (rejectJump (landingIP q a d)) = true ∧
    W (4096+4*landingIP q a d) +
        signExtend13 (BitVec.ofInt 13 (4*((stubFor (landingIP q a d) : ℤ)-landingIP q a d))) =
      W (4096+4*stubFor (landingIP q a d)) := by
  decide +kernel

theorem landing_reject_refines (index : RawIdx) (q : Fin 16) (s : MachineState)
    (global : Riscv.CodeAt s (W 4096) verifier)
    (pc : s.pc = W (landing0 q+4*lead q-dispatch index q))
    (bad : pairCap q < digit index.val (2*q.val)+coarseDigit index q)
    (fuel : ℕ) (bound : 4 ≤ fuel) :
    Riscv.Refines fuel s (pure (some false)) 4 := by
  let a : Fin 16 := ⟨digit index.val (2*q.val), by
    simpa [fineWidth] using fineDigit_lt index q q.isLt⟩
  let d : Fin 16 := ⟨coarseDigit index q, coarseDigit_lt index q⟩
  let ip := landingIP q a d
  obtain ⟨hlen, hrow, hstub, hadmit, htarget⟩ := rejecting_landing_facts q a d bad
  have loc := copy_located s global q ⟨d.val, by simpa [copies] using d.isLt⟩
  have fetch := loc (15-a.val+lead q) (by
    simp only [copyCode, List.length_append]; omega)
  have head : (copyCode q d)[15-a.val+lead q]? = some (rowInstr q d (15-a.val+lead q)) := by
    simp only [copyCode, List.append_assoc, List.getElem?_append, hlen, ↓reduceIte]
    simp only [hashRow, List.getElem?_map, List.getElem?_range,
      show 15-a.val+lead q < 2^fineWidth q by simpa [hashRow] using hlen, ↓reduceIte, Option.map_some]
  have addr : copyStart q d+4*(15-a.val+lead q) = landing0 q+4*lead q-dispatch index q := by
    simpa [fineWidth, a, d] using (pair_landing index q q.isLt).symm
  have ipc : 4096+4*ip = landing0 q+4*lead q-dispatch index q := by
    rw [← addr]
    simp only [ip, landingIP, copyStart, copiesStart, copiesIndex, copies]
    omega
  rw [head, hrow, W_add, addr, ← pc] at fetch
  have transition : step s = some (s.setPC (W (4096+4*stubFor ip))) := by
    rw [RiscvZkvm.Rv64.step, fetch]
    simp only [rejectJump, execInstrBr, if_true]
    rw [pc, ← ipc]
    exact congrArg (fun p => some (s.setPC p)) htarget
  have locReject : Riscv.CodeAt (s.setPC (W (4096+4*stubFor ip)))
      (W (4096+4*stubFor ip)) reject :=
    (rejectStub_located s global (stubFor ip) hstub).code_eq rfl
  have stop := reject_refines _ (fuel-1) locReject (by omega)
  rw [show fuel=(fuel-1)+1 by omega, show (4 : ℕ)=3+1 by omega]
  exact Riscv.Refines.branch fetch hadmit (fun h => nomatch h) transition stop

end OptimalOTS.RiscvMixedProgram

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (wire : List Bool) (pk : PublicKey)

/-- Length setup, prologue, both chains' hashes and the pointer move between them. -/
def pairCost (q : Fin 16) : ℕ := (lengthSetup q).length + (dispatchCode q).length +
  remaining index (leftChain q) + 2 + remaining index (rightChain q)

structure LengthEffect (s u : MachineState) (q : Fin 16) : Prop where
  length : u.getReg .x11 = W (chainBits (leftChain q))
  regs : ∀ r, r ≠ .x11 → u.getReg r = s.getReg r
  mem : u.mem=s.mem
  code : u.code=s.code

theorem lengthSetup_ready (s : MachineState) (q : ℕ) : Riscv.LinearReady s (lengthSetup q) := by
  unfold lengthSetup
  split_ifs <;> simp [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem prevBits_left (q : Fin 16) (h8 : q.val ≠ 6) :
    prevBits (leftChain q) = chainBits (leftChain q) := by
  revert q; decide

theorem prevBits_right (q : Fin 16) : prevBits (rightChain q) = chainBits (rightChain q) := by
  revert q; decide

theorem lengthSetup_effect (s : MachineState) (q : Fin 16)
    (h : s.getReg .x11 = W (prevBits (leftChain q))) :
    LengthEffect s ((lengthSetup q).foldl execInstrBr s) q := by
  by_cases hq : q.val=6
  · have he : q=6 := Fin.ext hq
    subst q
    refine ⟨?_, ?_, rfl, rfl⟩
    · simp [lengthSetup, execInstrBr, getReg_setReg_ite, chainBits, leftChain, W, getReg_x0']
      decide
    · intro r hr; simp [lengthSetup, execInstrBr, getReg_setReg_ite, hr]
  · have hw := prevBits_left q hq
    simp only [lengthSetup, if_neg hq, List.foldl_nil]
    exact ⟨h.trans (congrArg W hw), fun _ _ => rfl, rfl, rfl⟩

theorem pairCost_eq (q : Fin 16) : pairCost index q =
    (lengthSetup q).length + 6 +
      remaining index (leftChain q) + remaining index (rightChain q) := by
  unfold pairCost
  rw [dispatchCode_length]
  omega

/-- The state after a pair's length setup, ready for its prologue. -/
theorem after_lengthSetup (q : Fin 16) (s : MachineState) (x : graph.Assignment)
    (inv : ChainsInv index wire pk s x (leftChain q)) :
    let s1 := (lengthSetup q).foldl execInstrBr s
    LengthEffect s s1 q ∧ Ctx s1 index wire pk ∧ s1.getReg .x10 = W (prevInput (leftChain q)) ∧
      PayloadFrom s1 wire (leftChain q) ∧ Completed s1 (tops x) (leftChain q) := by
  intro s1
  have E := lengthSetup_effect s q inv.length
  refine ⟨E, inv.ctx.frame (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact E.regs _ (by decide)) E.mem E.code,
    by rw [E.regs .x10 (by decide)]; exact inv.input,
    fun j hj => memBits_of_mem_eq E.mem (inv.payload j hj),
    fun j hj => memBits_of_mem_eq E.mem (inv.done j hj)⟩

/-- Pair 0 starts at `freeLanding`; later pairs start with `x1` holding pair 0's link. -/
theorem prologue_facts (q : Fin 16) (s : MachineState) (x : graph.Assignment)
    (inv : ChainsInv index wire pk s x (leftChain q))
    (start : q.val = 0 → s.pc = W freeLanding) :
    let s1 := (lengthSetup q).foldl execInstrBr s
    (q.val = 0 → s1.pc = W freeLanding) ∧ (q.val ≠ 0 → s1.getReg .x1 = W rootBase) := by
  intro s1
  have E := lengthSetup_effect s q inv.length
  obtain ⟨-, s1ctx, -⟩ := after_lengthSetup index wire pk q s x inv
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have hl : lengthSetup q = [] := by simp [lengthSetup, h0]
    change ((lengthSetup q).foldl execInstrBr s).pc = _
    rw [hl, List.foldl_nil]
    exact start h0
  · have ho := inv.out (by simp [leftChain])
    rw [← E.regs .x12 (by decide)] at ho
    exact s1ctx.link (k := (leftChain q).val - 1) (by simp [leftChain]; omega)
      (by simp [leftChain]; omega) ho

/-- One pair runs its two graph chains and reaches the next block with all invariants restored. -/
theorem pair_refines (q : Fin 16)
    (good : digit index.val (2*q.val)+coarseDigit index q ≤ pairCap q)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index wire pk u z (2*q.val+3) →
      (∃ junk, Riscv.CodeAt u u.pc (nextCode q ++ junk)) →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,cursor (2*q.val+3))) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index wire pk s x (leftChain q))
    (start : q.val = 0 → s.pc = W freeLanding)
    (located : ∃ junk, Riscv.CodeAt s s.pc (prologue q ++ junk))
    (bound : pairCost index q+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (viewPayload wire) (chainNodes (leftChain q) ++ chainNodes (rightChain q))
        x (cursor (leftChain q)) >>= K) (pairCost index q+c) := by
  let A := leftChain q
  let B := rightChain q
  let NA := remaining index A
  let NB := remaining index B
  let L := (lengthSetup q).length
  have cost : pairCost index q = L+((dispatchCode q).length+(NA+(2+NB))) := by
    unfold pairCost; dsimp [L,NA,NB,A,B]; omega
  rw [cost] at bound ⊢
  obtain ⟨junk0, located⟩ := located
  rw [prologue_parts] at located
  simp only [List.append_assoc] at located
  have ready := lengthSetup_ready s q
  set s1 := (lengthSetup q).foldl execInstrBr s with hs1
  obtain ⟨E, s1ctx, s1input, s1payload, s1done⟩ := after_lengthSetup index wire pk q s x inv
  obtain ⟨s1start, s1link⟩ := prologue_facts index wire pk q s x inv start
  have s1loc : Riscv.CodeAt s1 s1.pc (dispatchCode q ++ junk0) := by
    rw [show s1.pc=s.pc+W (4*L) from Riscv.linear_fold_pc s _ ready]
    exact located.append_right.code_eq E.code
  rw [show fuel=L+(fuel-L) by omega,
    show L+((dispatchCode q).length+(NA+(2+NB)))+c =
      L+((dispatchCode q).length+(NA+(2+(NB+c)))) by omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hs1, runNodes'_append, bind_assoc]
  apply prologue_refines index wire pk q A rfl s1 x s1ctx s1input E.length s1payload s1done junk0
    s1start s1link s1loc _ (NA+(2+(NB+c))) (fuel-L) (by omega)
  intro s3 prep3 pc3
  have loc3 := landing_located index s3 prep3.inv.ctx.code q good
  rw [← pc3] at loc3
  apply table_refines index wire pk A
    (enter B (prevInput B) ++ (List.replicate NB .ECALL ++ nextCode q))
    (fun r => runNodes' index (viewPayload wire) (chainNodes B) r.1 r.2 >>= K)
    (2+(NB+c)) (2+(NB+rest)) (s3.pc + W (4 * remaining index A)) ?_
    s3 x (fuel-L-(dispatchCode q).length) prep3 (by simpa only [List.append_assoc] using loc3)
    rfl (by omega)
  intro s4 x4 inv4 loc4 _ left4 hleft4
  dsimp only
  rw [← cursor_step A]
  change Riscv.Refines left4 s4
    (runNodes' index (viewPayload wire) (chainNodes B) x4 (cursor B) >>= K) (2+(NB+c))
  have lenB : s4.getReg .x11 = W (chainBits B) := by
    rw [inv4.length]
    congr 1
    exact prevBits_right q
  have out4 : s4.getReg .x12 = W (outAddr (2*q.val+1)) := inv4.out (by omega)
  apply move_refines index wire pk q B rfl s4 x4 (List.replicate NB .ECALL ++ nextCode q)
    inv4.ctx inv4.input out4 lenB inv4.payload inv4.done loc4 _ (NB+c) left4 (by omega)
  intro s5 inv5 held5 loc5
  apply table_refines index wire pk B (nextCode q) K c rest (s5.pc + W (4 * remaining index B)) ?_
    s5 x4 (left4-2) ⟨inv5, held5⟩ loc5 rfl (by omega)
  intro s6 x6 inv6 loc6 _ left6 hleft6
  have endIndex : B.val+1 = 2*q.val+3 := by dsimp [B,rightChain]
  rw [endIndex] at inv6
  rw [← cursor_step B, endIndex]
  exact continuation s6 x6 inv6 ⟨[], by simpa only [List.append_nil] using loc6⟩ left6 hleft6

/-- Length setup, prologue, and the landing's jump to a rejection stub. -/
def badPairCost (q : Fin 16) : ℕ := (lengthSetup q).length + (dispatchCode q).length + 4

/-- Exact charge of the staged chain/root program, including rejecting paths. -/
def stagedCost (index : RawIdx) : (n q : ℕ) → ℕ
  | 0, _ => 20
  | n+1, q => if hq : q < 16 then
      if PairAllowed index.val q then pairCost index ⟨q,hq⟩ + stagedCost index n (q+1)
      else badPairCost ⟨q,hq⟩
    else 0

/-- A forbidden table entry rejects before any hash of the pair. -/
theorem pair_bad_refines (q : Fin 16)
    (bad : pairCap q < digit index.val (2*q.val)+coarseDigit index q)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index wire pk s x (leftChain q))
    (start : q.val = 0 → s.pc = W freeLanding)
    (located : ∃ junk, Riscv.CodeAt s s.pc (prologue q ++ junk))
    (bound : badPairCost q ≤ fuel) :
    Riscv.Refines fuel s (pure (some false)) (badPairCost q) := by
  let L := (lengthSetup q).length
  obtain ⟨junk, located⟩ := located
  rw [prologue_parts] at located
  simp only [List.append_assoc] at located
  have ready := lengthSetup_ready s q
  set s1 := (lengthSetup q).foldl execInstrBr s with hs1
  obtain ⟨E, s1ctx, s1input, s1payload, s1done⟩ := after_lengthSetup index wire pk q s x inv
  obtain ⟨s1start, s1link⟩ := prologue_facts index wire pk q s x inv start
  have loc : Riscv.CodeAt s1 s1.pc (dispatchCode q ++ junk) := by
    rw [show s1.pc=s.pc+W (4*L) from Riscv.linear_fold_pc s _ ready]
    exact located.append_right.code_eq E.code
  unfold badPairCost at bound ⊢
  rw [show fuel=L+(fuel-L) by omega,
    show L+(dispatchCode q).length+4 = L+((dispatchCode q).length+4) by omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hs1]
  apply prologue_refines index wire pk q (leftChain q) rfl s1 x s1ctx s1input E.length s1payload
    s1done junk s1start s1link loc _ 4 (fuel-L) (by omega)
  intro s3 prep3 pc3
  exact landing_reject_refines index q s3 prep3.inv.ctx.code pc3 bad
    (fuel-L-(dispatchCode q).length) (by omega)

end OptimalOTS.RiscvMixedProgram
