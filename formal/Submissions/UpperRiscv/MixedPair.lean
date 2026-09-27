import Submissions.UpperRiscv.MixedReject

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedDigits

variable (index : RawIdx) (v : ℕ) (wire : List Bool) (pk : PublicKey) {a : ℕ}

def pairCost (q : Fin 16) : ℕ := (lengthSetup q).length +
  (2+2*earlyHash (leftChain q)) + 2 + remaining index v (leftChain q) +
  (2+2*earlyHash (rightChain q)) + remaining index v (rightChain q)

def badPairCost (q : Fin 16) : ℕ :=
  (lengthSetup q).length + (2+2*earlyHash (leftChain q)) + 2 + 4

structure LengthEffect (s u : MachineState) (q : Fin 16) : Prop where
  length : u.getReg .x11 = W (chainBits (leftChain q))
  regs : ∀ r, r ≠ .x11 → u.getReg r = s.getReg r
  mem : u.mem=s.mem
  code : u.code=s.code

theorem lengthSetup_ready (s : MachineState) (q : ℕ) : Riscv.LinearReady s (lengthSetup q) := by
  unfold lengthSetup widthChange
  split_ifs <;> simp [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem lengthSetup_cases' : ∀ q : Fin 16,
    (lengthSetup q = [] ∧ prevBits (leftChain q) = chainBits (leftChain q)) ∨
    (lengthSetup q = [.ADDI .x11 .x0 (BitVec.ofNat 12 (chainBits (leftChain q)))]) := by
  decide +kernel

theorem prevBits_right' : ∀ q : Fin 16, prevBits (rightChain q) = chainBits (rightChain q) := by
  decide +kernel

theorem lengthSetup_effect (s : MachineState) (q : Fin 16)
    (h : s.getReg .x11 = W (prevBits (leftChain q))) :
    LengthEffect s ((lengthSetup q).foldl execInstrBr s) q := by
  rcases lengthSetup_cases' q with ⟨he, hw⟩ | he
  · rw [he, List.foldl_nil]
    exact ⟨h.trans (congrArg W hw), fun _ _ => rfl, rfl, rfl⟩
  · rw [he]
    have hb := chainBits_le (leftChain q)
    refine ⟨?_, ?_, rfl, rfl⟩
    · simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ite]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, if_true, getReg_x0']
      rw [signExtend12_nat _ (by omega)]
      exact BitVec.zero_add _
    · intro r hr; simp [execInstrBr, getReg_setReg_ite, hr]

theorem pairCost_eq (q : Fin 16) (hv : v < 16) : pairCost index v q =
    (lengthSetup q).length+6+2*earlyHash (leftChain q)+2*earlyHash (rightChain q) +
      (digit index.val (2*q.val)+1-rowShort (leftChain q)) +
      (coarseDigit index q+1-rowShort (rightChain q)) := by
  have ha := remaining_left index v q hv
  have hb := remaining_right index v q hv
  have ba := earlyHash_cases (leftChain q)
  have bb := earlyHash_cases (rightChain q)
  unfold pairCost
  rw [ha, hb]
  omega

/-- One pair runs its two graph chains and reaches the next block with all invariants restored. -/
theorem pair_refines (q : Fin 16) (hv : v < 16)
    (good : digit index.val (2*q.val)+coarseDigit index q ≤ pairCap q)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : 5328 ≤ wire.length)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index v wire pk a u z (2*(q.val+1)+1) →
      (∃ junk, Riscv.CodeAt u u.pc (nextCode q ++ junk)) →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,Payload.graphOff (2*(q.val+1)+1))) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index v wire pk a s x (leftChain q))
    (located : ∃ junk, Riscv.CodeAt s s.pc (prologue q ++ junk))
    (bound : pairCost index v q+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index v (Payload.permute wire)
        (entryNodes index v (leftChain q) ++ tableNodes index v (leftChain q) ++
          chainNodes (rightChain q))
        x (Payload.graphOff (leftChain q)) >>= K) (pairCost index v q+c) := by
  let A := leftChain q
  let B := rightChain q
  let EA := 2+2*earlyHash A
  let EB := 2+2*earlyHash B
  let NA := remaining index v A
  let NB := remaining index v B
  let L := (lengthSetup q).length
  have cost : pairCost index v q = L+(EA+(2+(NA+(EB+NB)))) := by
    unfold pairCost; dsimp [L,EA,EB,NA,NB,A,B]; omega
  rw [cost] at bound ⊢
  obtain ⟨junk0, located⟩ := located
  rw [prologue_parts] at located
  simp only [List.append_assoc] at located
  have ready := lengthSetup_ready s q
  set s1 := (lengthSetup q).foldl execInstrBr s with hs1
  have E := lengthSetup_effect s q inv.length
  have s1ctx : Ctx s1 index v pk a := inv.ctx.frame (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact E.regs _ (by decide)) E.mem E.code
  have s1input : s1.getReg .x10 = W (prevInput A) := by rw [E.regs .x10 (by decide)]; exact inv.input
  have s1payload : PayloadFrom s1 wire A := fun j hj => memBits_of_mem_eq E.mem (inv.payload j hj)
  have s1done : Completed s1 x A := fun j hj => memBits_of_mem_eq E.mem (inv.done j hj)
  have s1tail : TailInv index v wire s1 x A := memBits_of_mem_eq E.mem inv.tail
  have s1loc : Riscv.CodeAt s1 s1.pc
      (enter A (prevInput A) ++ (dispatchCode q ++ junk0)) := by
    rw [show s1.pc=s.pc+W (4*L) from Riscv.linear_fold_pc s _ ready]
    exact located.append_right.code_eq E.code
  rw [show fuel=L+(fuel-L) by omega,
    show L+(EA+(2+(NA+(EB+NB))))+c = L+(EA+(2+(NA+(EB+(NB+c))))) by omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hs1]
  rw [List.append_assoc, runNodes'_append, bind_assoc]
  apply enter_refines index v wire pk A (dispatchCode q ++ junk0)
    (fun r => runNodes' index v (Payload.permute wire) (tableNodes index v A ++ chainNodes B)
      r.1 r.2 >>= K)
    (2+(NA+(EB+(NB+c)))) (2+(NA+(EB+(NB+rest)))) hlen ?_
    s1 x (fuel-L) s1ctx s1input E.length s1payload s1done s1tail s1loc (by dsimp [EA] at *; omega)
  intro s2 x2 prep2 loc2 left2 hleft2
  dsimp only
  apply dispatch_refines index v wire pk q A rfl s2 x2 prep2.inv junk0 loc2 _
    (NA+(EB+(NB+c))) left2 (by omega)
  intro s3 inv3 mem3 pc3
  have prep3 := Prepared.frame index v wire pk prep2 inv3 mem3
  obtain ⟨junk, loc3⟩ := landing_located index v hv s3 inv3.ctx.code q good
  rw [← pc3] at loc3
  rw [runNodes'_append, bind_assoc]
  apply table_refines index v wire pk A
    (enter B (prevInput B) ++ (List.replicate NB .ECALL ++ (nextCode q ++ junk)))
    (fun r => runNodes' index v (Payload.permute wire) (chainNodes B) r.1 r.2 >>= K)
    (EB+(NB+c)) (EB+(NB+rest)) hlen ?_
    s3 x2 (left2-2) prep3 (by simpa only [List.append_assoc] using loc3) (by omega)
  intro s4 x4 inv4 loc4 left4 hleft4
  dsimp only
  have hcur : Payload.graphOff A + chainBits A = Payload.graphOff B :=
    (graphOff_step' A).symm
  rw [hcur]
  rw [chain_entry_split index v B, runNodes'_append, bind_assoc]
  have lenB : s4.getReg .x11 = W (chainBits B) := by
    rw [inv4.length]
    have := prevBits_right' q
    dsimp [A, B, leftChain, rightChain] at this ⊢
    rw [this]
  apply enter_refines index v wire pk B (List.replicate NB .ECALL ++ (nextCode q ++ junk))
    (fun r => runNodes' index v (Payload.permute wire) (tableNodes index v B) r.1 r.2 >>= K)
    (NB+c) (NB+rest) hlen ?_ s4 x4 left4 inv4.ctx inv4.input lenB inv4.payload inv4.done inv4.tail
    loc4 (by dsimp [EB] at *; omega)
  intro s5 x5 prep5 loc5 left5 hleft5
  dsimp only
  apply table_refines index v wire pk B (nextCode q ++ junk) K c rest hlen ?_
    s5 x5 left5 prep5 loc5 hleft5
  intro s6 x6 inv6 loc6 left6 hleft6
  have endIndex : B.val+1 = 2*(q.val+1)+1 := by dsimp [B,rightChain]; omega
  rw [endIndex] at inv6
  have hcur2 : Payload.graphOff B + chainBits B = Payload.graphOff (2*(q.val+1)+1) := by
    have := graphOff_step' B
    rw [← endIndex]
    exact this.symm
  rw [hcur2]
  exact continuation s6 x6 inv6 ⟨junk,loc6⟩ left6 hleft6

/-- A forbidden table entry rejects after precisely the first entry hash, if any. -/
theorem pair_bad_refines (q : Fin 16)
    (bad : pairCap q < digit index.val (2*q.val)+coarseDigit index q)
    (hlen : 5328 ≤ wire.length)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index v wire pk a s x (leftChain q))
    (located : ∃ junk, Riscv.CodeAt s s.pc (prologue q ++ junk))
    (bound : badPairCost q ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index v (Payload.permute wire) (entryNodes index v (leftChain q)) x
        (Payload.graphOff (leftChain q)) >>= fun _ => pure (some false)) (badPairCost q) := by
  let A := leftChain q
  let L := (lengthSetup q).length
  let EA := 2+2*earlyHash A
  have cost : badPairCost q = L+(EA+(2+4)) := by
    unfold badPairCost; dsimp [L,EA,A]; omega
  rw [cost] at bound ⊢
  obtain ⟨junk, located⟩ := located
  rw [prologue_parts] at located
  simp only [List.append_assoc] at located
  have ready := lengthSetup_ready s q
  set s1 := (lengthSetup q).foldl execInstrBr s with hs1
  have E := lengthSetup_effect s q inv.length
  have ctx : Ctx s1 index v pk a := inv.ctx.frame (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact E.regs _ (by decide)) E.mem E.code
  have input : s1.getReg .x10 = W (prevInput A) := by
    rw [E.regs .x10 (by decide)]; exact inv.input
  have payload : PayloadFrom s1 wire A := fun j hj => memBits_of_mem_eq E.mem (inv.payload j hj)
  have done : Completed s1 x A := fun j hj => memBits_of_mem_eq E.mem (inv.done j hj)
  have tailI : TailInv index v wire s1 x A := memBits_of_mem_eq E.mem inv.tail
  have loc : Riscv.CodeAt s1 s1.pc (enter A (prevInput A) ++ (dispatchCode q ++ junk)) := by
    rw [show s1.pc=s.pc+W (4*L) from Riscv.linear_fold_pc s _ ready]
    exact located.append_right.code_eq E.code
  rw [show fuel=L+(fuel-L) by omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hs1]
  apply enter_refines index v wire pk A (dispatchCode q ++ junk)
    (fun _ => pure (some false)) (2+4) (2+4) hlen ?_
    s1 x (fuel-L) ctx input E.length payload done tailI loc (by dsimp [EA] at *; omega)
  intro s2 x2 prep loc2 left hleft
  apply dispatch_refines index v wire pk q A rfl s2 x2 prep.inv junk loc2 _ 4 left (by omega)
  intro s3 inv3 _ pc3
  exact landing_reject_refines index q s3 inv3.ctx.code pc3 bad (left-2) (by omega)

/-- Exact charge of the staged pair/root program, including rejecting paths. -/
def stagedCost (index : RawIdx) (v : ℕ) : (n q : ℕ) → ℕ
  | 0, _ => 22
  | n+1, q => if hq : q < 16 then
      if PairAllowed index.val q then pairCost index v ⟨q,hq⟩ + stagedCost index v n (q+1)
      else badPairCost ⟨q,hq⟩
    else 0

end OptimalOTS.RiscvMixedProgram
