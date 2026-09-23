import Submissions.UpperRiscv.MixedLanding

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (wire : List Bool) (pk : PublicKey)

def pairCost (q : Fin 16) : ℕ := (lengthSetup q).length +
  (2+2*earlyHash (leftChain q)) + 2 + remaining index (leftChain q) +
  (2+2*earlyHash (rightChain q)) + remaining index (rightChain q)

structure LengthEffect (s u : MachineState) (q : Fin 16) : Prop where
  length : u.getReg .x11 = W (chainBits (leftChain q))
  regs : ∀ r, r ≠ .x11 → u.getReg r = s.getReg r
  mem : u.mem=s.mem
  code : u.code=s.code

theorem lengthSetup_ready (s : MachineState) (q : ℕ) : Riscv.LinearReady s (lengthSetup q) := by
  unfold lengthSetup
  split_ifs <;> simp [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem lengthSetup_effect (s : MachineState) (q : Fin 16)
    (h : s.getReg .x11 = W (prevBits (leftChain q))) :
    LengthEffect s ((lengthSetup q).foldl execInstrBr s) q := by
  by_cases hq : q.val=12
  · have he : q=12 := Fin.ext hq
    subst q
    refine ⟨?_, ?_, rfl, rfl⟩
    · simp [lengthSetup, execInstrBr, getReg_setReg_ite, chainBits, leftChain, W, getReg_x0']
      all_goals decide
    · intro r hr; simp [lengthSetup, execInstrBr, getReg_setReg_ite, hr]
  · have hw : prevBits (leftChain q) = chainBits (leftChain q) := by
      change (if 2*q.val ≤ 24 then 160 else 192) = (if 2*q.val < 24 then 160 else 192)
      split_ifs <;> omega
    simp only [lengthSetup, if_neg hq, List.foldl_nil]
    exact ⟨h.trans (congrArg W hw), fun _ _ => rfl, rfl, rfl⟩

theorem pairCost_eq (q : Fin 16) : pairCost index q =
    (lengthSetup q).length+6+earlyHash (leftChain q)+earlyHash (rightChain q) +
      (32-RiscvUpperForest.ForestVerifier.pos index (leftChain q)) +
      (32-RiscvUpperForest.ForestVerifier.pos index (rightChain q)) := by
  have ha := pos_le index (leftChain q)
  have hb := pos_le index (rightChain q)
  have ba := earlyHash_cases (leftChain q)
  have bb := earlyHash_cases (rightChain q)
  unfold pairCost remaining
  omega

/-- One pair runs its two graph chains and reaches the next block with all invariants restored. -/
theorem pair_refines (q : Fin 16)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (hlen : wire.length = 5376)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      ChainsInv index wire pk u z (2*(q.val+1)) →
      (∃ junk, Riscv.CodeAt u u.pc (nextCode q ++ junk)) →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,cursor (2*(q.val+1)))) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index wire pk s x (leftChain q))
    (located : ∃ junk, Riscv.CodeAt s s.pc (prologue q ++ junk))
    (bound : pairCost index q+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (Payload.permute wire) (chainNodes (leftChain q) ++ chainNodes (rightChain q))
        x (cursor (leftChain q)) >>= K) (pairCost index q+c) := by
  let A := leftChain q
  let B := rightChain q
  let EA := 2+2*earlyHash A
  let EB := 2+2*earlyHash B
  let NA := remaining index A
  let NB := remaining index B
  let L := (lengthSetup q).length
  have cost : pairCost index q = L+(EA+(2+(NA+(EB+NB)))) := by
    unfold pairCost; dsimp [L,EA,EB,NA,NB,A,B]; omega
  rw [cost] at bound ⊢
  obtain ⟨junk0, located⟩ := located
  rw [prologue_parts] at located
  simp only [List.append_assoc] at located
  have ready := lengthSetup_ready s q
  set s1 := (lengthSetup q).foldl execInstrBr s with hs1
  have E := lengthSetup_effect s q inv.length
  have s1ctx : Ctx s1 index pk := inv.ctx.frame (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl <;> exact E.regs _ (by decide)) E.mem E.code
  have s1input : s1.getReg .x10 = W (prevInput A) := by rw [E.regs .x10 (by decide)]; exact inv.input
  have s1payload : PayloadFrom s1 wire A := fun j hj => memBits_of_mem_eq E.mem (inv.payload j hj)
  have s1done : Completed s1 (tops x) A := fun j hj => memBits_of_mem_eq E.mem (inv.done j hj)
  have s1loc : Riscv.CodeAt s1 s1.pc
      (enter A (prevInput A) ++ (dispatchCode q ++ junk0)) := by
    rw [show s1.pc=s.pc+W (4*L) from Riscv.linear_fold_pc s _ ready]
    exact located.append_right.code_eq E.code
  rw [show fuel=L+(fuel-L) by omega,
    show L+(EA+(2+(NA+(EB+NB))))+c = L+(EA+(2+(NA+(EB+(NB+c))))) by omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hs1]
  rw [runNodes'_append, chain_entry_split index A, runNodes'_append]
  simp only [bind_assoc]
  apply enter_refines index wire pk A (dispatchCode q ++ junk0)
    (fun r => runNodes' index (Payload.permute wire) (tableNodes index A) r.1 r.2 >>= fun r =>
      runNodes' index (Payload.permute wire) (chainNodes B) r.1 r.2 >>= K)
    (2+(NA+(EB+(NB+c)))) (2+(NA+(EB+(NB+rest)))) hlen ?_
    s1 x (fuel-L) s1ctx s1input E.length s1payload s1done s1loc (by dsimp [EA] at *; omega)
  intro s2 x2 prep2 loc2 left2 hleft2
  dsimp only
  apply dispatch_refines index wire pk q A rfl s2 x2 prep2.inv junk0 loc2 _
    (NA+(EB+(NB+c))) left2 (by omega)
  intro s3 inv3 mem3 pc3
  have prep3 := prep2.frame inv3 mem3
  obtain ⟨junk, loc3⟩ := landing_located index s3 inv3.ctx.code q
  rw [← pc3] at loc3
  apply table_refines index wire pk A
    (enter B (prevInput B) ++ (List.replicate NB .ECALL ++ (nextCode q ++ junk)))
    (fun r => runNodes' index (Payload.permute wire) (chainNodes B) r.1 r.2 >>= K)
    (EB+(NB+c)) (EB+(NB+rest)) hlen ?_
    s3 x2 (left2-2) prep3 (by simpa only [List.append_assoc] using loc3) (by omega)
  intro s4 x4 inv4 loc4 left4 hleft4
  dsimp only
  rw [← cursor_step A]
  change Riscv.Refines left4 s4
    (runNodes' index (Payload.permute wire) (chainNodes B) x4 (cursor B) >>= K) (EB+(NB+c))
  rw [chain_entry_split index B, runNodes'_append, bind_assoc]
  have lenB : s4.getReg .x11 = W (chainBits B) := by
    rw [inv4.length]
    congr 1
    change (if 2*q.val+1 ≤ 24 then 160 else 192) = (if 2*q.val+1 < 24 then 160 else 192)
    split_ifs <;> omega
  apply enter_refines index wire pk B (List.replicate NB .ECALL ++ (nextCode q ++ junk))
    (fun r => runNodes' index (Payload.permute wire) (tableNodes index B) r.1 r.2 >>= K)
    (NB+c) (NB+rest) hlen ?_ s4 x4 left4 inv4.ctx inv4.input lenB inv4.payload inv4.done loc4
    (by dsimp [EB] at *; omega)
  intro s5 x5 prep5 loc5 left5 hleft5
  dsimp only
  apply table_refines index wire pk B (nextCode q ++ junk) K c rest hlen ?_
    s5 x5 left5 prep5 loc5 hleft5
  intro s6 x6 inv6 loc6 left6 hleft6
  have endIndex : B.val+1 = 2*(q.val+1) := by dsimp [B,rightChain]; omega
  rw [endIndex] at inv6
  rw [← cursor_step B, endIndex]
  exact continuation s6 x6 inv6 ⟨junk,loc6⟩ left6 hleft6

end OptimalOTS.RiscvMixedProgram
