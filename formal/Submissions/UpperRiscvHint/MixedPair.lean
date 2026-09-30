import Submissions.UpperRiscvHint.MixedHelpers

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.RiscvMixedProgram
variable {credit : BitVec 64}
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : ChainIndex) (wire : List Bool) (pk : PublicKey)

/-- The right chain's share of a pair: a skip costs only the skip row's checksum unit (none after
a redirect, whose correction already ran); otherwise the pointer pair and its hashes. -/
def rightCost (q : Fin 16) : ℕ :=
  if skipFlag index q then (if PairCode.helper q (rawPair index.val q) = 0 then 1 else 0)
  else 2 + remaining index (rightChain q)

/-- Length setup, prologue, both chains' hashes and the pointer move between them. -/
def pairCost (q : Fin 16) : ℕ := (lengthSetup q).length + 4 +
  pairFee index q + remaining index (leftChain q) + rightCost index q

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

/-- After a skipped cap pair the width is unchanged: chains up to 13 are 192-bit. -/
theorem prevBits_skip (q : Fin 16) (h : q.val < 6) :
    prevBits (rightChain q) = prevBits (2*q.val+3) := by
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

/-- Where `x10` starts a pair: the previous chain's state, or after a skipped right chain the
state of the chain before it. -/
def entryBase (sk : Bool) (k : ℕ) : ℕ := if sk then prevInput (k-1) else prevInput k
/-- The chain `x12` addresses when a pair starts. -/
def entryOut (sk : Bool) (k : ℕ) : ℕ := if sk then k-2 else k-1

/-- `ChainsInv`, with `x10` and `x12` one chain back after a skipped right chain. -/
structure EntryInv (sk : Bool) (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop where
  ctx : Ctx (credit := credit) s index wire pk
  input : s.getReg .x10 = W (entryBase sk k)
  out : 2 ≤ k → s.getReg .x12 = W (outAddr (entryOut sk k))
  length : s.getReg .x11 = W (prevBits k)
  payload : PayloadFrom s wire k
  done : Completed s (tops x) k

theorem ChainsInv.entry {s : MachineState} {x : graph.Assignment} {k : ℕ}
    (inv : ChainsInv (credit := credit) index wire pk s x k) :
    EntryInv (credit := credit) index wire pk false s x k :=
  ⟨inv.ctx, inv.input, fun h => inv.out (by omega), inv.length, inv.payload, inv.done⟩

theorem EntryInv.chains {s : MachineState} {x : graph.Assignment} {k : ℕ}
    (inv : EntryInv (credit := credit) index wire pk false s x k) (hk : k ≠ 1) :
    ChainsInv (credit := credit) index wire pk s x k := by
  refine ⟨inv.ctx, inv.input, fun h => inv.out (by omega), inv.length, inv.payload, inv.done⟩

/-- The code a pair starts at, and the code after it. -/
def entryCode (sk : Bool) (q : ℕ) : Code := if sk then skipPrologue q else prologue q
def exitCode (q : Fin 16) : Code := if skipFlag index q then skipNext q else nextCode q

theorem entryCode_parts (sk : Bool) (q : Fin 16) (hsk : sk = true → 1 ≤ q.val) :
    entryCode sk q = lengthSetup q ++ dispatchCode q (entryBase sk (leftChain q)) := by
  cases sk
  · simp only [entryCode, entryBase, Bool.false_eq_true, if_false]
    rw [prologue_parts]; rfl
  · simp only [entryCode, entryBase, if_true]
    rw [skipPrologue_parts]
    have h := hsk rfl
    congr 2
    unfold prevInput leftChain
    rw [if_neg (by simp; omega)]
    congr 1 <;> (try simp) <;> omega

theorem entryBase_front (sk : Bool) (q : Fin 16) (hsk : sk = true → 1 ≤ q.val ∧ q.val ≤ 6) :
    FrontBase q (entryBase sk (leftChain q)) := by
  cases sk
  · exact frontBase_prev q
  · obtain ⟨h1, h6⟩ := hsk rfl
    have e : entryBase true (leftChain q) = work (2*q.val-1) := by
      unfold entryBase prevInput leftChain
      simp only [if_true]
      rw [if_neg (by simp; omega)]
      congr 1
    rw [e]; exact frontBase_skip q h1 h6

theorem pairCost_eq (q : Fin 16) : pairCost index q =
    (lengthSetup q).length + 4 + pairFee index q + remaining index (leftChain q) + rightCost index q :=
  rfl

theorem ChainsInv.recredit {s t : MachineState} {x : graph.Assignment} {k : ℕ}
    (inv : ChainsInv (credit := credit) index wire pk s x k) (next : Word)
    (regs : ∀ r, r ≠ .x27 → t.getReg r = s.getReg r)
    (mem : t.mem = s.mem) (code : t.code = s.code) (sum : t.getReg .x27 = next) :
    ChainsInv (credit := next) index wire pk t x k := by
  refine ⟨inv.ctx.recredit next regs mem code sum, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs .x10 (by decide)]; exact inv.input
  · intro h; rw [regs .x12 (by decide)]; exact inv.out h
  · rw [regs .x11 (by decide)]; exact inv.length
  · intro j hj; exact memBits_of_mem_eq mem (inv.payload j hj)
  · intro j hj; exact memBits_of_mem_eq mem (inv.done j hj)

/-- A skipped right chain: its view value is its top, no instruction runs, and the pointers
stay one chain back. -/
theorem skipped_refines (k : Chain) (hidden : 32 ≤ firstAt index k) (hk : 2 ≤ k.val)
    (hbits : prevBits k = prevBits (k.val+1))
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c : ℕ)
    (continuation : ∀ z : graph.Assignment,
      EntryInv (credit := credit) index wire pk true s z (k.val+1) →
      Riscv.Refines fuel s (K (z,cursor k+chainBits k)) c)
    (inv : ChainsInv (credit := credit) index wire pk s x k) :
    Riscv.Refines fuel s
      (runNodes' index (viewPayload wire) (chainNodes k) x (cursor k) >>= K) c := by
  have cap : k.val < 13 ∨ 31 ≤ k.val := by
    by_contra h
    have : firstAt index k ≤ 31 := by
      unfold firstAt firstEval; rw [if_neg h]; exact pos_le index k
    omega
  have hb : topBits k = chainBits k := topBits_of_cap cap
  obtain ⟨x', run, frame⟩ := prefix_run index (viewPayload wire) k 32 hidden x (cursor k)
  rw [chain_split_hidden, runNodes'_append, run, pure_bind,
    top_run_read index (viewPayload wire) k hidden, pure_bind]
  have hc : cursor k + topBits k = cursor k + chainBits k := by rw [hb]
  rw [hc]
  apply continuation
  refine ⟨inv.ctx, ?_, ?_, ?_, fun j hj => inv.payload j (by omega), ?_⟩
  · rw [inv.input]; unfold entryBase; simp
  · intro _
    rw [inv.out (by omega)]; unfold entryOut; simp
  · rw [inv.length, hbits]
  · intro j hj
    by_cases he : j = k
    · subst j
      rw [tops_update_top]
      apply (memBits_cast _ _ _ _).mpr
      rw [ofBits_take]
      have hw : graph.len (top k).fin = chainBits k := by rw [graph_len_fin]; exact hb
      have e : work k = topAddr k := by
        rw [work_eq' k]
        unfold topAddr
        rw [topOff_cap cap]
      have key : ∀ n, n = chainBits k →
          MemBits s (W (topAddr k)) (ofBits n ((viewPayload wire).drop (cursor k))) := by
        intro n hn
        subst hn
        rw [viewPayload_read wire k, ← e]
        exact inv.payload k le_rfl
      exact key _ hw
    · rw [tops_update_top_other _ _ _ he, frame]
      exact inv.done j (by have hne : j.val ≠ k.val := fun h => he (Fin.ext h); omega)

theorem firstAt_of_remaining (k : Chain) (h : remaining index k = 0) : 32 ≤ firstAt index k := by
  unfold remaining at h; omega

theorem pairCorrection_fixed (q : Fin 16) (h : PairCode.helper q.val (rawPair index.val q) = 0) :
    pairCorrection index q = 4 * PairCode.skip q.val (rawPair index.val q) := by
  have g : mappedPair q (rawPair index.val q).1 (15-(rawPair index.val q).2.val) =
      ((rawPair index.val q).1.val, 15-(rawPair index.val q).2.val) := by
    by_contra hne
    have := redirected_fee q _ _ hne
    rw [Prod.mk.eta] at this
    omega
  exact (fixed_fee_correction q _ _ g).2

theorem landCorrection_plain (q : Fin 16) (h : skipFlag index q = false) :
    landCorrection index q = pairCorrection index q := by
  unfold landCorrection
  split_ifs with hh
  · rw [pairCorrection_fixed index q hh]
    have : PairCode.skip q.val (rawPair index.val q) ≠ 1 := by
      intro e; rw [(skipFlag_iff index q).mpr e] at h; exact Bool.noConfusion h
    have hl := WeightedPairs.skip_le (PairCode.kind q.val) (PairCode.complement (rawPair index.val q))
    change PairCode.skip q.val (rawPair index.val q) ≤ 1 at hl
    omega
  · rfl

/-- Pair 0 starts at `freeLanding`; later pairs start with `x1` holding pair 0's link. -/
theorem entry_link (sk : Bool) (q : Fin 16) (hsk : sk = true → 1 ≤ q.val ∧ q.val ≤ 6)
    (s : MachineState) (x : graph.Assignment)
    (inv : EntryInv (credit := credit) index wire pk sk s x (leftChain q)) (h0 : q.val ≠ 0) :
    s.getReg .x1 = W rootBase := by
  have hk : 2 ≤ (leftChain q).val := by simp [leftChain]; omega
  have ho := inv.out hk
  cases sk
  · exact inv.ctx.base (k := (leftChain q).val - 1) (by simp [leftChain]; omega)
      (by simp [leftChain]; omega) (by simpa [entryOut] using ho)
  · exact inv.ctx.base (k := (leftChain q).val - 2) (by simp [leftChain]; omega)
      (by simp [leftChain]; omega) (by simpa [entryOut] using ho)

/-- One pair runs its two graph chains and reaches the next block with all invariants restored;
a skipped right chain leaves the pointers one chain back. -/
theorem pair_refines (q : Fin 16)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest : ℕ)
    (continuation : ∀ (u : MachineState) (z : graph.Assignment),
      EntryInv (credit := credit + W (pairCorrection index q)) index wire pk (skipFlag index q) u z
        (2*q.val+3) →
      (∃ junk, Riscv.CodeAt u u.pc (exitCode index q ++ junk)) →
      ∀ left, rest ≤ left → Riscv.Refines left u (K (z,cursor (2*q.val+3))) c)
    (sk : Bool) (hsk : sk = true → 1 ≤ q.val ∧ q.val ≤ 6)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : EntryInv (credit := credit) index wire pk sk s x (leftChain q))
    (start : q.val = 0 → s.pc = W freeLanding)
    (located : ∃ junk, Riscv.CodeAt s s.pc (entryCode sk q ++ junk))
    (bound : pairCost index q+rest ≤ fuel) :
    Riscv.Refines fuel s
      (runNodes' index (viewPayload wire) (chainNodes (leftChain q) ++ chainNodes (rightChain q))
        x (cursor (leftChain q)) >>= K) (pairCost index q+c) := by
  let A := leftChain q
  let B := rightChain q
  let NA := remaining index A
  let T := rightCost index q
  let F := pairFee index q
  let L := (lengthSetup q).length
  have cost : pairCost index q = L+((dispatchCode q (entryBase sk A)).length+(F+(NA+T))) := by
    unfold pairCost; rw [dispatchCode_length]; dsimp [L,NA,T,A,F]; omega
  rw [cost] at bound ⊢
  obtain ⟨junk0, located⟩ := located
  rw [entryCode_parts sk q (fun h => (hsk h).1)] at located
  simp only [List.append_assoc] at located
  have ready := lengthSetup_ready s q
  set s1 := (lengthSetup q).foldl execInstrBr s with hs1
  have E := lengthSetup_effect s q inv.length
  have s1ctx : Ctx (credit := credit) s1 index wire pk :=
    inv.ctx.frame (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact E.regs _ (by decide))
      E.mem E.code
  have s1input : s1.getReg .x10 = W (entryBase sk A) := by rw [E.regs .x10 (by decide)]; exact inv.input
  have s1payload : PayloadFrom s1 wire A := fun j hj => memBits_of_mem_eq E.mem (inv.payload j hj)
  have s1done : Completed s1 (tops x) A := fun j hj => memBits_of_mem_eq E.mem (inv.done j hj)
  have s1start : q.val = 0 → s1.pc = W freeLanding := by
    intro h0
    have hl : lengthSetup q = [] := by simp [lengthSetup, h0]
    change ((lengthSetup q).foldl execInstrBr s).pc = _
    rw [hl, List.foldl_nil]
    exact start h0
  have s1link : q.val ≠ 0 → s1.getReg .x1 = W rootBase := by
    intro h0
    rw [E.regs .x1 (by decide)]
    exact entry_link index wire pk sk q hsk s x inv h0
  have s1loc : Riscv.CodeAt s1 s1.pc (dispatchCode q (entryBase sk A) ++ junk0) := by
    rw [show s1.pc=s.pc+W (4*L) from Riscv.linear_fold_pc s _ ready]
    exact located.append_right.code_eq E.code
  rw [show fuel=L+(fuel-L) by omega,
    show L+((dispatchCode q (entryBase sk A)).length+(F+(NA+T)))+c =
      L+((dispatchCode q (entryBase sk A)).length+(F+(NA+(T+c)))) by omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hs1, runNodes'_append, bind_assoc]
  apply prologue_refines index wire pk q A rfl (entryBase sk A) (entryBase_front sk q hsk) s1 x s1ctx
    s1input E.length s1payload s1done junk0 s1start s1link s1loc _ (F+(NA+(T+c))) (fuel-L) (by omega)
  intro s3 prep3 pc3
  apply landing_refines index wire pk q _ (NA+(T+c)) (NA+(T+rest)) ?_
    s3 prep3 pc3 (fuel-L-(dispatchCode q (entryBase sk A)).length) (by omega)
  intro sH prepH locH leftH hleftH
  apply table_refines index wire pk A (afterLeft index q)
    (fun r => runNodes' index (viewPayload wire) (chainNodes B) r.1 r.2 >>= K)
    (T+c) (T+rest) (sH.pc + W (4 * remaining index A)) ?_
    sH x leftH prepH locH rfl (by omega)
  intro s4 x4 inv4 loc4 _ left4 hleft4
  dsimp only
  rw [← cursor_step A]
  change Riscv.Refines left4 s4
    (runNodes' index (viewPayload wire) (chainNodes B) x4 (cursor B) >>= K) (T+c)
  have endIndex : B.val+1 = 2*q.val+3 := by dsimp [B,rightChain]
  by_cases hskip : skipFlag index q = true
  · -- the right chain is skipped
    have hcap := skipFlag_cap index q hskip
    have hNB : remaining index B = 0 := skipFlag_right index q hskip
    have hidden : 32 ≤ firstAt index B := firstAt_of_remaining index B hNB
    have hbits : prevBits B = prevBits (B.val+1) := by
      rw [endIndex]; exact prevBits_skip q hcap
    have hB2 : 2 ≤ B.val := by dsimp [B,rightChain]; omega
    have exitEq : exitCode index q = skipNext q := by unfold exitCode; rw [if_pos hskip]
    have inv4' : ChainsInv (credit := credit + W (landCorrection index q)) index wire pk s4 x4 B := by
      simpa only [A, leftChain, B, rightChain] using inv4
    by_cases hh : PairCode.helper q.val (rawPair index.val q) = 0
    · have hT : T = 1 := by dsimp [T]; unfold rightCost; rw [if_pos hskip, if_pos hh]
      have hsk1 : PairCode.skip q.val (rawPair index.val q) = 1 := (skipFlag_iff index q).mp hskip
      have land0 : landCorrection index q = 0 := by unfold landCorrection; rw [if_pos hh]
      have corr4 : pairCorrection index q = 4 := by rw [pairCorrection_fixed index q hh, hsk1]
      have loc4' : Riscv.CodeAt s4 s4.pc ([.ADDI .x27 .x27 (imm12 4)] ++ skipNext q) := by
        have e : afterLeft index q = [.ADDI .x27 .x27 (imm12 4)] ++ skipNext q := by
          unfold afterLeft; rw [if_pos hskip, if_pos hh]
        rw [← e]; exact loc4
      let lin : Code := [.ADDI .x27 .x27 (imm12 4)]
      have lready : Riscv.LinearReady s4 lin := by
        simp [lin, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
      let u := lin.foldl execInstrBr s4
      have uregs : ∀ r, r ≠ .x27 → u.getReg r = s4.getReg r := by
        intro r hr; simp [u, lin, execInstrBr, getReg_setReg_ite, hr]
      have umem : u.mem = s4.mem := rfl
      have ucode : u.code = s4.code := by simp [u, lin, execInstrBr]
      have usum : u.getReg .x27 = credit + W (pairCorrection index q) := by
        have imm : signExtend12 (imm12 4) = W 4 := signExtend12_nat 4 (by norm_num)
        simp [u, lin, execInstrBr, getReg_setReg_ite, imm, inv4'.ctx.checksum, land0, corr4]
      have invU := inv4'.recredit index wire pk (credit + W (pairCorrection index q)) uregs umem ucode usum
      have uloc : Riscv.CodeAt u u.pc (skipNext q) := by
        rw [show u.pc = s4.pc + W (4*lin.length) from Riscv.linear_fold_pc _ _ lready]
        exact loc4'.append_right.code_eq ucode
      have hl1 : lin.length = 1 := rfl
      rw [hT, show left4 = lin.length + (left4-1) by rw [hl1]; have : rightCost index q = 1 := hT; omega,
        show 1+c = lin.length + c by rw [hl1]]
      apply Riscv.Refines.linear _ loc4'.append_left lready
      apply skipped_refines index wire pk B hidden hB2 hbits u x4 (left4-1) K c _ invU
      intro z invZ
      rw [← cursor_step B, endIndex]
      rw [endIndex] at invZ
      apply continuation u z (by rw [hskip]; exact invZ) ⟨[], by rw [exitEq]; simpa using uloc⟩
      have : rightCost index q = T := rfl
      omega
    · have hT : T = 0 := by dsimp [T]; unfold rightCost; rw [if_pos hskip, if_neg hh]
      have land : landCorrection index q = pairCorrection index q := by
        unfold landCorrection; rw [if_neg hh]
      have loc4' : Riscv.CodeAt s4 s4.pc (skipNext q) := by
        have e : afterLeft index q = skipNext q := by
          unfold afterLeft; rw [if_pos hskip, if_neg hh, List.nil_append]
        rw [← e]; exact loc4
      rw [hT, Nat.zero_add]
      rw [land] at inv4'
      apply skipped_refines index wire pk B hidden hB2 hbits s4 x4 left4 K c _ inv4'
      intro z invZ
      rw [← cursor_step B, endIndex]
      rw [endIndex] at invZ
      apply continuation s4 z (by rw [hskip]; exact invZ) ⟨[], by rw [exitEq]; simpa using loc4'⟩
      have : rightCost index q = T := rfl
      omega
  · -- the ordinary right chain
    have hflag : skipFlag index q = false := by simpa using hskip
    let NB := remaining index B
    have hT : T = 2 + NB := by dsimp [T,NB]; unfold rightCost; rw [if_neg hskip]
    have exitEq : exitCode index q = nextCode q := by unfold exitCode; rw [if_neg hskip]
    have land := landCorrection_plain index q hflag
    have loc4' : Riscv.CodeAt s4 s4.pc
        (enter B (prevInput B) ++ (List.replicate NB .ECALL ++ nextCode q)) := by
      have e : afterLeft index q = enter B (prevInput B) ++ (List.replicate NB .ECALL ++ nextCode q) := by
        unfold afterLeft; rw [if_neg hskip, List.append_assoc]
      rw [← e]; exact loc4
    rw [land] at inv4
    rw [hT] at hleft4 ⊢
    have lenB : s4.getReg .x11 = W (chainBits B) := by
      rw [inv4.length]
      congr 1
      exact prevBits_right q
    have out4 : s4.getReg .x12 = W (outAddr (2*q.val+1)) := inv4.out (by omega)
    rw [show 2+NB+c = 2+(NB+c) by omega]
    apply move_refines index wire pk q B rfl s4 x4 (List.replicate NB .ECALL ++ nextCode q)
      inv4.ctx inv4.input out4 lenB inv4.payload inv4.done loc4' _ (NB+c) left4 (by omega)
    intro s5 inv5 held5 loc5
    apply table_refines index wire pk B (nextCode q) K c rest (s5.pc + W (4 * remaining index B)) ?_
      s5 x4 (left4-2) ⟨inv5, held5⟩ loc5 rfl (by omega)
    intro s6 x6 inv6 loc6 _ left6 hleft6
    rw [endIndex] at inv6
    rw [← cursor_step B, endIndex]
    exact continuation s6 x6 (by rw [hflag]; exact inv6.entry index wire pk)
      ⟨[], by rw [exitEq]; simpa only [List.append_nil] using loc6⟩ left6 hleft6

/-- Exact charge after the free chain; every weighted pair is admitted. -/
def stagedCost (index : ChainIndex) : (n q : ℕ) → ℕ
  | 0, _ => 21
  | n+1, q => if hq : q < 16 then
      pairCost index ⟨q,hq⟩ + stagedCost index n (q+1)
    else 0

end OptimalOTS.RiscvMixedProgram
