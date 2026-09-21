import Submissions.UpperRiscv.ChainPrologue

/-!
# The hash steps of a chain

Level `t` of chain `k` hashes the 192-bit value at the slot and writes the answer eight bytes
below the slot, exactly as the specification evaluates the nodes `ci k t`, `ch k t`, `cv k t`:
the high 192 bits of the answer land on the slot and are the next input.
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (payload : List Bool) (pk : PublicKey)

/-! ## Small facts -/

theorem fin_ne_of_ne {m n : Name} (h : m ≠ n) : m.fin ≠ n.fin :=
  fun e => h (Name.fin_injective e)

theorem writeHash_regs (w : MachineState) (a : BitVec hashBits) (r : Reg) :
    (Riscv.writeHash w a).getReg r = w.getReg r := by
  simp [Riscv.writeHash]

theorem writeHash_code (w : MachineState) (a : BitVec hashBits) :
    (Riscv.writeHash w a).code = w.code := by
  simp [Riscv.writeHash]

theorem writeHash_pc (w : MachineState) (a : BitVec hashBits) :
    (Riscv.writeHash w a).pc = w.pc + 4 := rfl

theorem trunc_extract (y : BitVec 256) : Forest.trunc y = y.extractLsb' 64 192 := rfl

theorem lo192_extract (y : BitVec 256) : lo192 y = y.extractLsb' 0 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lo192, hi]

/-- The high 192 bits of an answer written eight bytes below a slot lie on the slot. -/
theorem holds_of_answer {s : MachineState} {k : ℕ} (hk : k < 28) {y : BitVec 256}
    (h : MemBits s (W (slotAddr k - 8)) y) : Holds s k (Forest.trunc y) := by
  have hs := slot_bounds k hk
  have e := memBits_extract (start := 64) (len := 192) h (by decide) (by decide)
  rw [show (64 : ℕ) / 8 = 8 by norm_num, W_add,
    show slotAddr k - 8 + 8 = slotAddr k by unfold slotAddr payloadAddr; omega] at e
  rw [trunc_extract]
  exact e

/-- The low 192 bits of an answer written eight bytes below a slot. -/
theorem lo_of_answer {s : MachineState} {k : ℕ} {y : BitVec 256}
    (h : MemBits s (W (slotAddr k - 8)) y) : MemBits s (W (slotAddr k - 8)) (lo192 y) := by
  have e := memBits_extract (start := 0) (len := 192) h (by decide) (by decide)
  rw [show (0 : ℕ) / 8 = 0 by norm_num, BitVec.add_zero] at e
  rw [lo192_extract]
  exact e

/-! ## Invariant within a chain -/

/-- Machine facts holding before the hash step of level `t` of chain `k`. The level `t` only
indexes the invariant; the program counter is tracked by the located code. -/
structure StepInv (s : MachineState) (x : graph.Assignment) (k : Fin 28) (t : ℕ) : Prop where
  ctx : Ctx s index pk
  input : s.getReg .x10 = slotW k
  out : s.getReg .x12 = W (slotAddr k - 8)
  payload : PayloadFrom s payload (k.val + 1)
  done : 1 ≤ k.val → MemBits s (W regionAddr) (lowCat (topFun (tops x)) (k.val - 1))

/-- The three specification steps of a level, as one hash of the input `v`. -/
def tripleUpdate (x : graph.Assignment) (k : Fin 28) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) : graph.Assignment :=
  Function.update (Function.update (Function.update x (ci k t).fin v)
    (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm))
    (cv k t).fin (((y.cast (graph_len_fin (ch k t)).symm).cast (lenF_ch k t)).cast
      (graph_len_fin (cv k t)).symm)

/-- The disclosed level: the input is read from the payload. -/
theorem triple_run_read (k : Fin 28) (t : Fin 32) (ht : RiscvUpperForest.ForestVerifier.pos index k = t.val)
    (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index payload [ci k t, ch k t, cv k t] x cursor =
      hash (ofBits (graph.len (ci k t).fin) ((payload.drop cursor).take (graph.len (ci k t).fin)))
        >>= fun y => pure (tripleUpdate x k t
          (ofBits (graph.len (ci k t).fin) ((payload.drop cursor).take (graph.len (ci k t).fin))) y,
          cursor + 192) := by
  have hle : RiscvUpperForest.ForestVerifier.pos index k ≤ t.val := le_of_eq ht
  simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_pos ht, if_pos hle,
    pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def, Function.update_self,
    tripleUpdate]

/-- A level above the disclosed one: the input is the previous value. -/
theorem triple_run_step (k : Fin 28) (t : Fin 32) (ht : RiscvUpperForest.ForestVerifier.pos index k < t.val)
    (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index payload [ci k t, ch k t, cv k t] x cursor =
      hash ((Forest.trunc (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm)
        >>= fun y => pure (tripleUpdate x k t
          ((Forest.trunc (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm) y, cursor) := by
  have hne : ¬ RiscvUpperForest.ForestVerifier.pos index k = t.val := by omega
  have hle : RiscvUpperForest.ForestVerifier.pos index k ≤ t.val := le_of_lt ht
  simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hne, if_pos ht,
    if_pos hle, pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
    Function.update_self, tripleUpdate]

theorem tripleUpdate_cv (x : graph.Assignment) (k : Fin 28) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    tripleUpdate x k t v y (cv k t).fin =
      ((y.cast (graph_len_fin (ch k t)).symm).cast (lenF_ch k t)).cast
        (graph_len_fin (cv k t)).symm := by
  simp only [tripleUpdate, Function.update_self]

theorem tripleUpdate_other (x : graph.Assignment) (k : Fin 28) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits)
    (n : Name) (h1 : n ≠ ci k t) (h2 : n ≠ ch k t) (h3 : n ≠ cv k t) :
    tripleUpdate x k t v y n.fin = x n.fin := by
  simp only [tripleUpdate]
  rw [Function.update_of_ne (fin_ne_of_ne h3), Function.update_of_ne (fin_ne_of_ne h2),
    Function.update_of_ne (fin_ne_of_ne h1)]

/-- The trunc of the value node is the trunc of the answer. -/
theorem trunc_tripleUpdate_cv (x : graph.Assignment) (k : Fin 28) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) :
    Forest.trunc (tripleUpdate x k t v y (cv k t).fin) = Forest.trunc y := by
  rw [tripleUpdate_cv]
  apply BitVec.eq_of_toNat_eq
  simp only [Forest.trunc, BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_cast, lenF_fin]
  rfl

/-- The root prefix only reads the tops of the chains up to `j`. -/
theorem lowCat_congr {c c' : ℕ → BitVec 256} :
    ∀ j, (∀ i, i ≤ j → c i = c' i) → lowCat c j = lowCat c' j
  | 0, h => by simp only [lowCat]; rw [h 0 le_rfl]
  | j + 1, h => by
    simp only [lowCat]
    rw [h (j + 1) le_rfl, lowCat_congr j (fun i hi => h i (by omega))]

theorem tops_tripleUpdate (x : graph.Assignment) (k : Fin 28) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) (k' : Fin 28) (hk : k' ≠ k) :
    tops (tripleUpdate x k t v y) k' = tops x k' := by
  unfold tops
  rw [tripleUpdate_other x k t v y (cv k' 31) (by simp) (by simp)
    (fun e => hk (Name.cv.inj e).1)]

theorem topFun_tripleUpdate (x : graph.Assignment) (k : Fin 28) (t : Fin 32)
    (v : BitVec (graph.len (ci k t).fin)) (y : BitVec hashBits) (i : ℕ) (hi : i ≠ k.val) :
    topFun (tops (tripleUpdate x k t v y)) i = topFun (tops x) i := by
  unfold topFun
  split_ifs with hi28
  · exact tops_tripleUpdate x k t v y ⟨i, hi28⟩ (fun e => hi (congrArg Fin.val e))
  · rfl

/-- The region below chain `k`'s answer is untouched by its hash steps. -/
theorem lowCat_frame {s t : MachineState} {k : ℕ} (hk : k < 28) (hk1 : 1 ≤ k)
    {c : ℕ → BitVec 256} (frame : SlotFrame s t k)
    (held : MemBits s (W regionAddr) (lowCat c (k - 1))) :
    MemBits t (W regionAddr) (lowCat c (k - 1)) := by
  apply memBits_of_word_frame s t _ _ held
  intro i hi
  apply frame
  left
  have hs := slot_bounds k hk
  rw [alignToDword_toNat, BitVec.toNat_add, W_toNat _ (by norm_num [regionAddr]),
    BitVec.toNat_ofNat]
  unfold slotAddr payloadAddr at hs ⊢
  unfold regionAddr
  omega

/-- The slots above chain `k` are untouched by its hash steps. -/
theorem payloadFrom_frame {s t : MachineState} {k : ℕ} (hk : k < 28) (frame : SlotFrame s t k)
    (held : PayloadFrom s payload (k + 1)) : PayloadFrom t payload (k + 1) := by
  intro j hj hj28
  apply memBits_of_word_frame s t _ _ (held j hj hj28)
  intro i hi
  apply frame
  right
  have hs := slot_bounds k hk
  have hs' := slot_bounds j hj28
  rw [alignToDword_toNat, BitVec.toNat_add, slotAddr_toNat j hj28, BitVec.toNat_ofNat]
  unfold slotAddr payloadAddr at hs hs' ⊢
  omega

/-- Level `t` of chain `k`: one hash, at one cycle. -/
theorem step_refines (k : Fin 28) (t : Fin 32)
    (tail : Code) (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool))
    (c budget cursor cursor' : ℕ) (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (v : BitVec (graph.len (ci k t).fin))
    (hrun : runNodes' index payload [ci k t, ch k t, cv k t] x cursor =
      hash v >>= fun y => pure (tripleUpdate x k t v y, cursor'))
    (inv : StepInv index payload pk s x k t) (held : Holds s k v)
    (located : Riscv.CodeAt s s.pc (.ECALL :: tail)) (bound : 1 + budget ≤ fuel)
    (continuation : ∀ (u : MachineState) (y : BitVec hashBits),
      StepInv index payload pk u (tripleUpdate x k t v y) k (t.val + 1) →
      MemBits u (W (slotAddr k - 8)) y → Riscv.CodeAt u u.pc tail →
      ∀ left, budget ≤ left → Riscv.Refines left u (K (tripleUpdate x k t v y, cursor')) c) :
    Riscv.Refines fuel s (runNodes' index payload [ci k t, ch k t, cv k t] x cursor >>= K)
      (1 + c) := by
  rw [hrun]
  simp only [bind_assoc, pure_bind]
  have hs := slot_bounds k k.isLt
  have hsn : 0x400040 ≤ slotAddr k ∧ slotAddr k + 24 ≤ 0x400040 + 24 * 28 ∧ slotAddr k % 8 = 0 := by
    unfold payloadAddr at hs; exact hs
  have fetch : s.code s.pc = some .ECALL := located.head
  have valid : Riscv.hashArgumentsValid s = true := by
    have r1 : isValidOutputRange (slotW k) 24 = true :=
      range_ok _ _ (by unfold slotAddr payloadAddr at hs ⊢; omega)
        (by unfold slotAddr payloadAddr at hs ⊢; omega) (by norm_num) (by norm_num)
    have r2 := hashOutput_ok (slotAddr k - 8) (by unfold slotAddr payloadAddr at hs ⊢; omega)
      (by unfold slotAddr payloadAddr at hs ⊢; omega) (by unfold slotAddr payloadAddr at hs ⊢; omega)
    have e24 : ((192 : Word).toNat + 7) / 8 = 24 := rfl
    unfold Riscv.hashArgumentsValid
    rw [inv.input, inv.out, inv.ctx.length, e24, r1, Bool.true_and]
    exact r2
  have wInput : Riscv.hashInput s = ⟨graph.len (ci k t).fin, v⟩ := by
    apply hashInput_of_memBits inv.input
    · rw [inv.ctx.length, graph_len_fin]; rfl
    · exact held
  have blocks : blockCost (graph.len (ci k t).fin) = 1 := by
    rw [graph_len_fin]; show blockCost 192 = 1; decide
  rw [show fuel = (fuel - 1) + 1 by omega]
  have step := Riscv.Refines.hash (fuel := fuel - 1) fetch inv.ctx.call valid
    (k := fun y => K (tripleUpdate x k t v y, cursor')) (c := c) ?_
  · rw [wInput, blocks] at step
    exact step
  intro y
  set u := Riscv.writeHash s y with hu
  have uRegs : ∀ r, u.getReg r = s.getReg r := fun r => by rw [hu, writeHash_regs]
  have outFrame : ∀ addr, (∀ j, j < 4 → addr ≠ W (slotAddr k - 8) + BitVec.ofNat 64 (8 * j)) →
      u.getMem addr = s.getMem addr := by
    intro addr outside
    rw [hu, writeHash_frame _ _ _ (by rw [inv.out]; exact outside)]
  have frame : SlotFrame s u k := by
    intro addr haddr
    apply outFrame
    intro j hj e
    rw [e, BitVec.toNat_add, W_toNat _ (by unfold slotAddr payloadAddr at hs ⊢; omega),
      BitVec.toNat_ofNat] at haddr
    omega
  have uPc : u.pc = s.pc + 4 := by rw [hu, writeHash_pc]
  have uCode : u.code = s.code := by rw [hu, writeHash_code]
  have uLocated : Riscv.CodeAt u u.pc tail := by
    rw [uPc]
    exact located.tail.code_eq uCode
  have al : alignToDword (W (slotAddr k - 8)) = W (slotAddr k - 8) :=
    aligned_W _ (by omega) (by omega)
  have answer : MemBits u (W (slotAddr k - 8)) y := by
    have h := writeHash_memBits s y (by rw [inv.out]; exact al)
    rw [inv.out] at h
    exact h
  apply continuation u y ?_ answer uLocated (fuel - 1) (by omega)
  refine ⟨inv.ctx.frame k k.isLt (fun r _ => uRegs r) frame uCode,
    by rw [uRegs]; exact inv.input, by rw [uRegs]; exact inv.out,
    payloadFrom_frame payload k.isLt frame inv.payload, ?_⟩
  · intro hk1
    have e : lowCat (topFun (tops (tripleUpdate x k t v y))) (k.val - 1) =
        lowCat (topFun (tops x)) (k.val - 1) := by
      apply lowCat_congr
      intro i hi
      exact topFun_tripleUpdate x k t v y i (by omega)
    rw [e]
    exact lowCat_frame k.isLt hk1 frame (inv.done hk1)

end OptimalOTS.Riscv2Program
