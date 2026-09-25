import Submissions.UpperLeanIsa.MachineProgram
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Running the HL-GROUP-3 bytecode

The execution framework for `HLG3.program T` (every result assumes the table facts `T.Hyp`):

* the relation of a cell-level instruction on cell values, `CInstr.RelB B v`, parametric in the
  `BLAKE2S` relation `B`: `Rel f` (answers from a fixed table `f`) and `RelNH` (`BLAKE2S ↦ True`,
  all a run in the cache-free `support` semantics yields). A dispatch's relation records the
  landing: `[H_f] ∈ K` is `g ^ e` for an entry `e` of frame `f`, and `[H'_f] ∈ K`;
* frame-1 normal forms of every instruction (`exec_xor` … `exec_blake`), and the composite
  dispatch step `runCost_dispatch`: the landing in frame `F_f` and the entry's return are
  collapsed into one deterministic two-instruction step (`frame_fail` rules out every other
  landing);
* the `Walk`: a slot sequence in frame `1` from `s` to the sentinel along which the relation holds,
  a dispatch counting two instructions;
* the bridges: a completing run in any semantics `Sem` is a `Walk` (`walk_of_sem`; instances
  for the fixed-table and the `support` semantics), and a `Walk` of fixed-table relations is a
  completing run (`sim_of_walk`).
-/

namespace OptimalOTS.HLG3

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

variable {T : Tab}

/-! ## Relations -/

/-- A relation on the nine `BLAKE2S` cells `m, cv₀, cv₁, out₀, out₁, md`. -/
abbrev BlakeRel := (Fin 4 → E) → E → E → E → E → E → Prop

/-- The `BLAKE2S` relation under the fixed table `f`. -/
def oracleRel (f : HashTable) : BlakeRel := fun m cv0 cv1 o0 o1 md =>
  LeanIsa.OracleCompressCells m cv0 cv1 o0 o1 md (f ⟨896, LeanIsa.blake2sQuery m cv0 cv1 md⟩)

/-- The trivial `BLAKE2S` relation of the cache-free semantics. -/
def trueRel : BlakeRel := fun _ _ _ _ _ _ => True

/-- The relation an instruction asserts on the cell values `v` in frame `1`. A dispatch's is its
landing; entries (only executable in their frame) and the trap never hold. -/
def CInstr.RelB (B : BlakeRel) (v : ℕ → E) : CInstr → Prop
  | .init => v oneCell = oneV ∧ v lenCell = natV 5503
  | .xor a b c => v c = v a + v b
  | .mul a b c => v c = v a * v b
  | .setc a k => v a = k
  | .blake m0 m1 m2 m3 cv out md =>
      B ![v m0, v m1, v m2, v m3] (v cv) (v (cv + 1)) (v out) (v (out + 1)) (v md)
  | .dispatch k => IsInK (v (hCell k)) ∧ IsInK (v (h1Cell k)) ∧
      ∃ e, IsEntry k e ∧ (v (hCell k)).limb 0 = gpow e
  | .exit => IsInK (v (gpCell 13))
  | .entry _ => False
  | .pad => False

/-- The fixed-table relation. -/
abbrev CInstr.Rel (f : HashTable) (v : ℕ → E) (ci : CInstr) : Prop := ci.RelB (oracleRel f) v

/-- The hash-free relation. -/
abbrev CInstr.RelNH (v : ℕ → E) (ci : CInstr) : Prop := ci.RelB trueRel v

theorem CInstr.relNH_of_relB {B : BlakeRel} {v : ℕ → E} {ci : CInstr} (h : ci.RelB B v) :
    ci.RelNH v := by
  cases ci
  all_goals first | exact h | trivial

/-- The constants every jump relies on: `ONE` and the 15 frames. -/
def Pinned (v : ℕ → E) : Prop := v oneCell = oneV ∧ ∀ k < 15, v (fCell k) = frameV k

/-- The loader's capped length, including every oversized raw signature. -/
def LengthDomain (v : ℕ → E) : Prop := ∃ n ≤ 5505, v lenCell = natV n

theorem lengthDomain_load {κ : ℕ} (h16 : 16 ≤ κ) (pk : PublicKey) (m : Message)
    (σ : List Bool) (L : MemImage κ) : LengthDomain (Lx (LeanIsa.loadInput pk m σ L)) := by
  refine ⟨min σ.length (OptimalOTS.maxSignatureBits + 1), Nat.min_le_right _ _, ?_⟩
  have hc : lenCell < 2^κ := lt_of_lt_of_le (by decide : lenCell < 2^16)
    (Nat.pow_le_pow_right (by norm_num) h16)
  rw [Lx, dif_pos hc, LeanIsa.loadInput, if_pos (by change lenCell < LeanIsa.inputCells; decide)]
  exact inputWord_len pk m σ

/-! ## The successor slot -/

/-- The slot index of a program counter: `i` when `pc = g ^ i` with `i < 2 ^ 18`, else `2 ^ 18`. -/
def slotOf (pc : K) : ℕ :=
  if h : ∃ i, i < 2 ^ 18 ∧ pc = gpow i then Classical.choose h else 2 ^ 18

theorem slotOf_gpow {i : ℕ} (hi : i < 2 ^ 18) : slotOf (gpow i) = i := by
  unfold slotOf
  have h : ∃ j, j < 2 ^ 18 ∧ gpow i = gpow j := ⟨i, hi, rfl⟩
  rw [dif_pos h]
  obtain ⟨hj, hji⟩ := Classical.choose_spec h
  exact (gpow_inj (by omega) (by omega) hji).symm

theorem slotOf_spec {pc : K} (h : slotOf pc < 2 ^ 18) : pc = gpow (slotOf pc) := by
  unfold slotOf at h ⊢
  split_ifs at h ⊢ with hex
  · exact (Classical.choose_spec hex).2
  · omega

/-- The successor slot of an instruction at slot `s` on the cell values `v`. -/
def CInstr.nextOf (v : ℕ → E) (s : ℕ) : CInstr → ℕ
  | .dispatch k => slotOf ((v (h1Cell k)).limb 0)
  | .exit => slotOf ((v (gpCell 13)).limb 0)
  | _ => s + 1

/-- The successor of slot `s`. -/
def nextSlot (T : Tab) (v : ℕ → E) (s : ℕ) : ℕ := (cinstrAt T s).nextOf v s

/-- A walk: from slot `s`, `n` executed instructions of total cost `c`, every visited slot's
relation `RelB B` holding on `v` and below the sentinel, each followed by its `nextSlot`, ending
at the sentinel. -/
inductive Walk (T : Tab) (B : BlakeRel) (v : ℕ → E) : ℕ → ℕ → ℕ → Prop
  | done : Walk T B v 0 sentinel 0
  | step {n s c : ℕ} : s < sentinel → (cinstrAt T s).RelB B v → Walk T B v n (nextSlot T v s) c →
      Walk T B v (n + (cinstrAt T s).steps) s ((cinstrAt T s).cost + c)

theorem Walk.le_sentinel {T : Tab} {B : BlakeRel} {v : ℕ → E} {n s c : ℕ} (h : Walk T B v n s c) :
    s ≤ sentinel := by
  cases h with
  | done => exact le_refl _
  | step hs _ _ => exact le_of_lt hs

/-! ## Values -/

theorem isInK_ofK (a : K) : IsInK (ofK a) := (isInK_iff _).mpr ⟨a, rfl⟩

theorem limb_ofK_zero (a : K) : (ofK a).limb 0 = a := by simp

theorem ofK_one_ne_zero : ofK (1 : K) ≠ 0 := by
  intro h
  have := congrArg (fun z : E => z.limb 0) h
  simp [limb_zero] at this

theorem ofK_limb {x : E} (h : IsInK x) : x = ofK (x.limb 0) := by
  obtain ⟨a, rfl⟩ := (isInK_iff x).mp h
  rw [limb_ofK_zero]

/-! ## Reads -/

section Reads

variable {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (L : MemImage κ)
include h16 hκ

/-- In frame `1`, operand `gpow c` reads cell `c` (`c < 2 ^ 16 ≤ 2 ^ κ`). -/
theorem read_one {c : ℕ} (hc : c < 2 ^ 16) : L.read (1 * gpow c) = some (Lx L c) := by
  rw [one_mul]
  exact read_gpow_some hκ L (mod_ord_of_lt (by unfold ordG; omega))
    (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) h16))

theorem read_one_g {c : ℕ} (hc : c + 1 < 2 ^ 16) :
    L.read (1 * (g * gpow c)) = some (Lx L (c + 1)) := by
  rw [g_mul_gpow]; exact read_one h16 hκ L hc

/-- In frame `F_k`, the shifted operand `sop k c` reads cell `c`. -/
theorem read_frame_sop {k c : ℕ} (hk : k < 15) (hc : c < 2 ^ 16) :
    L.read (frame k * sop k c) = some (Lx L c) := by
  rw [frame, sop, gpow_mul_gpow]
  refine read_gpow_some hκ L ?_ (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) h16))
  have hb := frameExp_bounds hk
  unfold eLen at hb
  rw [mod_ord_of_ge (by unfold ordG; omega) (by unfold ordG; omega)]
  unfold ordG; omega

end Reads

/-! ## Frame-1 normal forms -/

theorem guard_some {p : Prop} [Decidable p] (r : Regs K) :
    ((guard p : Option Unit).bind fun _ => some r) = if p then some r else none := by
  by_cases hp : p
  · rw [if_pos hp, show (guard p : Option Unit) = some () from if_pos hp]; rfl
  · rw [if_neg hp, show (guard p : Option Unit) = none from if_neg hp]; rfl

theorem limb_oneV : oneV.limb 0 = 1 := limb_ofK_zero 1

section Normal

variable {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (L : MemImage κ) (pc : K)
include h16 hκ

theorem exec_xor {a b c : ℕ} (hb : (CInstr.xor a b c).Bounded) :
    LeanIsa.execute L ⟨pc, 1⟩ (CInstr.xor a b c).toInstr =
      pure (if Lx L c = Lx L a + Lx L b then some ⟨g * pc, 1⟩ else none) := by
  obtain ⟨ha, hb, hc⟩ := hb
  show pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (.xor (gpow a) (gpow b) (gpow c))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute, read_one h16 hκ L ha, read_one h16 hκ L hb,
    read_one h16 hκ L hc, Option.bind_eq_bind, Option.bind_some]
  exact guard_some _

theorem exec_mul {a b c : ℕ} (hb : (CInstr.mul a b c).Bounded) :
    LeanIsa.execute L ⟨pc, 1⟩ (CInstr.mul a b c).toInstr =
      pure (if Lx L c = Lx L a * Lx L b then some ⟨g * pc, 1⟩ else none) := by
  obtain ⟨ha, hb, hc⟩ := hb
  show pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (.mulNative (gpow a) (gpow b) (gpow c))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute, read_one h16 hκ L ha, read_one h16 hκ L hb,
    read_one h16 hκ L hc, Option.bind_eq_bind, Option.bind_some]
  exact guard_some _

theorem exec_setc {a : ℕ} {k : E} (hb : (CInstr.setc a k).Bounded) :
    LeanIsa.execute L ⟨pc, 1⟩ (CInstr.setc a k).toInstr =
      pure (if Lx L a = k then some ⟨g * pc, 1⟩ else none) := by
  show pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (.setConstant (gpow a) k)) = _
  congr 1
  simp only [LeanerVM.Semantics.execute, read_one h16 hκ L hb, Option.bind_eq_bind,
    Option.bind_some]
  exact guard_some _

/-- One indirect read checks the capped length and asserts ONE = fp = 1. -/
theorem exec_init (hd : LengthDomain (Lx L)) :
    LeanIsa.execute L ⟨pc, 1⟩ CInstr.init.toInstr =
      pure (if Lx L oneCell = oneV ∧ Lx L lenCell = natV 5503
        then some ⟨g * pc, 1⟩ else none) := by
  obtain ⟨n, hn, hv⟩ := hd
  have hnat : natV n = ofK (BitVec.ofNat 64 n) := LengthGate.natV_ofK hn
  have hk : IsInK (natV n) := by rw [hnat]; exact isInK_ofK _
  have hl : (natV n).limb 0 = BitVec.ofNat 64 n := by rw [hnat]; exact limb_ofK_zero _
  have heq : natV n = natV 5503 ↔ n = 5503 := by
    constructor
    · intro h
      have h' := congrArg (fun x => (LeanIsa.cellBits x).toNat) h
      simp only [cellBits_natV, BitVec.toNat_ofNat] at h'
      rw [Nat.mod_eq_of_lt (by omega)] at h'
      norm_num at h'
      exact h'
    · rintro rfl; rfl
  show pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
    (.deref (gpow lenCell) LengthGate.scale (gpow lenCell) .fp)) = _
  simp only [LeanerVM.Semantics.execute, read_one h16 hκ L (by decide : lenCell < 2^16),
    Option.bind_eq_bind, Option.bind_some, hv]
  rw [show (guard (IsInK (natV n)) : Option Unit) = some () from if_pos hk]
  simp only [Option.bind_some, hl]
  by_cases he : n = 5503
  · subst n
    rw [LengthGate.target_address,
      show L.read (gpow 48) = some (Lx L oneCell) from by
        change L.read (gpow oneCell) = some (Lx L oneCell)
        simpa only [one_mul] using read_one h16 hκ L (by decide : oneCell < 2^16)]
    simp only [Option.bind_some, LeanerVM.Semantics.derefSource, heq, and_true]
    exact congrArg pure (guard_some _)
  · rw [LengthGate.wrong_length_read hκ hn he L]
    simp [heq, he]

theorem exec_blake {m0 m1 m2 m3 cv out md : ℕ} (hb : (CInstr.blake m0 m1 m2 m3 cv out md).Bounded) :
    LeanIsa.execute L ⟨pc, 1⟩ (CInstr.blake m0 m1 m2 m3 cv out md).toInstr =
      (hash (LeanIsa.blake2sQuery ![Lx L m0, Lx L m1, Lx L m2, Lx L m3] (Lx L cv) (Lx L (cv + 1))
          (Lx L md)) >>= fun ans =>
        pure (if LeanIsa.OracleCompressCells ![Lx L m0, Lx L m1, Lx L m2, Lx L m3] (Lx L cv)
          (Lx L (cv + 1)) (Lx L out) (Lx L (out + 1)) (Lx L md) ans
          then some ⟨g * pc, 1⟩ else none)) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := hb
  simp only [CInstr.toInstr, LeanIsa.execute, Matrix.cons_val, Fin.isValue,
    read_one h16 hκ L c0, read_one h16 hκ L c1, read_one h16 hκ L c2, read_one h16 hκ L c3,
    read_one h16 hκ L (show cv < 2 ^ 16 by omega), read_one_g h16 hκ L c4,
    read_one h16 hκ L (show out < 2 ^ 16 by omega), read_one_g h16 hκ L c5,
    read_one h16 hκ L c6, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rfl

/-- The dispatch `JUMP(ONE, H_k, F_k)` in frame `1`. -/
theorem exec_dispatch {k : ℕ} (hk : k < 15) (hpin : Pinned (Lx L)) :
    LeanIsa.execute L ⟨pc, 1⟩ (CInstr.dispatch k).toInstr =
      pure (if IsInK (Lx L (hCell k)) then some ⟨(Lx L (hCell k)).limb 0, frame k⟩ else none) := by
  show pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
    (.jump (gpow oneCell) (gpow (hCell k)) (gpow (fCell k)))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,
    read_one h16 hκ L (show oneCell < 2 ^ 16 by unfold oneCell; omega),
    read_one h16 hκ L (show hCell k < 2 ^ 16 by unfold hCell; split_ifs <;> omega),
    read_one h16 hκ L (show fCell k < 2 ^ 16 by unfold fCell cCell; split_ifs <;> omega),
    Option.bind_eq_bind, Option.bind_some, hpin.1, hpin.2 k hk]
  by_cases hH : IsInK (Lx L (hCell k))
  · have hin : IsInK oneV ∧ IsInK (Lx L (hCell k)) ∧ IsInK (frameV k) :=
      ⟨isInK_ofK 1, hH, isInK_ofK _⟩
    rw [show (guard (IsInK oneV ∧ IsInK (Lx L (hCell k)) ∧ IsInK (frameV k)) : Option Unit) =
      some () from if_pos hin, if_pos hH]
    simp only [Option.bind_some, oneV, if_neg ofK_one_ne_zero, frameV, limb_ofK_zero]
    rfl
  · rw [show (guard (IsInK oneV ∧ IsInK (Lx L (hCell k)) ∧ IsInK (frameV k)) : Option Unit) =
      none from if_neg (fun h => hH h.2.1), if_neg hH]
    rfl

/-- The exit `JUMP(ONE, GP_13, ONE)` in frame `1`. -/
theorem exec_exit (hpin : Pinned (Lx L)) :
    LeanIsa.execute L ⟨pc, 1⟩ CInstr.exit.toInstr =
      pure (if IsInK (Lx L (gpCell 13)) then some ⟨(Lx L (gpCell 13)).limb 0, 1⟩ else none) := by
  show pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
    (.jump (gpow oneCell) (gpow (gpCell 13)) (gpow oneCell))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,
    read_one h16 hκ L (show oneCell < 2 ^ 16 by unfold oneCell; omega),
    read_one h16 hκ L (show gpCell 13 < 2 ^ 16 by decide),
    Option.bind_eq_bind, Option.bind_some, hpin.1]
  by_cases hH : IsInK (Lx L (gpCell 13))
  · have hin : IsInK oneV ∧ IsInK (Lx L (gpCell 13)) ∧ IsInK oneV :=
      ⟨isInK_ofK 1, hH, isInK_ofK 1⟩
    rw [show (guard (IsInK oneV ∧ IsInK (Lx L (gpCell 13)) ∧ IsInK oneV) : Option Unit) =
      some () from if_pos hin, if_pos hH]
    simp only [Option.bind_some, oneV, if_neg ofK_one_ne_zero, limb_ofK_zero]
    rfl
  · rw [show (guard (IsInK oneV ∧ IsInK (Lx L (gpCell 13)) ∧ IsInK oneV) : Option Unit) =
      none from if_neg (fun h => hH h.2.1), if_neg hH]
    rfl

/-- The entry `I0_k` in its own frame returns to frame `1` at `[H'_k]`. -/
theorem exec_entry_own {k : ℕ} (hk : k < 15) (hpin : Pinned (Lx L)) :
    LeanIsa.execute L ⟨pc, frame k⟩ (CInstr.entry k).toInstr =
      pure (if IsInK (Lx L (h1Cell k)) then some ⟨(Lx L (h1Cell k)).limb 0, 1⟩ else none) := by
  show pure (LeanerVM.Semantics.execute L ⟨pc, frame k⟩
    (.jump (sop k oneCell) (sop k (h1Cell k)) (sop k oneCell))) = _
  congr 1
  simp only [LeanerVM.Semantics.execute,
    read_frame_sop h16 hκ L hk (show oneCell < 2 ^ 16 by unfold oneCell; omega),
    read_frame_sop h16 hκ L hk (show h1Cell k < 2 ^ 16 by unfold h1Cell; split_ifs <;> omega),
    Option.bind_eq_bind, Option.bind_some, hpin.1]
  by_cases hH : IsInK (Lx L (h1Cell k))
  · have hin : IsInK oneV ∧ IsInK (Lx L (h1Cell k)) ∧ IsInK oneV :=
      ⟨isInK_ofK 1, hH, isInK_ofK 1⟩
    rw [show (guard (IsInK oneV ∧ IsInK (Lx L (h1Cell k)) ∧ IsInK oneV) : Option Unit) =
      some () from if_pos hin, if_pos hH]
    simp only [Option.bind_some, oneV, if_neg ofK_one_ne_zero, limb_ofK_zero]
    rfl
  · rw [show (guard (IsInK oneV ∧ IsInK (Lx L (h1Cell k)) ∧ IsInK oneV) : Option Unit) =
      none from if_neg (fun h => hH h.2.1), if_neg hH]
    rfl

end Normal

/-! ## The loop -/

section Loop

variable {κ : ℕ}

theorem initial_eq : (Regs.initial : Regs K) = ⟨gpow 0, 1⟩ :=
  congrArg (fun x : K => (⟨x, 1⟩ : Regs K)) gpow_zero'.symm

/-- One step of the loop, for an arbitrary program and registers. -/
theorem runCost_succ_of (prog : Program) (L : MemImage κ) (m : ℕ) (r : Regs K) (ins : Instr)
    (hne : r.pc ≠ prog.finalPc) (hf : prog.fetch r.pc = some ins) :
    LeanIsa.runCost prog L (m + 1) r =
      (LeanIsa.execute L r ins >>= fun x =>
        x.elim (pure none) fun next =>
          Option.map (LeanIsa.weight ins.opcode + ·) <$> LeanIsa.runCost prog L m next) := by
  rw [LeanIsa.runCost.eq_2, if_neg hne, hf]
  refine congrArg (fun F : Option (Regs K) → OracleComp Spec (Option ℕ) =>
    LeanIsa.execute L r ins >>= F) (funext fun x => ?_)
  cases x <;> rfl

theorem runCost_slot (L : MemImage κ) (m : ℕ) {s : ℕ} (hs : s < sentinel) (fp : K) :
    LeanIsa.runCost (program T) L (m + 1) ⟨gpow s, fp⟩ =
      (LeanIsa.execute L ⟨gpow s, fp⟩ (cinstrAt T s).toInstr >>= fun x =>
        x.elim (pure none) fun next =>
          Option.map (LeanIsa.weight (cinstrAt T s).toInstr.opcode + ·) <$>
            LeanIsa.runCost (program T) L m next) :=
  runCost_succ_of (program T) L m ⟨gpow s, fp⟩ _ (gpow_ne_finalPc T hs)
    (fetch_eq T (by unfold sentinel at hs; omega))

theorem runCost_zero_eq (L : MemImage κ) (r : Regs K) :
    LeanIsa.runCost (program T) L 0 r =
      pure (if r.pc = (program T).finalPc ∧ r.fp = 1 then some 0 else none) := by
  rw [LeanIsa.runCost.eq_1]

theorem runCost_zero_slot (L : MemImage κ) {s : ℕ} (hs : s < sentinel) :
    LeanIsa.runCost (program T) L 0 ⟨gpow s, 1⟩ = pure none := by
  rw [runCost_zero_eq, if_neg (fun e => gpow_ne_finalPc T hs e.1)]

theorem runCost_zero_sentinel (L : MemImage κ) :
    LeanIsa.runCost (program T) L 0 ⟨gpow sentinel, 1⟩ = pure (some 0) := by
  rw [runCost_zero_eq, if_pos ⟨(finalPc_eq T).symm, rfl⟩]

theorem runCost_succ_sentinel (L : MemImage κ) (n : ℕ) (fp : K) :
    LeanIsa.runCost (program T) L (n + 1) ⟨gpow sentinel, fp⟩ = pure none := by
  rw [LeanIsa.runCost.eq_2]; exact if_pos (finalPc_eq T).symm

/-- A landed state `⟨h, F_k⟩` never completes unless `h` is an entry of chain `k`. -/
theorem runCost_frame_none (hT : T.Hyp) (hκ : κ ≤ 32) (L : MemImage κ) {k : ℕ} (hk : k < 15) {h : K}
    (hno : ∀ e, IsEntry k e → h ≠ gpow e) (n : ℕ) :
    LeanIsa.runCost (program T) L n ⟨h, frame k⟩ = pure none := by
  cases n with
  | zero =>
    rw [LeanIsa.runCost.eq_1]
    exact congrArg pure (if_neg fun hc => frame_ne_one hk hc.2)
  | succ n =>
    rw [LeanIsa.runCost.eq_2]
    split_ifs with hf
    · rfl
    · split
      · rfl
      · rename_i ins hins
        obtain ⟨i, hi, rfl⟩ := (program T).fetch_eq_some_iff.mp hins
        have hs : ¬ IsEntry k i := fun he => hno i he hi
        rw [show LeanIsa.execute L ⟨h, frame k⟩ ((program T).code i) = pure none from
          frame_fail hT hκ L h hk hs, pure_bind]

theorem map_map_add (a b : ℕ) (x : OracleComp Spec (Option ℕ)) :
    Option.map (a + ·) <$> (Option.map (b + ·) <$> x) = Option.map ((a + b) + ·) <$> x := by
  rw [Functor.map_map]
  congr 1
  funext o
  cases o <;> simp [Nat.add_assoc]

variable (hT : T.Hyp) (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (L : MemImage κ)
include hT h16 hκ

open scoped Classical in
/-- **The composite dispatch step.** From a dispatch slot, two instructions later the run is in
frame `1` at `[H'_k]` when the landing relation holds, and fails otherwise. -/
theorem runCost_dispatch (hpin : Pinned (Lx L)) {s k : ℕ} (hs : s < sentinel)
    (hci : cinstrAt T s = .dispatch k) (n : ℕ) :
    LeanIsa.runCost (program T) L (n + 2) ⟨gpow s, 1⟩ =
      if (CInstr.dispatch k).RelNH (Lx L) then
        Option.map (2 + ·) <$> LeanIsa.runCost (program T) L n ⟨(Lx L (h1Cell k)).limb 0, 1⟩
      else pure none := by
  have hk : k < 15 := by have := cinstrAt_bounded hT s; rw [hci] at this; exact this
  rw [runCost_slot L (n + 1) hs, hci, exec_dispatch h16 hκ L _ hk hpin]
  by_cases hH : IsInK (Lx L (hCell k))
  · rw [if_pos hH, pure_bind, Option.elim_some]
    by_cases hex : ∃ e, IsEntry k e ∧ (Lx L (hCell k)).limb 0 = gpow e
    · obtain ⟨e, he, hx⟩ := hex
      have hlt := isEntry_lt he
      rw [hx, runCost_slot L n (by omega), cinstrAt_of_entry hT he,
        exec_entry_own h16 hκ L _ he.1 hpin]
      by_cases hH1 : IsInK (Lx L (h1Cell k))
      · rw [if_pos hH1, pure_bind, Option.elim_some, if_pos ⟨hH, hH1, e, he, hx⟩, map_map_add]
        rfl
      · rw [if_neg hH1, pure_bind, Option.elim_none, if_neg (fun h => hH1 h.2.1), map_pure]
        rfl
    · have hno : ∀ e, IsEntry k e → (Lx L (hCell k)).limb 0 ≠ gpow e :=
        fun e he h => hex ⟨e, he, h⟩
      rw [runCost_frame_none hT hκ L (by omega) hno, map_pure, if_neg (fun h => hex h.2.2)]
      rfl
  · rw [if_neg hH, pure_bind, Option.elim_none, if_neg (fun h => hH h.1)]

theorem runCost_dispatch_one (hpin : Pinned (Lx L)) {s k : ℕ} (hs : s < sentinel)
    (hci : cinstrAt T s = .dispatch k) :
    LeanIsa.runCost (program T) L 1 ⟨gpow s, 1⟩ = pure none := by
  have hk : k < 15 := by have := cinstrAt_bounded hT s; rw [hci] at this; exact this
  rw [runCost_slot L 0 hs, hci, exec_dispatch h16 hκ L _ hk hpin]
  split_ifs
  · rw [pure_bind, Option.elim_some, LeanIsa.runCost.eq_1,
      if_neg (fun hc => frame_ne_one hk hc.2), map_pure]; rfl
  · rw [pure_bind, Option.elim_none]

omit hT in
open scoped Classical in
/-- The exit step. -/
theorem runCost_exit (hpin : Pinned (Lx L)) {s : ℕ} (hs : s < sentinel)
    (hci : cinstrAt T s = .exit) (n : ℕ) :
    LeanIsa.runCost (program T) L (n + 1) ⟨gpow s, 1⟩ =
      if CInstr.exit.RelNH (Lx L) then
        Option.map (1 + ·) <$> LeanIsa.runCost (program T) L n ⟨(Lx L (gpCell 13)).limb 0, 1⟩
      else pure none := by
  rw [runCost_slot L n hs, hci, exec_exit h16 hκ L _ hpin]
  by_cases hH : IsInK (Lx L (gpCell 13))
  · rw [if_pos hH, pure_bind, Option.elim_some,
      if_pos (show CInstr.exit.RelNH (Lx L) from hH)]; rfl
  · rw [if_neg hH, pure_bind, Option.elim_none,
      if_neg (show ¬ CInstr.exit.RelNH (Lx L) from hH)]

omit h16 in
/-- Entries and pads fail in frame `1`. -/
theorem runCost_dead {s : ℕ} (hs : s < sentinel) (hci : (cinstrAt T s).RelNH (Lx L) = False ∧
    (cinstrAt T s).straight = false ∧ (∀ k, cinstrAt T s ≠ .dispatch k) ∧ cinstrAt T s ≠ .exit)
    (n : ℕ) : LeanIsa.runCost (program T) L (n + 1) ⟨gpow s, 1⟩ = pure none := by
  obtain ⟨-, hst, hd, hx⟩ := hci
  rw [runCost_slot L n hs]
  generalize hc : cinstrAt T s = ci at hst hd hx
  cases ci with
  | entry k =>
    have hk : IsEntry k s := cinstrAt_eq_entry hc
    rw [show LeanIsa.execute L ⟨gpow s, 1⟩ (CInstr.entry k).toInstr = pure none by
      rw [← hc]; exact entry_fail_frame_one hT hκ L _ hk, pure_bind]; rfl
  | pad => rw [exec_pad, pure_bind]; rfl
  | dispatch k => exact absurd rfl (hd k)
  | exit => exact absurd rfl hx
  | xor => simp [CInstr.straight] at hst
  | mul => simp [CInstr.straight] at hst
  | init => simp [CInstr.straight] at hst
  | setc => simp [CInstr.straight] at hst
  | blake => simp [CInstr.straight] at hst

end Loop

/-! ## Semantics -/

/-- A set-valued semantics of oracle computations with the monad laws the bridges need: the
fixed-table semantics and the cache-free `support` semantics are instances. -/
structure Sem where
  S : {α : Type} → OracleComp Spec α → Set α
  pure_iff : ∀ {α : Type} (a x : α), x ∈ S (pure a) ↔ x = a
  bind_iff : ∀ {α β : Type} (oa : OracleComp Spec α) (f : α → OracleComp Spec β) (y : β),
    y ∈ S (oa >>= f) ↔ ∃ a ∈ S oa, y ∈ S (f a)

/-- The fixed-table semantics. -/
def simSem (f : HashTable) : Sem where
  S oa := support (simulateQ (unifFwdAnswerImpl f) oa)
  pure_iff a x := by rw [simulateQ_pure, mem_support_pure_iff]
  bind_iff oa g y := by rw [simulateQ_bind, mem_support_bind_iff]

/-- The cache-free `support` semantics. -/
def suppSem : Sem where
  S oa := support oa
  pure_iff a x := mem_support_pure_iff x a
  bind_iff oa g y := mem_support_bind_iff oa g y

theorem Sem.map_iff (Sm : Sem) {α β : Type} (oa : OracleComp Spec α) (f : α → β) (y : β) :
    y ∈ Sm.S (f <$> oa) ↔ ∃ a ∈ Sm.S oa, f a = y := by
  rw [map_eq_bind_pure_comp, Sm.bind_iff]
  simp only [Function.comp_apply, Sm.pure_iff]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩⟩

theorem Sem.some_not_pure_none (Sm : Sem) {c : ℕ} : some c ∉ Sm.S (pure none) := by
  rw [Sm.pure_iff]; exact Option.some_ne_none c

theorem Sem.some_map_add (Sm : Sem) {a c : ℕ} {x : OracleComp Spec (Option ℕ)}
    (h : some c ∈ Sm.S (Option.map (a + ·) <$> x)) : ∃ c', c = a + c' ∧ some c' ∈ Sm.S x := by
  rw [Sm.map_iff] at h
  obtain ⟨o, ho, hc⟩ := h
  cases o with
  | none => exact absurd hc (by simp)
  | some c' => exact ⟨c', (Option.some.inj hc).symm, ho⟩

/-! ## The bridges -/

section Bridges

variable {κ : ℕ} (hT : T.Hyp) (h16 : 16 ≤ κ) (hκ : κ ≤ 32) {L : MemImage κ}

/-- A completing run starts at a slot of the program. -/
theorem runCost_pc_valid (Sm : Sem) {n c : ℕ} {r : Regs K}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) L n r)) : ∃ i, i < 2 ^ 18 ∧ r.pc = gpow i := by
  by_contra hno
  have hne : r.pc ≠ (program T).finalPc := fun e =>
    hno ⟨sentinel, by unfold sentinel; omega, e.trans (finalPc_eq T)⟩
  cases n with
  | zero =>
    rw [runCost_zero_eq, if_neg (fun e => hne e.1)] at h
    exact Sm.some_not_pure_none h
  | succ n =>
    have hf : (program T).fetch r.pc = none :=
      (Program.fetch_eq_none_iff (program T)).mpr fun i hi => hno ⟨(i : ℕ), i.isLt, hi⟩
    rw [LeanIsa.runCost.eq_2, if_neg hne, hf] at h
    exact Sm.some_not_pure_none h

theorem straight_steps {ci : CInstr} (h : ci.straight = true) : ci.steps = 1 := by
  cases ci <;> simp_all [CInstr.straight, CInstr.steps]

theorem straight_weight {ci : CInstr} (h : ci.straight = true) :
    LeanIsa.weight ci.toInstr.opcode = ci.cost := by
  cases ci <;> simp_all [CInstr.straight, CInstr.cost, CInstr.toInstr, LeanIsa.weight] <;> rfl

theorem nextOf_straight {ci : CInstr} (h : ci.straight = true) (v : ℕ → E) (s : ℕ) :
    ci.nextOf v s = s + 1 := by
  cases ci <;> simp_all [CInstr.straight, CInstr.nextOf]

theorem nextSlot_straight (v : ℕ → E) {s : ℕ} (h : (cinstrAt T s).straight = true) :
    nextSlot T v s = s + 1 := nextOf_straight h v s

include hT h16 hκ in
/-- **Walk of a run.** In any semantics whose straight-line steps yield the relation `RelB B`, a
completing run from slot `s` is a walk of `RelB B`. -/
theorem walk_of_sem (Sm : Sem) (B : BlakeRel) (hpin : Pinned (Lx L))
    (hst : ∀ s pc x, (cinstrAt T s).straight = true →
      x ∈ Sm.S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt T s).toInstr) →
        x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt T s).RelB B (Lx L))) :
    ∀ n s c, s < 2 ^ 18 → some c ∈ Sm.S (LeanIsa.runCost (program T) L n ⟨gpow s, 1⟩) →
      Walk T B (Lx L) n s c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s c hs h
  by_cases hsen : s = sentinel
  · subst hsen
    cases n with
    | zero =>
      rw [runCost_zero_sentinel, Sm.pure_iff] at h
      obtain rfl := Option.some.inj h
      exact Walk.done
    | succ n =>
      rw [runCost_succ_sentinel] at h
      exact absurd h Sm.some_not_pure_none
  have hlt : s < sentinel := by unfold sentinel at hsen ⊢; omega
  cases n with
  | zero => rw [runCost_zero_slot L hlt] at h; exact absurd h Sm.some_not_pure_none
  | succ m =>
  cases hstr : (cinstrAt T s).straight with
  | true =>
    rw [runCost_slot L m hlt, Sm.bind_iff] at h
    obtain ⟨x, hx, hc⟩ := h
    rcases hst s _ x hstr hx with rfl | ⟨rfl, hrel⟩
    · exact absurd hc Sm.some_not_pure_none
    · rw [Option.elim_some, straight_weight hstr, g_mul_gpow] at hc
      obtain ⟨c', rfl, hc'⟩ := Sm.some_map_add hc
      have hw := ih m (by omega) (s + 1) c' (by unfold sentinel at hlt; omega) hc'
      rw [← nextSlot_straight (Lx L) hstr] at hw
      have := Walk.step hlt hrel hw
      rwa [straight_steps hstr] at this
  | false =>
  generalize hci : cinstrAt T s = ci at hstr
  cases ci with
  | dispatch k =>
    cases m with
    | zero => rw [runCost_dispatch_one hT h16 hκ L hpin hlt hci] at h
              exact absurd h Sm.some_not_pure_none
    | succ m' =>
      rw [runCost_dispatch hT h16 hκ L hpin hlt hci] at h
      split_ifs at h with hrel
      · obtain ⟨c', rfl, hc'⟩ := Sm.some_map_add h
        obtain ⟨i, hi, hpc⟩ := runCost_pc_valid Sm hc'
        change (Lx L (h1Cell k)).limb 0 = gpow i at hpc
        rw [hpc] at hc'
        have hw := ih m' (by omega) i c' hi hc'
        have hn : nextSlot T (Lx L) s = i := by
          unfold nextSlot; rw [hci]; show slotOf _ = i; rw [hpc, slotOf_gpow hi]
        rw [← hn] at hw
        have := Walk.step (T := T) (B := B) hlt
          (show (cinstrAt T s).RelB B (Lx L) by rw [hci]; exact hrel) hw
        rwa [hci] at this
      · exact absurd h Sm.some_not_pure_none
  | exit =>
    rw [runCost_exit h16 hκ L hpin hlt hci] at h
    split_ifs at h with hrel
    · obtain ⟨c', rfl, hc'⟩ := Sm.some_map_add h
      obtain ⟨i, hi, hpc⟩ := runCost_pc_valid Sm hc'
      change (Lx L (gpCell 13)).limb 0 = gpow i at hpc
      rw [hpc] at hc'
      have hw := ih m (by omega) i c' hi hc'
      have hn : nextSlot T (Lx L) s = i := by
        unfold nextSlot; rw [hci]; show slotOf _ = i; rw [hpc, slotOf_gpow hi]
      rw [← hn] at hw
      have := Walk.step (T := T) (B := B) hlt
        (show (cinstrAt T s).RelB B (Lx L) by rw [hci]; exact hrel) hw
      rwa [hci] at this
    · exact absurd h Sm.some_not_pure_none
  | entry k =>
    rw [runCost_dead hT hκ L hlt (by rw [hci]; exact ⟨rfl, rfl, by simp, by simp⟩)] at h
    exact absurd h Sm.some_not_pure_none
  | pad =>
    rw [runCost_dead hT hκ L hlt (by rw [hci]; exact ⟨rfl, rfl, by simp, by simp⟩)] at h
    exact absurd h Sm.some_not_pure_none
  | xor => simp [CInstr.straight] at hstr
  | mul => simp [CInstr.straight] at hstr
  | init => simp [CInstr.straight] at hstr
  | setc => simp [CInstr.straight] at hstr
  | blake => simp [CInstr.straight] at hstr

include hT h16 hκ in
/-- The fixed-table straight-line step. -/
theorem sim_straight (hd : LengthDomain (Lx L)) (f : HashTable) (s : ℕ) (pc : K) (x : Option (Regs K))
    (hs : (cinstrAt T s).straight = true)
    (hx : x ∈ (simSem f).S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt T s).toInstr)) :
    x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt T s).Rel f (Lx L)) := by
  have hb := cinstrAt_bounded hT s
  generalize cinstrAt T s = ci at hs hx hb
  change x ∈ support (simulateQ (unifFwdAnswerImpl f) _) at hx
  cases ci with
  | init =>
    rw [exec_init h16 hκ L pc hd, simulateQ_pure, mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | xor a b c =>
    rw [exec_xor h16 hκ L pc hb, simulateQ_pure, mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | mul a b c =>
    rw [exec_mul h16 hκ L pc hb, simulateQ_pure, mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | setc a k =>
    rw [exec_setc h16 hκ L pc hb, simulateQ_pure, mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | blake m0 m1 m2 m3 cv out md =>
    rw [exec_blake h16 hκ L pc hb, simulateQ_bind, fixed_hash, pure_bind, simulateQ_pure,
      mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | _ => simp [CInstr.straight] at hs

include hT h16 hκ in
/-- The cache-free straight-line step. -/
theorem supp_straight (hd : LengthDomain (Lx L)) (s : ℕ) (pc : K) (x : Option (Regs K))
    (hs : (cinstrAt T s).straight = true)
    (hx : x ∈ suppSem.S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt T s).toInstr)) :
    x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt T s).RelNH (Lx L)) := by
  have hb := cinstrAt_bounded hT s
  generalize cinstrAt T s = ci at hs hx hb
  change x ∈ support _ at hx
  cases ci with
  | init =>
    rw [exec_init h16 hκ L pc hd, mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | xor a b c =>
    rw [exec_xor h16 hκ L pc hb, mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | mul a b c =>
    rw [exec_mul h16 hκ L pc hb, mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | setc a k =>
    rw [exec_setc h16 hκ L pc hb, mem_support_pure_iff] at hx
    split_ifs at hx with hr
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl hx
  | blake m0 m1 m2 m3 cv out md =>
    rw [exec_blake h16 hκ L pc hb, mem_support_bind_iff] at hx
    obtain ⟨ans, -, hx⟩ := hx
    rw [mem_support_pure_iff] at hx
    split_ifs at hx
    · exact Or.inr ⟨hx, trivial⟩
    · exact Or.inl hx
  | _ => simp [CInstr.straight] at hs

include hT h16 hκ in
/-- **Walk of a fixed-table run.** -/
theorem walk_of_sim (hd : LengthDomain (Lx L)) (f : HashTable) (hpin : Pinned (Lx L)) {n s c : ℕ} (hs : s < 2 ^ 18)
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) L n ⟨gpow s, 1⟩))) :
    Walk T (oracleRel f) (Lx L) n s c :=
  walk_of_sem hT h16 hκ (simSem f) (oracleRel f) hpin (sim_straight hT h16 hκ hd f) n s c hs h

include hT h16 hκ in
/-- **Walk of a `support` run.** -/
theorem walk_of_supp (hd : LengthDomain (Lx L)) (hpin : Pinned (Lx L)) {n s c : ℕ} (hs : s < 2 ^ 18)
    (h : some c ∈ support (LeanIsa.runCost (program T) L n ⟨gpow s, 1⟩)) :
    Walk T trueRel (Lx L) n s c :=
  walk_of_sem hT h16 hκ suppSem trueRel hpin (supp_straight hT h16 hκ hd) n s c hs h

include hT h16 hκ in
/-- **Run of a walk.** Under a fixed table, a walk whose relations hold is a completing run of
exactly its steps and cost. -/
theorem sim_of_walk (f : HashTable) (hpin : Pinned (Lx L)) {n s c : ℕ}
    (hw : Walk T (oracleRel f) (Lx L) n s c) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost (program T) L n ⟨gpow s, 1⟩) =
      pure (some c) := by
  induction hw with
  | done => rw [runCost_zero_sentinel, simulateQ_pure]
  | @step n s c hs hR hw ih =>
    have hb := cinstrAt_bounded hT s
    cases hstr : (cinstrAt T s).straight with
    | true =>
      rw [straight_steps hstr, runCost_slot L n hs, simulateQ_bind]
      have hex : simulateQ (unifFwdAnswerImpl f)
          (LeanIsa.execute L ⟨gpow s, 1⟩ (cinstrAt T s).toInstr) = pure (some ⟨gpow (s + 1), 1⟩) := by
        rw [← g_mul_gpow]
        revert hR hb
        generalize cinstrAt T s = ci at hstr
        intro hR hb
        cases ci with
        | init =>
          have hd : LengthDomain (Lx L) := ⟨5503, by omega, hR.2⟩
          have hR' : Lx L oneCell = oneV ∧ Lx L lenCell = natV 5503 := hR
          rw [exec_init h16 hκ L _ hd, if_pos hR', simulateQ_pure]
        | xor a b c =>
          have hR' : Lx L c = Lx L a + Lx L b := hR
          rw [exec_xor h16 hκ L _ hb, if_pos hR', simulateQ_pure]
        | mul a b c =>
          have hR' : Lx L c = Lx L a * Lx L b := hR
          rw [exec_mul h16 hκ L _ hb, if_pos hR', simulateQ_pure]
        | setc a k =>
          have hR' : Lx L a = k := hR
          rw [exec_setc h16 hκ L _ hb, if_pos hR', simulateQ_pure]
        | blake m0 m1 m2 m3 cv out md =>
          rw [exec_blake h16 hκ L _ hb, simulateQ_bind, fixed_hash, pure_bind, simulateQ_pure]
          exact congrArg pure (if_pos hR)
        | _ => simp [CInstr.straight] at hstr
      rw [hex, pure_bind, Option.elim_some, simulateQ_map, ← nextSlot_straight (Lx L) hstr, ih,
        map_pure, Option.map_some, straight_weight hstr]
    | false =>
      generalize hci : cinstrAt T s = ci at hstr hR hb
      cases ci with
      | dispatch k =>
        rw [show (CInstr.dispatch k).steps = 2 from rfl, runCost_dispatch hT h16 hκ L hpin hs hci,
          if_pos (CInstr.relNH_of_relB hR), simulateQ_map]
        have hpc : (Lx L (h1Cell k)).limb 0 = gpow (nextSlot T (Lx L) s) := by
          have hn : nextSlot T (Lx L) s = slotOf ((Lx L (h1Cell k)).limb 0) := by
            unfold nextSlot; rw [hci]; rfl
          rw [hn]
          exact slotOf_spec (by rw [← hn]; have := hw.le_sentinel; unfold sentinel at this; omega)
        rw [hpc, ih, map_pure, Option.map_some]
        rfl
      | exit =>
        rw [show CInstr.exit.steps = 1 from rfl, runCost_exit h16 hκ L hpin hs hci,
          if_pos (CInstr.relNH_of_relB hR), simulateQ_map]
        have hpc : (Lx L (gpCell 13)).limb 0 = gpow (nextSlot T (Lx L) s) := by
          have hn : nextSlot T (Lx L) s = slotOf ((Lx L (gpCell 13)).limb 0) := by
            unfold nextSlot; rw [hci]; rfl
          rw [hn]
          exact slotOf_spec (by rw [← hn]; have := hw.le_sentinel; unfold sentinel at this; omega)
        rw [hpc, ih, map_pure, Option.map_some]
        rfl
      | entry k => exact hR.elim
      | pad => exact hR.elim
      | _ => simp [CInstr.straight] at hstr

end Bridges

end

end OptimalOTS.HLG3
