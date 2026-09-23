import Submissions.UpperLeanIsa.MachineProgram
import Submissions.UpperLeanIsa.Correctness
import OptimalOTS.LeanIsa

/-!
# Running the baseline bytecode

The execution framework for `Machine.program`:

* `Lx L c`, the total view of an image, and the cell-read lemmas;
* `Holds f L k`, the relation of instruction `k` in frame `1` under the fixed table `f`, with its
  characterisation per decoded slot (`holds_step0` … `holds_haltJump`);
* the fixed-table semantics (`simulateQ (unifFwdAnswerImpl f)`): a completing run has exactly
  `N` steps, costs `totalCost`, and every relation held (`run_complete`); conversely all
  relations make the run complete (`run_of_holds`);
* the `support` semantics: every completing run costs `totalCost` (`support_run`), hence
  `cycles : S.CyclesAtMost claim`.

The run is analysed along the straight-line path `(gpow k, 1)`, `k = 0 … N`. Every instruction
before the last is not a `JUMP`, so it either fails or steps to `(gpow (k + 1), 1)`; the last
three (Segment F) pin two cells and jump to `Regs.final program`.
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters LeanerVM.Semantics OracleComp

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Reading cells -/

/-- The word of cell `c`, total: `0` past the end of the image. -/
def Lx {κ : ℕ} (L : MemImage κ) (c : ℕ) : E := if h : c < 2 ^ κ then L ⟨c, h⟩ else 0

theorem Lx_of_lt {κ : ℕ} (L : MemImage κ) {c : ℕ} (h : c < 2 ^ κ) : Lx L c = L ⟨c, h⟩ :=
  dif_pos h

theorem Lx_of_not_lt {κ : ℕ} (L : MemImage κ) {c : ℕ} (h : ¬ c < 2 ^ κ) : Lx L c = 0 :=
  dif_neg h

theorem lt64_of_le_maxLogMem {κ : ℕ} (hκ : κ ≤ maxLogMem) : κ < 64 :=
  lt_of_le_of_lt hκ (by decide)

theorem lt_order_of_lt {c : ℕ} (h : c < 131072) : c < 2 ^ 64 - 1 :=
  lt_of_lt_of_le h (by norm_num)

theorem read_op_of_lt {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) {c : ℕ} (h : c < 2 ^ κ) :
    L.read (op c) = some (Lx L c) := by
  rw [Lx_of_lt L h]
  exact MemImage.read_gpow hκ L ⟨c, h⟩

theorem read_op_of_ge {κ : ℕ} (L : MemImage κ) {c : ℕ} (h : 2 ^ κ ≤ c)
    (hc : c < 2 ^ 64 - 1) : L.read (op c) = none := by
  show L.read (gpow c) = none
  rw [MemImage.read, gLog?_gpow_eq_none h hc, Option.map_none]

theorem read_op_eq_some_iff {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) {c : ℕ}
    (hc : c < 2 ^ 64 - 1) {v : E} : L.read (op c) = some v ↔ c < 2 ^ κ ∧ Lx L c = v := by
  by_cases h : c < 2 ^ κ
  · rw [read_op_of_lt hκ L h]
    exact ⟨fun e => ⟨h, Option.some.inj e⟩, fun e => by rw [e.2]⟩
  · rw [read_op_of_ge L (Nat.le_of_not_lt h) hc]
    exact ⟨fun e => (Option.some_ne_none v e.symm).elim, fun e => absurd e.1 h⟩

/-- The cell-read lemma: in frame `1`, the operand `gpow c` reads cell `c`. -/
theorem read_one_mul_gpow_iff {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) {c : ℕ}
    (hc : c < 2 ^ 64 - 1) {v : E} :
    L.read (1 * gpow c) = some v ↔ ∃ h : c < 2 ^ κ, L ⟨c, h⟩ = v := by
  rw [one_mul]
  change L.read (op c) = some v ↔ _
  rw [read_op_eq_some_iff hκ L hc]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨h, by rw [← Lx_of_lt L h]; exact e⟩
  · rintro ⟨h, e⟩
    exact ⟨h, by rw [Lx_of_lt L h]; exact e⟩

/-! ## `guard` in `Option` -/

theorem optGuard_eq_some {p : Prop} {hd : Decidable p} {u : Unit}
    (h : (guard p : Option Unit) = some u) : p := by
  by_contra hp
  have hg : (guard p : Option Unit) = none := if_neg hp
  rw [hg] at h
  exact Option.some_ne_none u h.symm

theorem optGuard_bind_eq_some_iff {α : Type} (p : Prop) {hd : Decidable p}
    (f : Unit → Option α) (b : α) : Option.bind (guard p) f = some b ↔ p ∧ f () = some b := by
  by_cases hp : p
  · have hg : (guard p : Option Unit) = some () := if_pos hp
    rw [hg, Option.bind_some]
    exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
  · have hg : (guard p : Option Unit) = none := if_neg hp
    rw [hg, Option.bind_none]
    exact ⟨fun h => (Option.some_ne_none b h.symm).elim, fun h => absurd h.1 hp⟩

theorem optGuard_bind_of_pos {α : Type} {p : Prop} {hd : Decidable p} (hp : p)
    (f : Unit → Option α) : Option.bind (guard p) f = f () := by
  have hg : (guard p : Option Unit) = some () := if_pos hp
  rw [hg, Option.bind_some]

/-! ## The pure instructions -/

section Pure

variable {κ : ℕ}

theorem exec_xor_iff (hκ : κ < 64) (L : MemImage κ) (pc : K) {a b c : ℕ}
    (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) (hc : c < 2 ^ 64 - 1) (y : Regs K) :
    LeanerVM.Semantics.execute L ⟨pc, 1⟩ (.xor (op a) (op b) (op c)) = some y ↔
      (a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a + Lx L b) ∧ y = ⟨g * pc, 1⟩ := by
  constructor
  · intro h
    simp only [LeanerVM.Semantics.execute, one_mul, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨va, hva, vb, hvb, vc, hvc, u, hu, hy⟩ := h
    obtain ⟨ha', rfl⟩ := (read_op_eq_some_iff hκ L ha).mp hva
    obtain ⟨hb', rfl⟩ := (read_op_eq_some_iff hκ L hb).mp hvb
    obtain ⟨hc', rfl⟩ := (read_op_eq_some_iff hκ L hc).mp hvc
    exact ⟨⟨ha', hb', hc', optGuard_eq_some hu⟩, (Option.some.inj hy).symm⟩
  · rintro ⟨⟨ha', hb', hc', hrel⟩, rfl⟩
    simp only [LeanerVM.Semantics.execute, one_mul, read_op_of_lt hκ L ha',
      read_op_of_lt hκ L hb', read_op_of_lt hκ L hc', Option.bind_eq_bind, Option.bind_some]
    rw [optGuard_bind_eq_some_iff]
    exact ⟨hrel, rfl⟩

theorem exec_mul_iff (hκ : κ < 64) (L : MemImage κ) (pc : K) {a b c : ℕ}
    (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) (hc : c < 2 ^ 64 - 1) (y : Regs K) :
    LeanerVM.Semantics.execute L ⟨pc, 1⟩ (.mulNative (op a) (op b) (op c)) = some y ↔
      (a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a * Lx L b) ∧ y = ⟨g * pc, 1⟩ := by
  constructor
  · intro h
    simp only [LeanerVM.Semantics.execute, one_mul, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨va, hva, vb, hvb, vc, hvc, u, hu, hy⟩ := h
    obtain ⟨ha', rfl⟩ := (read_op_eq_some_iff hκ L ha).mp hva
    obtain ⟨hb', rfl⟩ := (read_op_eq_some_iff hκ L hb).mp hvb
    obtain ⟨hc', rfl⟩ := (read_op_eq_some_iff hκ L hc).mp hvc
    exact ⟨⟨ha', hb', hc', optGuard_eq_some hu⟩, (Option.some.inj hy).symm⟩
  · rintro ⟨⟨ha', hb', hc', hrel⟩, rfl⟩
    simp only [LeanerVM.Semantics.execute, one_mul, read_op_of_lt hκ L ha',
      read_op_of_lt hκ L hb', read_op_of_lt hκ L hc', Option.bind_eq_bind, Option.bind_some]
    rw [optGuard_bind_eq_some_iff]
    exact ⟨hrel, rfl⟩

theorem exec_set_iff (hκ : κ < 64) (L : MemImage κ) (pc : K) {a : ℕ}
    (ha : a < 2 ^ 64 - 1) (v : E) (y : Regs K) :
    LeanerVM.Semantics.execute L ⟨pc, 1⟩ (.setConstant (op a) v) = some y ↔
      (a < 2 ^ κ ∧ Lx L a = v) ∧ y = ⟨g * pc, 1⟩ := by
  constructor
  · intro h
    simp only [LeanerVM.Semantics.execute, one_mul, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨va, hva, u, hu, hy⟩ := h
    obtain ⟨ha', rfl⟩ := (read_op_eq_some_iff hκ L ha).mp hva
    exact ⟨⟨ha', optGuard_eq_some hu⟩, (Option.some.inj hy).symm⟩
  · rintro ⟨⟨ha', hv⟩, rfl⟩
    simp only [LeanerVM.Semantics.execute, one_mul, read_op_of_lt hκ L ha',
      Option.bind_eq_bind, Option.bind_some]
    rw [optGuard_bind_eq_some_iff]
    exact ⟨hv, rfl⟩

theorem exec_xor_next (L : MemImage κ) (r : Regs K) (oa ob oc : K) {y : Regs K}
    (h : LeanerVM.Semantics.execute L r (.xor oa ob oc) = some y) : y = r.next := by
  simp only [LeanerVM.Semantics.execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, hy⟩ := h
  exact (Option.some.inj hy).symm

theorem exec_mul_next (L : MemImage κ) (r : Regs K) (oa ob oc : K) {y : Regs K}
    (h : LeanerVM.Semantics.execute L r (.mulNative oa ob oc) = some y) : y = r.next := by
  simp only [LeanerVM.Semantics.execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, hy⟩ := h
  exact (Option.some.inj hy).symm

theorem exec_set_next (L : MemImage κ) (r : Regs K) (o : K) (v : E) {y : Regs K}
    (h : LeanerVM.Semantics.execute L r (.setConstant o v) = some y) : y = r.next := by
  simp only [LeanerVM.Semantics.execute, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, hy⟩ := h
  exact (Option.some.inj hy).symm

/-- The halting `JUMP`, once its two cells hold ONE and FPC, lands on the final registers. -/
theorem exec_halt_jump (hκ : κ < 64) (L : MemImage κ) (pc : K)
    (h0 : haltOneCell < 2 ^ κ ∧ Lx L haltOneCell = oneV)
    (h1 : haltFpcCell < 2 ^ κ ∧ Lx L haltFpcCell = fpcV) :
    LeanerVM.Semantics.execute L ⟨pc, 1⟩
      (.jump (op haltOneCell) (op haltFpcCell) (op haltOneCell)) =
        some (Regs.final program) := by
  have r0 : L.read (op haltOneCell) = some oneV := by rw [read_op_of_lt hκ L h0.1, h0.2]
  have r1 : L.read (op haltFpcCell) = some fpcV := by rw [read_op_of_lt hκ L h1.1, h1.2]
  have hp : IsInK oneV ∧ IsInK fpcV ∧ IsInK oneV := ⟨isInK_oneV, isInK_fpcV, isInK_oneV⟩
  simp only [LeanerVM.Semantics.execute, one_mul, r0, r1, Option.bind_eq_bind,
    Option.bind_some]
  rw [optGuard_bind_of_pos hp, if_neg oneV_ne_zero]
  all_goals rfl

end Pure

/-! ## `BLAKE2S` -/

/-- The nine reads of a `BLAKE2S`, exactly as `LeanIsa.execute` performs them. -/
def blakeReads {κ : ℕ} (L : MemImage κ) (r : Regs K) (om : Fin 4 → K) (ocv oout omd : K) :
    Option ((Fin 4 → E) × E × E × E × E × E) := do
  let m0 ← L.read (r.fp * om 0)
  let m1 ← L.read (r.fp * om 1)
  let m2 ← L.read (r.fp * om 2)
  let m3 ← L.read (r.fp * om 3)
  let cv0 ← L.read (r.fp * ocv)
  let cv1 ← L.read (r.fp * (g * ocv))
  let out0 ← L.read (r.fp * oout)
  let out1 ← L.read (r.fp * (g * oout))
  let md ← L.read (r.fp * omd)
  pure ((![m0, m1, m2, m3] : Fin 4 → E), cv0, cv1, out0, out1, md)

/-- The oracle step of a `BLAKE2S` whose reads succeeded, exactly as `LeanIsa.execute`. -/
def blakeTail (r : Regs K) :
    (Fin 4 → E) × E × E × E × E × E → OracleComp Spec (Option (Regs K))
  | (m, cv0, cv1, out0, out1, md) => do
    let answer ← hash (LeanIsa.blake2sQuery m cv0 cv1 md)
    pure (if LeanIsa.OracleCompressCells m cv0 cv1 out0 out1 md answer then some r.next
      else none)

theorem blakeReads_eq_some_iff {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) (pc : K)
    {m0 m1 m2 m3 cv out md : ℕ}
    (hb : (CInstr.blake m0 m1 m2 m3 cv out md).Bounded (2 ^ 64 - 1))
    (p : (Fin 4 → E) × E × E × E × E × E) :
    blakeReads L ⟨pc, 1⟩ ![op m0, op m1, op m2, op m3] (op cv) (op out) (op md) = some p ↔
      (m0 < 2 ^ κ ∧ m1 < 2 ^ κ ∧ m2 < 2 ^ κ ∧ m3 < 2 ^ κ ∧ cv < 2 ^ κ ∧ cv + 1 < 2 ^ κ ∧
        out < 2 ^ κ ∧ out + 1 < 2 ^ κ ∧ md < 2 ^ κ) ∧
      p = (![Lx L m0, Lx L m1, Lx L m2, Lx L m3], Lx L cv, Lx L (cv + 1), Lx L out,
        Lx L (out + 1), Lx L md) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := hb
  have b4' : cv < 2 ^ 64 - 1 := by omega
  have b5' : out < 2 ^ 64 - 1 := by omega
  constructor
  · intro h
    simp only [blakeReads, Matrix.cons_val, Fin.isValue, one_mul, g_mul_op,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x0, h0, x1, h1, x2, h2, x3, h3, x4, h4, x5, h5, x6, h6, x7, h7, x8, h8, hp⟩ := h
    obtain ⟨c0, rfl⟩ := (read_op_eq_some_iff hκ L b0).mp h0
    obtain ⟨c1, rfl⟩ := (read_op_eq_some_iff hκ L b1).mp h1
    obtain ⟨c2, rfl⟩ := (read_op_eq_some_iff hκ L b2).mp h2
    obtain ⟨c3, rfl⟩ := (read_op_eq_some_iff hκ L b3).mp h3
    obtain ⟨c4, rfl⟩ := (read_op_eq_some_iff hκ L b4').mp h4
    obtain ⟨c5, rfl⟩ := (read_op_eq_some_iff hκ L b4).mp h5
    obtain ⟨c6, rfl⟩ := (read_op_eq_some_iff hκ L b5').mp h6
    obtain ⟨c7, rfl⟩ := (read_op_eq_some_iff hκ L b5).mp h7
    obtain ⟨c8, rfl⟩ := (read_op_eq_some_iff hκ L b6).mp h8
    exact ⟨⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩, (Option.some.inj hp).symm⟩
  · rintro ⟨⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩, rfl⟩
    simp only [blakeReads, Matrix.cons_val, Fin.isValue, one_mul, g_mul_op,
      read_op_of_lt hκ L c0, read_op_of_lt hκ L c1, read_op_of_lt hκ L c2,
      read_op_of_lt hκ L c3, read_op_of_lt hκ L c4, read_op_of_lt hκ L c5,
      read_op_of_lt hκ L c6, read_op_of_lt hκ L c7, read_op_of_lt hκ L c8,
      Option.bind_eq_bind, Option.bind_some]
    all_goals rfl

theorem sim_blakeTail (f : HashTable) (r : Regs K) (m : Fin 4 → E) (cv0 cv1 out0 out1 md : E) :
    simulateQ (unifFwdAnswerImpl f) (blakeTail r (m, cv0, cv1, out0, out1, md)) =
      pure (if LeanIsa.OracleCompressCells m cv0 cv1 out0 out1 md
          (f ⟨896, LeanIsa.blake2sQuery m cv0 cv1 md⟩) then some r.next else none) := by
  first
    | (rw [blakeTail, simulateQ_bind, fixed_hash, pure_bind, simulateQ_pure]; done)
    | (rw [blakeTail, simulateQ_bind, fixed_hash]; rfl)
    | (simp only [blakeTail, simulateQ_bind, fixed_hash, pure_bind, simulateQ_pure]; done)
    | simp [blakeTail, fixed_hash]

theorem supp_blakeTail (r : Regs K) (p : (Fin 4 → E) × E × E × E × E × E)
    {x : Option (Regs K)} (hx : x ∈ support (blakeTail r p)) : x = none ∨ x = some r.next := by
  obtain ⟨m, cv0, cv1, out0, out1, md⟩ := p
  rw [blakeTail, mem_support_bind_iff] at hx
  obtain ⟨ans, -, hx⟩ := hx
  rw [mem_support_pure_iff] at hx
  split_ifs at hx
  · exact Or.inr hx
  · exact Or.inl hx

/-! ## The relation of an instruction -/

/-- The relation of a cell-level instruction on the image, read in frame `1` under the table `f`,
as plain equations on `Lx`: every cell read is in range and the instruction's relation holds.
For `BLAKE2S` the answer is `f ⟨896, blake2sQuery …⟩`. -/
def CInstr.Rel (f : HashTable) {κ : ℕ} (L : MemImage κ) : CInstr → Prop
  | .xor a b c => a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a + Lx L b
  | .mul a b c => a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a * Lx L b
  | .setc a v => a < 2 ^ κ ∧ Lx L a = v
  | .blake m0 m1 m2 m3 cv out md =>
      (m0 < 2 ^ κ ∧ m1 < 2 ^ κ ∧ m2 < 2 ^ κ ∧ m3 < 2 ^ κ ∧ cv < 2 ^ κ ∧ cv + 1 < 2 ^ κ ∧
        out < 2 ^ κ ∧ out + 1 < 2 ^ κ ∧ md < 2 ^ κ) ∧
      LeanIsa.OracleCompressCells ![Lx L m0, Lx L m1, Lx L m2, Lx L m3] (Lx L cv)
        (Lx L (cv + 1)) (Lx L out) (Lx L (out + 1)) (Lx L md)
        (f ⟨896, LeanIsa.blake2sQuery ![Lx L m0, Lx L m1, Lx L m2, Lx L m3] (Lx L cv)
          (Lx L (cv + 1)) (Lx L md)⟩)
  | .jump a b c =>
      a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ IsInK (Lx L a) ∧ IsInK (Lx L b) ∧ IsInK (Lx L c)

/-- The relation of instruction `k` holds on `L` in frame `1` under the table `f`. -/
def Holds (f : HashTable) {κ : ℕ} (L : MemImage κ) (k : ℕ) : Prop := (cinstrAt k).Rel f L

section Rel

variable (f : HashTable) {κ : ℕ} (L : MemImage κ)

theorem holds_iff (k : ℕ) : Holds f L k ↔ (cinstrAt k).Rel f L := Iff.rfl

theorem rel_xor (a b c : ℕ) :
    (CInstr.xor a b c).Rel f L ↔
      a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a + Lx L b := Iff.rfl

theorem rel_mul (a b c : ℕ) :
    (CInstr.mul a b c).Rel f L ↔
      a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a * Lx L b := Iff.rfl

theorem rel_setc (a : ℕ) (v : E) : (CInstr.setc a v).Rel f L ↔ a < 2 ^ κ ∧ Lx L a = v :=
  Iff.rfl

theorem rel_blake (m0 m1 m2 m3 cv out md : ℕ) :
    (CInstr.blake m0 m1 m2 m3 cv out md).Rel f L ↔
      (m0 < 2 ^ κ ∧ m1 < 2 ^ κ ∧ m2 < 2 ^ κ ∧ m3 < 2 ^ κ ∧ cv < 2 ^ κ ∧ cv + 1 < 2 ^ κ ∧
        out < 2 ^ κ ∧ out + 1 < 2 ^ κ ∧ md < 2 ^ κ) ∧
      LeanIsa.OracleCompressCells ![Lx L m0, Lx L m1, Lx L m2, Lx L m3] (Lx L cv)
        (Lx L (cv + 1)) (Lx L out) (Lx L (out + 1)) (Lx L md)
        (f ⟨896, LeanIsa.blake2sQuery ![Lx L m0, Lx L m1, Lx L m2, Lx L m3] (Lx L cv)
          (Lx L (cv + 1)) (Lx L md)⟩) := Iff.rfl

theorem rel_jump (a b c : ℕ) :
    (CInstr.jump a b c).Rel f L ↔
      a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ IsInK (Lx L a) ∧ IsInK (Lx L b) ∧
        IsInK (Lx L c) := Iff.rfl

theorem holds_of_eq_xor {k a b c : ℕ} (h : cinstrAt k = .xor a b c) :
    Holds f L k ↔ a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a + Lx L b := by
  rw [holds_iff, h]
  all_goals exact Iff.rfl

theorem holds_of_eq_mul {k a b c : ℕ} (h : cinstrAt k = .mul a b c) :
    Holds f L k ↔ a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a * Lx L b := by
  rw [holds_iff, h]
  all_goals exact Iff.rfl

theorem holds_of_eq_setc {k a : ℕ} {v : E} (h : cinstrAt k = .setc a v) :
    Holds f L k ↔ a < 2 ^ κ ∧ Lx L a = v := by
  rw [holds_iff, h]
  all_goals exact Iff.rfl

end Rel

/-! ## One instruction under a fixed table -/

section Fixed

variable {κ : ℕ}

theorem sim_exec_pos (hκ : κ < 64) (f : HashTable) (L : MemImage κ) (pc : K) {ci : CInstr}
    (hb : ci.Bounded (2 ^ 64 - 1)) (hj : ci.isJump = false) (hr : ci.Rel f L) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.execute L ⟨pc, 1⟩ ci.toInstr) =
      pure (some ⟨g * pc, 1⟩) := by
  cases ci with
  | xor a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    have hx := (exec_xor_iff hκ L pc ha hb' hc ⟨g * pc, 1⟩).mpr ⟨hr, rfl⟩
    show simulateQ (unifFwdAnswerImpl f)
      (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.xor (op a) (op b) (op c)))) = _
    rw [hx, simulateQ_pure]
  | mul a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    have hx := (exec_mul_iff hκ L pc ha hb' hc ⟨g * pc, 1⟩).mpr ⟨hr, rfl⟩
    show simulateQ (unifFwdAnswerImpl f)
      (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.mulNative (op a) (op b) (op c)))) = _
    rw [hx, simulateQ_pure]
  | setc a v =>
    have hx := (exec_set_iff hκ L pc hb v ⟨g * pc, 1⟩).mpr ⟨hr, rfl⟩
    show simulateQ (unifFwdAnswerImpl f)
      (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.setConstant (op a) v))) = _
    rw [hx, simulateQ_pure]
  | blake m0 m1 m2 m3 cv out md =>
    obtain ⟨⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩, hocc⟩ := hr
    -- Rewrite the nine reads inside the contract's own `match`, which then reduces.
    simp only [CInstr.toInstr, LeanIsa.execute, Matrix.cons_val, Fin.isValue, one_mul, g_mul_op,
      read_op_of_lt hκ L c0, read_op_of_lt hκ L c1, read_op_of_lt hκ L c2,
      read_op_of_lt hκ L c3, read_op_of_lt hκ L c4, read_op_of_lt hκ L c5,
      read_op_of_lt hκ L c6, read_op_of_lt hκ L c7, read_op_of_lt hκ L c8,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    first
      | exact (sim_blakeTail f ⟨pc, 1⟩ ![Lx L m0, Lx L m1, Lx L m2, Lx L m3] (Lx L cv)
          (Lx L (cv + 1)) (Lx L out) (Lx L (out + 1)) (Lx L md)).trans
          (by rw [if_pos hocc]; all_goals rfl)
      | (rw [simulateQ_bind, fixed_hash, pure_bind, simulateQ_pure, if_pos hocc]
         all_goals rfl)
  | jump a b c => exact absurd hj (by simp [CInstr.isJump])

/-- Every outcome of one instruction under a fixed table fails, or steps to the next slot with
the instruction's relation holding. -/
theorem sim_exec_supp (hκ : κ < 64) (f : HashTable) (L : MemImage κ) (pc : K) {ci : CInstr}
    (hb : ci.Bounded (2 ^ 64 - 1)) (hj : ci.isJump = false) {x : Option (Regs K)}
    (hx : x ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.execute L ⟨pc, 1⟩ ci.toInstr))) :
    x = none ∨ (x = some (Regs.next ⟨pc, 1⟩) ∧ ci.Rel f L) := by
  cases ci with
  | xor a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    change x ∈ support (simulateQ (unifFwdAnswerImpl f)
      (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.xor (op a) (op b) (op c))) :
        OracleComp Spec (Option (Regs K)))) at hx
    rw [simulateQ_pure, mem_support_pure_iff] at hx
    rw [hx]
    cases h : LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.xor (op a) (op b) (op c)) with
    | none => exact Or.inl rfl
    | some y =>
      obtain ⟨hrel, hy⟩ := (exec_xor_iff hκ L pc ha hb' hc y).mp h
      rw [hy]
      exact Or.inr ⟨rfl, hrel⟩
  | mul a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    change x ∈ support (simulateQ (unifFwdAnswerImpl f)
      (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.mulNative (op a) (op b) (op c))) :
        OracleComp Spec (Option (Regs K)))) at hx
    rw [simulateQ_pure, mem_support_pure_iff] at hx
    rw [hx]
    cases h : LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.mulNative (op a) (op b) (op c)) with
    | none => exact Or.inl rfl
    | some y =>
      obtain ⟨hrel, hy⟩ := (exec_mul_iff hκ L pc ha hb' hc y).mp h
      rw [hy]
      exact Or.inr ⟨rfl, hrel⟩
  | setc a v =>
    change x ∈ support (simulateQ (unifFwdAnswerImpl f)
      (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.setConstant (op a) v)) :
        OracleComp Spec (Option (Regs K)))) at hx
    rw [simulateQ_pure, mem_support_pure_iff] at hx
    rw [hx]
    cases h : LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.setConstant (op a) v) with
    | none => exact Or.inl rfl
    | some y =>
      obtain ⟨hrel, hy⟩ := (exec_set_iff hκ L pc hb v y).mp h
      rw [hy]
      exact Or.inr ⟨rfl, hrel⟩
  | blake m0 m1 m2 m3 cv out md =>
    simp only [CInstr.toInstr, LeanIsa.execute] at hx
    split at hx
    · rw [simulateQ_pure, mem_support_pure_iff] at hx
      exact Or.inl hx
    · rename_i hR
      obtain ⟨hbnd, hp⟩ := (blakeReads_eq_some_iff hκ L pc hb _).mp
        (by first | exact hR | exact hR.symm)
      first
        | (simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp)
        | subst hp
      rw [simulateQ_bind, mem_support_bind_iff] at hx
      obtain ⟨ans, hans, hx⟩ := hx
      rw [fixed_hash, mem_support_pure_iff] at hans
      subst hans
      rw [simulateQ_pure, mem_support_pure_iff] at hx
      split_ifs at hx with hocc
      · exact Or.inr ⟨hx, hbnd, hocc⟩
      · exact Or.inl hx
  | jump a b c => exact absurd hj (by simp [CInstr.isJump])

end Fixed

/-! ## One instruction in the `support` semantics -/

section Support

variable {κ : ℕ}

theorem supp_exec_next (L : MemImage κ) (pc : K) {ci : CInstr} (hj : ci.isJump = false)
    {x : Option (Regs K)} (hx : x ∈ support (LeanIsa.execute L ⟨pc, 1⟩ ci.toInstr)) :
    x = none ∨ x = some (Regs.next ⟨pc, 1⟩) := by
  cases ci with
  | xor a b c =>
    change x ∈ support (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
      (Instr.xor (op a) (op b) (op c))) : OracleComp Spec (Option (Regs K))) at hx
    rw [mem_support_pure_iff] at hx
    rw [hx]
    cases h : LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.xor (op a) (op b) (op c)) with
    | none => exact Or.inl rfl
    | some y =>
      have hy : y = Regs.next ⟨pc, 1⟩ := exec_xor_next L ⟨pc, 1⟩ (op a) (op b) (op c) h
      rw [hy]
      exact Or.inr rfl
  | mul a b c =>
    change x ∈ support (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
      (Instr.mulNative (op a) (op b) (op c))) : OracleComp Spec (Option (Regs K))) at hx
    rw [mem_support_pure_iff] at hx
    rw [hx]
    cases h : LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.mulNative (op a) (op b) (op c)) with
    | none => exact Or.inl rfl
    | some y =>
      have hy : y = Regs.next ⟨pc, 1⟩ := exec_mul_next L ⟨pc, 1⟩ (op a) (op b) (op c) h
      rw [hy]
      exact Or.inr rfl
  | setc a v =>
    change x ∈ support (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
      (Instr.setConstant (op a) v)) : OracleComp Spec (Option (Regs K))) at hx
    rw [mem_support_pure_iff] at hx
    rw [hx]
    cases h : LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.setConstant (op a) v) with
    | none => exact Or.inl rfl
    | some y =>
      have hy : y = Regs.next ⟨pc, 1⟩ := exec_set_next L ⟨pc, 1⟩ (op a) v h
      rw [hy]
      exact Or.inr rfl
  | blake m0 m1 m2 m3 cv out md =>
    simp only [CInstr.toInstr, LeanIsa.execute] at hx
    split at hx
    · rw [mem_support_pure_iff] at hx
      exact Or.inl hx
    · rw [mem_support_bind_iff] at hx
      obtain ⟨ans, -, hx⟩ := hx
      rw [mem_support_pure_iff] at hx
      split_ifs at hx
      · exact Or.inr hx
      · exact Or.inl hx
  | jump a b c => exact absurd hj (by simp [CInstr.isJump])

theorem supp_set_rel (hκ : κ < 64) (L : MemImage κ) {pc : K} {a : ℕ} {v : E} {y : Regs K}
    (hy : some y ∈ support (LeanIsa.execute L ⟨pc, 1⟩ (CInstr.setc a v).toInstr))
    (ha : a < 2 ^ 64 - 1) : a < 2 ^ κ ∧ Lx L a = v := by
  change some y ∈ support (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
    (Instr.setConstant (op a) v)) : OracleComp Spec (Option (Regs K))) at hy
  rw [mem_support_pure_iff] at hy
  exact ((exec_set_iff hκ L pc ha v y).mp hy.symm).1

end Support

/-! ## The loop along the straight-line path -/

section Loop

variable {κ : ℕ}

theorem initial_eq : (Regs.initial : Regs K) = ⟨gpow 0, 1⟩ :=
  congrArg (fun x : K => (⟨x, 1⟩ : Regs K)) gpow_zero.symm

theorem next_gpow (k : ℕ) : Regs.next (⟨gpow k, 1⟩ : Regs K) = ⟨gpow (k + 1), 1⟩ :=
  congrArg (fun x : K => (⟨x, 1⟩ : Regs K)) (g_mul_gpow k)

/-- One step of the loop, for an arbitrary program and registers: nothing concrete is ever
unfolded, so the kernel check of the instance below stays small. -/
theorem runCost_succ_of (prog : Program) (L : MemImage κ) (m : ℕ) (r : Regs K) (ins : Instr)
    (hne : r.pc ≠ prog.finalPc) (hf : prog.fetch r.pc = some ins) :
    LeanIsa.runCost prog L (m + 1) r =
      (LeanIsa.execute L r ins >>= fun x =>
        x.elim (pure none) fun next =>
          Option.map (LeanIsa.weight ins.opcode + ·) <$> LeanIsa.runCost prog L m next) := by
  first
    | rw [LeanIsa.runCost.eq_2, if_neg hne, hf]
    | rw [LeanIsa.runCost, if_neg hne, hf]
  -- Both sides bind the same `execute`; the continuations agree case by case (no comparison of
  -- two stuck matchers is ever needed).
  refine congrArg (fun F : Option (Regs K) → OracleComp Spec (Option ℕ) =>
    LeanIsa.execute L r ins >>= F) (funext fun x => ?_)
  cases x <;> rfl

theorem runCost_succ_eq (L : MemImage κ) (m k : ℕ) (hk : k < N) :
    LeanIsa.runCost program L (m + 1) ⟨gpow k, 1⟩ =
      (LeanIsa.execute L ⟨gpow k, 1⟩ (cinstrAt k).toInstr >>= fun x =>
        x.elim (pure none) fun next =>
          Option.map (LeanIsa.weight (cinstrAt k).toInstr.opcode + ·) <$>
            LeanIsa.runCost program L m next) :=
  runCost_succ_of program L m ⟨gpow k, 1⟩ (cinstrAt k).toInstr (gpow_ne_finalPc hk)
    (fetch_eq k hk)

theorem runCost_zero_of_lt (L : MemImage κ) (k : ℕ) (hk : k < N) :
    LeanIsa.runCost program L 0 ⟨gpow k, 1⟩ = pure none := by
  have hne := gpow_ne_finalPc hk
  simp [LeanIsa.runCost, hne]

theorem runCost_final_zero (L : MemImage κ) :
    LeanIsa.runCost program L 0 (Regs.final program) = pure (some 0) := by
  simp [LeanIsa.runCost, Regs.final]

theorem runCost_final_succ (L : MemImage κ) (n : ℕ) :
    LeanIsa.runCost program L (n + 1) (Regs.final program) = pure none := by
  first
    | (rw [LeanIsa.runCost.eq_2]
       exact if_pos (show (Regs.final program).pc = program.finalPc from rfl))
    | (rw [LeanIsa.runCost]
       exact if_pos (show (Regs.final program).pc = program.finalPc from rfl))

theorem holds_haltOne_iff (f : HashTable) (L : MemImage κ) :
    Holds f L F_start ↔ haltOneCell < 2 ^ κ ∧ Lx L haltOneCell = oneV := by
  rw [holds_iff, cinstrAt_haltOne]
  all_goals exact Iff.rfl

theorem holds_haltFpc_iff (f : HashTable) (L : MemImage κ) :
    Holds f L (F_start + 1) ↔ haltFpcCell < 2 ^ κ ∧ Lx L haltFpcCell = fpcV := by
  rw [holds_iff, cinstrAt_haltFpc]
  all_goals exact Iff.rfl

theorem holds_haltJump_iff (f : HashTable) (L : MemImage κ) :
    Holds f L (F_start + 2) ↔
      haltOneCell < 2 ^ κ ∧ haltFpcCell < 2 ^ κ ∧ haltOneCell < 2 ^ κ ∧
        IsInK (Lx L haltOneCell) ∧ IsInK (Lx L haltFpcCell) ∧ IsInK (Lx L haltOneCell) := by
  rw [holds_iff, cinstrAt_haltJump]
  all_goals exact Iff.rfl

/-- The halting `JUMP` relation follows from the two constants before it. -/
theorem holds_haltJump_of (f : HashTable) (L : MemImage κ) (H0 : Holds f L F_start)
    (H1 : Holds f L (F_start + 1)) : Holds f L (F_start + 2) := by
  rw [holds_haltOne_iff] at H0
  rw [holds_haltFpc_iff] at H1
  rw [holds_haltJump_iff]
  refine ⟨H0.1, H1.1, H0.1, ?_, ?_, ?_⟩
  · rw [H0.2]; exact isInK_oneV
  · rw [H1.2]; exact isInK_fpcV
  · rw [H0.2]; exact isInK_oneV

theorem execute_haltJump (hκ : κ < 64) (L : MemImage κ) (pc : K)
    (h0 : haltOneCell < 2 ^ κ ∧ Lx L haltOneCell = oneV)
    (h1 : haltFpcCell < 2 ^ κ ∧ Lx L haltFpcCell = fpcV) :
    LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt (F_start + 2)).toInstr =
      pure (some (Regs.final program)) := by
  rw [cinstrAt_haltJump]
  show (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
    (Instr.jump (op haltOneCell) (op haltFpcCell) (op haltOneCell))) :
      OracleComp Spec (Option (Regs K))) = _
  rw [exec_halt_jump hκ L pc h0 h1]

/-! ### Fixed table -/

theorem sim_step_pos (hκ : κ < 64) (f : HashTable) (L : MemImage κ) (m k : ℕ)
    (hk : k + 1 < N) (hh : Holds f L k) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L (m + 1) ⟨gpow k, 1⟩) =
      Option.map ((cinstrAt k).cost + ·) <$>
        simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L m ⟨gpow (k + 1), 1⟩) := by
  have hkN : k < N := by omega
  have hx := sim_exec_pos hκ f L (gpow k) (cinstrAt_bounded k hkN) (cinstrAt_isJump k hk) hh
  first
    | (rw [runCost_succ_eq L m k hkN, simulateQ_bind, hx, pure_bind, Option.elim_some,
        simulateQ_map, CInstr.weight_toInstr, g_mul_gpow]; done)
    | (simp only [runCost_succ_eq L m k hkN, simulateQ_bind, hx, pure_bind, Option.elim_some,
        simulateQ_map, CInstr.weight_toInstr, g_mul_gpow]; done)

theorem sim_zero_not_mem (f : HashTable) (L : MemImage κ) (k : ℕ) (hk : k < N) (c : ℕ) :
    some c ∉ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L 0 ⟨gpow k, 1⟩)) := by
  rw [runCost_zero_of_lt L k hk, simulateQ_pure, mem_support_pure_iff]
  exact Option.some_ne_none c

theorem sim_peel (hκ : κ < 64) (f : HashTable) (L : MemImage κ) {m k c : ℕ} (hk : k + 1 < N)
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L (m + 1) ⟨gpow k, 1⟩))) :
    Holds f L k ∧ ∃ c', some c' ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L m ⟨gpow (k + 1), 1⟩)) ∧ c = (cinstrAt k).cost + c' := by
  have hkN : k < N := by omega
  rw [runCost_succ_eq L m k hkN, simulateQ_bind, mem_support_bind_iff] at h
  obtain ⟨x, hx, hc⟩ := h
  rcases sim_exec_supp hκ f L (gpow k) (cinstrAt_bounded k hkN) (cinstrAt_isJump k hk) hx with
    rfl | ⟨rfl, hh⟩
  · rw [Option.elim_none, simulateQ_pure, mem_support_pure_iff] at hc
    exact absurd hc (Option.some_ne_none c)
  · refine ⟨hh, ?_⟩
    rw [Option.elim_some, simulateQ_map, support_map] at hc
    obtain ⟨o, ho, hoc⟩ := hc
    rcases o with _ | c'
    · simp at hoc
    · refine ⟨c', ?_, ?_⟩
      · rwa [next_gpow] at ho
      · rw [CInstr.weight_toInstr] at hoc
        exact (Option.some.inj hoc).symm

theorem sim_jump_step (hκ : κ < 64) (f : HashTable) (L : MemImage κ) (m k : ℕ)
    (hk : k = F_start + 2) (H0 : Holds f L F_start) (H1 : Holds f L (F_start + 1)) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L (m + 1) ⟨gpow k, 1⟩) =
      Option.map (1 + ·) <$>
        simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L m (Regs.final program)) := by
  subst hk
  have hkN : F_start + 2 < N := by
    have := F_start_add_three
    omega
  rw [holds_haltOne_iff] at H0
  rw [holds_haltFpc_iff] at H1
  rw [runCost_succ_eq L m (F_start + 2) hkN, execute_haltJump hκ L _ H0 H1, pure_bind,
    Option.elim_some, simulateQ_map, cinstrAt_haltJump]
  all_goals rfl

theorem sim_jump (hκ : κ < 64) (f : HashTable) (L : MemImage κ) (k : ℕ)
    (hk : k = F_start + 2) (H0 : Holds f L F_start) (H1 : Holds f L (F_start + 1)) {m c : ℕ}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L (m + 1) ⟨gpow k, 1⟩))) : m = 0 ∧ c = 1 := by
  rw [sim_jump_step hκ f L m k hk H0 H1, support_map] at h
  obtain ⟨o, ho, hoc⟩ := h
  cases m with
  | zero =>
    rw [runCost_final_zero, simulateQ_pure, mem_support_pure_iff] at ho
    subst ho
    exact ⟨rfl, (Option.some.inj hoc).symm⟩
  | succ m =>
    rw [runCost_final_succ, simulateQ_pure, mem_support_pure_iff] at ho
    subst ho
    simp at hoc

/-- Segment F under a fixed table: exactly three more steps, three cycles, all relations. The
start index is a variable `k = F_start`, so no concrete counter is ever unified. -/
theorem sim_tail (hκ : κ < 64) (f : HashTable) (L : MemImage κ) (k : ℕ) (hkF : k = F_start)
    {m c : ℕ} (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L m ⟨gpow k, 1⟩))) :
    m = 3 ∧ c = 3 ∧ Holds f L k ∧ Holds f L (k + 1) ∧ Holds f L (k + 2) := by
  have hFN := F_start_add_three
  have e0 : cinstrAt k = .setc haltOneCell oneV := by rw [hkF]; exact cinstrAt_haltOne
  have e1 : cinstrAt (k + 1) = .setc haltFpcCell fpcV := by rw [hkF]; exact cinstrAt_haltFpc
  have ec0 : (cinstrAt k).cost = 1 := by rw [e0]; all_goals rfl
  have ec1 : (cinstrAt (k + 1)).cost = 1 := by rw [e1]; all_goals rfl
  cases m with
  | zero => exact absurd h (sim_zero_not_mem f L k (by omega) c)
  | succ m =>
    obtain ⟨H0, c1, h1, hc1⟩ := sim_peel hκ f L (m := m) (k := k) (c := c) (by omega) h
    cases m with
    | zero => exact absurd h1 (sim_zero_not_mem f L (k + 1) (by omega) c1)
    | succ m =>
      obtain ⟨H1, c2, h2, hc2⟩ :=
        sim_peel hκ f L (m := m) (k := k + 1) (c := c1) (by omega) h1
      cases m with
      | zero => exact absurd h2 (sim_zero_not_mem f L (k + 1 + 1) (by omega) c2)
      | succ m =>
        have H0' : Holds f L F_start := by rw [← hkF]; exact H0
        have H1' : Holds f L (F_start + 1) := by rw [← hkF]; exact H1
        obtain ⟨hm, hc3⟩ :=
          sim_jump hκ f L (k + 1 + 1) (by omega) H0' H1' (m := m) (c := c2) h2
        refine ⟨by omega, by omega, H0, H1, ?_⟩
        have H2 := holds_haltJump_of f L H0' H1'
        rw [hkF]
        exact H2

theorem sim_aux (hκ : κ < 64) (f : HashTable) (L : MemImage κ) :
    ∀ m k c, k ≤ F_start →
      some c ∈ support (simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost program L m ⟨gpow k, 1⟩)) →
      k + m = N ∧ c = costFrom k ∧ ∀ k', k ≤ k' → k' < N → Holds f L k' := by
  have hFN := F_start_add_three
  intro m
  induction m with
  | zero =>
    intro k c hk h
    exact absurd h (sim_zero_not_mem f L k (by omega) c)
  | succ m ih =>
    intro k c hk h
    rcases Nat.lt_or_ge k F_start with hlt | hge
    · obtain ⟨hh, c', hc', rfl⟩ := sim_peel hκ f L (m := m) (k := k) (c := c) (by omega) h
      obtain ⟨h1, h2, h3⟩ := ih (k + 1) c' (by omega) hc'
      refine ⟨by omega, by rw [h2, costFrom_succ k (by omega)], fun k' hk1 hk2 => ?_⟩
      by_cases hkk : k' = k
      · rw [hkk]; exact hh
      · exact h3 k' (by omega) hk2
    · have hkF : k = F_start := le_antisymm hk hge
      obtain ⟨hm, hc, H0, H1, H2⟩ := sim_tail hκ f L k hkF (m := m + 1) (c := c) h
      refine ⟨by omega, by rw [hc, hkF, costFrom_F_start], fun k' hk1 hk2 => ?_⟩
      rcases (show k' = k ∨ k' = k + 1 ∨ k' = k + 2 by omega) with hk' | hk' | hk'
      · rw [hk']; exact H0
      · rw [hk']; exact H1
      · rw [hk']; exact H2

/-- **Completeness of the path**: under a fixed table, a completing run has exactly `N` steps,
costs `totalCost`, and every instruction's relation held. -/
theorem run_complete {κ : ℕ} (hκ : κ ≤ maxLogMem) (f : HashTable) (L : MemImage κ) {n c : ℕ}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L n Regs.initial))) :
    n = N ∧ c = totalCost ∧ ∀ k < N, Holds f L k := by
  rw [initial_eq] at h
  obtain ⟨h1, h2, h3⟩ := sim_aux (lt64_of_le_maxLogMem hκ) f L n 0 c (Nat.zero_le _) h
  exact ⟨by omega, h2.trans costFrom_zero, fun k hk => h3 k (Nat.zero_le _) hk⟩

/-- `run_complete` for the equational form of a completing run. -/
theorem run_complete_of_eq {κ : ℕ} (hκ : κ ≤ maxLogMem) (f : HashTable) (L : MemImage κ)
    {n c : ℕ} (h : simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L n Regs.initial) =
      pure (some c)) :
    n = N ∧ c = totalCost ∧ ∀ k < N, Holds f L k :=
  run_complete hκ f L (by rw [h, mem_support_pure_iff])

theorem sim_tail_pos (hκ : κ < 64) (f : HashTable) (L : MemImage κ)
    (H0 : Holds f L F_start) (H1 : Holds f L (F_start + 1)) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L 3 ⟨gpow F_start, 1⟩) =
      pure (some 3) := by
  have hFN := F_start_add_three
  have e2 : simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L (0 + 1) ⟨gpow (F_start + 1 + 1), 1⟩) = pure (some 1) := by
    rw [sim_jump_step hκ f L 0 (F_start + 1 + 1) (by omega) H0 H1, runCost_final_zero,
      simulateQ_pure, map_pure]
    all_goals rfl
  have e1 : simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L (0 + 1 + 1) ⟨gpow (F_start + 1), 1⟩) = pure (some 2) := by
    rw [sim_step_pos hκ f L (0 + 1) (F_start + 1) (by omega) H1, e2, map_pure,
      cinstrAt_haltFpc]
    all_goals rfl
  have e0 : simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L (0 + 1 + 1 + 1) ⟨gpow F_start, 1⟩) = pure (some 3) := by
    rw [sim_step_pos hκ f L (0 + 1 + 1) F_start (by omega) H0, e1, map_pure, cinstrAt_haltOne]
    all_goals rfl
  exact e0

theorem sim_run_aux (hκ : κ < 64) (f : HashTable) (L : MemImage κ)
    (hall : ∀ k < N, Holds f L k) :
    ∀ d k, k + d = F_start →
      simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L (d + 3) ⟨gpow k, 1⟩) =
        pure (some (costFrom k)) := by
  have hFN := F_start_add_three
  intro d
  induction d with
  | zero =>
    intro k hk
    obtain rfl : k = F_start := by omega
    rw [costFrom_F_start]
    exact sim_tail_pos hκ f L (hall _ (by omega)) (hall _ (by omega))
  | succ d ih =>
    intro k hk
    have e : d + 1 + 3 = d + 3 + 1 := by omega
    rw [e, sim_step_pos hκ f L (d + 3) k (by omega) (hall k (by omega)),
      ih (k + 1) (by omega), map_pure, Option.map_some, ← costFrom_succ k (by omega)]

/-- **Soundness of the path**: if every relation holds under a fixed table, the run of `N`
steps completes with cost `totalCost`. -/
theorem run_of_holds {κ : ℕ} (hκ : κ ≤ maxLogMem) (f : HashTable) (L : MemImage κ)
    (hall : ∀ k < N, Holds f L k) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L N Regs.initial) =
      pure (some totalCost) := by
  have h := sim_run_aux (lt64_of_le_maxLogMem hκ) f L hall F_start 0 (by omega)
  rw [costFrom_zero] at h
  rw [initial_eq]
  exact h

/-! ### The `support` semantics -/

theorem supp_peel (hκ : κ < 64) (L : MemImage κ) {m k c : ℕ} (hk : k + 1 < N)
    (h : some c ∈ support (LeanIsa.runCost program L (m + 1) ⟨gpow k, 1⟩)) :
    ∃ c', some c' ∈ support (LeanIsa.runCost program L m ⟨gpow (k + 1), 1⟩) ∧
      c = (cinstrAt k).cost + c' ∧
      ∃ y, some y ∈ support (LeanIsa.execute L ⟨gpow k, 1⟩ (cinstrAt k).toInstr) := by
  rw [runCost_succ_eq L m k (by omega), mem_support_bind_iff] at h
  obtain ⟨x, hx, hc⟩ := h
  rcases supp_exec_next L (gpow k) (cinstrAt_isJump k hk) hx with rfl | rfl
  · rw [Option.elim_none, mem_support_pure_iff] at hc
    exact absurd hc (Option.some_ne_none c)
  · rw [Option.elim_some, support_map] at hc
    obtain ⟨o, ho, hoc⟩ := hc
    rcases o with _ | c'
    · simp at hoc
    · refine ⟨c', ?_, ?_, _, hx⟩
      · rwa [next_gpow] at ho
      · rw [CInstr.weight_toInstr] at hoc
        exact (Option.some.inj hoc).symm

theorem haltOneCell_lt : haltOneCell < 2 ^ 64 - 1 := lt_order_of_lt (by decide)

theorem haltFpcCell_lt : haltFpcCell < 2 ^ 64 - 1 := lt_order_of_lt (by decide)

theorem supp_jump (hκ : κ < 64) (L : MemImage κ) (k : ℕ) (hk : k = F_start + 2)
    (H0 : haltOneCell < 2 ^ κ ∧ Lx L haltOneCell = oneV)
    (H1 : haltFpcCell < 2 ^ κ ∧ Lx L haltFpcCell = fpcV) {m c : ℕ}
    (h : some c ∈ support (LeanIsa.runCost program L (m + 1) ⟨gpow k, 1⟩)) :
    m = 0 ∧ c = 1 := by
  subst hk
  have hkN : F_start + 2 < N := by
    have := F_start_add_three
    omega
  rw [runCost_succ_eq L m (F_start + 2) hkN, execute_haltJump hκ L _ H0 H1, pure_bind,
    Option.elim_some, support_map] at h
  obtain ⟨o, ho, hoc⟩ := h
  rw [cinstrAt_haltJump] at hoc
  cases m with
  | zero =>
    rw [runCost_final_zero, mem_support_pure_iff] at ho
    subst ho
    exact ⟨rfl, (Option.some.inj hoc).symm⟩
  | succ m =>
    rw [runCost_final_succ, mem_support_pure_iff] at ho
    subst ho
    simp at hoc

/-- Segment F in the `support` semantics: exactly three more steps and three cycles. -/
theorem supp_tail (hκ : κ < 64) (L : MemImage κ) (k : ℕ) (hkF : k = F_start) {m c : ℕ}
    (h : some c ∈ support (LeanIsa.runCost program L m ⟨gpow k, 1⟩)) : m = 3 ∧ c = 3 := by
  have hFN := F_start_add_three
  have e0 : cinstrAt k = .setc haltOneCell oneV := by rw [hkF]; exact cinstrAt_haltOne
  have e1 : cinstrAt (k + 1) = .setc haltFpcCell fpcV := by rw [hkF]; exact cinstrAt_haltFpc
  have ec0 : (cinstrAt k).cost = 1 := by rw [e0]; all_goals rfl
  have ec1 : (cinstrAt (k + 1)).cost = 1 := by rw [e1]; all_goals rfl
  cases m with
  | zero =>
    rw [runCost_zero_of_lt L k (by omega), mem_support_pure_iff] at h
    exact absurd h (Option.some_ne_none c)
  | succ m =>
    obtain ⟨c1, h1, hc1, y0, hy0⟩ := supp_peel hκ L (m := m) (k := k) (c := c) (by omega) h
    cases m with
    | zero =>
      rw [runCost_zero_of_lt L (k + 1) (by omega), mem_support_pure_iff] at h1
      exact absurd h1 (Option.some_ne_none c1)
    | succ m =>
      obtain ⟨c2, h2, hc2, y1, hy1⟩ :=
        supp_peel hκ L (m := m) (k := k + 1) (c := c1) (by omega) h1
      cases m with
      | zero =>
        rw [runCost_zero_of_lt L (k + 1 + 1) (by omega), mem_support_pure_iff] at h2
        exact absurd h2 (Option.some_ne_none c2)
      | succ m =>
        rw [e0] at hy0
        rw [e1] at hy1
        have H0 := supp_set_rel hκ L hy0 haltOneCell_lt
        have H1 := supp_set_rel hκ L hy1 haltFpcCell_lt
        obtain ⟨hm, hc3⟩ :=
          supp_jump hκ L (k + 1 + 1) (by omega) H0 H1 (m := m) (c := c2) h2
        exact ⟨by omega, by omega⟩

theorem supp_aux (hκ : κ < 64) (L : MemImage κ) :
    ∀ m k c, k ≤ F_start → some c ∈ support (LeanIsa.runCost program L m ⟨gpow k, 1⟩) →
      k + m = N ∧ c = costFrom k := by
  have hFN := F_start_add_three
  intro m
  induction m with
  | zero =>
    intro k c hk h
    rw [runCost_zero_of_lt L k (by omega), mem_support_pure_iff] at h
    exact absurd h (Option.some_ne_none c)
  | succ m ih =>
    intro k c hk h
    rcases Nat.lt_or_ge k F_start with hlt | hge
    · obtain ⟨c', hc', rfl, -⟩ := supp_peel hκ L (m := m) (k := k) (c := c) (by omega) h
      obtain ⟨h1, h2⟩ := ih (k + 1) c' (by omega) hc'
      exact ⟨by omega, by rw [h2, costFrom_succ k (by omega)]⟩
    · have hkF : k = F_start := le_antisymm hk hge
      obtain ⟨hm, hc⟩ := supp_tail hκ L k hkF (m := m + 1) (c := c) h
      exact ⟨by omega, by rw [hc, hkF, costFrom_F_start]⟩

/-- Every completing run, under any answers, has `N` steps and costs `totalCost`. -/
theorem support_run {κ : ℕ} (hκ : κ ≤ maxLogMem) (L : MemImage κ) {n cost : ℕ}
    (h : some cost ∈ support (LeanIsa.runCost program L n Regs.initial)) :
    n = N ∧ cost = totalCost := by
  rw [initial_eq] at h
  obtain ⟨h1, h2⟩ := supp_aux (lt64_of_le_maxLogMem hκ) L n 0 cost (Nat.zero_le _) h
  exact ⟨by omega, h2.trans costFrom_zero⟩

end Loop

/-- **Cycles**: any submission running this bytecode completes within `claim` cycles. -/
theorem cycles (S : LeanIsa.Submission) (hS : S.program = program) : S.CyclesAtMost claim := by
  intro pk msg σ κ _ hκ L n cost h
  have h' : some cost ∈ support
      (LeanIsa.runCost program (LeanIsa.loadInput pk msg σ L) n Regs.initial) := by
    rw [← hS]
    exact h
  obtain ⟨-, rfl⟩ := support_run hκ _ h'
  exact le_refl _

/-- The seeded rows of a submission running this bytecode at memory size `2 ^ 17`. -/
theorem seededRows_lt (S : LeanIsa.Submission) (hS : S.program = program) (hm : S.memLog = 17) :
    S.seededRows < LeanIsa.maxSeededRows := by
  unfold LeanIsa.Submission.seededRows
  rw [hS, hm]
  exact seeded

/-! ## The relation of each decoded slot -/

section Slots

variable (f : HashTable) {κ : ℕ} (L : MemImage κ)

theorem holds_const {a : ℕ} (ha : a < A_len) : Holds f L a ↔ (constInstr a).Rel f L := by
  rw [holds_iff, cinstrAt_const ha]

theorem holds_step {i j r : ℕ} (hi : i < 34) (hj : j < 255) (hr : r < 10) :
    Holds f L (A_len + 2553 * i + 10 * j + r) ↔ (stepInstr i j r).Rel f L := by
  rw [holds_iff, cinstrAt_step hi hj hr]

theorem holds_end {i e : ℕ} (hi : i < 34) (he : e < 3) :
    Holds f L (A_len + 2553 * i + 2550 + e) ↔ (endInstr i e).Rel f L := by
  rw [holds_iff, cinstrAt_end hi he]

/-! ### Segment A -/

theorem holds_zero : Holds f L 0 ↔ zCell < 2 ^ κ ∧ Lx L zCell = zeroV := by
  rw [holds_const f L (show 0 < A_len by decide), constInstr_zero]
  all_goals exact Iff.rfl

theorem holds_one : Holds f L 1 ↔ z2Cell < 2 ^ κ ∧ Lx L z2Cell = zeroV := by
  rw [holds_const f L (show 1 < A_len by decide), constInstr_one]
  all_goals exact Iff.rfl

theorem holds_two : Holds f L 2 ↔ oneCell < 2 ^ κ ∧ Lx L oneCell = oneV := by
  rw [holds_const f L (show 2 < A_len by decide), constInstr_two]
  all_goals exact Iff.rfl

theorem holds_three : Holds f L 3 ↔ fpcCell < 2 ^ κ ∧ Lx L fpcCell = fpcV := by
  rw [holds_const f L (show 3 < A_len by decide), constInstr_three]
  all_goals exact Iff.rfl

theorem holds_chainId {i : ℕ} (hi : i < 34) :
    Holds f L (4 + i) ↔ chainIdCell i < 2 ^ κ ∧ Lx L (chainIdCell i) = chainIdV i := by
  have hA := A_len_eq
  rw [holds_const f L (show 4 + i < A_len by omega), constInstr_chainId hi]
  all_goals exact Iff.rfl

theorem holds_rootMd {r : ℕ} (hr : r < 34) :
    Holds f L (38 + r) ↔ rootMdCell r < 2 ^ κ ∧ Lx L (rootMdCell r) = rootMdV r := by
  have hA := A_len_eq
  rw [holds_const f L (show 38 + r < A_len by omega), constInstr_rootMd hr]
  all_goals exact Iff.rfl

theorem holds_pos {j : ℕ} (hj : j < 255) :
    Holds f L (72 + j) ↔ posCell j < 2 ^ κ ∧ Lx L (posCell j) = posV j := by
  have hA := A_len_eq
  rw [holds_const f L (show 72 + j < A_len by omega), constInstr_pos hj]
  all_goals exact Iff.rfl

theorem holds_wv {p j : ℕ} (hp : p < 16) (hj : j < 255) :
    Holds f L (327 + 255 * p + j) ↔ wvCell p j < 2 ^ κ ∧ Lx L (wvCell p j) = wvV p j := by
  have hA := A_len_eq
  rw [holds_const f L (show 327 + 255 * p + j < A_len by omega), constInstr_wv hp hj]
  all_goals exact Iff.rfl

theorem holds_wu {j : ℕ} (hj : j < 255) :
    Holds f L (4407 + j) ↔ wuCell j < 2 ^ κ ∧ Lx L (wuCell j) = wuV j := by
  have hA := A_len_eq
  rw [holds_const f L (show 4407 + j < A_len by omega), constInstr_wu hj]
  all_goals exact Iff.rfl

theorem holds_wuHi {j : ℕ} (hj : j < 255) :
    Holds f L (4662 + j) ↔ wuHiCell j < 2 ^ κ ∧ Lx L (wuHiCell j) = wuHiV j := by
  have hA := A_len_eq
  rw [holds_const f L (show 4662 + j < A_len by omega), constInstr_wuHi hj]
  all_goals exact Iff.rfl

theorem holds_wuLo {j : ℕ} (hj : j < 255) :
    Holds f L (4917 + j) ↔ wuLoCell j < 2 ^ κ ∧ Lx L (wuLoCell j) = wuLoV j := by
  have hA := A_len_eq
  rw [holds_const f L (show 4917 + j < A_len by omega), constInstr_wuLo hj]
  all_goals exact Iff.rfl

theorem holds_ubHi : Holds f L 5172 ↔ ubHiCell < 2 ^ κ ∧ Lx L ubHiCell = ubHiV := by
  rw [holds_const f L (show 5172 < A_len by decide), constInstr_ubHi]
  all_goals exact Iff.rfl

theorem holds_ubLo : Holds f L 5173 ↔ ubLoCell < 2 ^ κ ∧ Lx L ubLoCell = ubLoV := by
  rw [holds_const f L (show 5173 < A_len by decide), constInstr_ubLo]
  all_goals exact Iff.rfl

theorem holds_vb {p : ℕ} (hp : p < 16) :
    Holds f L (5174 + p) ↔ vbCell p < 2 ^ κ ∧ Lx L (vbCell p) = vbV p := by
  have hA := A_len_eq
  rw [holds_const f L (show 5174 + p < A_len by omega), constInstr_vb hp]
  all_goals exact Iff.rfl

theorem holds_len : Holds f L 5190 ↔ lenCell < 2 ^ κ ∧ Lx L lenCell = lenV := by
  rw [holds_const f L (show 5190 < A_len by decide), constInstr_len]
  all_goals exact Iff.rfl

/-! ### Segment B, the ten slots of step `j` of chain `i` -/

theorem holds_step0 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 0) ↔
      tCell i j < 2 ^ κ ∧ tCell i j < 2 ^ κ ∧ tCell i j < 2 ^ κ ∧
        Lx L (tCell i j) = Lx L (tCell i j) * Lx L (tCell i j) := by
  rw [holds_step f L hi hj (r := 0) (by decide)]
  all_goals exact Iff.rfl

theorem holds_step1 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 1) ↔
      tPrevCell i j < 2 ^ κ ∧ tCell i j < 2 ^ κ ∧ tPrevCell i j < 2 ^ κ ∧
        Lx L (tPrevCell i j) = Lx L (tPrevCell i j) * Lx L (tCell i j) := by
  rw [holds_step f L hi hj (r := 1) (by decide)]
  all_goals exact Iff.rfl

theorem holds_step2 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 2) ↔
      xCell i j < 2 ^ κ ∧ sigCell i < 2 ^ κ ∧ sCell i j < 2 ^ κ ∧
        Lx L (sCell i j) = Lx L (xCell i j) + Lx L (sigCell i) := by
  rw [holds_step f L hi hj (r := 2) (by decide)]
  all_goals exact Iff.rfl

theorem holds_step3 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 3) ↔
      tPrevCell i j < 2 ^ κ ∧ sCell i j < 2 ^ κ ∧ uCell i j < 2 ^ κ ∧
        Lx L (uCell i j) = Lx L (tPrevCell i j) * Lx L (sCell i j) := by
  rw [holds_step f L hi hj (r := 3) (by decide)]
  all_goals exact Iff.rfl

theorem holds_step4 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 4) ↔
      sigCell i < 2 ^ κ ∧ uCell i j < 2 ^ κ ∧ inCell i j < 2 ^ κ ∧
        Lx L (inCell i j) = Lx L (sigCell i) + Lx L (uCell i j) := by
  rw [holds_step f L hi hj (r := 4) (by decide)]
  all_goals exact Iff.rfl

/-- The chain step's `BLAKE2S`: `m = (in_j, I_i, J_j, Z)`, `cv = (48, 49)`, output
`(x_{j+1}, h_j)` (`xCell_succ_add_one : xCell i (j + 1) + 1 = hCell i j`), metadata ONE. -/
theorem holds_step5 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 5) ↔
      (inCell i j < 2 ^ κ ∧ chainIdCell i < 2 ^ κ ∧ posCell j < 2 ^ κ ∧ zCell < 2 ^ κ ∧
        zCell < 2 ^ κ ∧ zCell + 1 < 2 ^ κ ∧ xCell i (j + 1) < 2 ^ κ ∧
        xCell i (j + 1) + 1 < 2 ^ κ ∧ oneCell < 2 ^ κ) ∧
      LeanIsa.OracleCompressCells
        ![Lx L (inCell i j), Lx L (chainIdCell i), Lx L (posCell j), Lx L zCell]
        (Lx L zCell) (Lx L (zCell + 1)) (Lx L (xCell i (j + 1))) (Lx L (xCell i (j + 1) + 1))
        (Lx L oneCell)
        (f ⟨896, LeanIsa.blake2sQuery
          ![Lx L (inCell i j), Lx L (chainIdCell i), Lx L (posCell j), Lx L zCell]
          (Lx L zCell) (Lx L (zCell + 1)) (Lx L oneCell)⟩) := by
  rw [holds_step f L hi hj (r := 5) (by decide)]
  all_goals exact Iff.rfl

theorem holds_step6 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 6) ↔
      tCell i j < 2 ^ κ ∧ wvCell (bytePos i) j < 2 ^ κ ∧ pVCell i j < 2 ^ κ ∧
        Lx L (pVCell i j) = Lx L (tCell i j) * Lx L (wvCell (bytePos i) j) := by
  rw [holds_step f L hi hj (r := 6) (by decide)]
  all_goals exact Iff.rfl

theorem holds_step7 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 7) ↔
      aVCell i j < 2 ^ κ ∧ pVCell i j < 2 ^ κ ∧ aVCell i (j + 1) < 2 ^ κ ∧
        Lx L (aVCell i (j + 1)) = Lx L (aVCell i j) + Lx L (pVCell i j) := by
  rw [holds_step f L hi hj (r := 7) (by decide)]
  all_goals exact Iff.rfl

theorem holds_step8 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 8) ↔
      tCell i j < 2 ^ κ ∧ wuSelCell i j < 2 ^ κ ∧ pUCell i j < 2 ^ κ ∧
        Lx L (pUCell i j) = Lx L (tCell i j) * Lx L (wuSelCell i j) := by
  rw [holds_step f L hi hj (r := 8) (by decide)]
  all_goals exact Iff.rfl

theorem holds_step9 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    Holds f L (A_len + 2553 * i + 10 * j + 9) ↔
      aUCell i j < 2 ^ κ ∧ pUCell i j < 2 ^ κ ∧ aUCell i (j + 1) < 2 ^ κ ∧
        Lx L (aUCell i (j + 1)) = Lx L (aUCell i j) + Lx L (pUCell i j) := by
  rw [holds_step f L hi hj (r := 9) (by decide)]
  all_goals exact Iff.rfl

/-! ### Segment B, the endpoint of chain `i` -/

theorem holds_end0 {i : ℕ} (hi : i < 34) :
    Holds f L (A_len + 2553 * i + 2550 + 0) ↔
      xCell i 255 < 2 ^ κ ∧ sigCell i < 2 ^ κ ∧ e0Cell i < 2 ^ κ ∧
        Lx L (e0Cell i) = Lx L (xCell i 255) + Lx L (sigCell i) := by
  rw [holds_end f L hi (e := 0) (by decide)]
  all_goals exact Iff.rfl

theorem holds_end1 {i : ℕ} (hi : i < 34) :
    Holds f L (A_len + 2553 * i + 2550 + 1) ↔
      tCell i 254 < 2 ^ κ ∧ e0Cell i < 2 ^ κ ∧ e1Cell i < 2 ^ κ ∧
        Lx L (e1Cell i) = Lx L (tCell i 254) * Lx L (e0Cell i) := by
  rw [holds_end f L hi (e := 1) (by decide)]
  all_goals exact Iff.rfl

theorem holds_end2 {i : ℕ} (hi : i < 34) :
    Holds f L (A_len + 2553 * i + 2550 + 2) ↔
      sigCell i < 2 ^ κ ∧ e1Cell i < 2 ^ κ ∧ endCell i < 2 ^ κ ∧
        Lx L (endCell i) = Lx L (sigCell i) + Lx L (e1Cell i) := by
  rw [holds_end f L hi (e := 2) (by decide)]
  all_goals exact Iff.rfl

/-! ### Segments C and D -/

theorem holds_link {h s : ℕ} (hh : h < 2) (hs : s < 15) :
    Holds f L (C_start + 15 * h + s) ↔
      linkAccCell h s < 2 ^ κ ∧ dCell (linkChain h (s + 1)) < 2 ^ κ ∧
        linkAccCell h (s + 1) < 2 ^ κ ∧
        Lx L (linkAccCell h (s + 1)) =
          Lx L (linkAccCell h s) + Lx L (dCell (linkChain h (s + 1))) := by
  rw [holds_iff, cinstrAt_link hh hs]
  all_goals exact Iff.rfl

theorem holds_prod {s : ℕ} (hs : s < 31) :
    Holds f L (D_start + s) ↔
      prodAccCell s < 2 ^ κ ∧ pCell (s + 1) < 2 ^ κ ∧ prodAccCell (s + 1) < 2 ^ κ ∧
        Lx L (prodAccCell (s + 1)) = Lx L (prodAccCell s) * Lx L (pCell (s + 1)) := by
  rw [holds_iff, cinstrAt_prod (show s < 32 by omega), prodInstr, if_pos hs]
  all_goals exact Iff.rfl

theorem holds_prodCheck :
    Holds f L (D_start + 31) ↔
      pCell 32 < 2 ^ κ ∧ pCell 33 < 2 ^ κ ∧ prodAccCell 31 < 2 ^ κ ∧
        Lx L (prodAccCell 31) = Lx L (pCell 32) * Lx L (pCell 33) := by
  rw [holds_iff, cinstrAt_prod (show (31 : ℕ) < 32 by decide), prodInstr,
    if_neg (show ¬ ((31 : ℕ) < 31) by decide)]
  all_goals exact Iff.rfl

/-! ### Segments E and F -/

/-- Root absorption `t`: `m = (end_t, Z, Z, Z)`, `cv = S_t`, `out = S_{t+1}`,
`md = R_{33 - t}`. -/
theorem holds_absorb {t : ℕ} (ht : t < 34) :
    Holds f L (E_start + t) ↔
      (endCell t < 2 ^ κ ∧ zCell < 2 ^ κ ∧ zCell < 2 ^ κ ∧ zCell < 2 ^ κ ∧
        rootStateCell t < 2 ^ κ ∧ rootStateCell t + 1 < 2 ^ κ ∧
        rootStateCell (t + 1) < 2 ^ κ ∧ rootStateCell (t + 1) + 1 < 2 ^ κ ∧
        rootMdCell (33 - t) < 2 ^ κ) ∧
      LeanIsa.OracleCompressCells ![Lx L (endCell t), Lx L zCell, Lx L zCell, Lx L zCell]
        (Lx L (rootStateCell t)) (Lx L (rootStateCell t + 1)) (Lx L (rootStateCell (t + 1)))
        (Lx L (rootStateCell (t + 1) + 1)) (Lx L (rootMdCell (33 - t)))
        (f ⟨896, LeanIsa.blake2sQuery ![Lx L (endCell t), Lx L zCell, Lx L zCell, Lx L zCell]
          (Lx L (rootStateCell t)) (Lx L (rootStateCell t + 1))
          (Lx L (rootMdCell (33 - t)))⟩) := by
  rw [holds_iff, cinstrAt_root (show t < 35 by omega), rootInstr, if_pos ht]
  all_goals exact Iff.rfl

theorem holds_pk :
    Holds f L (E_start + 34) ↔
      rootStateCell 34 < 2 ^ κ ∧ zCell < 2 ^ κ ∧ pkCell < 2 ^ κ ∧
        Lx L pkCell = Lx L (rootStateCell 34) + Lx L zCell := by
  rw [holds_iff, cinstrAt_root (show (34 : ℕ) < 35 by decide), rootInstr,
    if_neg (show ¬ ((34 : ℕ) < 34) by decide)]
  all_goals exact Iff.rfl

theorem holds_halt {u : ℕ} (hu : u < 3) : Holds f L (F_start + u) ↔ (haltInstr u).Rel f L := by
  rw [holds_iff, cinstrAt_halt hu]

end Slots

end

end OptimalOTS.LeanIsaBaseline.Machine
