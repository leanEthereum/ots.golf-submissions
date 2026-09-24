import Submissions.UpperLeanIsa.MachineProgram
import Submissions.UpperLeanIsa.Correctness
import OptimalOTS.LeanIsa

/-!
# Running the RT-128 bytecode

The execution framework for `Machine.program` (design `NOTES.md` §9.2):

* `Lx L c`, the total view of an image, and the cell-read lemmas;
* the pure instructions (`exec_xor_iff` … `exec_jump_iff`) and the `BLAKE2S` tail;
* `CInstr.Rel f L` (the relation of an instruction under the fixed table `f`), `CInstr.RelNH L`
  (the same with `BLAKE2S ↦ True`, the only information the `support` semantics yields), and
  `Holds` / `HoldsNH` at a slot; `.pad` has relation `False`: it is the trap;
* `slotOf`, `nextSlot` and the `Walk`: a slot sequence from `s` to the sentinel along which a
  relation `R` holds at every executed slot, with its step count and cost;
* the semantic bridges: a completing run under a fixed table is a `Walk (Holds f L)`
  (`walk_of_sim`), a completing run in the `support` semantics is a `Walk (HoldsNH L)`
  (`walk_of_supp`), and a `Walk (Holds f L)` is a completing run (`sim_of_walk`).

All three run in frame `fp = 1`; every `JUMP` of the program has frame operand `oneCell`
(`jump_f`), and slot 0 pins `oneCell := oneV` (`one_of_sim`, `one_of_supp`), so a taken `JUMP`
keeps `fp = 1`.
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

theorem lt_order_of_lt {c : ℕ} (h : c < 65536) : c < 2 ^ 64 - 1 :=
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

/-- The `JUMP` successor: `(g · pc, 1)` when the condition cell is `0`, otherwise the target and
frame cells' `K` values. All three cells are in range and in `K` either way. -/
theorem exec_jump_iff (hκ : κ < 64) (L : MemImage κ) (pc : K) {a b c : ℕ}
    (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) (hc : c < 2 ^ 64 - 1) (y : Regs K) :
    LeanerVM.Semantics.execute L ⟨pc, 1⟩ (.jump (op a) (op b) (op c)) = some y ↔
      (a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧
        IsInK (Lx L a) ∧ IsInK (Lx L b) ∧ IsInK (Lx L c)) ∧
      y = if Lx L a = 0 then ⟨g * pc, 1⟩ else ⟨(Lx L b).limb 0, (Lx L c).limb 0⟩ := by
  constructor
  · intro h
    simp only [LeanerVM.Semantics.execute, one_mul, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨va, hva, vb, hvb, vc, hvc, u, hu, hy⟩ := h
    obtain ⟨ha', rfl⟩ := (read_op_eq_some_iff hκ L ha).mp hva
    obtain ⟨hb', rfl⟩ := (read_op_eq_some_iff hκ L hb).mp hvb
    obtain ⟨hc', rfl⟩ := (read_op_eq_some_iff hκ L hc).mp hvc
    obtain ⟨i1, i2, i3⟩ := optGuard_eq_some hu
    exact ⟨⟨ha', hb', hc', i1, i2, i3⟩, (Option.some.inj hy).symm⟩
  · rintro ⟨⟨ha', hb', hc', i1, i2, i3⟩, rfl⟩
    simp only [LeanerVM.Semantics.execute, one_mul, read_op_of_lt hκ L ha',
      read_op_of_lt hκ L hb', read_op_of_lt hκ L hc', Option.bind_eq_bind, Option.bind_some]
    rw [optGuard_bind_eq_some_iff]
    exact ⟨⟨i1, i2, i3⟩, rfl⟩

/-- The trap: `Instr.xor 0 0 0` reads address `0`, which is never an address. -/
theorem exec_pad (L : MemImage κ) (r : Regs K) :
    LeanerVM.Semantics.execute L r (.xor 0 0 0) = none := by
  simp only [LeanerVM.Semantics.execute, mul_zero, MemImage.read_zero, Option.bind_eq_bind,
    Option.bind_none]

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
  rw [blakeTail, simulateQ_bind, fixed_hash, pure_bind, simulateQ_pure]

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
For `BLAKE2S` the answer is `f ⟨896, blake2sQuery …⟩`. The trap `.pad` never holds. -/
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
  | .pad => False

/-- The hash-free relation: `Rel` with `BLAKE2S ↦ True`. It does not mention the table, and it
is all a completing run in the `support` semantics (no oracle cache) tells about a slot. -/
def CInstr.RelNH {κ : ℕ} (L : MemImage κ) : CInstr → Prop
  | .xor a b c => a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a + Lx L b
  | .mul a b c => a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a * Lx L b
  | .setc a v => a < 2 ^ κ ∧ Lx L a = v
  | .blake .. => True
  | .jump a b c =>
      a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ IsInK (Lx L a) ∧ IsInK (Lx L b) ∧ IsInK (Lx L c)
  | .pad => False

/-- The relation of slot `s` holds on `L` in frame `1` under the table `f`. -/
def Holds (f : HashTable) {κ : ℕ} (L : MemImage κ) (s : ℕ) : Prop := (cinstrAt s).Rel f L

/-- The hash-free relation of slot `s` holds on `L` in frame `1`. -/
def HoldsNH {κ : ℕ} (L : MemImage κ) (s : ℕ) : Prop := (cinstrAt s).RelNH L

theorem CInstr.relNH_of_rel {f : HashTable} {κ : ℕ} {L : MemImage κ} {ci : CInstr}
    (h : ci.Rel f L) : ci.RelNH L := by
  cases ci
  all_goals first | exact h | trivial

theorem holdsNH_of_holds {f : HashTable} {κ : ℕ} {L : MemImage κ} {s : ℕ} (h : Holds f L s) :
    HoldsNH L s := CInstr.relNH_of_rel h

/-- The value a slot's `SET` pins, read off any relation implying `HoldsNH`. -/
theorem setc_of_holdsNH {κ : ℕ} {L : MemImage κ} {s a : ℕ} {v : E} (hs : cinstrAt s = .setc a v)
    (h : HoldsNH L s) : a < 2 ^ κ ∧ Lx L a = v := by
  unfold HoldsNH at h
  rw [hs] at h
  exact h

theorem xor_of_holdsNH {κ : ℕ} {L : MemImage κ} {s a b c : ℕ} (hs : cinstrAt s = .xor a b c)
    (h : HoldsNH L s) : a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a + Lx L b := by
  unfold HoldsNH at h
  rw [hs] at h
  exact h

theorem mul_of_holdsNH {κ : ℕ} {L : MemImage κ} {s a b c : ℕ} (hs : cinstrAt s = .mul a b c)
    (h : HoldsNH L s) : a < 2 ^ κ ∧ b < 2 ^ κ ∧ c < 2 ^ κ ∧ Lx L c = Lx L a * Lx L b := by
  unfold HoldsNH at h
  rw [hs] at h
  exact h

theorem not_holdsNH_pad {κ : ℕ} {L : MemImage κ} {s : ℕ} (hs : cinstrAt s = .pad) :
    ¬ HoldsNH L s := by
  unfold HoldsNH
  rw [hs]
  exact id

theorem CInstr.isJump_eq_true {ci : CInstr} (h : ci.isJump = true) :
    ∃ a b c, ci = .jump a b c := by
  cases ci
  all_goals first | exact ⟨_, _, _, rfl⟩ | simp [CInstr.isJump] at h

/-! ## One instruction under a fixed table -/

section Fixed

variable {κ : ℕ}

theorem exec_pad_eq (L : MemImage κ) (r : Regs K) :
    LeanIsa.execute L r CInstr.pad.toInstr = pure none := by
  show (pure (LeanerVM.Semantics.execute L r (.xor 0 0 0)) : OracleComp Spec (Option (Regs K))) = _
  rw [exec_pad]

theorem exec_jump_eq (L : MemImage κ) (r : Regs K) (a b c : ℕ) :
    LeanIsa.execute L r (CInstr.jump a b c).toInstr =
      pure (LeanerVM.Semantics.execute L r (.jump (op a) (op b) (op c))) := rfl

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
    exact (sim_blakeTail f ⟨pc, 1⟩ ![Lx L m0, Lx L m1, Lx L m2, Lx L m3] (Lx L cv)
      (Lx L (cv + 1)) (Lx L out) (Lx L (out + 1)) (Lx L md)).trans
      (by rw [if_pos hocc]; all_goals rfl)
  | jump a b c => exact absurd hj (by simp [CInstr.isJump])
  | pad => exact hr.elim

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
        hR
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
      rw [simulateQ_bind, mem_support_bind_iff] at hx
      obtain ⟨ans, hans, hx⟩ := hx
      rw [fixed_hash, mem_support_pure_iff] at hans
      subst hans
      rw [simulateQ_pure, mem_support_pure_iff] at hx
      split_ifs at hx with hocc
      · exact Or.inr ⟨hx, hbnd, hocc⟩
      · exact Or.inl hx
  | jump a b c => exact absurd hj (by simp [CInstr.isJump])
  | pad =>
    rw [exec_pad_eq, simulateQ_pure, mem_support_pure_iff] at hx
    exact Or.inl hx

end Fixed

/-! ## One instruction in the `support` semantics -/

section Support

variable {κ : ℕ}

/-- In the `support` semantics a non-jump instruction fails, or steps to the next slot with its
hash-free relation holding. -/
theorem supp_exec (hκ : κ < 64) (L : MemImage κ) (pc : K) {ci : CInstr}
    (hb : ci.Bounded (2 ^ 64 - 1)) (hj : ci.isJump = false) {x : Option (Regs K)}
    (hx : x ∈ support (LeanIsa.execute L ⟨pc, 1⟩ ci.toInstr)) :
    x = none ∨ (x = some (Regs.next ⟨pc, 1⟩) ∧ ci.RelNH L) := by
  cases ci with
  | xor a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    change x ∈ support (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
      (Instr.xor (op a) (op b) (op c))) : OracleComp Spec (Option (Regs K))) at hx
    rw [mem_support_pure_iff] at hx
    rw [hx]
    cases h : LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.xor (op a) (op b) (op c)) with
    | none => exact Or.inl rfl
    | some y =>
      obtain ⟨hrel, hy⟩ := (exec_xor_iff hκ L pc ha hb' hc y).mp h
      rw [hy]
      exact Or.inr ⟨rfl, hrel⟩
  | mul a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    change x ∈ support (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
      (Instr.mulNative (op a) (op b) (op c))) : OracleComp Spec (Option (Regs K))) at hx
    rw [mem_support_pure_iff] at hx
    rw [hx]
    cases h : LeanerVM.Semantics.execute L ⟨pc, 1⟩ (Instr.mulNative (op a) (op b) (op c)) with
    | none => exact Or.inl rfl
    | some y =>
      obtain ⟨hrel, hy⟩ := (exec_mul_iff hκ L pc ha hb' hc y).mp h
      rw [hy]
      exact Or.inr ⟨rfl, hrel⟩
  | setc a v =>
    change x ∈ support (pure (LeanerVM.Semantics.execute L ⟨pc, 1⟩
      (Instr.setConstant (op a) v)) : OracleComp Spec (Option (Regs K))) at hx
    rw [mem_support_pure_iff] at hx
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
    · rw [mem_support_pure_iff] at hx
      exact Or.inl hx
    · rw [mem_support_bind_iff] at hx
      obtain ⟨ans, -, hx⟩ := hx
      rw [mem_support_pure_iff] at hx
      split_ifs at hx
      · exact Or.inr ⟨hx, trivial⟩
      · exact Or.inl hx
  | jump a b c => exact absurd hj (by simp [CInstr.isJump])
  | pad =>
    rw [exec_pad_eq, mem_support_pure_iff] at hx
    exact Or.inl hx

end Support

/-! ## The loop -/

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
  rw [LeanIsa.runCost.eq_2, if_neg hne, hf]
  refine congrArg (fun F : Option (Regs K) → OracleComp Spec (Option ℕ) =>
    LeanIsa.execute L r ins >>= F) (funext fun x => ?_)
  cases x <;> rfl

theorem runCost_zero_eq (L : MemImage κ) (r : Regs K) :
    LeanIsa.runCost program L 0 r =
      pure (if r.pc = program.finalPc ∧ r.fp = 1 then some 0 else none) := by
  rw [LeanIsa.runCost.eq_1]

theorem runCost_succ_final (L : MemImage κ) (n : ℕ) {r : Regs K} (h : r.pc = program.finalPc) :
    LeanIsa.runCost program L (n + 1) r = pure none := by
  rw [LeanIsa.runCost.eq_2]; exact if_pos h

theorem runCost_succ_fetch_none (L : MemImage κ) (n : ℕ) {r : Regs K}
    (hne : r.pc ≠ program.finalPc) (hf : program.fetch r.pc = none) :
    LeanIsa.runCost program L (n + 1) r = pure none := by
  rw [LeanIsa.runCost.eq_2, if_neg hne, hf]

theorem runCost_succ_eq (L : MemImage κ) (m s : ℕ) (hs : s < sentinel) :
    LeanIsa.runCost program L (m + 1) ⟨gpow s, 1⟩ =
      (LeanIsa.execute L ⟨gpow s, 1⟩ (cinstrAt s).toInstr >>= fun x =>
        x.elim (pure none) fun next =>
          Option.map (LeanIsa.weight (cinstrAt s).toInstr.opcode + ·) <$>
            LeanIsa.runCost program L m next) :=
  runCost_succ_of program L m ⟨gpow s, 1⟩ (cinstrAt s).toInstr (gpow_ne_finalPc hs)
    (fetch_eq (by rw [sentinel] at hs; omega))

theorem gpow_sentinel : gpow sentinel = program.finalPc := by
  rw [finalPc_eq]; rfl

theorem eq_sentinel_of_gpow {s : ℕ} (hs : s < 2 ^ 16) (h : gpow s = program.finalPc) :
    s = sentinel := by
  rw [finalPc_eq] at h
  exact gpow_injOn (lt_of_lt_of_le hs (by norm_num)) (show 2 ^ 16 - 1 < 2 ^ 64 - 1 by norm_num) h

theorem finalPc_ne_of_lt {s : ℕ} (hs : s < sentinel) : gpow s ≠ program.finalPc :=
  gpow_ne_finalPc hs

end Loop

/-! ## Slots, successors and walks -/

/-- The slot index of a program counter: `i` when `pc = g ^ i` with `i < 2 ^ 16`, else `2 ^ 16`
(past the sentinel, where no walk lives). -/
def slotOf (pc : K) : ℕ :=
  if h : ∃ i, i < 2 ^ 16 ∧ pc = gpow i then Classical.choose h else 2 ^ 16

theorem slotOf_gpow {i : ℕ} (hi : i < 2 ^ 16) : slotOf (gpow i) = i := by
  unfold slotOf
  have h : ∃ j, j < 2 ^ 16 ∧ gpow i = gpow j := ⟨i, hi, rfl⟩
  rw [dif_pos h]
  obtain ⟨hj, hji⟩ := Classical.choose_spec h
  exact (gpow_injOn (lt_of_lt_of_le hi (by norm_num)) (lt_of_lt_of_le hj (by norm_num)) hji).symm

theorem slotOf_spec {pc : K} (h : slotOf pc < 2 ^ 16) : pc = gpow (slotOf pc) := by
  unfold slotOf at h ⊢
  split_ifs at h ⊢ with hex
  · exact (Classical.choose_spec hex).2
  · omega

/-- The successor slot of an instruction at slot `s`: the fall-through `s + 1`, or for a taken
`JUMP` the slot of its target cell's `K` value. -/
def CInstr.nextOf {κ : ℕ} (L : MemImage κ) (s : ℕ) : CInstr → ℕ
  | .jump a b _ => if Lx L a = 0 then s + 1 else slotOf ((Lx L b).limb 0)
  | _ => s + 1

/-- The successor of slot `s` on the image `L`. -/
def nextSlot {κ : ℕ} (L : MemImage κ) (s : ℕ) : ℕ := (cinstrAt s).nextOf L s

theorem nextSlot_of_jump {κ : ℕ} (L : MemImage κ) {s a b c : ℕ} (h : cinstrAt s = .jump a b c) :
    nextSlot L s = if Lx L a = 0 then s + 1 else slotOf ((Lx L b).limb 0) := by
  unfold nextSlot
  rw [h]
  rfl

theorem nextSlot_of_not_jump {κ : ℕ} (L : MemImage κ) {s : ℕ} (h : (cinstrAt s).isJump = false) :
    nextSlot L s = s + 1 := by
  unfold nextSlot
  generalize cinstrAt s = ci at h
  cases ci
  all_goals first | rfl | simp [CInstr.isJump] at h

/-- A walk: from slot `s`, `n` executed slots of total cost `c`, every one satisfying `R` and
below the sentinel, each followed by its `nextSlot`, ending exactly at the sentinel. -/
inductive Walk (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) : ℕ → ℕ → ℕ → Prop
  | done : Walk R L 0 sentinel 0
  | step {n s c : ℕ} : s < sentinel → R s → Walk R L n (nextSlot L s) c →
      Walk R L (n + 1) s ((cinstrAt s).cost + c)

theorem Walk.le_sentinel {R : ℕ → Prop} {κ : ℕ} {L : MemImage κ} {n s c : ℕ}
    (h : Walk R L n s c) : s ≤ sentinel := by
  cases h with
  | done => exact le_refl _
  | step hs _ _ => exact le_of_lt hs

/-- `Lx L oneCell = oneV` makes `(Lx L oneCell).limb 0 = 1`: a taken `JUMP` keeps `fp = 1`. -/
theorem limb_one {κ : ℕ} {L : MemImage κ} (hone : Lx L oneCell = oneV) :
    (Lx L oneCell).limb 0 = 1 := by
  rw [hone, oneV]; simp

theorem limb_tgtV (t : ℕ) : (tgtV t).limb 0 = gpow t := by
  rw [tgtV]; simp

/-- The registers after a `JUMP` in frame `1` whose frame cell holds ONE. -/
def jumpPc {κ : ℕ} (L : MemImage κ) (a b s : ℕ) : K :=
  if Lx L a = 0 then gpow (s + 1) else (Lx L b).limb 0

theorem exec_jump_one {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) (hone : Lx L oneCell = oneV) {s a b : ℕ}
    (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) (y : Regs K) :
    LeanerVM.Semantics.execute L ⟨gpow s, 1⟩ (.jump (op a) (op b) (op oneCell)) = some y ↔
      (CInstr.jump a b oneCell).RelNH L ∧ y = ⟨jumpPc L a b s, 1⟩ := by
  rw [exec_jump_iff hκ L (gpow s) ha hb (lt_order_of_lt (by decide)) y, limb_one hone,
    g_mul_gpow, jumpPc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2]; split_ifs <;> rfl
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2]; split_ifs <;> rfl

/-! ## The semantic bridges -/

section Bridges

variable {κ : ℕ}

theorem bounded64 (s : ℕ) : (cinstrAt s).Bounded (2 ^ 64 - 1) :=
  (cinstrAt_bounded s).mono (by norm_num)

theorem cinstrAt_zero : cinstrAt 0 = .setc oneCell oneV := by
  rw [cinstrAt_const (show 0 < 127 by decide), Nat.zero_add, posCell_one, posV_one]

/-- A completing run under a fixed table starts at a slot of the program. -/
theorem runCost_pc_valid_sim (f : HashTable) (L : MemImage κ) {n c : ℕ} {r : Regs K}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L n r))) :
    ∃ i, i < 2 ^ 16 ∧ r.pc = gpow i := by
  by_contra hno
  have hne : r.pc ≠ program.finalPc := fun e =>
    hno ⟨2 ^ 16 - 1, by norm_num, e.trans finalPc_eq⟩
  cases n with
  | zero =>
    rw [runCost_zero_eq, if_neg (fun e => hne e.1), simulateQ_pure, mem_support_pure_iff] at h
    exact Option.some_ne_none c h
  | succ n =>
    have hf : program.fetch r.pc = none :=
      (Program.fetch_eq_none_iff program).mpr fun i hi => hno ⟨(i : ℕ), i.isLt, hi⟩
    rw [runCost_succ_fetch_none L n hne hf, simulateQ_pure, mem_support_pure_iff] at h
    exact Option.some_ne_none c h

/-- A completing run in the `support` semantics starts at a slot of the program. -/
theorem runCost_pc_valid_supp (L : MemImage κ) {n c : ℕ} {r : Regs K}
    (h : some c ∈ support (LeanIsa.runCost program L n r)) :
    ∃ i, i < 2 ^ 16 ∧ r.pc = gpow i := by
  by_contra hno
  have hne : r.pc ≠ program.finalPc := fun e =>
    hno ⟨2 ^ 16 - 1, by norm_num, e.trans finalPc_eq⟩
  cases n with
  | zero =>
    rw [runCost_zero_eq, if_neg (fun e => hne e.1), mem_support_pure_iff] at h
    exact Option.some_ne_none c h
  | succ n =>
    have hf : program.fetch r.pc = none :=
      (Program.fetch_eq_none_iff program).mpr fun i hi => hno ⟨(i : ℕ), i.isLt, hi⟩
    rw [runCost_succ_fetch_none L n hne hf, mem_support_pure_iff] at h
    exact Option.some_ne_none c h

theorem runCost_zero_not_mem_sim (f : HashTable) (L : MemImage κ) {s : ℕ} (hs : s < sentinel)
    (c : ℕ) : some c ∉ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L 0 ⟨gpow s, 1⟩)) := by
  rw [runCost_zero_eq, if_neg (fun e => finalPc_ne_of_lt hs e.1), simulateQ_pure,
    mem_support_pure_iff]
  exact Option.some_ne_none c

theorem runCost_zero_not_mem_supp (L : MemImage κ) {s : ℕ} (hs : s < sentinel) (c : ℕ) :
    some c ∉ support (LeanIsa.runCost program L 0 ⟨gpow s, 1⟩) := by
  rw [runCost_zero_eq, if_neg (fun e => finalPc_ne_of_lt hs e.1), mem_support_pure_iff]
  exact Option.some_ne_none c

/-- Slot 0 pins ONE: every completing run under a fixed table has `oneCell = oneV`. -/
theorem one_of_sim (hκ : κ ≤ maxLogMem) {f : HashTable} {L : MemImage κ} {n c : ℕ}
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L n ⟨gpow 0, 1⟩))) : Lx L oneCell = oneV := by
  cases n with
  | zero => exact absurd h (runCost_zero_not_mem_sim f L (by decide) c)
  | succ n =>
    rw [runCost_succ_eq L n 0 (by decide), simulateQ_bind, mem_support_bind_iff] at h
    obtain ⟨x, hx, hc⟩ := h
    have hb := bounded64 0
    rw [cinstrAt_zero] at hb hx hc
    rcases sim_exec_supp (lt64_of_le_maxLogMem hκ) f L (gpow 0) hb rfl hx with rfl | ⟨rfl, hrel⟩
    · rw [Option.elim_none, simulateQ_pure, mem_support_pure_iff] at hc
      exact absurd hc (Option.some_ne_none c)
    · exact hrel.2

/-- Slot 0 pins ONE: every completing run in the `support` semantics has `oneCell = oneV`. -/
theorem one_of_supp (hκ : κ ≤ maxLogMem) {L : MemImage κ} {n c : ℕ}
    (h : some c ∈ support (LeanIsa.runCost program L n ⟨gpow 0, 1⟩)) : Lx L oneCell = oneV := by
  cases n with
  | zero => exact absurd h (runCost_zero_not_mem_supp L (by decide) c)
  | succ n =>
    rw [runCost_succ_eq L n 0 (by decide), mem_support_bind_iff] at h
    obtain ⟨x, hx, hc⟩ := h
    have hb := bounded64 0
    rw [cinstrAt_zero] at hb hx hc
    rcases supp_exec (lt64_of_le_maxLogMem hκ) L (gpow 0) hb rfl hx with rfl | ⟨rfl, hrel⟩
    · rw [Option.elim_none, mem_support_pure_iff] at hc
      exact absurd hc (Option.some_ne_none c)
    · exact hrel.2

theorem lt_sentinel_of_mem_sim (f : HashTable) (L : MemImage κ) {n s c : ℕ} (hs : s < 2 ^ 16)
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L (n + 1) ⟨gpow s, 1⟩))) : s < sentinel := by
  by_contra hge
  have hs' : s = sentinel := by rw [sentinel] at hge ⊢; omega
  rw [runCost_succ_final L n (show (⟨gpow s, 1⟩ : Regs K).pc = program.finalPc by
    rw [hs']; exact gpow_sentinel), simulateQ_pure, mem_support_pure_iff] at h
  exact Option.some_ne_none c h

theorem lt_sentinel_of_mem_supp (L : MemImage κ) {n s c : ℕ} (hs : s < 2 ^ 16)
    (h : some c ∈ support (LeanIsa.runCost program L (n + 1) ⟨gpow s, 1⟩)) : s < sentinel := by
  by_contra hge
  have hs' : s = sentinel := by rw [sentinel] at hge ⊢; omega
  rw [runCost_succ_final L n (show (⟨gpow s, 1⟩ : Regs K).pc = program.finalPc by
    rw [hs']; exact gpow_sentinel), mem_support_pure_iff] at h
  exact Option.some_ne_none c h

/-- The successor slot of a `JUMP` from a valid program counter. -/
theorem nextSlot_of_jumpPc (L : MemImage κ) {s a b c i : ℕ} (hci : cinstrAt s = .jump a b c)
    (hs : s < sentinel) (hi : i < 2 ^ 16) (hpc : jumpPc L a b s = gpow i) : nextSlot L s = i := by
  rw [nextSlot_of_jump L hci]
  unfold jumpPc at hpc
  split_ifs at hpc ⊢
  · rw [sentinel] at hs
    exact gpow_injOn (lt_order_of_lt (by omega)) (lt_order_of_lt (by omega)) hpc
  · rw [hpc, slotOf_gpow hi]

/-- `nextSlot` of a `JUMP` below the sentinel is its `jumpPc`. -/
theorem jumpPc_of_le (L : MemImage κ) {s a b c : ℕ} (hci : cinstrAt s = .jump a b c)
    (hle : nextSlot L s ≤ sentinel) : jumpPc L a b s = gpow (nextSlot L s) := by
  rw [nextSlot_of_jump L hci] at hle ⊢
  unfold jumpPc
  split_ifs at hle ⊢
  · rfl
  · exact slotOf_spec (by rw [sentinel] at hle; omega)

/-- **Walk of a fixed-table run.** A completing run under a fixed table from slot `s` is a walk
along which every executed slot's relation holds. -/
theorem walk_of_sim (hκ : κ ≤ maxLogMem) {f : HashTable} {L : MemImage κ}
    (hone : Lx L oneCell = oneV) {n s c : ℕ} (hs : s < 2 ^ 16)
    (h : some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program L n ⟨gpow s, 1⟩))) : Walk (Holds f L) L n s c := by
  have hκ' := lt64_of_le_maxLogMem hκ
  induction n generalizing s c with
  | zero =>
    rw [runCost_zero_eq, simulateQ_pure, mem_support_pure_iff] at h
    split_ifs at h with h0
    · obtain rfl : c = 0 := (Option.some.inj h)
      obtain rfl := eq_sentinel_of_gpow hs h0.1
      exact Walk.done
  | succ n ih =>
    have hlt := lt_sentinel_of_mem_sim f L hs h
    rw [runCost_succ_eq L n s hlt, simulateQ_bind, mem_support_bind_iff] at h
    obtain ⟨x, hx, hc⟩ := h
    cases hj : (cinstrAt s).isJump with
    | false =>
      rcases sim_exec_supp hκ' f L (gpow s) (bounded64 s) hj hx with rfl | ⟨rfl, hrel⟩
      · rw [Option.elim_none, simulateQ_pure, mem_support_pure_iff] at hc
        exact absurd hc (Option.some_ne_none c)
      · rw [Option.elim_some, simulateQ_map, support_map] at hc
        obtain ⟨o, ho, hoc⟩ := hc
        rcases o with _ | c'
        · simp at hoc
        · rw [CInstr.weight_toInstr] at hoc
          obtain rfl : c = (cinstrAt s).cost + c' := (Option.some.inj hoc).symm
          rw [next_gpow] at ho
          have hw := ih (s := s + 1) (by rw [sentinel] at hlt; omega) ho
          rw [← nextSlot_of_not_jump L hj] at hw
          exact Walk.step hlt hrel hw
    | true =>
      obtain ⟨a, b, c0, hci⟩ := CInstr.isJump_eq_true hj
      obtain rfl := jump_f hci
      have hb := bounded64 s
      rw [hci] at hb
      obtain ⟨ha, hb', -⟩ := hb
      rw [hci, exec_jump_eq, simulateQ_pure, mem_support_pure_iff] at hx
      subst hx
      cases hy : LeanerVM.Semantics.execute L ⟨gpow s, 1⟩ (.jump (op a) (op b) (op oneCell)) with
      | none =>
        rw [hy, Option.elim_none, simulateQ_pure, mem_support_pure_iff] at hc
        exact absurd hc (Option.some_ne_none c)
      | some y =>
        obtain ⟨hrel, rfl⟩ := (exec_jump_one hκ' L hone ha hb' y).mp hy
        rw [hy, Option.elim_some, simulateQ_map, support_map] at hc
        obtain ⟨o, ho, hoc⟩ := hc
        rcases o with _ | c'
        · simp at hoc
        · rw [CInstr.weight_toInstr] at hoc
          obtain rfl : c = (cinstrAt s).cost + c' := (Option.some.inj hoc).symm
          have hH : Holds f L s := by
            unfold Holds; rw [hci]; exact hrel
          obtain ⟨i, hi, hpc⟩ := runCost_pc_valid_sim f L ho
          change jumpPc L a b s = gpow i at hpc
          rw [hpc] at ho
          have hw := ih hi ho
          rw [← nextSlot_of_jumpPc L hci hlt hi hpc] at hw
          exact Walk.step hlt hH hw

/-- **Walk of a `support` run.** A completing run in the `support` semantics from slot `s` is a
walk along which every executed slot's hash-free relation holds. -/
theorem walk_of_supp (hκ : κ ≤ maxLogMem) {L : MemImage κ} (hone : Lx L oneCell = oneV)
    {n s c : ℕ} (hs : s < 2 ^ 16)
    (h : some c ∈ support (LeanIsa.runCost program L n ⟨gpow s, 1⟩)) :
    Walk (HoldsNH L) L n s c := by
  have hκ' := lt64_of_le_maxLogMem hκ
  induction n generalizing s c with
  | zero =>
    rw [runCost_zero_eq, mem_support_pure_iff] at h
    split_ifs at h with h0
    · obtain rfl : c = 0 := (Option.some.inj h)
      obtain rfl := eq_sentinel_of_gpow hs h0.1
      exact Walk.done
  | succ n ih =>
    have hlt := lt_sentinel_of_mem_supp L hs h
    rw [runCost_succ_eq L n s hlt, mem_support_bind_iff] at h
    obtain ⟨x, hx, hc⟩ := h
    cases hj : (cinstrAt s).isJump with
    | false =>
      rcases supp_exec hκ' L (gpow s) (bounded64 s) hj hx with rfl | ⟨rfl, hrel⟩
      · rw [Option.elim_none, mem_support_pure_iff] at hc
        exact absurd hc (Option.some_ne_none c)
      · rw [Option.elim_some, support_map] at hc
        obtain ⟨o, ho, hoc⟩ := hc
        rcases o with _ | c'
        · simp at hoc
        · rw [CInstr.weight_toInstr] at hoc
          obtain rfl : c = (cinstrAt s).cost + c' := (Option.some.inj hoc).symm
          rw [next_gpow] at ho
          have hw := ih (s := s + 1) (by rw [sentinel] at hlt; omega) ho
          rw [← nextSlot_of_not_jump L hj] at hw
          exact Walk.step hlt hrel hw
    | true =>
      obtain ⟨a, b, c0, hci⟩ := CInstr.isJump_eq_true hj
      obtain rfl := jump_f hci
      have hb := bounded64 s
      rw [hci] at hb
      obtain ⟨ha, hb', -⟩ := hb
      rw [hci, exec_jump_eq, mem_support_pure_iff] at hx
      subst hx
      cases hy : LeanerVM.Semantics.execute L ⟨gpow s, 1⟩ (.jump (op a) (op b) (op oneCell)) with
      | none =>
        rw [hy, Option.elim_none, mem_support_pure_iff] at hc
        exact absurd hc (Option.some_ne_none c)
      | some y =>
        obtain ⟨hrel, rfl⟩ := (exec_jump_one hκ' L hone ha hb' y).mp hy
        rw [hy, Option.elim_some, support_map] at hc
        obtain ⟨o, ho, hoc⟩ := hc
        rcases o with _ | c'
        · simp at hoc
        · rw [CInstr.weight_toInstr] at hoc
          obtain rfl : c = (cinstrAt s).cost + c' := (Option.some.inj hoc).symm
          have hH : HoldsNH L s := by
            unfold HoldsNH; rw [hci]; exact hrel
          obtain ⟨i, hi, hpc⟩ := runCost_pc_valid_supp L ho
          change jumpPc L a b s = gpow i at hpc
          rw [hpc] at ho
          have hw := ih hi ho
          rw [← nextSlot_of_jumpPc L hci hlt hi hpc] at hw
          exact Walk.step hlt hH hw

/-- **Run of a walk.** Under a fixed table, a walk from slot `s` whose relations hold is a
completing run of exactly its steps and cost. -/
theorem sim_of_walk (hκ : κ ≤ maxLogMem) {f : HashTable} {L : MemImage κ}
    (hone : Lx L oneCell = oneV) {n s c : ℕ} (hw : Walk (Holds f L) L n s c) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program L n ⟨gpow s, 1⟩) =
      pure (some c) := by
  have hκ' := lt64_of_le_maxLogMem hκ
  induction hw with
  | done =>
    rw [runCost_zero_eq, if_pos ⟨gpow_sentinel, rfl⟩, simulateQ_pure]
  | @step n s c hs hR hw ih =>
    rw [runCost_succ_eq L n s hs, simulateQ_bind]
    cases hj : (cinstrAt s).isJump with
    | false =>
      rw [sim_exec_pos hκ' f L (gpow s) (bounded64 s) hj hR, pure_bind, Option.elim_some,
        simulateQ_map, g_mul_gpow, ← nextSlot_of_not_jump L hj, ih, map_pure, Option.map_some,
        CInstr.weight_toInstr]
    | true =>
      obtain ⟨a, b, c0, hci⟩ := CInstr.isJump_eq_true hj
      obtain rfl := jump_f hci
      have hb := bounded64 s
      rw [hci] at hb
      obtain ⟨ha, hb', -⟩ := hb
      have hrel : (CInstr.jump a b oneCell).RelNH L := by
        have h' := hR
        unfold Holds at h'
        rw [hci] at h'
        exact h'
      have hex : LeanerVM.Semantics.execute L ⟨gpow s, 1⟩ (.jump (op a) (op b) (op oneCell)) =
          some ⟨gpow (nextSlot L s), 1⟩ :=
        (exec_jump_one hκ' L hone ha hb' _).mpr ⟨hrel, by rw [jumpPc_of_le L hci hw.le_sentinel]⟩
      rw [CInstr.weight_toInstr, hci, exec_jump_eq, hex, simulateQ_pure, pure_bind,
        Option.elim_some, simulateQ_map, ih, map_pure, Option.map_some]

end Bridges

end

end OptimalOTS.LeanIsaBaseline.Machine
