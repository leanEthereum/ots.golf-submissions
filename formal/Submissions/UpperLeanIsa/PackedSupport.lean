import Submissions.UpperLeanIsa.FourMachineDecode
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! Cell relations and oracle semantics shared by the packed affine machine.
No legacy two-slot entry execution theorem is imported. -/
namespace OptimalOTS.HLFour
open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV HashTable inputWord_len cellBits_natV fixed_hash)
noncomputable section
variable {T : Tab} {κ : ℕ}

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
  | .init => v oneCell = oneV ∧ v lenCell = natV 5504
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

/-- The constants every jump relies on: `ONE` and the 14 frames. -/
def Pinned (v : ℕ → E) : Prop := v oneCell = oneV ∧ ∀ k < 14, v (fCell k) = frameV k

/-- The loader's capped length and its zero padding at short-length aliases. -/
def LengthDomain (v : ℕ → E) : Prop := ∃ n ≤ 5505, v lenCell = natV n ∧
  ∀ a, (n,a) ∈ OptimalOTS.HLG3.LengthGate128.lowAliases → v a = 0

/-- Four existing cost constants rule out the remaining length aliases. -/
def PrePinned (v : ℕ → E) : Prop := ∀ c, 1 ≤ c → c ≤ 4 → v (cCell c) = cV c

theorem prepinned_of_pinned {v : ℕ → E} (h : Pinned v) : PrePinned v := by
  intro c hc hc4
  by_cases hc1 : c = 1
  · subst c
    have hf := h.2 0 (by decide)
    change v (cCell 1) = frameV 0 at hf
    exact hf.trans (frameV_eq_cV (by decide : (0 : ℕ) ≠ 1))
  · have hf := h.2 c (by omega)
    simpa only [fCell, if_neg hc1, frameV_eq_cV hc1, if_neg (show c ≠ 0 by omega)] using hf

theorem lengthDomain_exact {v : ℕ → E} (h : v lenCell = natV 5504) : LengthDomain v := by
  refine ⟨5504, by omega, h, ?_⟩
  intro a ha
  simp [OptimalOTS.HLG3.LengthGate128.lowAliases] at ha

theorem lengthDomain_load {κ : ℕ} (h16 : 16 ≤ κ) (pk : PublicKey) (m : Message)
    (σ : List Bool) (L : MemImage κ) : LengthDomain (Lx (LeanIsa.loadInput pk m σ L)) := by
  refine ⟨min σ.length (OptimalOTS.maxSignatureBits + 1), Nat.min_le_right _ _, ?_, ?_⟩
  · have hc : lenCell < 2^κ := lt_of_lt_of_le (by decide : lenCell < 2^16)
      (Nat.pow_le_pow_right (by norm_num) h16)
    rw [Lx, dif_pos hc, LeanIsa.loadInput, if_pos (by change lenCell < LeanIsa.inputCells; decide)]
    exact inputWord_len pk m σ
  · intro a ha
    obtain ⟨hn, h4, h47, hbits⟩ := OptimalOTS.HLG3.LengthGate128.low_alias_bounds _ ha
    have hs : σ.length ≤ 128 * (a - 4) := by unfold maxSignatureBits at *; omega
    have haκ : a < 2^κ := lt_of_lt_of_le (by omega : a < 2^16)
      (Nat.pow_le_pow_right (by norm_num) h16)
    rw [Lx, dif_pos haκ, LeanIsa.loadInput, if_pos (by change a < LeanIsa.inputCells; exact h47)]
    exact OptimalOTS.HLG3.inputWord_suffix_zero pk m σ h4 hs

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
theorem read_frame_sop {k c : ℕ} (hk : k < 14) (hc : c < 2 ^ 16) :
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


/-! ## Units and frames -/

/-- Unit `j` uses frame `j`, independently of the free digit. -/
def frU (_s j : ℕ) : ℕ := j

theorem frU_zero (s : ℕ) : frU s 0 = 0 := rfl
theorem frU_ne {s j : ℕ} (_hj : j ≠ 1) : frU s j = j := rfl
theorem frU_lt (s : ℕ) {j : ℕ} (hj : j < 14) : frU s j < 14 := hj
theorem frU_pos (s : ℕ) {j : ℕ} (hj : j ≠ 0) : frU s j ≠ 0 := hj
theorem gOf_frU (s : ℕ) {j : ℕ} (_h1 : j ≠ 0) (_hj : j < 14) : gOf (frU s j) = j-1 := rfl
theorem Wf_frU (s : ℕ) {j : ℕ} (_hj : j < 14) : Wf (frU s j) = Wf j := rfl

def zU (_s _u : ℕ) : Bool := false

theorem bodyF_frU_succ (T : Tab) (s : ℕ) {u : ℕ} (hu : u < 13) (x : ℕ) :
    bodyF T (frU s (u+1)) x = body T u x (zU s u) := bodyF_succ T hu x

theorem bodyF_frU_zero (T : Tab) (s x : ℕ) : bodyF T (frU s 0) x = fbody x := by
  rw [frU_zero, bodyF_zero]

/-- The control op after unit `j - 1`: the dispatch of unit `j`, or the exit. -/
def ctlF' (s j : ℕ) : CInstr := if j < 14 then .dispatch (frU s j) else .exit

theorem ctlOf_frU (s : ℕ) {j x : ℕ} (hj : j < 14) (_hx : j = 0 → x = s) :
    ctlOf (frU s j) x = ctlF' s (j+1) := by
  by_cases h0 : j = 0
  · subst j; rfl
  · simp only [frU,ctlOf,if_neg h0,gOf,Nat.sub_add_cancel (show 1 ≤ j by omega)]
    unfold ctlF ctlF' frU
    split_ifs <;> first | rfl | omega

/-! ## The index vector of an image -/

/-- The free digit read off the free landing hint. -/
def x0Of (v : ℕ → E) : ℕ := xOf 0 (slotOf ((v (hCell 0)).limb 0))

/-- The index of unit `f` read off its frame's landing hint. -/
def xsOf (v : ℕ → E) (f : ℕ) : ℕ := xOf (frU (x0Of v) f) (slotOf ((v (hCell (frU (x0Of v) f))).limb 0))

theorem xsOf_zero (v : ℕ → E) : xsOf v 0 = x0Of v := by
  unfold xsOf; rw [frU_zero]; rfl

/-- The landing hints of the index vector `xs`. -/
def Landing (v : ℕ → E) (xs : ℕ → ℕ) : Prop :=
  ∀ f < 14, v (hCell (frU (xs 0) f)) = ofK (gpow (ent (frU (xs 0) f) (xs f)))

/-- The index vector is in range. -/
def Valid (xs : ℕ → ℕ) : Prop := ∀ f < 14, xs f < Wf f

theorem digit_eq_of_entry {v : ℕ → E} {f e : ℕ} (he : IsEntry f e)
    (hx : (v (hCell f)).limb 0 = gpow e) :
    e = ent f (xOf f (slotOf ((v (hCell f)).limb 0))) ∧ xOf f (slotOf ((v (hCell f)).limb 0)) < Wf f := by
  have hlt := isEntry_lt he
  rw [hx, slotOf_gpow (by unfold sentinel at hlt; omega)]
  exact ⟨(isEntry_eq he).2, (isEntry_eq he).1⟩

/-- `H_f · g` lands after the entry. -/
theorem nextMul_mem (T : Tab) (s : ℕ) {j x : ℕ} (hj : j < 13) (hx : j = 0 → x = s) :
    CInstr.mul (hCell (frU s (j + 1))) gCell (h1Cell (frU s (j + 1))) ∈ bodyF T (frU s j) x := by
  by_cases h0 : j = 0
  · subst h0
    rw [bodyF_frU_zero, hx rfl]
    have : frU s (0 + 1) = frG0 s := rfl
    rw [this]; unfold fbody frG0; simp
  · obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    rw [bodyF_frU_succ T s (by omega), frU_ne (by omega)]
    unfold body
    simp only [List.mem_append, List.mem_singleton]
    right
    unfold nextOp; rw [if_pos (by omega)]

/-- The group hash total. -/
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

def gsum (T : Tab) (xs : ℕ → ℕ) : ℕ :=
  ∑ u ∈ Finset.range 13, cost T u (xs (u + 1))

theorem cost_le (hT : T.Hyp) {u x : ℕ} (hu : u < 13) (hx : x < VF u) :
    cost T u x ≤ 17 := by
  rw [hT.cost_eq u hu x hx]
  have := band_lt_17 hu hx
  omega

theorem charged_sum (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs) :
    (∑ w ∈ Finset.range 13, chargedCost T w (xs (w + 1))) + 8 =
      ∑ w ∈ Finset.range 13, cost T w (xs (w + 1)) := by
  apply LengthFrame.shifted_sum
  intro u hu
  have hx := hV (u + 1) (by omega)
  rw [Wf_succ hu] at hx
  exact LengthFrame.cost_lower hT hu hx

end
end OptimalOTS.HLFour
