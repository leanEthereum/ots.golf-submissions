import Submissions.UpperLeanIsa.BasicProperties

/-! Research support for omitting a finite nonce flag from the signature.

The verifier tries the possible flags and returns the first accepting witness.
This file proves its cost, determinism, fixed-oracle semantics, and the freshness
implication needed by a reduction. It does not prove security of a new scheme
or alter the certified 1124-cycle submission. -/

open OracleSpec OracleComp

namespace OptimalOTS.LeanIsaBaseline.Layer.ImplicitNonce

variable {Flag : Type}

/-- Search the finite flag space, keeping a witness for the security reduction. -/
def recover (test : Flag → OracleComp Spec Bool) : List Flag → OracleComp Spec (Option Flag)
  | [] => pure none
  | flag :: flags => do
      if ← test flag then pure (some flag) else recover test flags

/-- The corresponding search under a fixed oracle. -/
def recoverValue (test : Flag → Bool) : List Flag → Option Flag
  | [] => none
  | flag :: flags => if test flag then some flag else recoverValue test flags

theorem recover_cost (test : Flag → OracleComp Spec Bool) (V : ℕ)
    (h : ∀ flag, CostAtMost (test flag) V) (flags : List Flag) :
    CostAtMost (recover test flags) (flags.length * V) := by
  induction flags with
  | nil => exact cost_pure _ _
  | cons flag flags ih =>
    have hb := cost_bind (h flag) (fun ok =>
      cost_ite (ok = true) (a := pure (some flag)) (c := recover test flags)
        (fun _ => cost_pure (some flag) (flags.length * V)) (fun _ => ih))
    simpa only [recover, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using hb

theorem recover_deterministic (test : Flag → OracleComp Spec Bool)
    (h : ∀ flag, Deterministic (test flag)) (flags : List Flag) :
    Deterministic (recover test flags) := by
  induction flags with
  | nil => exact Params.deterministic_pure _
  | cons flag flags ih =>
    exact Params.deterministic_bind (h flag) (fun ok =>
      Params.deterministic_ite (ok = true)
        (fun _ => Params.deterministic_pure _) (fun _ => ih))

theorem fixed_recover (f : HashTable) (test : Flag → OracleComp Spec Bool)
    (value : Flag → Bool)
    (h : ∀ flag, simulateQ (unifFwdAnswerImpl f) (test flag) = pure (value flag))
    (flags : List Flag) :
    simulateQ (unifFwdAnswerImpl f) (recover test flags) = pure (recoverValue value flags) := by
  induction flags with
  | nil => simp [recover, recoverValue]
  | cons flag flags ih =>
    simp only [recover, simulateQ_bind, h, pure_bind, recoverValue]
    split <;> simp_all

theorem recoverValue_some {test : Flag → Bool} {flags : List Flag} {flag : Flag}
    (h : recoverValue test flags = some flag) : flag ∈ flags ∧ test flag = true := by
  induction flags with
  | nil => simp [recoverValue] at h
  | cons a flags ih =>
    by_cases ha : test a = true
    · rw [recoverValue, if_pos ha] at h
      cases Option.some.inj h
      exact ⟨List.mem_cons_self, ha⟩
    · rw [recoverValue, if_neg ha] at h
      obtain ⟨hm, ht⟩ := ih h
      exact ⟨List.mem_cons_of_mem a hm, ht⟩

/-- Any accepting explicit flag yields acceptance after omission. -/
theorem recoverValue_isSome (test : Flag → Bool) (flags : List Flag) :
    (recoverValue test flags).isSome = true ↔ ∃ flag ∈ flags, test flag = true := by
  induction flags with
  | nil => simp [recoverValue]
  | cons flag flags ih =>
    by_cases h : test flag = true
    · simp [recoverValue, h]
    · simp [recoverValue, h, ih]

/-- A new compressed message-signature pair lifts to a new explicit pair.
No injectivity assumption on the forgetting map is required. -/
theorem fresh_of_forget_fresh {Explicit Compact : Type} (forget : Explicit → Compact)
    {signed : Option Explicit} {candidate : Explicit}
    (h : signed.map forget ≠ some (forget candidate)) : signed ≠ some candidate := by
  intro he
  apply h
  rw [he]
  rfl

/-- An additional verification can be paid from a strictly larger fixed prefix.
This is arithmetic for a future reduction, not that reduction itself. -/
theorem overhead_absorbed {B K V : ℕ} {epsilon rate : ℚ}
    (hKV : V < K) (hKB : K ≤ B) (hr : 0 < rate) (he : epsilon < rate) :
    epsilon + rate * (B + V - K : ℕ) < rate * B := by
  have hrest : B + V - K + 1 ≤ B := by omega
  have hcast : ((B + V - K : ℕ) : ℚ) + 1 ≤ (B : ℚ) := by exact_mod_cast hrest
  have hm := mul_le_mul_of_nonneg_left hcast hr.le
  nlinarith

/-- Packed free-chain variants include one index hash in each block. -/
def freeVariantSlots (flags : ℕ) : ℕ :=
  flags * ((List.range 64).map (fun digit => digit + 6)).sum

theorem freeVariantSlots_eq (flags : ℕ) : freeVariantSlots flags = flags * 2400 := by
  have h : ((List.range 64).map (fun digit => digit + 6)).sum = 2400 := by decide
  simp [freeVariantSlots, h]

end OptimalOTS.LeanIsaBaseline.Layer.ImplicitNonce
