import Submissions.LowerGenerality3.Attack0

/-!
# Attacker R: reuse the query of an honest signature

The attacker draws a uniform message `m`, asks for its signature `σ`, reads the query `q` of the
verification of `(m, σ)` from its shape, asks the oracle for `q` (answered from the cache), and
forges on any other message that has a candidate querying `q` and accepting that answer. On the
event `GR` (the honest verification reads a cached point whose answer is useful for a second
message) it succeeds.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits securityBits maxSignatureBits keygenBudget signBudget

variable (S : OracleAlgorithm.Scheme) (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic)

/-- Some other message has a candidate querying `q` and accepting `y`. -/
def HasSecond (pk : PublicKey) (m : Message) (q : Query) (y : BitVec hashBits) : Prop :=
  ∃ m' σ', m' ≠ m ∧ ∃ f', shape S hv hd pk m' σ' = .one q f' ∧ f' y = true

/-- A second message with a candidate at `(q, y)`, if any. -/
def selR (pk : PublicKey) (m : Message) (q : Query) (y : BitVec hashBits) :
    Message × OracleAlgorithm.Signature :=
  if h : HasSecond S hv hd pk m q y then (h.choose, h.choose_spec.choose) else (m + 1, [])

theorem selR_spec {pk : PublicKey} {m : Message} {q : Query} {y : BitVec hashBits}
    (h : HasSecond S hv hd pk m q y) :
    (selR S hv hd pk m q y).1 ≠ m ∧ ∃ f', shape S hv hd pk (selR S hv hd pk m q y).1
      (selR S hv hd pk m q y).2 = .one q f' ∧ f' y = true := by
  simp only [selR, dif_pos h]
  exact h.choose_spec.choose_spec

/-- The forging stage. -/
def forgeR (pk : PublicKey) (m : Message) :
    Option OracleAlgorithm.Signature → OracleComp Spec (Message × OracleAlgorithm.Signature)
  | none => pure (m + 1, [])
  | some σ =>
    match shape S hv hd pk m σ with
    | .one q _ => (liftM (Spec.query (.inr q)) : OracleComp Spec (BitVec hashBits)) >>= fun y =>
        pure (selR S hv hd pk m q y)
    | .const _ => pure (m + 1, [])

def advR : OracleAlgorithm.Adversary where
  State := PublicKey × Message
  choose pk := do let m ← uniformMsg; pure (m, (pk, m))
  forge st σ := forgeR S hv hd st.1 st.2 σ

theorem experimentR_eq :
    S.weakExperiment (advR S hv hd) = (do
      let k ← S.keygen
      let m ← uniformMsg
      let σ₁ ← S.sign k.2 m
      let r ← forgeR S hv hd k.1 m σ₁
      let ok ← S.verify k.1 r.1 r.2
      pure (ok && (σ₁.isNone || decide (r.1 ≠ m)))) := by
  unfold OracleAlgorithm.Scheme.weakExperiment advR
  simp only [bind_assoc, pure_bind]

theorem cost_forgeR (pk : PublicKey) (m : Message) (σ : Option OracleAlgorithm.Signature) :
    CostAtMost (forgeR S hv hd pk m σ) 1 := by
  cases σ with
  | none => exact Costs.CostAtMost.mono (by trivial) (Nat.zero_le 1)
  | some σ =>
    simp only [forgeR]
    rcases hs : shape S hv hd pk m σ with b | ⟨q, f⟩
    · dsimp only
      exact Costs.CostAtMost.mono (by trivial) (Nat.zero_le 1)
    · dsimp only
      have hq := shape_short S hv hd pk m σ q f hs
      unfold CostAtMost
      rw [isQueryBound_query_bind_iff]
      refine ⟨?_, fun _ => ?_⟩
      · change blockCost q.1 ≤ 1
        unfold blockCost blockBits
        omega
      · trivial

theorem costR {K T : ℕ} (hk : S.KeygenCostAtMost K) (hs : S.SignCostAtMost T) :
    CostAtMost (S.weakExperiment (advR S hv hd)) (K + T + 2) := by
  rw [experimentR_eq]
  refine Costs.CostAtMost.bind_le hk (b₂ := T + 2) (fun k => ?_) le_rfl
  refine Costs.CostAtMost.bind_le cost_uniformMsg (b₂ := T + 2) (fun m => ?_) (by omega)
  refine Costs.CostAtMost.bind_le (hs k.2 m) (b₂ := 2) (fun σ => ?_) le_rfl
  refine Costs.CostAtMost.bind_le (cost_forgeR S hv hd k.1 m σ) (b₂ := 1) (fun r => ?_) le_rfl
  exact Costs.CostAtMost.bind_le (hv _ _ _) (b₂ := 0) (fun _ => by trivial) le_rfl

/-- The honest verification reads a cached point whose answer is useful for another message. -/
def GR (pk : PublicKey) (m : Message) (s : Option OracleAlgorithm.Signature × Cache) : Prop :=
  match s.1 with
  | none => False
  | some σ => ∃ q f y, shape S hv hd pk m σ = .one q f ∧ s.2 q = some y ∧ f y = true ∧
      Shared S hv hd pk q y

/-- On `GR`, the forgery is accepted with probability one. -/
theorem winR_of_GR {pk : PublicKey} {m : Message} {s : Option OracleAlgorithm.Signature × Cache}
    (h : GR S hv hd pk m s) :
    win (forgeR S hv hd pk m s.1 >>= fun r => S.verify pk r.1 r.2 >>= fun ok =>
      pure (ok && (s.1.isNone || decide (r.1 ≠ m)))) s.2 = 1 := by
  rcases s with ⟨σ?, c⟩
  cases σ? with
  | none => exact absurd h id
  | some σ =>
    obtain ⟨q, f, y, hs, hc, hf, m', m'', hne, ⟨σ', f', hs', hf'⟩, ⟨σ'', f'', hs'', hf''⟩⟩ := h
    have hex : HasSecond S hv hd pk m q y := by
      by_cases hm : m' = m
      · subst hm
        exact ⟨m'', σ'', Ne.symm hne, f'', hs'', hf''⟩
      · exact ⟨m', σ', hm, f', hs', hf'⟩
    obtain ⟨hr, fr, hsr, hfr⟩ := selR_spec S hv hd hex
    simp only [forgeR, hs]
    rw [win, run_bind, run_query_bind, oracleImpl_run_inr_some hc]
    simp only [pure_bind, run_pure]
    show win _ c = 1
    have hdec : decide ((selR S hv hd pk m q y).1 ≠ m) = true := decide_eq_true hr
    simp only [hdec, Option.isNone_some, Bool.false_or, Bool.and_true, bind_pure]
    rw [verify_eq_shape S hv hd, hsr, win_one_some hc, if_pos hfr]

/-- The success of attacker R is at least the mass of `GR`. -/
theorem successR :
    E (run S.keygen ∅) (fun k => E ($ᵗ BitVec msgBits) (fun m =>
      E (run (S.sign k.1.2 m) k.2) (fun s => if GR S hv hd k.1.1 m s then 1 else 0))) ≤
      probTrue (S.weakExperiment (advR S hv hd)) := by
  rw [experimentR_eq, probTrue_eq_win, win_bind]
  apply E_mono
  intro k
  rw [win_bind, run_uniformMsg, E_map]
  apply E_mono
  intro m
  rw [win_bind]
  apply E_mono
  intro s
  by_cases hg : GR S hv hd k.1.1 m s
  · rw [if_pos hg]
    exact (winR_of_GR S hv hd hg).ge
  · rw [if_neg hg]
    exact zero_le

end OptimalOTS.LowerGenerality3
