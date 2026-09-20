import Submissions.LowerGenerality3.Honest

/-!
# Useful oracle points

`Useful S hv hd pk m q y`: some candidate signature for `m` queries `q` and accepts the answer `y`.
`pm` is its rate over a uniform answer, `promising` the finite set of short queries whose rate is
at least `τ = 2^-25`, and `Good0` the existence of an unconditionally accepted candidate.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 4096

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

variable (S : OracleAlgorithm.Scheme) (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic)

/-- Some candidate for `m` queries `q` and accepts `y`. -/
def Useful (pk : PublicKey) (m : Message) (q : Query) (y : BitVec hashBits) : Prop :=
  ∃ σ f, shape S hv hd pk m σ = .one q f ∧ f y = true

/-- The rate of useful answers at `q` for `m`. -/
def pm (pk : PublicKey) (m : Message) (q : Query) : ℝ≥0∞ :=
  Pr[= true | (fun y => decide (Useful S hv hd pk m q y)) <$> ($ᵗ BitVec hashBits : ProbComp _)]

/-- The threshold of a promising query. -/
def τ : ℝ≥0∞ := 1 / 2 ^ 25

/-- The finite universe of short queries. -/
def shortQueries : Finset Query :=
  (Finset.range 513).sigma fun k => (Finset.univ : Finset (BitVec k))

theorem mem_shortQueries (q : Query) : q ∈ shortQueries ↔ q.1 ≤ 512 := by
  rcases q with ⟨k, u⟩
  simp [shortQueries, Finset.mem_sigma, Nat.lt_succ_iff]

/-- A query is promising for `m` when its useful rate is at least `τ`. -/
def Promising (pk : PublicKey) (m : Message) (q : Query) : Prop := τ ≤ pm S hv hd pk m q

/-- The promising short queries for `m`. -/
def promising (pk : PublicKey) (m : Message) : Finset Query :=
  shortQueries.filter (Promising S hv hd pk m)

theorem Promising_iff {pk : PublicKey} {m : Message} {q : Query} :
    Promising S hv hd pk m q ↔ τ ≤ pm S hv hd pk m q := Iff.rfl

attribute [irreducible] shortQueries promising Promising

/-- Some candidate for `m` is accepted on every oracle path. -/
def Good0 (pk : PublicKey) (m : Message) : Prop := ∃ σ, (shape S hv hd pk m σ).Uncond

/-- `(q, y)` is useful for `m` and for no other message. -/
def Lonely (pk : PublicKey) (m : Message) (q : Query) (y : BitVec hashBits) : Prop :=
  Useful S hv hd pk m q y ∧ ∀ m', Useful S hv hd pk m' q y → m' = m

/-- `(q, y)` is useful for at least two messages. -/
def Shared (pk : PublicKey) (q : Query) (y : BitVec hashBits) : Prop :=
  ∃ m m', m ≠ m' ∧ Useful S hv hd pk m q y ∧ Useful S hv hd pk m' q y

theorem lonely_or_shared {pk : PublicKey} {m : Message} {q : Query} {y : BitVec hashBits}
    (h : Useful S hv hd pk m q y) : Lonely S hv hd pk m q y ∨ Shared S hv hd pk q y := by
  by_cases hl : ∀ m', Useful S hv hd pk m' q y → m' = m
  · exact Or.inl ⟨h, hl⟩
  · push_neg at hl
    obtain ⟨m', hm', hne⟩ := hl
    exact Or.inr ⟨m, m', Ne.symm hne, h, hm'⟩

theorem useful_of_shape {pk : PublicKey} {m : Message} {σ : OracleAlgorithm.Signature}
    {q : Query} {f : BitVec hashBits → Bool} {y : BitVec hashBits}
    (hs : shape S hv hd pk m σ = .one q f) (hy : f y = true) : Useful S hv hd pk m q y :=
  ⟨σ, f, hs, hy⟩

theorem mem_promising {pk : PublicKey} {m : Message} {q : Query} :
    q ∈ promising S hv hd pk m ↔ q.1 ≤ 512 ∧ τ ≤ pm S hv hd pk m q := by
  unfold promising
  rw [Finset.mem_filter, mem_shortQueries, Promising_iff]

/-- The rate of a query outside the promising set is below `τ`. -/
theorem pm_lt_of_not_promising {pk : PublicKey} {m : Message} {q : Query} (hq : q.1 ≤ 512)
    (h : q ∉ promising S hv hd pk m) : pm S hv hd pk m q < τ := by
  by_contra hle
  exact h ((mem_promising S hv hd).mpr ⟨hq, not_lt.mp hle⟩)

end OptimalOTS.LowerGenerality3
