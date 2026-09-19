import Submissions.UpperRiscv.Scheme
import Submissions.UpperRiscv.Resample
import Submissions.UpperRiscv.Events
import Submissions.UpperRiscv.EncCharges
import Submissions.UpperRiscv.RowPotential
import Submissions.UpperRiscv.Keygen
import Submissions.UpperRiscv.Reconstruct

/-!
# The experiment in stages, and the potentials

The experiment of `forestScheme` against an adversary `A` is `keygen >>= rest A`, where `rest`
runs the attacker's first stage, signing (`sign_eq`: the signing loop `signIdx` followed by
encoding), the attacker's second stage and verification (`stB`).

The potentials of the security proof (see `DESIGN.md`): `ΦA` for the first stage (hidden keygen
points, `Spr`, and the encoding counts of the signing analysis), `ΦB` for the second stage; each
grows on average by at most `κ = 2 ε` per compression (`ΦA_charge`, `ΦB_charge_some`,
`ΦB_charge_none`) under the invariant `Inv` (encoding entries plus remaining budget at most
`2 ^ 127`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

attribute [local irreducible] validSet numValid


variable (A : Adversary)

/-! ## The experiment in stages -/

/-- The second stage of the attacker, followed by verification and the final check. -/
def stB (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option Signature) :
    OracleComp Spec Bool := do
  let (m₂, σ₂) ← A.forge st σ
  let ok ← forestScheme.verify pk m₂ σ₂
  return ok && decide (σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Signing and the second stage. -/
def rest₂ (pk : PublicKey) (sk : graph.Assignment) (y : Message × A.State) :
    OracleComp Spec Bool :=
  forestScheme.sign sk y.1 >>= stB A pk y.1 y.2

/-- Everything after key generation. -/
def rest (x : PublicKey × graph.Assignment) : OracleComp Spec Bool :=
  A.choose x.1 >>= rest₂ A x.1 x.2

theorem experiment_eq : GScheme.experiment forestScheme A = forestScheme.keygen >>= rest A := by
  unfold GScheme.experiment rest rest₂ stB
  congr 1

/-- The indicator of success. -/
def g (p : Bool × Cache) : ℝ≥0∞ := if p.1 = true then 1 else 0

theorem g_le_one (p : Bool × Cache) : g p ≤ 1 := by
  unfold g; split_ifs <;> simp

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- `probTrue` as an expectation over the lazy-oracle run from the empty cache. -/
theorem probTrue_eq_E_run (oa : OracleComp Spec Bool) :
    probTrue oa = E (run oa ∅) (fun p => if p.1 = true then 1 else 0) := by
  unfold probTrue
  rw [run'_eq, probOutput_map_eq_tsum_ite, E, expectedValue_def]
  refine tsum_congr fun x => ?_
  rcases x with ⟨b, c⟩
  cases b <;> simp

attribute [local semireducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem probTrue_eq : probTrue (GScheme.experiment forestScheme A) = E (run (GScheme.experiment forestScheme A) ∅) g := by
  generalize GScheme.experiment forestScheme A = oa
  rw [probTrue_eq_E_run]
  rfl

/-- The signature of the record `ξ` for the outcome `r` of the signing loop. -/
def sigOf (ξ : Rec) (r : Option (Nonce × Idx)) : Option Signature :=
  r.map fun r => (r.1, graph.encode (forestScheme.sets r.2) (graph.evalRec ξ))

/-- The disclosure set of the outcome of the signing loop. -/
def cutOf? (r : Option (Nonce × Idx)) : Option (Finset Name) :=
  r.map fun r => setsName r.2

/-- The index of the outcome of the signing loop. -/
def idxOf? (r : Option (Nonce × Idx)) : Option ℕ := r.map fun r => r.2.val

theorem trunc_cast_pot {n m : ℕ} (h : n = m) (x : BitVec n) : trunc (x.cast h) = trunc x := by
  subst h; rfl

theorem publicKey_eq_pkOf (ξ : Rec) : forestScheme.publicKey (graph.evalRec ξ) = pkOf ξ := by
  show trunc (graph.evalRec ξ rh.fin) = trunc (ξ.2 rh.fin)
  rw [← val_rh]
  unfold val
  exact (trunc_cast_pot _ _).symm

theorem sign_eq (ξ : Rec) (m : Message) :
    forestScheme.sign (graph.evalRec ξ) m = sigOf ξ <$> signIdx m :=
  sign_eq_map forestScheme (graph.evalRec ξ) m

/-! ## Potentials -/

/-- The charge per compression. -/
def κ : ℝ≥0∞ := 2 * ε

/-- The weight of a set of records. -/
def sumW (T : Finset Rec) : ℝ≥0∞ := ∑ ξ ∈ T, w

/-- An indicator. -/
def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

/-- The invariant: encoding entries plus remaining budget never exceed `2 ^ 127`. -/
def Inv (c : Cache) (b : ℕ) : Prop := encCount c + b ≤ 2 ^ 127

/-- The encoding part of the first-stage potential: `θ psi`, the row potential of
`RowPotential`. -/
def encTerm (c : Cache) : ℝ≥0∞ :=
  ENNReal.ofReal (Row.θ * psi c)

/-- The first-stage potential for the public key `pk`. -/
def ΦA (pk : BitVec 128) (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiberA pk, w * (ind (Cache.Hits c (kc ξ)) + ind (Spr c ξ)) + sumW (fiberA pk) * encTerm c

/-- The second-stage potential over the records `T`, with hidden points `fHid A?` and the index
`i?` of the signature. -/
def ΦB (T : Finset Rec) (A? : Option (Finset Name)) (d' : Cache) (i? : Option ℕ) (c : Cache) :
    ℝ≥0∞ :=
  ∑ ξ ∈ T, w * (ind (Cache.Hits c (fHid A? ξ)) + ind (Spr c ξ) +
    ind (∃ i, i? = some i ∧ IdxPost d' c i))

/-! ### Auxiliary facts -/

theorem one_le_queryCost (q : Query) : 1 ≤ queryCost (.inr q) := by
  show 1 ≤ blockCost q.1
  exact Nat.le_max_left _ _

theorem one_le_queryCost_ennreal (q : Query) : (1 : ℝ≥0∞) ≤ queryCost (.inr q) := by
  exact_mod_cast one_le_queryCost q

theorem Inv_fresh : ∀ (c : Cache) (b : ℕ) (q : Query), Inv c b → c q = none →
    queryCost (.inr q) ≤ b → ∀ u, Inv (c.cacheQuery q u) (b - queryCost (.inr q)) := by
  intro c b q hI _ _ u
  unfold Inv at *
  have h1 := encCount_cacheQuery_le c q u
  have h2 := one_le_queryCost q
  omega

theorem Inv_cached : ∀ (c : Cache) (b : ℕ) (q : Query), Inv c b → (c q).isSome →
    queryCost (.inr q) ≤ b → Inv c (b - queryCost (.inr q)) := by
  intro c b q hI _ _
  unfold Inv at *
  have := Nat.sub_le b (queryCost (.inr q))
  omega

theorem encCount_le_of_inv {c : Cache} {b : ℕ} (h : Inv c b) :
    encCount c ≤ 2 ^ 127 :=
  le_trans (Nat.le_add_right _ _) h

/-- The paper parameters satisfy the hypotheses of the row potential. -/
theorem paperRowHyp : RowHyp where
  nonce_eq := rfl
  idx_le := by decide
  two_le := le_trans (by norm_num) numValid_ge
  numCuts_le := by
    rw [numValid, card_validSet, comp_32_target]
    show 2 * 44383521204130784290044027201113527 ≤ 2 ^ 128
    norm_num
  trial_le := by show 24 * 2 ^ 20 ≤ 2 ^ 128; norm_num

theorem two_encCount_le {c : Cache} {b : ℕ} (h : Inv c b) :
    2 * encCount c ≤ 2 ^ idxBits := by
  have := encCount_le_of_inv h
  show 2 * encCount c ≤ 2 ^ 128
  omega

theorem ΦA_empty (pk : BitVec 128) : ΦA pk ∅ = 0 := by
  unfold ΦA encTerm
  simp [psi_empty, ind, Cache.not_hits_empty, not_spr_empty]

/-! ### Indicators and averages -/

theorem κ_eq_add : κ = ε + ε := by
  unfold κ; ring

theorem κ_mul_eq (X : ℝ≥0∞) : κ * X = ε * X + ε * X := by
  unfold κ; ring

theorem ε_le_κ : ε ≤ κ := by
  rw [κ_eq_add]; exact le_self_add

theorem sumW_mono {T T' : Finset Rec} (h : T ⊆ T') : sumW T ≤ sumW T' :=
  Finset.sum_le_sum_of_subset h

theorem ind_congr {p r : Prop} (h : p ↔ r) : ind p = ind r := by
  unfold ind; simp only [h]

theorem ind_or_le (p r : Prop) : ind (p ∨ r) ≤ ind p + ind r := by
  unfold ind
  by_cases hp : p <;> by_cases hr : r <;> simp [hp, hr]

theorem ind_exists_some (i : ℕ) (P : ℕ → Prop) :
    ind (∃ i', some i = some i' ∧ P i') = ind (P i) := by
  apply ind_congr; simp

theorem ind_exists_none (P : ℕ → Prop) :
    ind (∃ i', (none : Option ℕ) = some i' ∧ P i') = 0 := by
  simp [ind]

theorem w_mul_ind_le (p : Prop) [Decidable p] : w * ind p ≤ if p then w else 0 := by
  unfold ind; split_ifs <;> simp

/-- Averaging over a fresh answer commutes with a weighted sum over records. -/
theorem avg_sum_comm (T : Finset Rec) (f : Rec → BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ∑ ξ ∈ T, w * f ξ u =
      ∑ ξ ∈ T, w * ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f ξ u := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun u _ => ?_
  ring

theorem avg_const (X : ℝ≥0∞) :
    ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * X = X :=
  sum_inv_card_mul X

/-- Summing a per-record charge of `ε` with the weights `w`. -/
theorem sum_w_mul_le_add (T : Finset Rec) (a b : Rec → ℝ≥0∞) (h : ∀ ξ ∈ T, a ξ ≤ b ξ + ε) :
    ∑ ξ ∈ T, w * a ξ ≤ ∑ ξ ∈ T, w * b ξ + ε * sumW T := by
  unfold sumW
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ hξ => ?_
  rw [mul_comm ε w, ← mul_add]
  exact mul_le_mul_right (h ξ hξ) w

/-- A fresh answer can only create a hit at the queried point. -/
theorem hits_avg_le (T : Finset Rec) (f : Rec → Cache) (c : Cache) (q : Query) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f ξ)) ≤
      ∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)) + ∑ ξ ∈ T, w * ind ((f ξ q).isSome) := by
  rw [avg_sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [← mul_add]
  refine mul_le_mul_right ?_ w
  calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ind (Cache.Hits (c.cacheQuery q u) (f ξ))
      ≤ ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          (ind (Cache.Hits c (f ξ)) + ind ((f ξ q).isSome)) := by
        refine Finset.sum_le_sum fun u _ => mul_le_mul_right ?_ _
        rw [ind_congr (Cache.hits_cacheQuery c (f ξ) q u)]
        exact ind_or_le _ _
    _ = _ := sum_inv_card_mul _

/-- No hit at a point absent from every `f ξ`. -/
theorem hits_avg_eq (T : Finset Rec) (f : Rec → Cache) (c : Cache) (q : Query)
    (hf : ∀ ξ, f ξ q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f ξ)) =
      ∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  simp only [Cache.hits_cacheQuery, hf, Option.isSome_none, Bool.false_eq_true, or_false]

theorem spr_avg_le (T : Finset Rec) (c : Cache) (q : Query) (hq : c q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Spr (c.cacheQuery q u) ξ) ≤
      ∑ ξ ∈ T, w * ind (Spr c ξ) + ε * sumW T := by
  rw [avg_sum_comm]
  exact sum_w_mul_le_add T _ _ fun ξ _ => spr_charge c ξ q hq

theorem spr_avg_eq (T : Finset Rec) (c : Cache) (u₀ : EncInput) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Spr (c.cacheQuery (encQuery u₀) u) ξ) =
      ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Spr c ξ))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  exact spr_cacheQuery_enc c ξ u₀ u

theorem idxPost_avg_le (T : Finset Rec) (d' c : Cache) (u₀ : EncInput)
    (hq : c (encQuery u₀) = none) (i : ℕ) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ _ξ ∈ T, w * ind (IdxPost d' (c.cacheQuery (encQuery u₀) u) i) ≤
      ∑ _ξ ∈ T, w * ind (IdxPost d' c i) + ε * sumW T := by
  rw [avg_sum_comm]
  exact sum_w_mul_le_add T _ _ fun _ _ => idxPost_charge (by decide) d' c u₀ hq i

theorem idxPost_avg_eq (T : Finset Rec) (d' c : Cache) {q : Query}
    (hq : ∀ u : EncInput, q ≠ encQuery u) (i : ℕ) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ _ξ ∈ T, w * ind (IdxPost d' (c.cacheQuery q u) i) =
      ∑ _ξ ∈ T, w * ind (IdxPost d' c i) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (IdxPost d' c i))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  exact idxPost_cacheQuery_of_ne_enc d' c hq u i

theorem hits_charge_A' (pk : BitVec 128) {T : Finset Rec} (hT : T ⊆ fiberA pk) (q : Query) :
    ∑ ξ ∈ T, w * ind ((kc ξ q).isSome) ≤ ε * sumW (fiberA pk) :=
  calc ∑ ξ ∈ T, w * ind ((kc ξ q).isSome)
      ≤ ∑ ξ ∈ T, (if (kc ξ q).isSome then w else 0) :=
        Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ ξ ∈ fiberA pk, (if (kc ξ q).isSome then w else 0) := Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberA pk) := hits_charge_A pk q

theorem hits_charge_B' {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data) {T : Finset Rec}
    (hT : T ⊆ fiberB Ac dt) (q : Query) :
    ∑ ξ ∈ T, w * ind ((fHid (some Ac) ξ q).isSome) ≤ ε * sumW (fiberB Ac dt) :=
  calc ∑ ξ ∈ T, w * ind ((fHid (some Ac) ξ q).isSome)
      ≤ ∑ ξ ∈ T, (if (fHid (some Ac) ξ q).isSome then w else 0) :=
        Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ ξ ∈ fiberB Ac dt, (if (fHid (some Ac) ξ q).isSome then w else 0) :=
        Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberB Ac dt) := hits_charge_B hAc dt q

/-! ### The encoding term -/

theorem encTerm_cacheQuery_of_ne_enc (c : Cache) {q : Query}
    (hq : ∀ u : EncInput, q ≠ encQuery u) (u : BitVec hashBits) :
    encTerm (c.cacheQuery q u) = encTerm c := by
  unfold encTerm
  rw [psi_of_ne hq]

/-- A fresh encoding answer raises the encoding term by at most `κ = 2 ε` on average. -/
theorem encTerm_avg_le (c : Cache) {b : ℕ} (hc : Inv c b)
    (u₀ : EncInput) (hq : c (encQuery u₀) = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        encTerm (c.cacheQuery (encQuery u₀) u) ≤ encTerm c + κ := by
  obtain ⟨m₀, η₀, rfl⟩ := exists_append u₀
  exact psi_charge paperRowHyp (two_encCount_le hc) hq

/-! ### The charge bounds -/

theorem ΦA_eq (pk : BitVec 128) (c : Cache) :
    ΦA pk c = ∑ ξ ∈ fiberA pk, w * ind (Cache.Hits c (kc ξ)) + ∑ ξ ∈ fiberA pk, w * ind (Spr c ξ) +
      sumW (fiberA pk) * encTerm c := by
  unfold ΦA
  simp only [mul_add, Finset.sum_add_distrib]

theorem ΦB_eq (T : Finset Rec) (A? : Option (Finset Name)) (d' : Cache) (i? : Option ℕ)
    (c : Cache) :
    ΦB T A? d' i? c = ∑ ξ ∈ T, w * ind (Cache.Hits c (fHid A? ξ)) + ∑ ξ ∈ T, w * ind (Spr c ξ) +
      ∑ _ξ ∈ T, w * ind (∃ i, i? = some i ∧ IdxPost d' c i) := by
  unfold ΦB
  simp only [mul_add, Finset.sum_add_distrib]

theorem ΦA_charge (pk : BitVec 128) : ∀ (c : Cache) (b : ℕ) (q : Query), Inv c b → c q = none →
    queryCost (.inr q) ≤ b →
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ΦA pk (c.cacheQuery q u) ≤
      ΦA pk c + κ * sumW (fiberA pk) * queryCost (.inr q) := by
  intro c b q hI hq _
  refine le_trans ?_ (add_le_add_right
    (le_mul_of_one_le_right zero_le (one_le_queryCost_ennreal q)) _)
  simp only [ΦA_eq, mul_add, Finset.sum_add_distrib]
  by_cases hk : q.1 = msgBits + nonceBits
  · obtain ⟨u₀, rfl⟩ := exists_eq_encQuery_of_length_eq hk
    rw [hits_avg_eq _ _ _ _ (fun ξ => kc_enc ξ u₀), spr_avg_eq]
    have hE := encTerm_avg_le c hI u₀ hq
    have hsum : ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (sumW (fiberA pk) * encTerm (c.cacheQuery (encQuery u₀) u)) =
        sumW (fiberA pk) * ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          encTerm (c.cacheQuery (encQuery u₀) u) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    refine le_trans (add_le_add_right (hsum.le.trans (mul_le_mul_right hE _)) _) (le_of_eq ?_)
    ring
  · simp only [encTerm_cacheQuery_of_ne_enc c (ne_encQuery_of_length_ne hk), avg_const]
    have h1 := hits_avg_le (fiberA pk) kc c q
    have h2 := hits_charge_A' pk (Finset.Subset.refl _) q
    have h3 := spr_avg_le (fiberA pk) c q hq
    refine le_trans (add_le_add (add_le_add (h1.trans (add_le_add_right h2 _)) h3) le_rfl)
      (le_of_eq ?_)
    rw [κ_mul_eq]; ring

theorem ΦB_charge_some {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data) {T : Finset Rec}
    (hT : T ⊆ fiberB Ac dt) (d' : Cache) (i : ℕ) :
    ∀ (c : Cache) (b : ℕ) (q : Query), Inv c b → c q = none → queryCost (.inr q) ≤ b →
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ΦB T (some Ac) d' (some i) (c.cacheQuery q u) ≤
      ΦB T (some Ac) d' (some i) c + κ * sumW (fiberB Ac dt) * queryCost (.inr q) := by
  intro c b q _ hq _
  refine le_trans ?_ (add_le_add_right
    (le_mul_of_one_le_right zero_le (one_le_queryCost_ennreal q)) _)
  simp only [ΦB_eq, mul_add, Finset.sum_add_distrib, ind_exists_some]
  by_cases hk : q.1 = msgBits + nonceBits
  · obtain ⟨u₀, rfl⟩ := exists_eq_encQuery_of_length_eq hk
    rw [hits_avg_eq _ _ _ _ (fun ξ => fHid_enc (some Ac) ξ u₀), spr_avg_eq]
    have h3 := idxPost_avg_le T d' c u₀ hq i
    refine le_trans (add_le_add_right h3 _) ?_
    rw [← add_assoc]
    exact add_le_add_right (mul_le_mul' ε_le_κ (sumW_mono hT)) _
  · rw [idxPost_avg_eq T d' c (ne_encQuery_of_length_ne hk) i]
    have h1 := hits_avg_le T (fHid (some Ac)) c q
    have h2 := hits_charge_B' hAc dt hT q
    have h3 := spr_avg_le T c q hq
    have h3' := h3.trans (add_le_add_right (mul_le_mul_right (sumW_mono hT) ε) _)
    refine le_trans (add_le_add (add_le_add (h1.trans (add_le_add_right h2 _)) h3') le_rfl)
      (le_of_eq ?_)
    rw [κ_mul_eq]; ring

theorem ΦB_charge_none (pk : BitVec 128) {T : Finset Rec} (hT : T ⊆ fiberA pk) (d' : Cache) :
    ∀ (c : Cache) (b : ℕ) (q : Query), Inv c b → c q = none → queryCost (.inr q) ≤ b →
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ΦB T none d' none (c.cacheQuery q u) ≤
      ΦB T none d' none c + κ * sumW (fiberA pk) * queryCost (.inr q) := by
  intro c b q _ hq _
  refine le_trans ?_ (add_le_add_right
    (le_mul_of_one_le_right zero_le (one_le_queryCost_ennreal q)) _)
  simp only [ΦB_eq, mul_add, Finset.sum_add_distrib, ind_exists_none, mul_zero,
    Finset.sum_const_zero, add_zero, fHid_none]
  by_cases hk : q.1 = msgBits + nonceBits
  · obtain ⟨u₀, rfl⟩ := exists_eq_encQuery_of_length_eq hk
    rw [hits_avg_eq _ _ _ _ (fun ξ => kc_enc ξ u₀), spr_avg_eq]
    exact le_self_add
  · have h1 := hits_avg_le T kc c q
    have h2 := hits_charge_A' pk hT q
    have h3 := spr_avg_le T c q hq
    have h3' := h3.trans (add_le_add_right (mul_le_mul_right (sumW_mono hT) ε) _)
    refine le_trans (add_le_add (h1.trans (add_le_add_right h2 _)) h3') (le_of_eq ?_)
    rw [κ_mul_eq]; ring

end Forest

end OptimalOTS
