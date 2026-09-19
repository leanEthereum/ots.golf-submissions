import Submissions.LowerGenerality1.Conversion
import Submissions.LowerGenerality1.Patterns
import Submissions.LowerGenerality1.PatternSearch
import Submissions.LowerGenerality1.CostCore
import Submissions.LowerGenerality1.PatternHelpers
import Submissions.LowerGenerality1.WeakSecurity

/-! A forgery attack using equal reconstruction patterns. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.PatternAttack

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (S : Scheme)

def targets (i : Fin numCuts) : Finset ℕ := (S.samePattern i).image Fin.val

def fallback (m : Message) : Message × Signature :=
  (m, 0, List.replicate ((maxSignatureBits - nonceBits) + 1) false)

def fromResult (i : Fin numCuts) (xa xr : S.graph.Assignment) (m : Message) :
    Option (Nonce × ℕ) → Message × Signature
  | none => fallback m
  | some (η, n) =>
      if hn : n < numCuts then
        (m, η, Conversion.convert S i ⟨n, hn⟩ xa xr)
      else fallback m

def forgeFrom (T : ℕ) (i : Fin numCuts) (xa xr : S.graph.Assignment)
    (m₁ : Message) : OracleComp Spec (Message × Signature) := do
  let m₂ ← sampleBits msgBits
  if m₂ = m₁ then pure (fallback m₁) else
    fromResult S i xa xr m₂ <$> PatternSearch.search (targets S i) m₂ T 0

def forge (T : ℕ) (m₁ : Message) :
    Option Signature → OracleComp Spec (Message × Signature)
  | none => pure (fallback m₁)
  | some (η₁, pl) => do
      let n ← index m₁ η₁
      if hn : n < numCuts then
        let i : Fin numCuts := ⟨n, hn⟩
        let xa := S.graph.decode (S.sets i) pl
        let xr ← S.graph.reconstruct (S.sets i) xa
        forgeFrom S T i xa xr m₁
      else pure (fallback m₁)

def adversary (T : ℕ) : Adversary where
  State := Message
  choose _ := (fun m => (m,m)) <$> sampleBits msgBits
  forge := forge S T

/-- The final weak-security check after a signature was returned. -/
def check (pk : PublicKey) (m₁ : Message) (out : Message × Signature) :
    OracleComp Spec Bool := do
  let ok ← S.verify pk out.1 out.2
  return ok && decide (out.1 ≠ m₁)

def win (p : Bool × Cache) : ℝ≥0∞ := if p.1 = true then 1 else 0

theorem mem_targets (i : Fin numCuts) (n : ℕ) (hn : n ∈ targets S i) :
    ∃ j : Fin numCuts, j.val = n ∧ S.graph.evalHash (S.sets j) = S.graph.evalHash (S.sets i) := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
  refine ⟨j,rfl, (S.hashPattern_eq_iff j i).mp ?_⟩
  exact (Finset.mem_filter.mp hj).2

theorem card_targets (i : Fin numCuts) : (targets S i).card = (S.samePattern i).card :=
  Finset.card_image_of_injective _ Fin.val_injective

/-- A successful target search supplies a cache entry and an equal reconstruction pattern. -/
theorem check_fromResult (i : Fin numCuts) (x : S.graph.Assignment)
    (m₁ m₂ : Message) (hne : m₂ ≠ m₁) (c : Cache)
    (hc : S.graph.CacheConsistent x c) (η : Nonce) (n : ℕ) (hn : n ∈ targets S i)
    (w : BitVec hashBits) (hw : c ⟨msgBits + nonceBits,m₂ ++ η⟩ = some w)
    (hidx : (w.setWidth idxBits).toNat = n) :
    run (check S (S.publicKey x) m₁ (fromResult S i
      (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x))
      (Conversion.observed S i x) m₂ (some (η,n)))) c = pure (true,c) := by
  obtain ⟨j,rfl,hj⟩ := mem_targets S i n hn
  simp only [fromResult, dif_pos j.isLt, Fin.eta, check]
  rw [run_bind, Conversion.run_verify_convert_cached S i j x m₂ η c hc
    (by rw [Conversion.evalHashAt, Conversion.evalHashAt, hj]) w hw hidx, pure_bind, run_pure]
  have he : decide (m₂ ≠ m₁) = true := decide_eq_true hne
  rw [he]
  rfl

/-! Query costs. -/

theorem cost_forgeFrom (T : ℕ) (i : Fin numCuts) (xa xr : S.graph.Assignment)
    (m₁ : Message) (hidx : blockCost (msgBits + nonceBits) = 1) :
    CostAtMost (forgeFrom S T i xa xr m₁) T := by
  unfold forgeFrom
  refine (costAtMost_liftM_probComp _ 0).bind_le (b₂ := T) (fun m₂ => ?_) (by simp)
  split_ifs
  · exact costAtMost_pure _ _
  · exact (PatternSearch.cost_search hidx (targets S i) m₂ T 0).map _

theorem cost_forge (T : ℕ) (hidx : blockCost (msgBits + nonceBits) = 1)
    {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) (m₁ : Message) :
    ∀ σ, CostAtMost (forge S T m₁ σ) (1 + v + T)
  | none => costAtMost_pure _ _
  | some (η, pl) => by
    unfold forge
    refine (costAtMost_index hidx _ _).bind_le (b₂ := v + T) (fun n => ?_) (by omega)
    split_ifs with hn
    · refine ((S.graph.costAtMost_reconstruct _ _).mono (hv ⟨n,hn⟩)).bind
        (fun xr => cost_forgeFrom S T ⟨n,hn⟩ _ xr m₁ hidx)
    · exact costAtMost_pure _ _

theorem cost_experiment (T v : ℕ)
    (hidx : blockCost (msgBits + nonceBits) = 1)
    (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    CostAtMost (weakExperiment S (adversary S T))
      (keygenBudget + trials + T + 2*v + 2) := by
  unfold weakExperiment
  refine S.costAtMost_keygen.bind_le
    (b₂ := trials + (1+v+T) + (1+v)) (fun kg => ?_) (by omega)
  refine ((costAtMost_liftM_probComp _ 0).map _).bind_le
    (b₂ := trials + (1+v+T) + (1+v)) (fun st => ?_) (by simp)
  refine (S.costAtMost_sign hidx kg.2 st.1).bind_le
    (b₂ := (1+v+T) + (1+v)) (fun σ => ?_) (by omega)
  refine (cost_forge S T hidx hv st.2 σ).bind (fun out => ?_)
  exact (S.costAtMost_verify hidx hv kg.1 out.1 out.2).bind_le
    (fun _ => costAtMost_pure _ 0) (by simp)

/-! Success after receiving an honest signature in a large pattern class. -/

theorem search_check_ge (T : ℕ) (i : Fin numCuts) (x : S.graph.Assignment)
    (m₁ m₂ : Message) (hne : m₂ ≠ m₁) (c : Cache)
    (hc : S.graph.CacheConsistent x c) :
    E (run (PatternSearch.search (targets S i) m₂ T 0) c)
      (fun p => if p.1.isSome then 1 else 0) ≤
    E (run (PatternSearch.search (targets S i) m₂ T 0) c) (fun p =>
      E (run (check S (S.publicKey x) m₁ (fromResult S i
        (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x))
        (Conversion.observed S i x) m₂ p.1)) p.2) win) := by
  apply expectedValue_mono_of_support
  intro p hp
  rcases he : p.1 with _ | ⟨η,n⟩
  · simp [he]
  · obtain ⟨hn,w,hw,hidx⟩ := PatternSearch.search_support (targets S i) m₂ T 0 c p hp η n he
    have hc' := Graph.CacheConsistent.mono S.graph
      (sub_of_mem_support_run _ c p hp) hc
    rw [check_fromResult S i x m₁ m₂ hne p.2 hc' η n hn w hw hidx, E_pure]
    simp [win]

end OptimalOTS.PatternAttack
