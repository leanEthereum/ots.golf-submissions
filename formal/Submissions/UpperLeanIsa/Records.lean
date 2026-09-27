import Submissions.UpperLeanIsa.LayerWire
import Submissions.UpperLeanIsa.Cache
import Submissions.UpperLeanIsa.TierCodec

/-!
# Records of a layer scheme and their oracle points

A *record* is the randomness of key generation laid out by location: the 42 seeds and the full
256-bit answer at every keygen query. Chain step `(k, j)` (`j + 1 < len k`) and root call `r < 9`
are the locations. Distinct locations have distinct inputs in every pair of records
(`location_eq_of_input_eq`), because the three tag cells and the metadata separate them
syntactically (`Params.Hyp`); no probabilistic collision exception is needed.

`Params.Hyp` collects the facts about the parameters used by the security proof, including a
tier schedule of the codec (`tier`) whose numeric conditions hold.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Params

variable (P : Params)

/-- The standing hypotheses of the security proof. -/
structure Hyp : Prop where
  len_pos : ∀ k, 1 ≤ P.len k
  digit_lt : ∀ I k, P.digit I k < P.len k
  layer_pos : 1 ≤ P.layer
  tag_inj : ∀ (k k' : Fin numChains) (j j' : ℕ), j + 1 < P.len k → j' + 1 < P.len k' →
    P.tag k j 0 = P.tag k' j' 0 → P.tag k j 1 = P.tag k' j' 1 → P.tag k j 2 = P.tag k' j' 2 →
    k = k' ∧ j = j'
  chain_idx : P.cv ≠ P.idxCv
  tier : ∃ S : Tier.Sched, S.Valid ∧ P.TierHyp S

end Params

/-! ## Injectivity of the query layouts -/

theorem append_inj {a b : ℕ} {x x' : BitVec a} {y y' : BitVec b}
    (h : x ++ y = x' ++ y') : x = x' ∧ y = y' := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun z : BitVec (a + b) => z.extractLsb' b a) h
  · simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (a + b) => z.extractLsb' 0 b) h

theorem query_inj {a b : BitVec 896} (h : (⟨896, a⟩ : Query) = ⟨896, b⟩) : a = b :=
  eq_of_heq (Sigma.mk.inj_iff.mp h).2

namespace Params

variable {P : Params}

theorem chainInput_eq_iff (hP : P.Hyp) {k k' : Fin numChains} {j j' : ℕ}
    (hj : j + 1 < P.len k) (hj' : j' + 1 < P.len k') (x y : Word) :
    P.chainInput k j x = P.chainInput k' j' y ↔ k = k' ∧ j = j' ∧ x = y := by
  constructor
  · intro h
    have hb := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.1
    obtain ⟨h1, hx⟩ := append_inj hb
    obtain ⟨h2, h0⟩ := append_inj h1
    obtain ⟨h3, h1'⟩ := append_inj h2
    obtain ⟨hk, hjj⟩ := hP.tag_inj k k' j j' hj hj' h0 h1' h3
    exact ⟨hk, hjj, hx⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem chainInput_same_iff (k : Fin numChains) (j : ℕ) (x y : Word) :
    P.chainInput k j x = P.chainInput k j y ↔ x = y := by
  constructor
  · intro h
    have hb := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.1
    exact (append_inj hb).2
  · rintro rfl
    rfl

theorem chainInput_ne_idxInput (hP : P.Hyp) (k : Fin numChains) (j : ℕ) (x : Word)
    (m : Message) (η : Nonce) (pk : PublicKey) : P.chainInput k j x ≠ P.idxInput m η pk := by
  intro h
  exact hP.chain_idx ((hashInput_eq_iff _ _ _ _ _ _).mp h).1

end Params

end OptimalOTS.LeanIsaBaseline.Layer
