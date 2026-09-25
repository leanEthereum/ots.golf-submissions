import Submissions.UpperLeanIsa.LayerScheme
import Submissions.UpperLeanIsa.TierNumeric

/-!
# The class codec of rarest-cut signing

A *class* is the digit vector of an accepted index. The weight of an index is the number of
accepted indices with its digit vector; the signer keeps the trial of least weight.
`TierHyp P S` ties the scheme to a tier schedule: every accepted weight is a tier weight, and the
accepted indices of weight `S.a t` number `S.N t * S.a t` (`S.N t` classes of `S.a t` indices).

The tier of an index is the position of its weight in the schedule, `S.T` for a rejected index
(`tierI`); the tier of an answer is the tier of its index (`tierW`). The counting lemmas:

* `card_cls`: a class `v` is the class of `cweight v * 2 ^ 129` answers (D1);
* `card_tierW_lt`: the answers of tier `< t` number `(∑ s < t, N s * a s) * 2 ^ 129` (D2);
* `sum_classes`: sums over the classes regroup by tier (D3).
-/

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

/-- A class: a digit vector. -/
abbrev Cls := Fin numChains → ℕ

namespace Params

variable (P : Params)

/-- The scheme's codec agrees with the tier schedule `S`. -/
structure TierHyp (S : Tier.Sched) : Prop where
  K_eq : S.K = 127
  weight_mem : ∀ I : Index, P.Accepted I → ∃ t < S.T, P.weight I = S.a t
  card_weight : ∀ t < S.T,
    (Finset.univ.filter fun I : Index => P.Accepted I ∧ P.weight I = S.a t).card =
      S.N t * S.a t

/-- The weight of a class. -/
def cweight (v : Cls) : ℕ :=
  (Finset.univ.filter fun I : Index => P.Accepted I ∧ P.digit I = v).card

theorem weight_eq (I : Index) : P.weight I = P.cweight (P.digit I) := rfl

/-- The classes: digit vectors of accepted indices. -/
def classes : Finset Cls := (Finset.univ.filter P.Accepted).image P.digit

theorem mem_classes {v : Cls} : v ∈ P.classes ↔ ∃ I, P.Accepted I ∧ P.digit I = v := by
  simp [classes]

theorem digit_mem_classes {I : Index} (h : P.Accepted I) : P.digit I ∈ P.classes :=
  P.mem_classes.2 ⟨I, h, rfl⟩

/-- The class of an answer. -/
def cls (w : BitVec hashBits) : Option Cls :=
  if P.Accepted (indexSlice w) then some (P.digit (indexSlice w)) else none

theorem cls_eq_some {w : BitVec hashBits} {v : Cls} :
    P.cls w = some v ↔ P.Accepted (indexSlice w) ∧ P.digit (indexSlice w) = v := by
  unfold cls
  split_ifs with h <;> simp [h]

theorem cls_mem_classes {w : BitVec hashBits} {v : Cls} (h : P.cls w = some v) :
    v ∈ P.classes := by
  obtain ⟨h1, rfl⟩ := P.cls_eq_some.1 h
  exact P.digit_mem_classes h1

theorem card_cls (v : Cls) :
    (Finset.univ.filter fun w : BitVec hashBits => P.cls w = some v).card =
      P.cweight v * 2 ^ 129 := by
  simp only [cls_eq_some]
  exact card_indexSlice (fun I => P.Accepted I ∧ P.digit I = v)

variable (S : Tier.Sched)

/-- The tier of a class: the position of its weight in the schedule, `S.T` if none. -/
def ctier (v : Cls) : ℕ :=
  if h : ∃ t, t < S.T ∧ P.cweight v = S.a t then Nat.find h else S.T

/-- The tier of an index: `S.T` if rejected. -/
def tierI (I : Index) : ℕ := if P.Accepted I then P.ctier S (P.digit I) else S.T

/-- The tier of an answer. -/
def tierW (w : BitVec hashBits) : ℕ := P.tierI S (indexSlice w)

variable {P S}

theorem ctier_le (v : Cls) : P.ctier S v ≤ S.T := by
  unfold ctier
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem tierI_le (I : Index) : P.tierI S I ≤ S.T := by
  unfold tierI
  split_ifs
  · exact ctier_le _
  · exact le_rfl

theorem a_inj (hS : S.Valid) {s t : ℕ} (hs : s < S.T) (ht : t < S.T) (h : S.a s = S.a t) :
    s = t := by
  rcases lt_trichotomy s t with hst | rfl | hst
  · exact absurd h (hS.a_lt s t hst ht).ne
  · rfl
  · exact absurd h.symm (hS.a_lt t s hst hs).ne

theorem ctier_eq (hS : S.Valid) {v : Cls} {t : ℕ} (ht : t < S.T) (h : P.cweight v = S.a t) :
    P.ctier S v = t := by
  have hex : ∃ t, t < S.T ∧ P.cweight v = S.a t := ⟨t, ht, h⟩
  unfold ctier
  rw [dif_pos hex]
  have hs := Nat.find_spec hex
  exact a_inj hS hs.1 ht (hs.2.symm.trans h)

theorem ctier_spec (hT : P.TierHyp S) {v : Cls} (hv : v ∈ P.classes) :
    P.ctier S v < S.T ∧ P.cweight v = S.a (P.ctier S v) := by
  obtain ⟨I, hI, rfl⟩ := P.mem_classes.1 hv
  obtain ⟨t, ht, hw⟩ := hT.weight_mem I hI
  have hex : ∃ t, t < S.T ∧ P.cweight (P.digit I) = S.a t := ⟨t, ht, hw⟩
  unfold ctier
  rw [dif_pos hex]
  exact Nat.find_spec hex

theorem tierI_spec (hT : P.TierHyp S) {I : Index} (hI : P.Accepted I) :
    P.tierI S I < S.T ∧ P.weight I = S.a (P.tierI S I) := by
  unfold tierI
  rw [if_pos hI]
  exact ctier_spec hT (P.digit_mem_classes hI)

theorem tierI_of_not {I : Index} (hI : ¬ P.Accepted I) : P.tierI S I = S.T := by
  unfold tierI
  rw [if_neg hI]

theorem tierI_lt_T (hT : P.TierHyp S) {I : Index} : P.tierI S I < S.T ↔ P.Accepted I := by
  refine ⟨fun h => ?_, fun h => (tierI_spec hT h).1⟩
  by_contra hI
  rw [tierI_of_not hI] at h
  exact lt_irrefl _ h

/-- Weights and tiers order accepted indices alike. -/
theorem weight_lt_iff (hS : S.Valid) (hT : P.TierHyp S) {I J : Index} (hI : P.Accepted I)
    (hJ : P.Accepted J) : P.weight I < P.weight J ↔ P.tierI S I < P.tierI S J := by
  obtain ⟨hI1, hI2⟩ := tierI_spec hT hI
  obtain ⟨hJ1, hJ2⟩ := tierI_spec hT hJ
  rw [hI2, hJ2]
  constructor
  · intro h
    by_contra h'
    rcases (not_lt.1 h').lt_or_eq with h'' | h''
    · exact absurd h (hS.a_lt _ _ h'' hI1).not_gt
    · rw [h''] at h; exact lt_irrefl _ h
  · intro h
    exact hS.a_lt _ _ h hJ1

theorem tierI_eq_iff (hS : S.Valid) (hT : P.TierHyp S) {I : Index} {t : ℕ} (ht : t < S.T) :
    P.tierI S I = t ↔ P.Accepted I ∧ P.weight I = S.a t := by
  constructor
  · intro h
    have hI : P.Accepted I := (tierI_lt_T hT).1 (h ▸ ht)
    exact ⟨hI, h ▸ (tierI_spec hT hI).2⟩
  · rintro ⟨hI, hw⟩
    unfold tierI
    rw [if_pos hI]
    exact ctier_eq hS ht hw

theorem card_tierI_eq (hS : S.Valid) (hT : P.TierHyp S) {t : ℕ} (ht : t < S.T) :
    (Finset.univ.filter fun I : Index => P.tierI S I = t).card = S.N t * S.a t := by
  simp only [tierI_eq_iff hS hT ht]
  exact hT.card_weight t ht

theorem card_tierI_lt (hS : S.Valid) (hT : P.TierHyp S) {t : ℕ} (ht : t ≤ S.T) :
    (Finset.univ.filter fun I : Index => P.tierI S I < t).card =
      ∑ s ∈ Finset.range t, S.N s * S.a s := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hsplit : (Finset.univ.filter fun I : Index => P.tierI S I < t + 1) =
        (Finset.univ.filter fun I : Index => P.tierI S I < t) ∪
          (Finset.univ.filter fun I : Index => P.tierI S I = t) := by
      ext I
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    rw [hsplit, Finset.card_union_of_disjoint, ih (by omega), card_tierI_eq hS hT (by omega),
      Finset.sum_range_succ]
    rw [Finset.disjoint_filter]
    intro I _ h1 h2
    omega

theorem card_tierW_lt (hS : S.Valid) (hT : P.TierHyp S) {t : ℕ} (ht : t ≤ S.T) :
    (Finset.univ.filter fun w : BitVec hashBits => P.tierW S w < t).card =
      (∑ s ∈ Finset.range t, S.N s * S.a s) * 2 ^ 129 := by
  rw [← card_tierI_lt hS hT ht]
  exact card_indexSlice (fun I => P.tierI S I < t)

theorem cweight_of_mem (hT : P.TierHyp S) {v : Cls} (hv : v ∈ P.classes) :
    P.cweight v = S.a (P.ctier S v) := (ctier_spec hT hv).2

theorem tierI_eq_ctier {I : Index} (hI : P.Accepted I) :
    P.tierI S I = P.ctier S (P.digit I) := by
  unfold tierI; rw [if_pos hI]

theorem card_classes_tier (hS : S.Valid) (hT : P.TierHyp S) {t : ℕ} (ht : t < S.T) :
    (P.classes.filter fun v => P.ctier S v = t).card = S.N t := by
  have hpos := hS.a_pos t ht
  have hsum : (Finset.univ.filter fun I : Index => P.tierI S I = t).card =
      ∑ v ∈ P.classes.filter (fun v => P.ctier S v = t), P.cweight v := by
    have hset : (Finset.univ.filter fun I : Index => P.tierI S I = t) =
        (P.classes.filter fun v => P.ctier S v = t).biUnion
          (fun v => Finset.univ.filter fun I : Index => P.Accepted I ∧ P.digit I = v) := by
      ext I
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro h
        have hI : P.Accepted I := (tierI_lt_T hT).1 (h ▸ ht)
        exact ⟨P.digit I, ⟨P.digit_mem_classes hI, (tierI_eq_ctier hI).symm.trans h⟩, hI, rfl⟩
      · rintro ⟨v, ⟨-, hv⟩, hI, rfl⟩
        exact (tierI_eq_ctier hI).trans hv
    rw [hset, Finset.card_biUnion]
    · rfl
    · intro v _ v' _ hne
      rw [Function.onFun, Finset.disjoint_filter]
      rintro I - ⟨-, h1⟩ ⟨-, h2⟩
      exact hne (h1.symm.trans h2)
  have hconst : ∑ v ∈ P.classes.filter (fun v => P.ctier S v = t), P.cweight v =
      (P.classes.filter fun v => P.ctier S v = t).card * S.a t := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.1 hv
    rw [cweight_of_mem hT hv1, hv2]
  have := card_tierI_eq hS hT ht
  rw [hsum, hconst] at this
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- Sums over the classes regroup by tier (D3). -/
theorem sum_classes {M : Type*} [AddCommMonoid M] (hS : S.Valid) (hT : P.TierHyp S)
    (F : ℕ → M) :
    ∑ v ∈ P.classes, F (P.ctier S v) = ∑ t ∈ Finset.range S.T, S.N t • F t := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => P.ctier S v) (t := Finset.range S.T)
    (fun v hv => Finset.mem_range.2 (ctier_spec hT hv).1)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.1 hv).2]), Finset.sum_const,
    card_classes_tier hS hT (Finset.mem_range.1 ht)]

variable (P S) in
/-- The tier of a best trial: `S.T` for none. -/
def tierB : Option (Nonce × Index) → ℕ
  | none => S.T
  | some b => P.tierI S b.2

theorem tierB_le (β : Option (Nonce × Index)) : P.tierB S β ≤ S.T := by
  cases β with
  | none => exact le_rfl
  | some b => exact tierI_le _

/-- The signer's rule in tiers. -/
theorem better_iff (hS : S.Valid) (hT : P.TierHyp S) (I : Index) {β : Option (Nonce × Index)}
    (hβ : ∀ b, β = some b → P.Accepted b.2) :
    P.better I β = true ↔ P.tierI S I < P.tierB S β := by
  cases β with
  | none =>
    simp only [better, decide_eq_true_eq, tierB]
    exact (tierI_lt_T hT).symm
  | some b =>
    have hb := hβ b rfl
    simp only [better, Bool.and_eq_true, decide_eq_true_eq, tierB]
    by_cases hI : P.Accepted I
    · rw [weight_lt_iff hS hT hI hb]
      exact ⟨fun h => h.2, fun h => ⟨hI, h⟩⟩
    · rw [tierI_of_not hI]
      exact ⟨fun h => absurd h.1 hI, fun h => absurd h (not_lt.2 (tierI_le _))⟩

theorem tierW_eq_ctier {w : BitVec hashBits} {v : Cls} (h : P.cls w = some v) :
    P.tierW S w = P.ctier S v := by
  obtain ⟨h1, rfl⟩ := P.cls_eq_some.1 h
  exact tierI_eq_ctier h1

end Params

end OptimalOTS.LeanIsaBaseline.Layer
