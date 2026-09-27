import Submissions.UpperCompressions.CompactSchedule91

/-!
# Concrete 256-bit decoder for the chain-18 schedule

The compact schedule uses arbitrary, non-power-of-two alias multiplicities.
Consequently the decoder works directly in the full 256-bit oracle-output
space.  This module realizes the emitted finite table as an actual decoder and
proves its class, tier, and acceptance fibers exactly.
-/

namespace OptimalOTS.WeightedConstruction.LongChain91Schedule

open scoped Classical BigOperators
noncomputable section

set_option maxRecDepth 100000

abbrev Tier := Chain18Compact.Tier
abbrev population (j : Tier) : ℕ := Chain18Compact.classes j
abbrev Class := (j : Tier) × Fin (population j)
abbrev multiplicity (c : Class) : ℕ := Chain18Compact.aliases c.1
abbrev Alias := (c : Class) × Fin (multiplicity c)
abbrev M : ℕ := Chain18Compact.familyCardinality
abbrev A : ℕ := Chain18Compact.acceptedAliases

theorem card_class : Fintype.card Class = M := by
  simp only [Class, Fintype.card_sigma, Fintype.card_fin]
  unfold M Chain18Compact.familyCardinality
  rfl

theorem card_alias : Fintype.card Alias = A := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ c : Class, Chain18Compact.aliases c.1) = A
  rw [Fintype.sum_sigma]
  have hsum (j : Tier) :
      (∑ _k : Fin (population j), Chain18Compact.aliases j) =
        population j * Chain18Compact.aliases j := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [hsum]
  unfold A Chain18Compact.acceptedAliases
  rfl

def classEquiv : Class ≃ Fin M := Fintype.equivFinOfCardEq card_class
def aliasEquiv : Alias ≃ Fin A := Fintype.equivFinOfCardEq card_alias

def tier (i : Fin M) : Tier := (classEquiv.symm i).1

theorem accepted_lt : A < 2 ^ 256 := Chain18Compact.acceptedAliases_bounds.2

/-- Interpret the accepted prefix of the 256-bit oracle-output space as the
schedule's alias type. -/
def rawAlias (x : BitVec 256) : Option Alias :=
  if h : x.toNat < A then some (aliasEquiv.symm ⟨x.toNat, h⟩) else none

def rawClass (x : BitVec 256) : Option Class := (rawAlias x).map Sigma.fst

def decode (x : BitVec 256) : Option (Fin M) := (rawClass x).map classEquiv

def aliasBits (a : Alias) : BitVec 256 := BitVec.ofNat 256 (aliasEquiv a).val

theorem aliasBits_toNat (a : Alias) : (aliasBits a).toNat = (aliasEquiv a).val := by
  rw [aliasBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans (aliasEquiv a).isLt accepted_lt

@[simp] theorem rawAlias_aliasBits (a : Alias) : rawAlias (aliasBits a) = some a := by
  simp only [rawAlias, aliasBits_toNat, dif_pos (aliasEquiv a).isLt]
  rw [Equiv.symm_apply_apply]

theorem aliasBits_of_rawAlias {x : BitVec 256} {a : Alias}
    (h : rawAlias x = some a) : aliasBits a = x := by
  unfold rawAlias at h
  split_ifs at h with hx
  · simp only [Option.some.injEq] at h
    rw [← h]
    apply BitVec.eq_of_toNat_eq
    rw [aliasBits_toNat, Equiv.apply_symm_apply]

/-- A class's alias fiber is exactly its emitted multiplicity coordinate. -/
def aliasFiberEquiv (c : Class) :
    {a : Alias // a.1 = c} ≃ Fin (multiplicity c) where
  toFun a := a.property ▸ a.val.2
  invFun b := ⟨⟨c, b⟩, rfl⟩
  left_inv := by rintro ⟨⟨d, b⟩, h⟩; cases h; rfl
  right_inv _ := rfl

def rawFiberEquiv (c : Class) :
    {x : BitVec 256 // rawClass x = some c} ≃ {a : Alias // a.1 = c} :=
  (Equiv.ofBijective
    (fun a : {a : Alias // a.1 = c} =>
      (⟨aliasBits a.val, by simp [rawClass, a.property]⟩ :
        {x : BitVec 256 // rawClass x = some c}))
    (by
      constructor
      · intro a b h
        apply Subtype.ext
        have he := congrArg
          (fun x : {x : BitVec 256 // rawClass x = some c} => rawAlias x.val) h
        simpa using he
      · intro x
        have hx := x.property
        rw [rawClass, Option.map_eq_some_iff] at hx
        obtain ⟨a, ha, hc⟩ := hx
        exact ⟨⟨a, hc⟩, Subtype.ext (aliasBits_of_rawAlias ha)⟩)).symm

theorem rawClass_fiber (c : Class) :
    (Finset.univ.filter fun x : BitVec 256 => rawClass x = some c).card =
      multiplicity c := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rawFiberEquiv c),
    Fintype.card_congr (aliasFiberEquiv c), Fintype.card_fin]

theorem decode_eq_some (x : BitVec 256) (i : Fin M) :
    decode x = some i ↔ rawClass x = some (classEquiv.symm i) := by
  rw [decode, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c, hc, hi⟩
    have he : c = classEquiv.symm i := by
      apply classEquiv.injective
      simpa using hi
    simpa [he] using hc
  · intro h
    exact ⟨classEquiv.symm i, h, classEquiv.apply_symm_apply i⟩

theorem decode_fiber (i : Fin M) :
    (Finset.univ.filter fun x : BitVec 256 => decode x = some i).card =
      Chain18Compact.aliases (tier i) := by
  have he : (Finset.univ.filter fun x : BitVec 256 => decode x = some i) =
      Finset.univ.filter fun x : BitVec 256 =>
        rawClass x = some (classEquiv.symm i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decode_eq_some]
  rw [he, rawClass_fiber]
  rfl

def rawTier (x : BitVec 256) : Option Tier := (rawAlias x).map fun a => a.1.1

def acceptedEquiv : {x : BitVec 256 // (rawAlias x).isSome} ≃ Alias :=
  (Equiv.ofBijective
    (fun a : Alias =>
      (⟨aliasBits a, by simp⟩ : {x : BitVec 256 // (rawAlias x).isSome}))
    (by
      constructor
      · intro a b h
        have he := congrArg
          (fun x : {x : BitVec 256 // (rawAlias x).isSome} => rawAlias x.val) h
        simpa using he
      · intro x
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp x.property
        exact ⟨a, Subtype.ext (aliasBits_of_rawAlias ha)⟩)).symm

theorem accepted_count :
    (Finset.univ.filter fun x : BitVec 256 => (decode x).isSome).card = A := by
  have hisSome (x : BitVec 256) : (decode x).isSome = (rawAlias x).isSome := by
    simp [decode, rawClass]
  simp only [hisSome]
  rw [← Fintype.card_subtype, Fintype.card_congr acceptedEquiv, card_alias]

/-- Reindex a class sum by the emitted tier populations. -/
theorem sum_tier (f : Tier → ℝ) :
    (∑ i : Fin M, f (tier i)) = ∑ j : Tier, (population j : ℝ) * f j := by
  calc
    _ = ∑ c : Class, f c.1 := by
      apply Fintype.sum_equiv classEquiv.symm
      intro i
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

def classProbability (i : Fin M) : ℝ :=
  (Chain18Compact.aliases (tier i) : ℝ) / (Chain18Compact.R : ℝ)

theorem class_probability_real (i : Fin M) :
    ((Finset.univ.filter fun x : BitVec 256 => decode x = some i).card : ℝ) /
        2^256 = classProbability i := by
  rw [decode_fiber]
  unfold classProbability Chain18Compact.R
  norm_num

end
end OptimalOTS.WeightedConstruction.LongChain91Schedule
