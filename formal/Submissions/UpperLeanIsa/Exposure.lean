import Submissions.UpperLeanIsa.Resampling

/-! Public information determines all exposed oracle points. The complementary
cache contains exactly the chain steps before the signing cut. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleSpec
open scoped Classical
noncomputable section

attribute [local irreducible] queryLocation Record.query

private theorem data_source_eq (d : Cut) (ξ ζ : Record)
    (h : publicData d ξ = publicData d ζ) (i : Fin 39) (hi : (d i).val = 0) :
    ξ.1 i = ζ.1 i := by
  have he := congrArg (fun v : PublicData => v.1 i) h
  simp only [publicData, hi, if_true, Option.some.injEq] at he
  exact he

private theorem data_chain_eq (d : Cut) (ξ ζ : Record)
    (h : publicData d ξ = publicData d ζ) (i : Fin 39) (j : Fin 127)
    (hj : (d i).val ≤ j.val + 1) : ξ.2 (.inl (i, j)) = ζ.2 (.inl (i, j)) := by
  have he := congrArg (fun v : PublicData => v.2 (.inl (i, j))) h
  simp only [publicData, if_pos hj, Option.some.injEq] at he
  exact he

private theorem data_root_eq (d : Cut) (ξ ζ : Record)
    (h : publicData d ξ = publicData d ζ) (i : Fin 39) :
    ξ.2 (.inr i) = ζ.2 (.inr i) := by
  exact Option.some.inj (congrArg (fun v : PublicData => v.2 (.inr i)) h)

theorem data_word_eq (d : Cut) (ξ ζ : Record)
    (h : publicData d ξ = publicData d ζ) (i : Fin 39) (j : Fin 128)
    (hj : (d i).val ≤ j.val) : ξ.word i j = ζ.word i j := by
  unfold Record.word
  split
  · rename_i hz
    exact data_source_eq d ξ ζ h i (by omega)
  · rename_i hz
    rw [data_chain_eq d ξ ζ h i ⟨j.val - 1, by have := j.isLt; omega⟩ (by dsimp; omega)]

def Hidden (d : Cut) : HashLocation → Prop
  | .inl (i, j) => j.val < (d i).val
  | .inr _ => False

theorem exposed_query_eq (d : Cut) (ξ ζ : Record)
    (h : publicData d ξ = publicData d ζ) (a : HashLocation) (ha : ¬ Hidden d a) :
    ξ.query a = ζ.query a := by
  unfold Record.query
  apply congrArg (fun x : BitVec 896 => (⟨896, x⟩ : Query))
  cases a with
  | inl a =>
    rcases a with ⟨i, j⟩
    exact congrArg (chainInput i.val j.val)
      (data_word_eq d ξ ζ h i j.castSucc (by change ¬ j.val < (d i).val at ha; exact Nat.le_of_not_gt ha))
  | inr i =>
    dsimp only [Record.input, Record.endpoint]
    rw [data_word_eq d ξ ζ h i 127 (by have := (d i).isLt; change (d i).val ≤ 127; omega)]
    apply congrArg (fun cv => rootInput (rootTag i) cv (ζ.endpoint i))
    by_cases hi : i.val = 0
    · have hx : ξ.rootBefore i = (0 : BitVec 256) := dif_pos hi
      have hz : ζ.rootBefore i = (0 : BitVec 256) := dif_pos hi
      exact hx.trans hz.symm
    · let p : Fin 39 := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hx : ξ.rootBefore i = ξ.2 (.inr p) := dif_neg hi
      have hz : ζ.rootBefore i = ζ.2 (.inr p) := dif_neg hi
      exact hx.trans ((data_root_eq d ξ ζ h p).trans hz.symm)

theorem exposed_answer_eq (d : Cut) (ξ ζ : Record)
    (h : publicData d ξ = publicData d ζ) (a : HashLocation) (ha : ¬ Hidden d a) :
    ξ.2 a = ζ.2 a := by
  cases a with
  | inl a =>
    rcases a with ⟨i, j⟩
    apply data_chain_eq d ξ ζ h i j
    have := Nat.le_of_not_gt ha
    omega
  | inr i => exact data_root_eq d ξ ζ h i

def hiddenCache (d : Cut) (ξ : Record) : Cache := fun q =>
  match queryLocation q with
  | none => none
  | some a => if Hidden d a then ξ.cache q else none

def exposedCache (d : Cut) (ξ : Record) : Cache := fun q =>
  match queryLocation q with
  | none => none
  | some a => if Hidden d a then none else ξ.cache q

theorem exposure_partition (d : Cut) (ξ : Record) :
    Cache.extend (exposedCache d ξ) (hiddenCache d ξ) = ξ.cache := by
  funext q
  cases hl : queryLocation q with
  | none => simp only [Cache.extend, exposedCache, hiddenCache, Record.cache, hl, Option.or_none]
  | some a =>
    simp only [Cache.extend, exposedCache, hiddenCache, hl]
    split <;> simp

theorem exposure_disjoint (d : Cut) (ξ : Record) :
    Cache.Disjoint (exposedCache d ξ) (hiddenCache d ξ) := by
  intro q hq
  cases hl : queryLocation q with
  | none => simp only [hiddenCache, hl, Option.isSome_none, Bool.false_eq_true] at hq
  | some a =>
    by_cases ha : Hidden d a
    · simp only [exposedCache, hl, if_pos ha]
    · simp only [hiddenCache, hl, if_neg ha, Option.isSome_none, Bool.false_eq_true] at hq

theorem hiddenCache_some_iff (d : Cut) (ξ : Record) (q : Query) (u : BitVec hashBits) :
    hiddenCache d ξ q = some u ↔ ∃ a, Hidden d a ∧ ξ.query a = q ∧ ξ.2 a = u := by
  constructor
  · intro h
    cases hl : queryLocation q with
    | none => simp only [hiddenCache, hl, reduceCtorEq] at h
    | some a =>
      by_cases ha : Hidden d a
      · simp only [hiddenCache, hl, if_pos ha] at h
        obtain ⟨b, hb, hu⟩ := (ξ.cache_some_iff q u).mp h
        have he : b = a := Option.some.inj ((hb ▸ queryLocation_query ξ b).symm.trans hl)
        exact ⟨b, he ▸ ha, hb, hu⟩
      · simp only [hiddenCache, hl, if_neg ha, reduceCtorEq] at h
  · rintro ⟨a, ha, rfl, rfl⟩
    simp only [hiddenCache, queryLocation_query, if_pos ha, Record.cache_query]

theorem exposedCache_some_iff (d : Cut) (ξ : Record) (q : Query) (u : BitVec hashBits) :
    exposedCache d ξ q = some u ↔ ∃ a, ¬ Hidden d a ∧ ξ.query a = q ∧ ξ.2 a = u := by
  constructor
  · intro h
    cases hl : queryLocation q with
    | none => simp only [exposedCache, hl, reduceCtorEq] at h
    | some a =>
      by_cases ha : Hidden d a
      · simp only [exposedCache, hl, if_pos ha, reduceCtorEq] at h
      · simp only [exposedCache, hl, if_neg ha] at h
        obtain ⟨b, hb, hu⟩ := (ξ.cache_some_iff q u).mp h
        have he : b = a := Option.some.inj ((hb ▸ queryLocation_query ξ b).symm.trans hl)
        exact ⟨b, he ▸ ha, hb, hu⟩
  · rintro ⟨a, ha, rfl, rfl⟩
    simp only [exposedCache, queryLocation_query, if_neg ha, Record.cache_query]

theorem exposedCache_data_eq (d : Cut) (ξ ζ : Record)
    (h : publicData d ξ = publicData d ζ) : exposedCache d ξ = exposedCache d ζ := by
  funext q
  apply Option.ext
  intro u
  rw [exposedCache_some_iff, exposedCache_some_iff]
  constructor
  · rintro ⟨a, ha, hq, hu⟩
    exact ⟨a, ha, (exposed_query_eq d ξ ζ h a ha).symm.trans hq,
      (exposed_answer_eq d ξ ζ h a ha).symm.trans hu⟩
  · rintro ⟨a, ha, hq, hu⟩
    exact ⟨a, ha, (exposed_query_eq d ξ ζ h a ha).trans hq,
      (exposed_answer_eq d ξ ζ h a ha).trans hu⟩

end
end OptimalOTS.LeanIsaBaseline
