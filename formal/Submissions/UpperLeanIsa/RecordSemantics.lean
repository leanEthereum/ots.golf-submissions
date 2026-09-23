import Submissions.UpperLeanIsa.HiddenBound

/-! A programmed record agrees with the deterministic scheme evaluations.
These are semantic facts; distributional equivalence to random key generation
is established separately. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleSpec
open scoped Classical
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def Respects (f : HashTable) (ξ : Record) : Prop :=
  ∀ a, f (ξ.query a) = ξ.2 a

def Record.table (ξ : Record) : HashTable := fun q => (ξ.cache q).getD 0

theorem Record.table_respects (ξ : Record) : Respects ξ.table ξ := by
  intro a
  simp only [Record.table, Record.cache_query, Option.getD_some]

theorem chainValue_record (f : HashTable) (ξ : Record) (hf : Respects f ξ)
    (i : Fin 34) (j n : ℕ) (hj : j + n ≤ 255) :
    chainValue f i.val j n (ξ.word i ⟨j, by omega⟩) =
      ξ.word i ⟨j + n, by omega⟩ := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [chainValue]
    have hq : f ⟨896, chainInput i.val j (ξ.word i ⟨j, by omega⟩)⟩ =
        ξ.2 (.inl (i, ⟨j, by omega⟩)) := hf (.inl (i, ⟨j, by omega⟩))
    rw [hq]
    have hw : ξ.word i ⟨j + 1, by omega⟩ =
        (ξ.2 (.inl (i, ⟨j, by omega⟩))).extractLsb' 0 128 := by
      simp only [Record.word, dif_neg (Nat.succ_ne_zero j),
        Nat.add_sub_cancel]
    rw [← hw]
    have hn : j + 1 + n = j + (n + 1) := by omega
    simpa only [hn] using ih (j + 1) (by omega)

theorem endpoints_record (f : HashTable) (ξ : Record) (hf : Respects f ξ) :
    endpoints f ξ.1 = ξ.endpoint := by
  funext i
  exact chainValue_record f ξ hf i 0 255 (by omega)

theorem signedWords_record (f : HashTable) (ξ : Record) (hf : Respects f ξ) (m : Message) :
    signedWords f ξ.1 m = fun i => ξ.word i (afterSigning m i) := by
  funext i
  simpa only [Nat.zero_add, signedWords, afterSigning, Record.word, ↓reduceDIte] using chainValue_record f ξ hf i 0 (digit m i) (by simpa using digit_le m i)

def Record.rootState (ξ : Record) (k : Fin 35) : BitVec 256 :=
  if h : k.val = 0 then 0 else ξ.2 (.inr ⟨k.val - 1, by have := k.isLt; omega⟩)

theorem Record.rootState_before (ξ : Record) (i : Fin 34) :
    ξ.rootState i.castSucc = ξ.rootBefore i := rfl

theorem Record.rootState_after (ξ : Record) (i : Fin 34) :
    ξ.rootState i.succ = ξ.2 (.inr i) := by
  simp only [Record.rootState, Fin.val_succ, dif_neg (Nat.succ_ne_zero i.val), Nat.add_sub_cancel]

/-- The root fold reads only the root answers of the record. -/
theorem rootValueFold_record_of_roots (f : HashTable) (ξ : Record)
    (hf : ∀ i : Fin 34, f (ξ.query (.inr i)) = ξ.2 (.inr i))
    (n j : ℕ) (hj : j + n = 34) :
    rootValueFold f (List.ofFn (fun k : Fin n => ξ.endpoint ⟨j + k.val, by have := k.isLt; omega⟩))
      (ξ.rootState ⟨j, by omega⟩) = ξ.rootState 34 := by
  induction n generalizing j with
  | zero =>
    have : j = 34 := by omega
    subst j
    rfl
  | succ n ih =>
    let i : Fin 34 := ⟨j, by omega⟩
    let tail : Fin n → Word := fun k => ξ.endpoint ⟨j + 1 + k.val, by have := k.isLt; omega⟩
    have hlist : List.ofFn (fun k : Fin (n + 1) =>
        ξ.endpoint ⟨j + k.val, by have := k.isLt; omega⟩) = ξ.endpoint i :: List.ofFn tail := by
      rw [List.ofFn_succ]
      refine congrArg₂ List.cons ?_ ?_
      · apply congrArg ξ.endpoint
        apply Fin.ext
        simp [i]
      · apply congrArg List.ofFn
        funext k
        apply congrArg ξ.endpoint
        apply Fin.ext
        dsimp [tail]
        omega
    rw [hlist, rootValueFold]
    have ht : (rootTag i).val = n := by dsimp [rootTag, i]; omega
    have hb : ξ.rootState ⟨j, by omega⟩ = ξ.rootBefore i := rfl
    have hq : f ⟨896, LeanIsa.hashInput (ξ.rootState ⟨j, by omega⟩)
        ((ξ.endpoint i).setWidth 512) (BitVec.ofNat 128 (2 + (List.ofFn tail).length))⟩ =
        ξ.rootState ⟨j + 1, by omega⟩ := by
      rw [List.length_ofFn]
      have h := hf i
      change f ⟨896, LeanIsa.hashInput (ξ.rootBefore i) ((ξ.endpoint i).setWidth 512)
        (BitVec.ofNat 128 (2 + (rootTag i).val))⟩ = ξ.2 (.inr i) at h
      rw [ht] at h
      exact h.trans (ξ.rootState_after i).symm
    exact (congrArg (rootValueFold f (List.ofFn tail)) hq).trans (ih (j + 1) (by omega))

theorem rootValueFold_record (f : HashTable) (ξ : Record) (hf : Respects f ξ)
    (n j : ℕ) (hj : j + n = 34) :
    rootValueFold f (List.ofFn (fun k : Fin n => ξ.endpoint ⟨j + k.val, by have := k.isLt; omega⟩))
      (ξ.rootState ⟨j, by omega⟩) = ξ.rootState 34 :=
  rootValueFold_record_of_roots f ξ (fun i => hf (.inr i)) n j hj

/-- The public key is determined by the root answers alone. -/
theorem rootValue_record_of_roots (f : HashTable) (ξ : Record)
    (hf : ∀ i : Fin 34, f (ξ.query (.inr i)) = ξ.2 (.inr i)) :
    rootValue f ξ.endpoint = ξ.publicKey := by
  have h := rootValueFold_record_of_roots f ξ hf 34 0 (by omega)
  have hl : (fun k : Fin 34 => ξ.endpoint ⟨0 + k.val, by have := k.isLt; omega⟩) = ξ.endpoint := by
    funext k
    simp only [Nat.zero_add]
  rw [hl] at h
  change rootValueFold f (List.ofFn ξ.endpoint) 0 = ξ.2 (.inr 33) at h
  exact congrArg (fun x : BitVec hashBits => x.extractLsb' 0 128) h

theorem rootValue_record (f : HashTable) (ξ : Record) (hf : Respects f ξ) :
    rootValue f ξ.endpoint = ξ.publicKey :=
  rootValue_record_of_roots f ξ (fun i => hf (.inr i))

end
end OptimalOTS.LeanIsaBaseline
