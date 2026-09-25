import Submissions.UpperLeanIsa.FusionShape

/-! Dependency-aware hash inputs. Syntactic domain separation identifies a unique
chain location or root call even when the dependency words differ. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OptimalOTS
open scoped Classical
noncomputable section

abbrev Tops := ℕ → Word

/-- The group whose positive final steps bind a dependency bundle. -/
def owner (k : Fin 42) : Option (Fin 6) :=
  if k.val ∈ parents 0 then some 0 else if k.val ∈ parents 1 then some 1
  else if k.val ∈ parents 2 then some 2 else if k.val ∈ parents 3 then some 3
  else if k.val ∈ parents 4 then some 4 else if k.val ∈ parents 5 then some 5 else none

theorem owner_mem : ∀ k : Fin 42, ∀ u : Fin 6, owner k = some u ↔ k.val ∈ parents u := by
  decide

structure Params where
  codec : Layer.Params
  fusedMd : Fin 42 → Word
  rootMd : Fin 3 → Word

namespace Params
variable (P : Params)

def active (k : Fin 42) (j : ℕ) : Option (Fin 6) :=
  if j + 2 = P.codec.len k then owner k else none

theorem active_final {k : Fin 42} {j : ℕ} {u : Fin 6} (h : P.active k j = some u) :
    j + 2 = P.codec.len k := by
  unfold active at h
  split_ifs at h with he
  · exact he

def chainInput (t : Tops) (k : Fin 42) (j : ℕ) (x : Word) : BitVec 896 :=
  match P.active k j with
  | none => P.codec.chainInput k j x
  | some u => packet (fusionWords t u x (P.fusedMd k))

def rootInput (t : Tops) (r : Fin 3) (st : BitVec 256) : BitVec 896 :=
  if r.val = 0 then LeanIsa.hashInput (t 2 ++ t 1) (t 6 ++ t 5 ++ t 4 ++ t 3) (P.rootMd r)
  else if r.val = 1 then LeanIsa.hashInput (st.extractLsb' 0 128 ++ t 26)
    (t 11 ++ t 10 ++ t 9 ++ t 8) (P.rootMd r)
  else LeanIsa.hashInput (st.extractLsb' 0 128 ++ t 7)
    ((1 : Word) ++ (1 : Word) ++ (1 : Word) ++ (1 : Word)) (P.rootMd r)

structure Hyp : Prop where
  codec : P.codec.Hyp
  fused_inj : Function.Injective P.fusedMd
  fused_chain : ∀ k, P.fusedMd k ≠ P.codec.chainMd
  fused_idx : ∀ k, P.fusedMd k ≠ P.codec.idxMd
  fused_root : ∀ k r, P.fusedMd k ≠ P.rootMd r
  root_inj : Function.Injective P.rootMd
  root_chain : ∀ r, P.rootMd r ≠ P.codec.chainMd
  root_idx : ∀ r, P.rootMd r ≠ P.codec.idxMd

variable {P}

theorem chainInput_location (hP : P.Hyp) {k k' : Fin 42} {j j' : ℕ}
    (hj : j + 1 < P.codec.len k) (hj' : j' + 1 < P.codec.len k')
    (t t' : Tops) (x y : Word)
    (h : P.chainInput t k j x = P.chainInput t' k' j' y) : k = k' ∧ j = j' ∧ x = y := by
  unfold chainInput at h
  cases ha : P.active k j with
  | none =>
    cases hb : P.active k' j' with
    | none =>
      simp only [ha, hb] at h
      exact (Layer.Params.chainInput_eq_iff hP.codec hj hj' x y).mp h
    | some v =>
      simp only [ha, hb] at h
      have hm := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
      exact (hP.fused_chain k' hm.symm).elim
  | some u =>
    cases hb : P.active k' j' with
    | none =>
      simp only [ha, hb] at h
      have hm := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
      exact (hP.fused_chain k hm).elim
    | some v =>
      simp only [ha, hb] at h
      have hm := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
      have hk := hP.fused_inj hm
      subst k'
      have hjj : j = j' := by have := P.active_final ha; have := P.active_final hb; omega
      exact ⟨rfl, hjj, congrFun (packet_injective h) 2⟩

theorem chainInput_current {k : Fin 42} {j : ℕ} (t t' : Tops) (x y : Word)
    (h : P.chainInput t k j x = P.chainInput t' k j y) : x = y := by
  unfold chainInput at h
  cases ha : P.active k j with
  | none =>
    simp only [ha] at h
    exact (Layer.Params.chainInput_same_iff k j x y).mp h
  | some u =>
    simp only [ha] at h
    exact congrFun (packet_injective h) 2

theorem rootInput_location (hP : P.Hyp) (t t' : Tops) (r s : Fin 3) (st st' : BitVec 256)
    (h : P.rootInput t r st = P.rootInput t' s st') : r = s := by
  apply hP.root_inj
  unfold rootInput at h
  split_ifs at h <;> exact ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem chainInput_ne_rootInput (hP : P.Hyp) (t t' : Tops) (k : Fin 42) (j : ℕ)
    (x : Word) (r : Fin 3) (st : BitVec 256) : P.chainInput t k j x ≠ P.rootInput t' r st := by
  intro h
  unfold chainInput rootInput at h
  cases ha : P.active k j with
  | none =>
    simp only [ha] at h
    split_ifs at h <;> exact (hP.root_chain r) (((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).symm
  | some u =>
    simp only [ha] at h
    split_ifs at h <;> exact (hP.fused_root k r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem chainInput_ne_idxInput (hP : P.Hyp) (t : Tops) (k : Fin 42) (j : ℕ)
    (x : Word) (m : Message) (η : Nonce) (pk : PublicKey) :
    P.chainInput t k j x ≠ P.codec.idxInput m η pk := by
  intro h
  unfold chainInput at h
  cases ha : P.active k j with
  | none =>
    simp only [ha] at h
    exact Layer.Params.chainInput_ne_idxInput hP.codec k j x m η pk h
  | some u =>
    simp only [ha] at h
    exact (hP.fused_idx k) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem rootInput_ne_idxInput (hP : P.Hyp) (t : Tops) (r : Fin 3) (st : BitVec 256)
    (m : Message) (η : Nonce) (pk : PublicKey) : P.rootInput t r st ≠ P.codec.idxInput m η pk := by
  intro h
  unfold rootInput at h
  split_ifs at h <;> exact (hP.root_idx r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

end Params
end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
