import Submissions.UpperLeanIsa.FourShape

/-! Four-child packets use a metadata/message-tag pair to identify each parent. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.FourFusion
open OptimalOTS
open scoped Classical
noncomputable section

abbrev Tops := ℕ → Word

def owner (k : Fin 42) : Option (Fin 8) :=
  if k.val ∈ parents 0 then some 0 else if k.val ∈ parents 1 then some 1
  else if k.val ∈ parents 2 then some 2 else if k.val ∈ parents 3 then some 3
  else if k.val ∈ parents 4 then some 4 else if k.val ∈ parents 5 then some 5
  else if k.val ∈ parents 6 then some 6 else if k.val ∈ parents 7 then some 7
  else none

theorem owner_mem : ∀ k : Fin 42, ∀ u : Fin 8, owner k = some u ↔ k.val ∈ parents u := by decide

structure Params where
  codec : Layer.Params
  fusedTag : Fin 42 → Word
  fusedMd : Fin 42 → Word
  rootMd : Fin 1 → Word

namespace Params
variable (P : Params)

def active (k : Fin 42) (j : ℕ) : Option (Fin 8) :=
  if j + 2 = P.codec.len k then owner k else none

theorem active_final {k : Fin 42} {j : ℕ} {u : Fin 8} (h : P.active k j = some u) :
    j + 2 = P.codec.len k := by
  unfold active at h
  split_ifs at h with he
  exact he

def groupInput (t : Tops) (u : Fin 8) (k : Fin 42) (_j : ℕ) (x : Word) : BitVec 896 :=
  packet (fusionWords t u x (P.fusedTag k) (P.fusedMd k))

def chainInput (t : Tops) (k : Fin 42) (j : ℕ) (x : Word) : BitVec 896 :=
  match P.active k j with
  | none => P.codec.chainInput k j x
  | some u => P.groupInput t u k j x

def rootInput (t : Tops) (r : Fin 1) (_st : BitVec 256) : BitVec 896 :=
  packet (rootWords t (P.rootMd r))

structure Hyp : Prop where
  codec : P.codec.Hyp
  fused_inj : ∀ (k k' : Fin 42) (u v : Fin 8) (t t' : Tops) (x y : Word),
    owner k = some u → owner k' = some v →
    P.groupInput t u k 0 x = P.groupInput t' v k' 0 y → k = k'
  fused_chain : ∀ k, P.fusedMd k ≠ P.codec.chainMd
  fused_idx : ∀ k, P.fusedMd k ≠ P.codec.idxMd
  fused_root : ∀ k r, P.fusedMd k ≠ P.rootMd r
  root_inj : Function.Injective P.rootMd
  root_chain : ∀ r, P.rootMd r ≠ P.codec.chainMd
  root_idx : ∀ r, P.rootMd r ≠ P.codec.idxMd

variable {P}

theorem groupInput_binds {u : Fin 8} {k : Fin 42} {j : ℕ} (t t' : Tops) (x y : Word)
    (h : P.groupInput t u k j x = P.groupInput t' u k j y) : GroupBinds t t' u :=
  fusion_binds_children t t' u.isLt x y _ _ _ _ h

theorem groupInput_current {u : Fin 8} {k : Fin 42} {j : ℕ} (t t' : Tops) (x y : Word)
    (h : P.groupInput t u k j x = P.groupInput t' u k j y) : x = y :=
  congrFun (packet_injective h) 2

theorem chainInput_location (hP : P.Hyp) {k k' : Fin 42} {j j' : ℕ}
    (hj : j + 1 < P.codec.len k) (hj' : j' + 1 < P.codec.len k')
    (t t' : Tops) (x y : Word)
    (h : P.chainInput t k j x = P.chainInput t' k' j' y) : k = k' ∧ j = j' ∧ x = y := by
  unfold chainInput at h
  cases ha : P.active k j with
  | none =>
    cases hb : P.active k' j' with
    | none =>
      simp only [ha,hb] at h
      exact (Layer.Params.chainInput_eq_iff hP.codec hj hj' x y).mp h
    | some v =>
      simp only [ha,hb] at h
      exact (hP.fused_chain k' ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2.symm).elim
  | some u =>
    cases hb : P.active k' j' with
    | none =>
      simp only [ha,hb] at h
      exact (hP.fused_chain k ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).elim
    | some v =>
      simp only [ha,hb] at h
      have he := packet_injective h
      have ho : owner k = some u := by
        unfold active at ha
        split_ifs at ha
        exact ha
      have ho' : owner k' = some v := by
        unfold active at hb
        split_ifs at hb
        exact hb
      have hk := hP.fused_inj k k' u v t t' x y ho ho' h
      have hjk := P.active_final ha
      have hjk' := P.active_final hb
      subst k'
      exact ⟨rfl, by omega, congrFun he 2⟩

theorem chainInput_current {k : Fin 42} {j : ℕ} (t t' : Tops) (x y : Word)
    (h : P.chainInput t k j x = P.chainInput t' k j y) : x = y := by
  unfold chainInput at h
  cases ha : P.active k j with
  | none =>
    simp only [ha] at h
    exact (Layer.Params.chainInput_same_iff k j x y).mp h
  | some u =>
    simp only [ha] at h
    exact groupInput_current t t' x y h

theorem rootInput_location (_hP : P.Hyp) (t t' : Tops) (r s : Fin 1) (st st' : BitVec 256)
    (_h : P.rootInput t r st = P.rootInput t' s st') : r = s := Subsingleton.elim _ _

theorem chainInput_ne_rootInput (hP : P.Hyp) (t t' : Tops) (k : Fin 42) (j : ℕ)
    (x : Word) (r : Fin 1) (st : BitVec 256) : P.chainInput t k j x ≠ P.rootInput t' r st := by
  intro h
  unfold chainInput at h
  cases ha : P.active k j with
  | none =>
    simp only [ha] at h
    exact (hP.root_chain r) (((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).symm
  | some u =>
    simp only [ha] at h
    exact (hP.fused_root k r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

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

theorem rootInput_ne_idxInput (hP : P.Hyp) (t : Tops) (r : Fin 1) (st : BitVec 256)
    (m : Message) (η : Nonce) (pk : PublicKey) : P.rootInput t r st ≠ P.codec.idxInput m η pk := by
  intro h
  exact (hP.root_idx r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

end Params
end
end OptimalOTS.LeanIsaBaseline.Layer.FourFusion
