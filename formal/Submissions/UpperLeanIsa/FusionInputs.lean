import Submissions.UpperLeanIsa.FusionShape

/-! Dependency-aware hash inputs. Syntactic domain separation identifies a unique
chain location or root call even when the dependency words differ. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OptimalOTS
open scoped Classical
noncomputable section

abbrev Tops := ℕ → Word

/-- The group whose positive final steps bind a dependency bundle. -/
def owner (k : Fin 42) : Option (Fin 9) :=
  if k.val ∈ parents 0 then some 0 else if k.val ∈ parents 1 then some 1
  else if k.val ∈ parents 2 then some 2 else if k.val ∈ parents 3 then some 3
  else if k.val ∈ parents 4 then some 4 else if k.val ∈ parents 5 then some 5
  else if k.val ∈ parents 6 then some 6 else if k.val ∈ parents 7 then some 7
  else if k.val ∈ parents 8 then some 8 else none

theorem owner_mem : ∀ k : Fin 42, ∀ u : Fin 9, owner k = some u ↔ k.val ∈ parents u := by
  decide

/-- The chains whose final steps are three-dep parents. -/
def tripleOwned (k : Fin 42) : Prop := ∃ u : Fin 9, owner k = some u ∧ 5 ≤ u.val

structure Params where
  codec : Layer.Params
  fusedMd : Fin 42 → Word
  rootMd : Fin 1 → Word
  tripleCv : Fin 42 → BitVec 256

namespace Params
variable (P : Params)

def active (k : Fin 42) (j : ℕ) : Option (Fin 9) :=
  if j + 2 = P.codec.len k then owner k else none

theorem active_final {k : Fin 42} {j : ℕ} {u : Fin 9} (h : P.active k j = some u) :
    j + 2 = P.codec.len k := by
  unfold active at h
  split_ifs at h with he
  · exact he

/-- A three-dep final step has cv `tripleCv k` and chain metadata `ONE`. -/
def groupInput (t : Tops) (u : Fin 9) (k : Fin 42) (j : ℕ) (x : Word) : BitVec 896 :=
  if u.val < 5 then packet (fusionWords t u x (P.fusedMd k))
  else triplePacket (P.tripleCv k) t u x P.codec.chainMd

def chainInput (t : Tops) (k : Fin 42) (j : ℕ) (x : Word) : BitVec 896 :=
  match P.active k j with
  | none => P.codec.chainInput k j x
  | some u => P.groupInput t u k j x

/-- The root call; the state argument is unused by the single call. -/
def rootInput (t : Tops) (r : Fin 1) (_st : BitVec 256) : BitVec 896 :=
  packet (rootWords t (P.rootMd r))

structure Hyp : Prop where
  codec : P.codec.Hyp
  fused_inj : Function.Injective P.fusedMd
  fused_chain : ∀ k, P.fusedMd k ≠ P.codec.chainMd
  fused_idx : ∀ k, P.fusedMd k ≠ P.codec.idxMd
  fused_root : ∀ k r, P.fusedMd k ≠ P.rootMd r
  root_chain : ∀ r, P.rootMd r ≠ P.codec.chainMd
  root_idx : ∀ r, P.rootMd r ≠ P.codec.idxMd
  triple_cv : ∀ k, P.tripleCv k ≠ P.codec.cv
  /-- The cv words separate the three-dep parents. -/
  triple_inj : ∀ k k' : Fin 42, tripleOwned k → tripleOwned k' → P.tripleCv k = P.tripleCv k' →
    k = k'

variable {P}

theorem groupInput_binds {u : Fin 9} {k : Fin 42} {j : ℕ} (t t' : Tops) (x y : Word)
    (h : P.groupInput t u k j x = P.groupInput t' u k j y) : GroupBinds t t' u := by
  unfold groupInput at h
  split_ifs at h with h5
  · exact fusion_binds_children t t' h5 x y _ _ h
  · exact triple_binds (by omega) u.isLt h

theorem groupInput_current {u : Fin 9} {k : Fin 42} {j : ℕ} (t t' : Tops) (x y : Word)
    (h : P.groupInput t u k j x = P.groupInput t' u k j y) : x = y := by
  unfold groupInput at h
  split_ifs at h
  · exact congrFun (packet_injective h) 2
  · exact triple_current h

theorem owner_triple {k : Fin 42} {j : ℕ} {u : Fin 9} (h : P.active k j = some u)
    (hu : ¬ u.val < 5) : tripleOwned k := by
  unfold active at h
  split_ifs at h
  exact ⟨u, h, by omega⟩

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
      simp only [ha, hb, groupInput] at h
      split_ifs at h
      · exact (hP.fused_chain k' ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2.symm).elim
      · exact (hP.triple_cv k' ((hashInput_eq_iff _ _ _ _ _ _).mp h).1.symm).elim
  | some u =>
    cases hb : P.active k' j' with
    | none =>
      simp only [ha, hb, groupInput] at h
      split_ifs at h
      · exact (hP.fused_chain k ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).elim
      · exact (hP.triple_cv k ((hashInput_eq_iff _ _ _ _ _ _).mp h).1).elim
    | some v =>
      simp only [ha, hb, groupInput] at h
      have hjk := P.active_final ha
      have hjk' := P.active_final hb
      split_ifs at h with hu hv hv
      · have hk := hP.fused_inj ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
        subst k'
        exact ⟨rfl, by omega, congrFun (packet_injective h) 2⟩
      · exact (hP.fused_chain k ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).elim
      · exact (hP.fused_chain k' ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2.symm).elim
      · obtain ⟨hc, -, hx, -⟩ := triplePacket_eq h
        have hk := hP.triple_inj k k' (owner_triple ha hu) (owner_triple hb hv) hc
        subst k'
        exact ⟨rfl, by omega, hx⟩

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

theorem rootInput_location (t t' : Tops) (r s : Fin 1) (st st' : BitVec 256)
    (_h : P.rootInput t r st = P.rootInput t' s st') : r = s := Subsingleton.elim r s

theorem chainInput_ne_rootInput (hP : P.Hyp) (t t' : Tops) (k : Fin 42) (j : ℕ)
    (x : Word) (r : Fin 1) (st : BitVec 256) : P.chainInput t k j x ≠ P.rootInput t' r st := by
  intro h
  unfold chainInput rootInput at h
  cases ha : P.active k j with
  | none =>
    simp only [ha] at h
    exact (hP.root_chain r) (((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).symm
  | some u =>
    simp only [ha, groupInput] at h
    split_ifs at h
    · exact (hP.fused_root k r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
    · exact (hP.root_chain r) (((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).symm

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
    simp only [ha, groupInput] at h
    split_ifs at h
    · exact (hP.fused_idx k) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
    · exact hP.codec.chain_idx ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem rootInput_ne_idxInput (hP : P.Hyp) (t : Tops) (r : Fin 1) (st : BitVec 256)
    (m : Message) (η : Nonce) (pk : PublicKey) : P.rootInput t r st ≠ P.codec.idxInput m η pk := by
  intro h
  unfold rootInput at h
  exact (hP.root_idx r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

end Params
end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
