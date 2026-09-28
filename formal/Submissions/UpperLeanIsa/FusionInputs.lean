import Submissions.UpperLeanIsa.FusionShape

/-! Dependency-aware hash inputs. Syntactic domain separation identifies a unique
chain location or root call even when the dependency words differ. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OptimalOTS
open scoped Classical
noncomputable section

abbrev Tops := ℕ → Word

/-- The group whose positive final steps bind a dependency bundle. -/
def owner (k : Fin 42) : Option (Fin 7) :=
  if k.val ∈ parents 0 then some 0 else if k.val ∈ parents 1 then some 1
  else if k.val ∈ parents 2 then some 2 else if k.val ∈ parents 3 then some 3
  else if k.val ∈ parents 4 then some 4 else if k.val ∈ parents 5 then some 5
  else if k.val ∈ parents 6 then some 6 else none

theorem owner_mem : ∀ k : Fin 42, ∀ u : Fin 7, owner k = some u ↔ k.val ∈ parents u := by
  decide

structure Params where
  codec : Layer.Params
  fusedMd : Fin 42 → Word
  rootMd : Fin 2 → Word
  lightCv : BitVec 256

namespace Params
variable (P : Params)

def active (k : Fin 42) (j : ℕ) : Option (Fin 7) :=
  if j + 2 = P.codec.len k then owner k else none

theorem active_final {k : Fin 42} {j : ℕ} {u : Fin 7} (h : P.active k j = some u) :
    j + 2 = P.codec.len k := by
  unfold active at h
  split_ifs at h with he
  · exact he

/-- A light final step is an ordinary step with cv `lightCv` and top 7 in place of tag `A`. -/
def groupInput (t : Tops) (u : Fin 7) (k : Fin 42) (j : ℕ) (x : Word) : BitVec 896 :=
  if u.val = 6 then lightPacket P.lightCv (P.codec.tag k j 1) (P.codec.tag k j 2) t x P.codec.chainMd
  else packet (fusionWords t u x (P.fusedMd k))

def chainInput (t : Tops) (k : Fin 42) (j : ℕ) (x : Word) : BitVec 896 :=
  match P.active k j with
  | none => P.codec.chainInput k j x
  | some u => P.groupInput t u k j x

def rootInput (t : Tops) (r : Fin 2) (st : BitVec 256) : BitVec 896 :=
  if r.val = 0 then LeanIsa.hashInput (t 2 ++ t 1) (t 6 ++ t 5 ++ t 4 ++ t 3) (P.rootMd r)
  else LeanIsa.hashInput (st.extractLsb' 0 128 ++ t 26)
    (t 11 ++ t 10 ++ t 9 ++ t 8) (P.rootMd r)

structure Hyp : Prop where
  codec : P.codec.Hyp
  fused_inj : Function.Injective P.fusedMd
  fused_chain : ∀ k, P.fusedMd k ≠ P.codec.chainMd
  fused_idx : ∀ k, P.fusedMd k ≠ P.codec.idxMd
  fused_root : ∀ k r, P.fusedMd k ≠ P.rootMd r
  root_inj : Function.Injective P.rootMd
  root_chain : ∀ r, P.rootMd r ≠ P.codec.chainMd
  root_idx : ∀ r, P.rootMd r ≠ P.codec.idxMd
  light_cv : P.lightCv ≠ P.codec.cv
  /-- Tags `B, C` of the final steps separate the light parents. -/
  light_tag : ∀ k k' : Fin 42, owner k = some 6 → owner k' = some 6 →
    P.codec.tag k (P.codec.len k - 2) 1 = P.codec.tag k' (P.codec.len k' - 2) 1 →
    P.codec.tag k (P.codec.len k - 2) 2 = P.codec.tag k' (P.codec.len k' - 2) 2 → k = k'

variable {P}

theorem groupInput_binds {u : Fin 7} {k : Fin 42} {j : ℕ} (t t' : Tops) (x y : Word)
    (h : P.groupInput t u k j x = P.groupInput t' u k j y) : GroupBinds t t' u := by
  unfold groupInput at h
  split_ifs at h with h6
  · rw [show u.val = 6 from h6]
    exact light_binds h
  · exact fusion_binds_children t t' (by omega) x y _ _ h

theorem groupInput_current {u : Fin 7} {k : Fin 42} {j : ℕ} (t t' : Tops) (x y : Word)
    (h : P.groupInput t u k j x = P.groupInput t' u k j y) : x = y := by
  unfold groupInput at h
  split_ifs at h
  · exact light_current h
  · exact congrFun (packet_injective h) 2

theorem owner_light {k : Fin 42} {j : ℕ} (h : P.active k j = some 6) : owner k = some 6 := by
  unfold active at h
  split_ifs at h
  exact h

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
      · exact (hP.light_cv ((hashInput_eq_iff _ _ _ _ _ _).mp h).1.symm).elim
      · exact (hP.fused_chain k' ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2.symm).elim
  | some u =>
    cases hb : P.active k' j' with
    | none =>
      simp only [ha, hb, groupInput] at h
      split_ifs at h
      · exact (hP.light_cv ((hashInput_eq_iff _ _ _ _ _ _).mp h).1).elim
      · exact (hP.fused_chain k ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).elim
    | some v =>
      simp only [ha, hb, groupInput] at h
      have hjk := P.active_final ha
      have hjk' := P.active_final hb
      split_ifs at h with hu hv hv
      · obtain ⟨-, hb1, hc2, -, hx, -⟩ := lightPacket_eq h
        have hu6 : u = 6 := Fin.ext hu
        have hv6 : v = 6 := Fin.ext hv
        subst hu6 hv6
        rw [show j = P.codec.len k - 2 by omega, show j' = P.codec.len k' - 2 by omega] at hb1 hc2
        have hk := hP.light_tag k k' (owner_light ha) (owner_light hb) hb1 hc2
        subst k'
        exact ⟨rfl, by omega, hx⟩
      · exact (hP.fused_chain k' ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2.symm).elim
      · exact (hP.fused_chain k ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).elim
      · have hk := hP.fused_inj ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
        subst k'
        exact ⟨rfl, by omega, congrFun (packet_injective h) 2⟩

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

theorem rootInput_location (hP : P.Hyp) (t t' : Tops) (r s : Fin 2) (st st' : BitVec 256)
    (h : P.rootInput t r st = P.rootInput t' s st') : r = s := by
  apply hP.root_inj
  unfold rootInput at h
  split_ifs at h <;> exact ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem chainInput_ne_rootInput (hP : P.Hyp) (t t' : Tops) (k : Fin 42) (j : ℕ)
    (x : Word) (r : Fin 2) (st : BitVec 256) : P.chainInput t k j x ≠ P.rootInput t' r st := by
  intro h
  unfold chainInput rootInput at h
  cases ha : P.active k j with
  | none =>
    simp only [ha] at h
    split_ifs at h <;> exact (hP.root_chain r) (((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).symm
  | some u =>
    simp only [ha, groupInput] at h
    split_ifs at h
    · exact (hP.root_chain r) (((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).symm
    · exact (hP.root_chain r) (((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2).symm
    · exact (hP.fused_root k r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
    · exact (hP.fused_root k r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

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
    · exact hP.codec.chain_idx ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
    · exact (hP.fused_idx k) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem rootInput_ne_idxInput (hP : P.Hyp) (t : Tops) (r : Fin 2) (st : BitVec 256)
    (m : Message) (η : Nonce) (pk : PublicKey) : P.rootInput t r st ≠ P.codec.idxInput m η pk := by
  intro h
  unfold rootInput at h
  split_ifs at h <;> exact (hP.root_idx r) ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

end Params
end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
