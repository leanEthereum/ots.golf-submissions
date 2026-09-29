import Submissions.UpperLeanIsa.FreeLastBase
import Submissions.UpperLeanIsa.FourAdmissible
import Submissions.UpperLeanIsa.FourSecurity
import Submissions.UpperLeanIsa.FourActive
import Submissions.UpperLeanIsa.SplitDomains

namespace OptimalOTS.LeanIsaBaseline.Layer.FreeLastCodec
open LeanerVM.Parameters OptimalOTS.AffineFrames
noncomputable section
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def word (i : ℕ) : Word := LeanIsa.cellBits (ofK (FreeLastBase.base ^ i))

theorem word_eq (i : ℕ) : word i = (0 : BitVec 64) ++ (FreeLastBase.base ^ i : K) := by
  unfold word LeanIsa.cellBits
  rw [limb_ofK, limb_ofK]
  simp

theorem word_inj {i j : ℕ} (hi : i ≤ 300) (hj : j ≤ 300)
    (h : word i = word j) : i = j := by
  rw [word_eq, word_eq] at h
  have h' : FreeLastBase.base ^ i = FreeLastBase.base ^ j := by
    simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (64 + 64) => z.extractLsb' 0 64) h
  exact FreeLastBase.powers_injective hi hj h'


def lengthWord : Word := LeanIsa.cellBits (ofK lengthK)

theorem word_ne_length {i : ℕ} (hi : i ≤ 14) : word i ≠ lengthWord := by
  intro h
  have hl : lengthWord = (0 : BitVec 64) ++ (lengthK : K) := by
    unfold lengthWord LeanIsa.cellBits
    rw [limb_ofK, limb_ofK]
    simp
  rw [word_eq, hl] at h
  have hk : FreeLastBase.base ^ i = lengthK := by
    simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (64 + 64) => z.extractLsb' 0 64) h
  by_cases hz : i = 0
  · subst i
    rw [pow_zero] at hk
    exact lengthK_ne_one hk.symm
  · exact FreeLastSelect.length_ne FreeLastBase.layout (by omega) hi hk

def domainWord (i : ℕ) : Word := if i = 17 then lengthWord else word i

theorem domainWord_inj {i j : ℕ} (hi : i ≤ 14 ∨ i = 17) (hj : j ≤ 14 ∨ j = 17)
    (h : domainWord i = domainWord j) : i = j := by
  by_cases hi17 : i = 17
  · by_cases hj17 : j = 17
    · omega
    · have hj14 : j ≤ 14 := hj.resolve_right hj17
      have he : lengthWord = word j := by simpa [domainWord, hi17, hj17] using h
      exact (word_ne_length hj14 he.symm).elim
  · by_cases hj17 : j = 17
    · have hi14 : i ≤ 14 := hi.resolve_right hi17
      have he : word i = lengthWord := by simpa [domainWord, hi17, hj17] using h
      exact (word_ne_length hi14 he).elim
    · apply word_inj (by rcases hi with h | h <;> omega) (by rcases hj with h | h <;> omega)
      simpa [domainWord, hi17, hj17] using h

def tag (k : Fin numChains) (j : ℕ) : Fin 3 → Word :=
  ![word  ((FourChildCodec.off k + j) % 9),
    word  ((FourChildCodec.off k + j) / 9 % 9),
    word  ((FourChildCodec.off k + j) / 81)]

/-- Existing adjacent C1/C2 cells supply the normal chaining value; C11 separates the index. -/
def codec : Layer.Params := { FourChildCodec.params with
  tag := tag
  cv := word  2 ++ word  1
  chainMd := word  0
  idxMd := word  11
  rootMd r := word  (15+r) }

theorem tag_inj (k k' : Fin numChains) (j j' : ℕ)
    (hj : j + 1 < FourChildCodec.len k) (hj' : j' + 1 < FourChildCodec.len k')
    (h0 : tag  k j 0 = tag  k' j' 0) (h1 : tag  k j 1 = tag  k' j' 1)
    (h2 : tag  k j 2 = tag  k' j' 2) : k = k' ∧ j = j' := by
  unfold FourChildCodec.len at hj hj'
  obtain ⟨hp, hl⟩ := FourChildCodec.pos_facts k k.isLt j (by omega)
  obtain ⟨hp', hl'⟩ := FourChildCodec.pos_facts k' k'.isLt j' (by omega)
  simp only [tag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have e0 := word_inj  (by omega) (by omega) h0
  have e1 := word_inj  (by omega) (by omega) h1
  have e2 := word_inj  (by omega) (by omega) h2
  have hpp : FourChildCodec.off k + j = FourChildCodec.off k' + j' := by omega
  rw [hpp, hl'] at hl
  obtain ⟨hk, hjj⟩ := Prod.mk.inj hl
  exact ⟨Fin.ext hk.symm, hjj.symm⟩

/-- `TierHyp` reads only `layer` and `digit`. Transporting it along these two field equations
keeps the kernel from comparing the two concrete parameter records. -/
theorem tierHyp_transport {P Q : Layer.Params} {S : Tier.Sched} (hl : P.layer = Q.layer)
    (hd : P.digit = Q.digit) (h : Q.TierHyp S) : P.TierHyp S := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := P
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := Q
  dsimp only at hl hd
  subst hl hd
  exact ⟨h.1, h.2, h.3⟩

theorem codec_layer : (codec ).layer = FourChildCodec.layer := rfl
theorem codec_digit : (codec ).digit = FourChildCodec.digit := rfl
theorem base_layer : FourChildCodec.params.layer = FourChildCodec.layer := rfl
theorem base_digit : FourChildCodec.params.digit = FourChildCodec.digit := rfl

theorem tierHyp : (codec ).TierHyp FourChildNumeric.schedule :=
  tierHyp_transport ((codec_layer ).trans base_layer.symm)
    ((codec_digit ).trans base_digit.symm) FourChildCodec.tierHyp

theorem codec_hyp : (codec ).Hyp where
  len_pos := FourChildCodec.hyp.len_pos
  digit_lt := FourChildCodec.hyp.digit_lt
  layer_pos := FourChildCodec.hyp.layer_pos
  tag_inj := tag_inj
  chain_idx := by
    intro h
    have := word_inj  (i:=0) (j:=11) (by decide) (by decide) h
    omega
  chain_root := by
    intro r hr h
    have := word_inj  (i:=0) (j:=15+r) (by omega) (by omega) h
    omega
  root_idx := by
    intro r hr h
    have := word_inj  (i:=15+r) (j:=11) (by omega) (by omega) h
    omega
  root_inj := by
    intro r s hr hs h
    have := word_inj  (i:=15+r) (j:=15+s) (by omega) (by omega) h
    omega
  tier := ⟨FourChildNumeric.schedule, FourChildNumeric.schedule_valid, tierHyp ⟩
  keygen_le := FourChildCodec.hyp.keygen_le
  verify_le := FourChildCodec.hyp.verify_le
  len_zero := FourChildCodec.hyp.len_zero

def params : FourFusion.Params where
  codec := codec
  fusedMd k := domainWord  (FourFusion.mdIndex k).val
  fusedTag k := word  (FourFusion.tagIndex k).val
  rootMd r := word  (FourFusion.rootIndex r).val

theorem md_reserved : ∀ k, FourFusion.mdIndex k ≠ 0 ∧ FourFusion.mdIndex k ≠ 11 ∧
    ∀ r, FourFusion.mdIndex k ≠ FourFusion.rootIndex r := by decide

theorem root_reserved : ∀ r, FourFusion.rootIndex r ≠ 0 ∧
    FourFusion.rootIndex r ≠ 11 := by decide

theorem word_fin_inj {i j : Fin 47} (h : word  i = word  j) : i = j :=
  Fin.ext (word_inj  (by have := i.isLt; omega) (by have := j.isLt; omega) h)

theorem params_hyp : (params ).Hyp where
  codec := codec_hyp
  fused_inj := FourFusion.packet_location (params )
    (fun a b h => Fin.ext (domainWord_inj  (FourFusion.mdIndex_bounds a)
      (FourFusion.mdIndex_bounds b) h))
    (fun a b h => word_fin_inj  h)
  fused_chain := by
    intro k h
    have hi := domainWord_inj  (FourFusion.mdIndex_bounds k) (Or.inl (by decide)) (j:=0) h
    exact (md_reserved k).1 (Fin.ext hi)
  fused_idx := by
    intro k h
    have hi := domainWord_inj  (FourFusion.mdIndex_bounds k) (Or.inl (by decide)) (j:=11) h
    exact (md_reserved k).2.1 (Fin.ext hi)
  fused_root := by
    intro k r h
    have hi := domainWord_inj  (FourFusion.mdIndex_bounds k) (Or.inl (by decide)) (j:=4) h
    exact (md_reserved k).2.2 r (Fin.ext hi)
  root_inj := fun _ _ _ => Subsingleton.elim _ _
  root_chain := fun r h => (root_reserved r).1 (word_fin_inj  h)
  root_idx := fun r h => (root_reserved r).2 (word_fin_inj  h)

/-- The location order and `Earlier` read only the chain lengths. -/
theorem ordered_transport {P Q : FourFusion.Params} (h : P.codec.len = Q.codec.len)
    (hQ : Q.locationOrder.Pairwise FourFusion.Earlier) :
    P.locationOrder.Pairwise FourFusion.Earlier := by
  obtain ⟨⟨len, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩, a₉, a₁₀, a₁₁⟩ := P
  obtain ⟨⟨_, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈⟩, b₉, b₁₀, b₁₁⟩ := Q
  dsimp only at h
  subst h
  exact hQ.imp (S := @FourFusion.Earlier ⟨⟨len, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩, a₉, a₁₀, a₁₁⟩)
    fun {a b} hab => by
      rcases a with ⟨k, j⟩ | r <;> rcases b with ⟨k', j'⟩ | r' <;> exact hab

theorem length_transport {P Q : FourFusion.Params} (h : P.codec.len = Q.codec.len) :
    P.locationOrder.length = Q.locationOrder.length := by
  obtain ⟨⟨_, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := P
  obtain ⟨⟨_, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := Q
  dsimp only at h
  subst h
  rfl

/-- The parent-binding condition reads only `layer` and `digit`. -/
theorem binding_transport {P Q : FourFusion.Params} (hl : P.codec.layer = Q.codec.layer)
    (hd : P.codec.digit = Q.codec.digit)
    (h : ∀ I, Q.codec.Accepted I → ∀ u : Fin 8,
      ∃ k : Fin 42, k.val ∈ FourFusion.parents u ∧ 0 < Q.codec.digit I k) :
    ∀ I, P.codec.Accepted I → ∀ u : Fin 8,
      ∃ k : Fin 42, k.val ∈ FourFusion.parents u ∧ 0 < P.codec.digit I k := by
  obtain ⟨⟨_, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := P
  obtain ⟨⟨_, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := Q
  dsimp only at hl hd
  subst hl hd
  exact h

theorem params_len : (params ).codec.len = FourChildCodec.len := rfl
theorem base_len : FourFusion.params.codec.len = FourChildCodec.len := rfl
theorem params_layer : (params ).codec.layer = FourChildCodec.layer := rfl
theorem params_digit : (params ).codec.digit = FourChildCodec.digit := rfl
theorem four_layer : FourFusion.params.codec.layer = FourChildCodec.layer := rfl
theorem four_digit : FourFusion.params.codec.digit = FourChildCodec.digit := rfl

theorem ordered : (params ).locationOrder.Pairwise FourFusion.Earlier :=
  ordered_transport ((params_len ).trans base_len.symm) FourFusion.concrete_ordered

theorem location_count : (params ).locationOrder.length = 720 :=
  (length_transport ((params_len ).trans base_len.symm)).trans
    FourFusion.concrete_location_count

theorem securityHyp : (params ).SecurityHyp where
  toHyp := params_hyp
  ordered := ordered
  binding := binding_transport ((params_layer ).trans four_layer.symm)
    ((params_digit ).trans four_digit.symm) FourFusion.accepted_parent

theorem admissible : (params ).scheme.Admissible :=
  (params ).admissible (params_hyp ) (ordered ) FourChildNumeric.schedule_valid (tierHyp )
    (by rw [location_count]; decide) (by change 4 + 2 * 85 ≤ verifyBudget; decide)

theorem secure : (params ).scheme.Secure := (params ).secure (securityHyp )

end
end OptimalOTS.LeanIsaBaseline.Layer.FreeLastCodec
