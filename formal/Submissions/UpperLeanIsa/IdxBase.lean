import Submissions.UpperLeanIsa.Records
import Submissions.UpperLeanIsa.LayerAvailability
import Submissions.UpperLeanIsa.Master

/-!
# Index queries of a layer scheme

The vocabulary of the index-grinding analysis, ported from UpperRiscv (`SignIdx`, `Valid`):

* an *extended message* `emsg m pk = m ++ pk` and an *encoding input* `M ++ η`; the encoding
  query `encQuery (M ++ η)` is the index query `idxInput m η pk` (`encQuery_emsg`). Unlike the
  RISC-V layout, every leanISA query has 896 bits, so encoding queries are told apart from chain
  and root queries by their metadata (`chainInput_ne_encQuery`, `rootInput_ne_encQuery`), not by
  their length;
* the index of an answer `idxOf w` (the low 128 bits, as a natural number), the accepted
  indices `validSet`, with `validSet.card = numValid` (`card_validSet`);
* `card_idxOf_mem`: each index value is the index of exactly `2 ^ 128` answers.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

/-- The width of an extended message: the message above the public key. -/
abbrev emsgBits : ℕ := msgBits + pkBits

/-- An extended message. -/
abbrev EMessage := BitVec emsgBits

/-- An encoding input: an extended message above a nonce. -/
abbrev EncInput := BitVec (emsgBits + 128)

/-- The extended message of `m` under the public key `pk`. -/
def emsg (m : Message) (pk : PublicKey) : EMessage := m ++ pk

theorem append_pair_inj {m m' : EMessage} {η η' : Nonce} (h : m ++ η = m' ++ η') :
    m = m' ∧ η = η' := append_inj h

theorem append_nonce_inj (m : EMessage) {η η' : Nonce} (h : m ++ η = m ++ η') : η = η' :=
  (append_inj h).2

theorem exists_append (u : EncInput) : ∃ (m : EMessage) (η : Nonce), u = m ++ η := by
  refine ⟨u.extractLsb' 128 emsgBits, u.extractLsb' 0 128, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split_ifs with h
  · simp [BitVec.getLsbD_extractLsb', h]
  · rw [BitVec.getLsbD_extractLsb']
    have : i - 128 < emsgBits := by omega
    simp [this, show 128 + (i - 128) = i by omega]

theorem emsg_inj {m m' : Message} {pk pk' : PublicKey} (h : emsg m pk = emsg m' pk') :
    m = m' ∧ pk = pk' := append_inj h

theorem exists_emsg (M : EMessage) : ∃ (m : Message) (pk : PublicKey), M = emsg m pk := by
  refine ⟨M.extractLsb' pkBits msgBits, M.extractLsb' 0 pkBits, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold emsg
  rw [BitVec.getLsbD_append]
  split_ifs with h
  · simp [BitVec.getLsbD_extractLsb', h]
  · rw [BitVec.getLsbD_extractLsb']
    have : i - pkBits < msgBits := by unfold emsgBits at hi; omega
    simp [this, show pkBits + (i - pkBits) = i by omega]

namespace Params

variable (P : Params)

/-- The index query of an encoding input `emsg m pk ++ η`. -/
def encQuery (u : EncInput) : Query :=
  ⟨896, P.idxInput ((u.extractLsb' 128 emsgBits).extractLsb' pkBits msgBits)
    (u.extractLsb' 0 128) ((u.extractLsb' 128 emsgBits).extractLsb' 0 pkBits)⟩

theorem encQuery_emsg (m : Message) (pk : PublicKey) (η : Nonce) :
    P.encQuery (emsg m pk ++ η) = ⟨896, P.idxInput m η pk⟩ := by
  unfold encQuery emsg
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

theorem idxInput_inj {m m' : Message} {η η' : Nonce} {pk pk' : PublicKey}
    (h : P.idxInput m η pk = P.idxInput m' η' pk') : m = m' ∧ η = η' ∧ pk = pk' := by
  have hb := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.1
  obtain ⟨h1, hm⟩ := append_inj hb
  obtain ⟨hpk, hη⟩ := append_inj h1
  exact ⟨hm, hη, hpk⟩

theorem encQuery_inj {u u' : EncInput} (h : P.encQuery u = P.encQuery u') : u = u' := by
  obtain ⟨M, η, rfl⟩ := exists_append u
  obtain ⟨M', η', rfl⟩ := exists_append u'
  obtain ⟨m, pk, rfl⟩ := exists_emsg M
  obtain ⟨m', pk', rfl⟩ := exists_emsg M'
  rw [encQuery_emsg, encQuery_emsg] at h
  obtain ⟨hm, hη, hpk⟩ := P.idxInput_inj (query_inj h)
  rw [hm, hη, hpk]

theorem idx_eq_encQuery (m : Message) (η : Nonce) (pk : PublicKey) :
    (⟨896, P.idxInput m η pk⟩ : Query) = P.encQuery (emsg m pk ++ η) :=
  (P.encQuery_emsg m pk η).symm

theorem chainInput_ne_encQuery (hP : P.Hyp) (k : Fin numChains) (j : ℕ) (x : Word)
    (u : EncInput) : (⟨896, P.chainInput k j x⟩ : Query) ≠ P.encQuery u := by
  intro h
  exact P.chainInput_ne_idxInput hP k j x _ _ _ (query_inj h)

theorem rootInput_ne_encQuery (hP : P.Hyp) {r : ℕ} (hr : r < 9) (t : Fin numChains → Word)
    (st : BitVec 256) (u : EncInput) : (⟨896, P.rootInput t r st⟩ : Query) ≠ P.encQuery u := by
  intro h
  exact P.rootInput_ne_idxInput hP hr t st _ _ _ (query_inj h)

theorem record_query_ne_encQuery (hP : P.Hyp) (ξ : Record P) (a : Loc P) (u : EncInput) :
    ξ.query a ≠ P.encQuery u := by
  obtain ⟨M, η, rfl⟩ := exists_append u
  obtain ⟨m, pk, rfl⟩ := exists_emsg M
  rw [encQuery_emsg]
  exact ξ.query_ne_idx hP a m η pk

/-! ## Indices -/

/-- The index of an answer: its low 128 bits as a number. -/
def idxOf (w : BitVec hashBits) : ℕ := (w.extractLsb' 0 128).toNat

theorem idxOf_lt (w : BitVec hashBits) : idxOf w < 2 ^ 128 := (w.extractLsb' 0 128).isLt

/-- The accepted indices. -/
def validSet : Finset ℕ := (Finset.range (2 ^ 128)).filter fun n => P.Accepted (BitVec.ofNat 128 n)

/-- An accepted index. -/
abbrev Idx : Type := {i : ℕ // i ∈ P.validSet}

/-- The word of an index. -/
def idxWord (i : ℕ) : Word := BitVec.ofNat 128 i

theorem idxWord_idxOf (w : BitVec hashBits) : idxWord (idxOf w) = w.extractLsb' 0 128 := by
  unfold idxWord idxOf
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mem_validSet_lt {i : ℕ} (h : i ∈ P.validSet) : i < 2 ^ 128 := by
  unfold validSet at h
  exact Finset.mem_range.mp (Finset.mem_filter.mp h).1

theorem mem_validSet_iff (w : BitVec hashBits) :
    idxOf w ∈ P.validSet ↔ P.Accepted (w.extractLsb' 0 128) := by
  unfold validSet
  rw [Finset.mem_filter, ← idxWord, idxWord_idxOf]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.mpr (idxOf_lt w), h⟩⟩

theorem accepted_of_mem {i : ℕ} (h : i ∈ P.validSet) : P.Accepted (idxWord i) := by
  unfold validSet at h
  exact (Finset.mem_filter.mp h).2

theorem card_validSet : P.validSet.card = P.numValid := by
  unfold validSet numValid
  refine Finset.card_bij' (fun n _ => BitVec.ofNat 128 n) (fun I _ => I.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
    exact hn.2
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨I.isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hI⟩
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn.1]
  · intro I _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem numValid_le' : P.numValid ≤ 2 ^ 128 := by
  rw [← card_validSet]
  calc P.validSet.card ≤ (Finset.range (2 ^ 128)).card := Finset.card_filter_le _ _
    _ = 2 ^ 128 := Finset.card_range _

end Params

/-- Number of oracle answers whose index lies in a set of index values. -/
theorem card_idxOf_mem (A : Finset ℕ) (hA : ∀ n ∈ A, n < 2 ^ 128) :
    (Finset.univ.filter fun y : BitVec hashBits => Params.idxOf y ∈ A).card =
      A.card * 2 ^ (hashBits - 128) := by
  have hhb : hashBits = 256 := rfl
  have hH : 2 ^ hashBits = 2 ^ 128 * 2 ^ (hashBits - 128) := by
    rw [← pow_add, hhb]
  have hNpos : 0 < 2 ^ 128 := by positivity
  have hlow : ∀ y : BitVec hashBits, Params.idxOf y = y.toNat % 2 ^ 128 := by
    intro y
    unfold Params.idxOf
    rw [← BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.ushiftRight_zero,
      BitVec.toNat_setWidth]
  rw [← Finset.card_range (2 ^ (hashBits - 128)), ← Finset.card_product]
  refine Finset.card_nbij' (fun y => (y.toNat % 2 ^ 128, y.toNat / 2 ^ 128))
    (fun x => BitVec.ofNat hashBits (x.1 + 2 ^ 128 * x.2)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · rw [← hlow]; exact hy
    · rw [Nat.div_lt_iff_lt_mul hNpos]
      have := y.isLt
      rw [hH] at this
      linarith
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    have h1 : x.1 + 2 ^ 128 * x.2 < 2 ^ hashBits := by
      rw [hH]
      have := hA _ hx.1
      nlinarith
    rw [hlow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hA _ hx.1)]
    exact hx.1
  · intro y _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_add_div, Nat.mod_eq_of_lt y.isLt]
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    have hx1 := hA _ hx.1
    have h1 : x.1 + 2 ^ 128 * x.2 < 2 ^ hashBits := by
      rw [hH]
      nlinarith
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hx1, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hx1, zero_add]

theorem sum_fin_equivFin {α : Type*} {s : Finset α} {n : ℕ} (h : n = s.card) (G : α → ℝ≥0∞) :
    ∑ j : Fin n, G (s.equivFin.symm (Fin.cast h j)).1 = ∑ η ∈ s, G η := by
  rw [← Finset.sum_coe_sort s]
  exact Equiv.sum_comp ((finCongr h).trans s.equivFin.symm) (fun x => G x.1)

end OptimalOTS.LeanIsaBaseline.Layer
