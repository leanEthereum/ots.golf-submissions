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
* the index of an answer `idxOf w` (the low 127 bits, as a natural number), the accepted
  indices `validSet`, with `validSet.card = numValid` (`card_validSet`);
* `card_idxOf_mem`: each index value is the index of exactly `2 ^ 127` answers.
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
abbrev EncInput := BitVec (emsgBits + 127)

/-- The extended message of `m` under the public key `pk`. -/
def emsg (m : Message) (pk : PublicKey) : EMessage := m ++ pk

theorem append_pair_inj {m m' : EMessage} {η η' : Nonce} (h : m ++ η = m' ++ η') :
    m = m' ∧ η = η' := append_inj h

theorem append_nonce_inj (m : EMessage) {η η' : Nonce} (h : m ++ η = m ++ η') : η = η' :=
  (append_inj h).2

theorem exists_append (u : EncInput) : ∃ (m : EMessage) (η : Nonce), u = m ++ η := by
  refine ⟨u.extractLsb' 127 emsgBits, u.extractLsb' 0 127, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split_ifs with h
  · simp [BitVec.getLsbD_extractLsb', h]
  · rw [BitVec.getLsbD_extractLsb']
    have : i - 127 < emsgBits := by omega
    simp [this, show 127 + (i - 127) = i by omega]

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
  ⟨896, P.idxInput ((u.extractLsb' 127 emsgBits).extractLsb' pkBits msgBits)
    (u.extractLsb' 0 127) ((u.extractLsb' 127 emsgBits).extractLsb' 0 pkBits)⟩

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
  exact ⟨hm, nonceWord_injective hη, hpk⟩

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

theorem rootInput_ne_encQuery (hP : P.Hyp) {r : ℕ} (hr : r < 7) (t : Fin numChains → Word)
    (st : BitVec 256) (u : EncInput) : (⟨896, P.rootInput t r st⟩ : Query) ≠ P.encQuery u := by
  intro h
  exact P.rootInput_ne_idxInput hP hr t st _ _ _ (query_inj h)

theorem record_query_ne_encQuery (hP : P.Hyp) (ξ : Record P) (a : Loc P) (ha : ξ.ValidAt a)
    (u : EncInput) : ξ.query a ≠ P.encQuery u := by
  obtain ⟨M, η, rfl⟩ := exists_append u
  obtain ⟨m, pk, rfl⟩ := exists_emsg M
  rw [encQuery_emsg]
  exact ξ.query_ne_idx hP a ha m η pk

/-- Every encoding query is an index query. -/
theorem isIdxQuery_encQuery (u : EncInput) : IsIdxQuery P (P.encQuery u) := by
  obtain ⟨M, η, rfl⟩ := exists_append u
  obtain ⟨m, pk, rfl⟩ := exists_emsg M
  exact ⟨m, η, pk, P.encQuery_emsg m pk η⟩

/-- A decoded query is not an encoding query. -/
theorem not_enc_of_queryLocation (hP : P.Hyp) {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (u : EncInput) : q ≠ P.encQuery u := by
  obtain ⟨M, η, rfl⟩ := exists_append u
  obtain ⟨m, pk, rfl⟩ := exists_emsg M
  rw [encQuery_emsg]
  exact not_idx_of_queryLocation hP hl m η pk

/-! ## Indices -/

/-- The index of an answer: its low 127 bits as a number. -/
def idxOf (w : BitVec hashBits) : ℕ := (indexSlice w).toNat

theorem idxOf_lt (w : BitVec hashBits) : idxOf w < 2 ^ 127 := (indexSlice w).isLt

/-- The accepted indices. -/
def validSet : Finset ℕ := (Finset.range (2 ^ 127)).filter fun n => P.Accepted (BitVec.ofNat 127 n)

/-- An accepted index. -/
abbrev Idx : Type := {i : ℕ // i ∈ P.validSet}

/-- The word of an index. -/
def idxWord (i : ℕ) : Index := BitVec.ofNat 127 i

theorem idxWord_idxOf (w : BitVec hashBits) : idxWord (idxOf w) = indexSlice w := by
  unfold idxWord idxOf
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mem_validSet_lt {i : ℕ} (h : i ∈ P.validSet) : i < 2 ^ 127 := by
  unfold validSet at h
  exact Finset.mem_range.mp (Finset.mem_filter.mp h).1

theorem mem_validSet_iff (w : BitVec hashBits) :
    idxOf w ∈ P.validSet ↔ P.Accepted (indexSlice w) := by
  unfold validSet
  rw [Finset.mem_filter, ← idxWord, idxWord_idxOf]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.mpr (idxOf_lt w), h⟩⟩

theorem accepted_of_mem {i : ℕ} (h : i ∈ P.validSet) : P.Accepted (idxWord i) := by
  unfold validSet at h
  exact (Finset.mem_filter.mp h).2

theorem card_validSet : P.validSet.card = P.numValid := by
  unfold validSet numValid
  refine Finset.card_bij' (fun n _ => BitVec.ofNat 127 n) (fun I _ => I.toNat) ?_ ?_ ?_ ?_
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

theorem numValid_le' : P.numValid ≤ 2 ^ 127 := by
  rw [← card_validSet]
  calc P.validSet.card ≤ (Finset.range (2 ^ 127)).card := Finset.card_filter_le _ _
    _ = 2 ^ 127 := Finset.card_range _

end Params

/-- Every effective 127-bit index has exactly 2^129 full-answer preimages. -/
theorem card_idxOf_mem (A : Finset ℕ) (hA : ∀ n ∈ A, n < 2 ^ 127) :
    (Finset.univ.filter fun y : BitVec hashBits => Params.idxOf y ∈ A).card =
      A.card * 2 ^ (hashBits - 127) := by
  have hc : (Finset.univ.filter fun i : Index => i.toNat ∈ A).card = A.card := by
    refine Finset.card_nbij' (fun i : Index => i.toNat)
      (fun n => BitVec.ofNat 127 n) ?_ ?_ ?_ ?_
    · intro i hi
      simpa only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_coe] using hi
    · intro n hn
      simp only [Finset.mem_coe] at hn
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hA n hn)]
      exact hn
    · intro i _
      change BitVec.ofNat 127 i.toNat = i
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · intro n hn
      exact Nat.mod_eq_of_lt (hA n hn)
  change (Finset.univ.filter fun y : BitVec 256 => (indexSlice y).toNat ∈ A).card = _
  rw [card_indexSlice (fun i : Index => i.toNat ∈ A), hc]
  rfl

theorem sum_fin_equivFin {α : Type*} {s : Finset α} {n : ℕ} (h : n = s.card) (G : α → ℝ≥0∞) :
    ∑ j : Fin n, G (s.equivFin.symm (Fin.cast h j)).1 = ∑ η ∈ s, G η := by
  rw [← Finset.sum_coe_sort s]
  exact Equiv.sum_comp ((finCongr h).trans s.equivFin.symm) (fun x => G x.1)

end OptimalOTS.LeanIsaBaseline.Layer
