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
  their length.
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

end Params

theorem sum_fin_equivFin {α : Type*} {s : Finset α} {n : ℕ} (h : n = s.card) (G : α → ℝ≥0∞) :
    ∑ j : Fin n, G (s.equivFin.symm (Fin.cast h j)).1 = ∑ η ∈ s, G η := by
  rw [← Finset.sum_coe_sort s]
  exact Equiv.sum_comp ((finCongr h).trans s.equivFin.symm) (fun x => G x.1)

end OptimalOTS.LeanIsaBaseline.Layer
