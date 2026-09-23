import Submissions.UpperRiscv.Tree
import Submissions.UpperRiscv.Keygen
import Submissions.UpperRiscv.SignIdx

/-!
# Values of the concrete scheme

For a record `ξ : Rec` (sources and hash outputs), `val ξ n` is the value of node `n` in the
honest evaluation `graph.evalRec ξ`.  This file gives the explicit formulas (`val_src`, …,
`val_rh`), describes the keygen cache (`kc ξ`) through the keygen points `pointOf ξ h p` of the
hash nodes, splits it into the exposed and hidden parts relative to a disclosure set
(`fExp`, `fHid`), defines the event `Spr` (a cached answer at a non-keygen point that begins with
the honest output of a hash node with an input of that length), and records which record
coordinates each value depends on (`deps`), with the two coordinate updates `updSrc` and
`updHash`.

The oracle has no labels and the scheme uses none. A keygen point is the bare input
`⟨p.len, val ξ p⟩` of a hash node. Points of distinct hash nodes are distinct only for *good*
records (`DistinctRec`), which is all but a `2 ^ (-173)` fraction of them; every statement that
needs the keygen cache to be read back node by node assumes it. A keygen point never has the
length of an index query (`pointOf_ne_encQuery`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

/-- Records of the concrete graph. -/
abbrev Rec := graph.Rec

/-- The value of node `n` in the record `ξ`. -/
def val (ξ : Rec) (n : Name) : BitVec n.len := (graph.evalRec ξ n.fin).cast (graph_len_fin n)

/-! ### Auxiliary cast lemmas -/

theorem trunc_cast (k : Fin 32) {n m : ℕ} (h : n = m) (x : BitVec n) : trunc k (x.cast h) = trunc k x := by
  subst h; rfl

theorem trunc_eq_self (k : Fin 32) (x : BitVec (chainBits k)) : trunc k x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [trunc, BitVec.getLsbD_extractLsb', hi]

theorem trunc_trunc (k : Fin 32) {n : ℕ} (x : BitVec n) : trunc k (trunc k x) = trunc k x := trunc_eq_self k _

/-- On a hash output, `trunc k` is the state-width slice starting at bit `truncOff k`. -/
theorem trunc_256 (k : Fin 32) (x : BitVec 256) :
    trunc k x = x.extractLsb' (truncOff k) (chainBits k) := by
  unfold trunc
  rw [Nat.min_eq_left (by have := truncOff_add_le k; omega : truncOff k ≤ 256 - chainBits k)]

theorem cast_cast_eq {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x := by
  subst h₁; rfl

/-- The node equation of the concrete graph, with the kind computed by `kindOf`. -/
theorem evalRec_apply_fin (ξ : Rec) (n : Name) :
    graph.evalRec ξ n.fin =
      (kindOf n.fin n (ofFin_fin n)).value (graph.evalRec ξ) (ξ.1 n.fin) (ξ.2 n.fin) := by
  have := Graph.evalRec_apply graph ξ n.fin
  rwa [graph_kind_fin] at this

theorem trunc_evalRec (k : Fin 32) (ξ : Rec) (n : Name) : trunc k (graph.evalRec ξ n.fin) = trunc k (val ξ n) := by
  unfold val
  exact (trunc_cast k _ _).symm

theorem val_src (ξ : Rec) (k : Fin 32) : val ξ (src k) = (ξ.1 (src k).fin).cast (graph_len_fin _) := by
  unfold val
  rw [evalRec_apply_fin]
  rfl

/-- Truncation loses nothing on a value of 192 bits. -/
theorem trunc_injective_of_len (k : Fin 32) {w : ℕ} (hw : w = chainBits k) :
    Function.Injective (trunc k : BitVec w → BitVec (chainBits k)) := by
  subst hw
  intro x y e
  rwa [trunc_eq_self, trunc_eq_self] at e

/-- The input of the chain hash `ch k t`: the high 192 bits of the value of `prev k t`. -/
theorem val_ci (ξ : Rec) (k : Fin 32) (t : Fin 32) :
    val ξ (ci k t) = trunc k (val ξ (prev k t)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show trunc k (graph.evalRec ξ (prev k t).fin) = _
  rw [trunc_evalRec]
  rfl

theorem val_ch (ξ : Rec) (k : Fin 32) (t : Fin 32) : val ξ (ch k t) = ξ.2 (ch k t).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem trunc_val_ch (ξ : Rec) (k : Fin 32) (t : Fin 32) :
    trunc k (graph.evalRec ξ (ch k t).fin) = trunc k (ξ.2 (ch k t).fin) := by
  rw [trunc_evalRec, val_ch]
  rfl

/-- The value node of a level carries the full hash output. -/
theorem val_cv (ξ : Rec) (k : Fin 32) (t : Fin 32) : val ξ (cv k t) = ξ.2 (ch k t).fin := by
  apply BitVec.eq_of_toNat_eq
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value, detVal_cv, BitVec.toNat_cast]
  have h := evalRec_apply_fin ξ (ch k t)
  simp only [kindOf, NodeKind.value] at h
  rw [h]
  rfl

theorem trunc_val_cv (ξ : Rec) (k : Fin 32) (t : Fin 32) :
    trunc k (graph.evalRec ξ (cv k t).fin) = trunc k (ξ.2 (ch k t).fin) := by
  rw [trunc_evalRec, val_cv]
  rfl

/-- The first chain input reads the source. -/
theorem val_ci_zero (ξ : Rec) (k : Fin 32) (t : Fin 32) (ht : t.val = 0) :
    val ξ (ci k t) = val ξ (src k) := by
  have e : prev k t = src k := by simp [Name.prev, ht]
  rw [val_ci, e]
  exact trunc_eq_self k _

/-- A later chain input reads the previous chain hash. -/
theorem val_ci_succ (ξ : Rec) (k : Fin 32) (t : Fin 32) (ht : ¬ t.val = 0) :
    val ξ (ci k t) = trunc k (ξ.2 (ch k ⟨t.val - 1, by omega⟩).fin) := by
  have e : prev k t = cv k ⟨t.val - 1, by omega⟩ := by simp [Name.prev, ht]
  rw [val_ci, e, val_cv]
  rfl

theorem val_rc (ξ : Rec) : val ξ rc = rootCat fun k => ξ.2 (ch k 31).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show rootCat (fun k => (graph.evalRec ξ (cv k 31).fin).cast _) = _
  refine congrArg rootCat (funext fun k => ?_)
  have := val_cv ξ k 31
  unfold val at this
  exact this

theorem val_rh (ξ : Rec) : val ξ rh = ξ.2 rh.fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

/-- The 128-bit truncation. -/
def trunc128 {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

/-- The public key of a record: the first 128 bits of the root. -/
def pkOf (ξ : Rec) : BitVec 128 := trunc128 (ξ.2 rh.fin)

/-! ## Hash nodes and keygen points -/

/-- The node whose value a hash node hashes: its input. -/
def hashParent : Name → Option Name
  | ch k t => some (ci k t)
  | rh => some rc
  | _ => none

theorem hashParent_isSome_iff (h : Name) : (hashParent h).isSome ↔ h.cost ≠ 0 := by
  cases h <;> simp [hashParent, Name.cost]

theorem cost_ne_zero_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.cost ≠ 0 :=
  (hashParent_isSome_iff h).1 (by rw [hp]; rfl)

theorem child_hashParent {h p : Name} (hp : hashParent h = some p) : child p = some h := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  all_goals rfl

/-- The input of a hash node has length 152, 160, 192 (chains) or 6144 (root). -/
theorem len_hashParent_cases {h p : Name} (hp : hashParent h = some p) :
    p.len = 152 ∨ p.len = 160 ∨ p.len = 192 ∨ p.len = 6144 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · rename_i k t
    rcases chainBits_cases k with hk | hk | hk <;> simp [Name.len, hk]
  · simp [Name.len]

/-- Key generation and indexing use disjoint input lengths. -/
theorem len_hashParent_ne_enc {h p : Name} (hp : hashParent h = some p) :
    p.len ≠ emsgBits + nonceBits := by
  have e : emsgBits + nonceBits = 512 := rfl
  rw [e]
  rcases len_hashParent_cases hp with e | e | e | e <;> omega

/-- The keygen point of the hash node `h` with parent `p`: the bare input of `h`. The hash node
is not written next to the input (the oracle has no labels, the scheme no headers). -/
def pointOf (ξ : Rec) (_h p : Name) : Query := ⟨p.len, val ξ p⟩

theorem pointOf_inj_input {ξ ξ' : Rec} {h p : Name} (e : pointOf ξ h p = pointOf ξ' h p) :
    val ξ p = val ξ' p := by
  simp only [pointOf, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
  exact e

/-- A keygen point is not an index query: its length is 192 or 6080, never 384. -/
theorem pointOf_ne_encQuery {h p : Name} (hp : hashParent h = some p) (ξ : Rec)
    (u : EncInput) : pointOf ξ h p ≠ encQuery u :=
  ne_encQuery_of_length_ne (len_hashParent_ne_enc hp) u

/-- A query of the length of a hash input is not an index query. -/
theorem mk_ne_encQuery {h p : Name} (hp : hashParent h = some p) (u' : BitVec p.len)
    (u : EncInput) : (⟨p.len, u'⟩ : Query) ≠ encQuery u :=
  ne_encQuery_of_length_ne (len_hashParent_ne_enc hp) u

theorem sigma_mk_cast_eq {n m : ℕ} (h : n = m) (x : BitVec n) :
    (⟨n, x⟩ : Σ k, BitVec k) = ⟨m, x.cast h⟩ := by
  subst h; rfl

theorem sigma_val (ξ : Rec) (p : Name) :
    (⟨lenF p.fin, graph.evalRec ξ p.fin⟩ : Σ k, BitVec k) = ⟨p.len, val ξ p⟩ := by
  unfold val
  generalize graph.evalRec ξ p.fin = x
  exact sigma_mk_cast_eq (graph_len_fin p) x

theorem graph_point_fin (ξ : Rec) (h : Name) :
    graph.point (graph.evalRec ξ) h.fin = (hashParent h).map fun p => pointOf ξ h p := by
  unfold Graph.point
  rw [graph_kind_fin]
  cases h <;> simp only [kindOf, hashParent, Option.map_some, Option.map_none, pointOf]
  case ch k t => exact congrArg some (sigma_val ξ (ci k t))
  case rh => exact congrArg some (sigma_val ξ rc)

/-! ## Good records: distinct keygen points -/

/-- The keygen points of the record are pairwise distinct. -/
def DistinctRec (ξ : Rec) : Prop := graph.Distinct (graph.evalRec ξ)

theorem pointOf_inj_left {ξ : Rec} (hξ : DistinctRec ξ) {h h' p p' : Name}
    (hp : hashParent h = some p) (hp' : hashParent h' = some p')
    (e : pointOf ξ h p = pointOf ξ h' p') : h = h' := by
  have h1 : graph.point (graph.evalRec ξ) h.fin = some (pointOf ξ h p) := by
    rw [graph_point_fin, hp]; rfl
  have h2 : graph.point (graph.evalRec ξ) h'.fin = some (pointOf ξ h' p') := by
    rw [graph_point_fin, hp']; rfl
  rw [e] at h1
  exact Name.fin_injective (hξ _ _ _ h1 h2)

/-- The kind of the parent of a hash node: a deterministic node computing `detVal`. -/
theorem graph_kind_hashParent {h p : Name} (hp : hashParent h = some p) :
    ∃ ps hps hf, graph.kind p.fin =
      .det ps hps (fun x => (detVal p x).cast (graph_len_fin p).symm) hf := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact ⟨_, _, _, rfl⟩

/-- The parent of a hash node of the graph, by name. -/
theorem graph_kind_eq_hash {h : Name} {q : Fin N} {hq : q < h.fin} {hl : lenF h.fin = 256}
    (hk : graph.kind h.fin = .hash q hq hl) : ∃ p, hashParent h = some p ∧ q = p.fin := by
  rw [graph_kind_fin] at hk
  cases h <;> simp only [kindOf, reduceCtorEq] at hk
  case ch k t => exact ⟨ci k t, rfl, (NodeKind.hash.inj hk).symm⟩
  case rh => exact ⟨rc, rfl, (NodeKind.hash.inj hk).symm⟩

/-- The cache written by key generation. -/
def kc (ξ : Rec) : Cache := graph.keygenCache ξ

/-- An entry of the keygen cache is the point of some hash node with its output. -/
theorem kc_apply_some (ξ : Rec) (q : Query) (w : BitVec 256) (hw : kc ξ q = some w) :
    ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p ∧ w = ξ.2 h.fin := by
  obtain ⟨v, hv, rfl⟩ := Graph.keygenCache_apply_some graph ξ q w hw
  obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨ofFin v, fin_ofFin v⟩
  rw [graph_point_fin, Option.map_eq_some_iff] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  exact ⟨h, p, hp, rfl, rfl⟩

/-- For a good record, the keygen cache is read back node by node. -/
theorem kc_apply_iff {ξ : Rec} (hξ : DistinctRec ξ) (q : Query) (w : BitVec 256) :
    kc ξ q = some w ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p ∧ w = ξ.2 h.fin := by
  refine (Graph.keygenCache_apply_iff graph hξ q w).trans ?_
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨ofFin v, fin_ofFin v⟩
    rw [graph_point_fin, Option.map_eq_some_iff] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact ⟨h, p, hp, rfl, rfl⟩
  · rintro ⟨h, p, hp, rfl, rfl⟩
    exact ⟨h.fin, by rw [graph_point_fin, hp]; rfl, rfl⟩

theorem kc_isSome_iff (ξ : Rec) (q : Query) :
    (kc ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨h, p, hp, hq, -⟩ := kc_apply_some ξ q w hw
    exact ⟨h, p, hp, hq⟩
  · rintro ⟨h, p, hp, hq⟩
    have := Graph.keygenCache_isSome_of_point graph ξ h.fin q (by rw [graph_point_fin, hp, hq]; rfl)
    exact Option.isSome_iff_exists.1 this

/-- The keygen cache holds no index query. -/
theorem kc_enc (ξ : Rec) (u : EncInput) : kc ξ (encQuery u) = none := by
  rcases hk : kc ξ (encQuery u) with _ | w
  · rfl
  · obtain ⟨h, p, hp, hq, -⟩ := kc_apply_some ξ _ w hk
    exact absurd hq.symm (pointOf_ne_encQuery hp ξ u)

/-! ## Exposed and hidden points -/

/-- After signing at the disclosure set `A`, the points of the hash nodes evaluated at `A` are
exposed; when signing failed (`none`), nothing is exposed. -/
def Exposed (A? : Option (Finset Name)) (h : Name) : Prop := ∃ A, A? = some A ∧ Evaluated A h

theorem exposed_some_iff_evaluated (A : Finset Name) (h : Name) : Exposed (some A) h ↔ Evaluated A h := by
  simp [Exposed]

theorem not_exposed_none (h : Name) : ¬ Exposed none h := by
  rintro ⟨A, hA, -⟩
  cases hA

/-- The exposed part of the keygen cache: at the point of an exposed hash node, the honest
output of such a node (chosen canonically). For a good record this is `kc` on the exposed points
(`fExp_eq_kc`); unlike `kc`, it is invariant under resampling hidden coordinates for every record
(`Resample.fExp_updHash`). -/
def fExp (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if h : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p then
    some (ξ.2 (Classical.choose h).fin) else none

theorem fExp_eq_kc {A? : Option (Finset Name)} {ξ : Rec} (hξ : DistinctRec ξ) {q : Query}
    (h : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p) :
    fExp A? ξ q = kc ξ q := by
  unfold fExp
  rw [dif_pos h]
  obtain ⟨p, hp, -, hq⟩ := Classical.choose_spec h
  symm
  exact (kc_apply_iff hξ q _).2 ⟨_, p, hp, hq, rfl⟩

theorem fExp_eq_none {A? : Option (Finset Name)} (ξ : Rec) {q : Query}
    (h : ¬ ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p) :
    fExp A? ξ q = none := by
  unfold fExp
  rw [dif_neg h]

/-- The hidden part of the keygen cache. -/
def fHid (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p then kc ξ q else none

theorem extend_fExp_fHid (A? : Option (Finset Name)) {ξ : Rec} (hξ : DistinctRec ξ) :
    Cache.extend (fExp A? ξ) (fHid A? ξ) = kc ξ := by
  funext q
  simp only [Cache.extend_apply, fHid]
  by_cases h1 : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rw [fExp_eq_kc hξ h1]
    obtain ⟨h, p, hp, -, hq⟩ := h1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩)
    rw [hw]
    rfl
  · rw [fExp_eq_none ξ h1, Option.none_or]
    by_cases h2 : ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p
    · rw [if_pos h2]
    · rw [if_neg h2]
      rcases hk : kc ξ q with _ | w
      · rfl
      · exfalso
        obtain ⟨h, p, hp, hq, -⟩ := kc_apply_some ξ q w hk
        by_cases he : Exposed A? h
        · exact h1 ⟨h, p, hp, he, hq⟩
        · exact h2 ⟨h, p, hp, he, hq⟩

theorem disjoint_fExp_fHid (A? : Option (Finset Name)) {ξ : Rec} (hξ : DistinctRec ξ) :
    Cache.Disjoint (fExp A? ξ) (fHid A? ξ) := by
  intro q hq
  simp only [fHid] at hq
  split_ifs at hq with h2
  · obtain ⟨h, p, hp, he, hq⟩ := h2
    rw [fExp_eq_none]
    rintro ⟨h', p', hp', he', hq'⟩
    rw [hq] at hq'
    obtain rfl := pointOf_inj_left hξ hp hp' hq'
    exact he he'
  · simp at hq

theorem fHid_isSome_iff (A? : Option (Finset Name)) (ξ : Rec) (q : Query) :
    (fHid A? ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p := by
  simp only [fHid]
  split_ifs with hc
  · obtain ⟨h, p, hp, -, hq⟩ := id hc
    exact iff_of_true ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩) hc
  · exact iff_of_false (by simp) hc

theorem fHid_none (ξ : Rec) : fHid none ξ = kc ξ := by
  funext q
  simp only [fHid]
  split_ifs with hc
  · rfl
  · rcases hk : kc ξ q with _ | w
    · rfl
    · exfalso
      obtain ⟨h, p, hp, hq, -⟩ := kc_apply_some ξ q w hk
      exact hc ⟨h, p, hp, not_exposed_none h, hq⟩

theorem fExp_none (ξ : Rec) : fExp none ξ = ∅ := by
  funext q
  rw [fExp_eq_none]
  · rfl
  · rintro ⟨h, -, -, he, -⟩
    exact not_exposed_none h he

theorem fExp_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fExp A? ξ (encQuery u) = none := by
  rw [fExp_eq_none]
  rintro ⟨h, p, hp, -, hq⟩
  exact pointOf_ne_encQuery hp ξ u hq.symm

theorem fHid_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fHid A? ξ (encQuery u) = none := by
  simp only [fHid]
  rw [if_neg]
  rintro ⟨h, p, hp, -, hq⟩
  exact pointOf_ne_encQuery hp ξ u hq.symm

/-- A hidden point, when the cache came from a cut, is the point of a hash node that is not
evaluated. -/
theorem fHid_isSome_some_iff (A : Finset Name) (ξ : Rec) (q : Query) :
    (fHid (some A) ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧ q = pointOf ξ h p := by
  simp only [fHid_isSome_iff, exposed_some_iff_evaluated]

/-! ## The event `Spr` -/

/-- The 192-bit slice committed by the root: the low half of the cell, for every chain. -/
def rootSlice (_k : Fin 32) (w : BitVec 256) : BitVec 192 := lo192 w

/-- `sim ξ h w`: the answer `w` agrees with the honest output of the hash node `h` on the bits the
graph consumes: the high 192 bits along a chain, the low 192 bits at a chain top (read by the root
input) and the public-key prefix at the root. -/
def sim (ξ : Rec) : Name → BitVec 256 → Prop
  | ch k t, w => if t.val = 31 then rootSlice k w = rootSlice k (ξ.2 (ch k t).fin) else trunc k w = trunc k (ξ.2 (ch k t).fin)
  | rh, w => trunc128 w = trunc128 (ξ.2 rh.fin)
  | _, _ => False

theorem sim_self (ξ : Rec) (h : Name) (hh : (hashParent h).isSome) : sim ξ h (ξ.2 h.fin) := by
  cases h <;> simp only [hashParent, Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
    sim] at hh ⊢
  · split_ifs <;> rfl
  · rfl

theorem sim_ch_of_lt {ξ : Rec} {k : Fin 32} {t : Fin 32} (ht : t.val ≠ 31) {w : BitVec 256}
    (hs : sim ξ (ch k t) w) : trunc k w = trunc k (ξ.2 (ch k t).fin) := by
  simpa [sim, ht] using hs

theorem sim_ch_top {ξ : Rec} {k : Fin 32} {t : Fin 32} (ht : t.val = 31) {w : BitVec 256}
    (hs : sim ξ (ch k t) w) : rootSlice k w = rootSlice k (ξ.2 (ch k t).fin) := by
  simpa [sim, ht] using hs

theorem sim_ch_of_trunc {ξ : Rec} {k : Fin 32} {t : Fin 32} (ht : t.val ≠ 31) {w : BitVec 256}
    (hs : trunc k w = trunc k (ξ.2 (ch k t).fin)) : sim ξ (ch k t) w := by
  simpa [sim, ht] using hs

theorem sim_rh_iff (ξ : Rec) (w : BitVec 256) : sim ξ rh w ↔ trunc128 w = trunc128 (ξ.2 rh.fin) :=
  Iff.rfl

/-- Some cached answer, at a string of the input length of a hash node `h` but different from the
honest input of `h`, simulates the honest output of `h`. Without labels a string of length
`p.len` is a candidate preimage for every hash node with that input length, so the event is a
union over the hash nodes; the charge per fresh query stays below `ε` because a chain node is
simulated on 192 bits (`spr_charge`). -/
def Spr (c : Cache) (ξ : Rec) : Prop :=
  ∃ h p, hashParent h = some p ∧ ∃ u : BitVec p.len, u ≠ val ξ p ∧
    ∃ w, c ⟨p.len, u⟩ = some w ∧ sim ξ h w

theorem Spr.mono {c c' : Cache} (h : Cache.Sub c c') {ξ : Rec} (hs : Spr c ξ) :
    Spr c' ξ := by
  obtain ⟨hn, p, hp, u, hu, w, hw, ht⟩ := hs
  exact ⟨hn, p, hp, u, hu, w, h _ _ hw, ht⟩

/-- Caching an index query does not change `Spr`: no hash input has its length. -/
theorem spr_cacheQuery_enc (c : Cache) (ξ : Rec) (u : EncInput)
    (w : BitVec 256) : Spr (c.cacheQuery (encQuery u) w) ξ ↔ Spr c ξ := by
  have key : ∀ (h p : Name), hashParent h = some p → ∀ u' : BitVec p.len,
      c.cacheQuery (encQuery u) w ⟨p.len, u'⟩ = c ⟨p.len, u'⟩ :=
    fun h p hp u' => QueryCache.cacheQuery_of_ne _ _ (mk_ne_encQuery hp u' u)
  constructor
  · rintro ⟨h, p, hp, u', hu, w', hw, ht⟩
    rw [key h p hp] at hw
    exact ⟨h, p, hp, u', hu, w', hw, ht⟩
  · rintro ⟨h, p, hp, u', hu, w', hw, ht⟩
    refine ⟨h, p, hp, u', hu, w', ?_, ht⟩
    rw [key h p hp]
    exact hw

/-- An entry of an overlay is an entry of one of the two caches. -/
theorem spr_of_extend {c f : Cache} {ξ : Rec} (hs : Spr (Cache.extend c f) ξ) :
    Spr c ξ ∨ Spr f ξ := by
  obtain ⟨h, p, hp, u, hu, w, hw, ht⟩ := hs
  rw [Cache.extend_apply, Option.or_eq_some_iff] at hw
  rcases hw with hw | ⟨-, hw⟩
  · exact Or.inl ⟨h, p, hp, u, hu, w, hw, ht⟩
  · exact Or.inr ⟨h, p, hp, u, hu, w, hw, ht⟩

/-- The honest output of a hash node does not simulate that of another hash node whose input has
the same length. -/
def NoOutCollision (ξ : Rec) : Prop :=
  ∀ h p h' p', hashParent h = some p → hashParent h' = some p' → p.len = p'.len → h ≠ h' →
    ¬ sim ξ h (ξ.2 h'.fin)

/-- A good record: distinct keygen points and no output collision. -/
def GoodRec (ξ : Rec) : Prop := DistinctRec ξ ∧ NoOutCollision ξ

theorem not_spr_kc {ξ : Rec} (hξ : GoodRec ξ) : ¬ Spr (kc ξ) ξ := by
  rintro ⟨h, p, hp, u, hu, w, hw, ht⟩
  obtain ⟨h', p', hp', hq, rfl⟩ := kc_apply_some ξ _ w hw
  by_cases hh : h = h'
  · subst hh
    rw [hp] at hp'
    obtain rfl := Option.some.inj hp'
    exact hu (eq_of_heq (Sigma.mk.inj_iff.1 hq).2)
  · exact hξ.2 h p h' p' hp hp' (Sigma.mk.inj_iff.1 hq).1 hh ht

theorem sub_fExp_kc (A? : Option (Finset Name)) {ξ : Rec} (hξ : DistinctRec ξ) :
    Cache.Sub (fExp A? ξ) (kc ξ) := by
  intro q w hw
  by_cases hc : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rwa [fExp_eq_kc hξ hc] at hw
  · rw [fExp_eq_none ξ hc] at hw
    cases hw

theorem not_spr_fExp (A? : Option (Finset Name)) {ξ : Rec} (hξ : GoodRec ξ) :
    ¬ Spr (fExp A? ξ) ξ :=
  fun hs => not_spr_kc hξ (hs.mono (sub_fExp_kc A? hξ.1))

theorem not_spr_empty (ξ : Rec) : ¬ Spr ∅ ξ := by
  rintro ⟨h, p, hp, u, hu, w, hw, -⟩
  simp at hw

/-- `ε = 2 ^ (-128)`. -/
def ε : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 128)⁻¹

/-- At most `2 ^ (256 - m)` values of `256` bits have a given `m`-bit low part. -/
theorem card_filter_setWidth_le (m : ℕ) (hm : m ≤ 256) (a : BitVec m) :
    (Finset.univ.filter fun w : BitVec 256 => w.setWidth m = a).card ≤ 2 ^ (256 - m) := by
  have key : (Finset.univ.filter fun w : BitVec 256 => w.setWidth m = a).card ≤
      (Finset.univ : Finset (BitVec (256 - m))).card := by
    refine Finset.card_le_card_of_injOn (fun w => (w >>> m).setWidth (256 - m))
      (fun _ _ => Finset.mem_univ _) ?_
    intro w hw w' hw' e
    rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
    have hlow : ∀ i, i < m → w.getLsbD i = w'.getLsbD i := by
      intro i hi
      have := congrArg (fun x : BitVec m => x.getLsbD i) (hw.2.trans hw'.2.symm)
      simpa [BitVec.getLsbD_setWidth, hi] using this
    have hhigh : ∀ i, m ≤ i → i < 256 → w.getLsbD i = w'.getLsbD i := by
      intro i hi1 hi2
      have := congrArg (fun x : BitVec (256 - m) => x.getLsbD (i - m)) e
      have h1 : i - m < 256 - m := by omega
      have h2 : m + (i - m) = i := by omega
      simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h1, h2] using this
    apply BitVec.eq_of_getLsbD_eq
    intro i hi2
    by_cases hi : i < m
    · exact hlow i hi
    · exact hhigh i (by omega) hi2
  rw [Finset.card_univ, Fintype.card_bitVec] at key
  exact key

/-- At most `2 ^ 64` values of `256` bits have a given low 192 bits. -/
theorem card_filter_lo192_le' (a : BitVec 192) :
    (Finset.univ.filter fun w : BitVec 256 => lo192 w = a).card ≤ 2 ^ 64 :=
  card_filter_setWidth_le 192 (by norm_num) a

/-- At most `2 ^ 128` values of `256` bits have a given 128-bit prefix. -/
theorem card_filter_trunc128_le (a : BitVec 128) :
    (Finset.univ.filter fun w : BitVec 256 => trunc128 w = a).card ≤ 2 ^ 128 :=
  card_filter_setWidth_le 128 (by norm_num) a

/-- At most `2 ^ (256 - c)` values of `256` bits have a given `c`-bit window at bit `o`. -/
theorem card_filter_extract_le (o c : ℕ) (hoc : o + c ≤ 256) (a : BitVec c) :
    (Finset.univ.filter fun w : BitVec 256 => w.extractLsb' o c = a).card ≤ 2 ^ (256 - c) := by
  have key : (Finset.univ.filter fun w : BitVec 256 => w.extractLsb' o c = a).card ≤
      (Finset.univ : Finset (BitVec (256 - o - c + o))).card := by
    refine Finset.card_le_card_of_injOn
      (fun w => (w >>> (o + c)).setWidth (256 - o - c) ++ w.setWidth o)
      (fun _ _ => Finset.mem_univ _) ?_
    intro w hw w' hw' e
    rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hlo : i < o
    · have h := congrArg (fun x : BitVec (256 - o - c + o) => x.getLsbD i) e
      simpa only [BitVec.getLsbD_append, hlo, if_true, BitVec.getLsbD_setWidth, decide_true,
        Bool.true_and] using h
    · by_cases hmid : i < o + c
      · have h := congrArg (fun x : BitVec c => x.getLsbD (i - o)) (hw.2.trans hw'.2.symm)
        have h1 : i - o < c := by omega
        have h2 : o + (i - o) = i := by omega
        simpa only [BitVec.getLsbD_extractLsb', h1, decide_true, Bool.true_and, h2] using h
      · have h := congrArg (fun x : BitVec (256 - o - c + o) => x.getLsbD (i - c)) e
        have h1 : ¬ i - c < o := by omega
        have h2 : i - c - o < 256 - o - c := by omega
        have h3 : o + c + (i - c - o) = i := by omega
        simpa only [BitVec.getLsbD_append, h1, if_false, BitVec.getLsbD_setWidth, h2, decide_true,
          Bool.true_and, BitVec.getLsbD_ushiftRight, h3] using h
  have he : 256 - o - c + o = 256 - c := by omega
  rw [Finset.card_univ, Fintype.card_bitVec, he] at key
  exact key

/-- Fixing a chain's state slice (at least 152 bits, at bit `truncOff k`) leaves at most 104
unconstrained bits. -/
theorem card_filter_trunc_le' (k : Fin 32) (a : BitVec (chainBits k)) :
    (Finset.univ.filter fun w : BitVec 256 => trunc k w = a).card ≤ 2 ^ 104 := by
  refine le_trans (Finset.card_le_card fun w hw => ?_)
    ((card_filter_extract_le (truncOff k) (chainBits k) (truncOff_add_le k) a).trans
      (Nat.pow_le_pow_right (by norm_num) (by have := chainBits_ge k; omega)))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact (trunc_256 k w).symm.trans hw

/-- The root slice pins 192 of the 256 bits of a top. -/
theorem card_filter_rootSlice_le (k : Fin 32) (a : BitVec 192) :
    (Finset.univ.filter fun w : BitVec 256 => rootSlice k w = a).card ≤ 2 ^ 104 :=
  (card_filter_lo192_le' a).trans (by norm_num)

theorem card_filter_sim_le' (ξ : Rec) (h : Name) (hh : h ≠ rh) :
    (Finset.univ.filter fun w : BitVec 256 => sim ξ h w).card ≤ 2 ^ 104 := by
  cases h with
  | ch k t =>
    by_cases ht : t.val = 31
    · simpa [sim, ht] using card_filter_rootSlice_le k (rootSlice k (ξ.2 (ch k t).fin))
    · simpa [sim, ht] using card_filter_trunc_le' k (trunc k (ξ.2 (ch k t).fin))
  | rh => exact absurd rfl hh
  | src _ | ci _ _ | cv _ _ | rc =>
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun w _ hs => by simpa [sim] using hs)]
    exact Nat.zero_le _

/-- The hash nodes. -/
def hashNodes : Finset Name := Finset.univ.filter fun h => (hashParent h).isSome

theorem card_hashNodes : hashNodes.card = 1025 := by
  unfold hashNodes
  rw [Finset.card_filter, Name.sum_eq]
  simp only [hashParent, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, if_true,
    if_false, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  norm_num

theorem mem_hashNodes {h : Name} : h ∈ hashNodes ↔ (hashParent h).isSome := by
  simp [hashNodes]

attribute [irreducible] hashNodes

theorem eq_rh_of_hashParent_len {h p : Name} (hp : hashParent h = some p) (hl : p.len = 6144) :
    h = rh := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · simp [Name.len, chainBits] at hl
    split_ifs at hl <;> contradiction
  · rfl

/-- The answers simulating some hash node whose input has length `n`. -/
def simSet (ξ : Rec) (n : ℕ) : Finset (BitVec 256) :=
  Finset.univ.filter fun w => ∃ h p, hashParent h = some p ∧ p.len = n ∧ sim ξ h w

/-- At most `2 ^ 128` answers simulate some hash node of a given input length. -/
theorem card_simSet_le (ξ : Rec) (n : ℕ) : (simSet ξ n).card ≤ 2 ^ 128 := by
  by_cases hn : n = 6144
  · subst hn
    refine le_trans (Finset.card_le_card fun w hw => ?_) (card_filter_trunc128_le (trunc128 (ξ.2 rh.fin)))
    rw [simSet, Finset.mem_filter] at hw
    rw [Finset.mem_filter]
    obtain ⟨-, h, p, hp, hl, hs⟩ := hw
    obtain rfl := eq_rh_of_hashParent_len hp hl
    exact ⟨Finset.mem_univ _, hs⟩
  · have hsub : simSet ξ n ⊆ hashNodes.biUnion fun h =>
        Finset.univ.filter fun w : BitVec 256 => sim ξ h w ∧ h ≠ rh := by
      intro w hw
      rw [simSet, Finset.mem_filter] at hw
      obtain ⟨-, h, p, hp, hl, hs⟩ := hw
      rw [Finset.mem_biUnion]
      refine ⟨h, mem_hashNodes.2 (by rw [hp]; rfl), Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, ?_⟩⟩
      rintro rfl
      simp only [hashParent, Option.some.injEq] at hp
      subst hp
      exact hn hl.symm
    refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ h ∈ hashNodes, (Finset.univ.filter fun w : BitVec 256 => sim ξ h w ∧ h ≠ rh).card
        ≤ ∑ _h ∈ hashNodes, 2 ^ 104 := by
          refine Finset.sum_le_sum fun h _ => ?_
          by_cases hh : h = rh
          · subst hh
            rw [Finset.card_eq_zero.2]
            · exact Nat.zero_le _
            · ext w
              simp
          · refine le_trans (Finset.card_le_card fun w hw => ?_) (card_filter_sim_le' ξ h hh)
            rw [Finset.mem_filter] at hw ⊢
            exact ⟨hw.1, hw.2.1⟩
      _ = 1025 * 2 ^ 104 := by rw [Finset.sum_const, card_hashNodes, smul_eq_mul]
      _ ≤ 2 ^ 128 := by norm_num

theorem inv_card_bitVec_mul_two_pow : (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) : ℝ≥0∞) = ε := by
  have h0 : (2 : ℝ≥0∞) ^ 128 ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ 128 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : (2 : ℝ≥0∞) ^ 128 * 2 ^ 128 = 2 ^ 256 := by rw [← pow_add]
  rw [Fintype.card_bitVec, ε]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← e, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), mul_assoc, ENNReal.inv_mul_cancel h0 ht,
    mul_one]

/-- A fresh answer creates a `Spr` entry with probability at most `ε`. -/
theorem spr_charge (c : Cache) (ξ : Rec) (q : Query) (hq : c q = none) :
    ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
        (if Spr (c.cacheQuery q w) ξ then 1 else 0) ≤ (if Spr c ξ then 1 else 0) + ε := by
  by_cases hs : Spr c ξ
  · rw [if_pos hs]
    calc ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (if Spr (c.cacheQuery q w) ξ then 1 else 0)
        ≤ ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 1 := by
          refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ zero_le
          split_ifs <;> simp
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
              (ENNReal.natCast_ne_top _)]
      _ ≤ 1 + ε := le_self_add
  · rw [if_neg hs, zero_add]
    -- a new `Spr` entry sits at `q`; its answer simulates some hash node of the query's length
    have key : ∀ w, Spr (c.cacheQuery q w) ξ → w ∈ simSet ξ q.1 := by
      rintro w ⟨h, p, hp, u, hu, w', hw', ht⟩
      by_cases hqq : (⟨p.len, u⟩ : Query) = q
      · subst hqq
        rw [QueryCache.cacheQuery_self] at hw'
        obtain rfl := Option.some.inj hw'
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h, p, hp, rfl, ht⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hw'
        exact (hs ⟨h, p, hp, u, hu, w', hw', ht⟩).elim
    calc ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (if Spr (c.cacheQuery q w) ξ then 1 else 0)
        ≤ ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (if w ∈ simSet ξ q.1 then 1 else 0) := by
          refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ zero_le
          split_ifs with h1 h2
          · exact le_rfl
          · exact absurd (key w h1) h2
          · exact zero_le_one
          · exact le_rfl
      _ = (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((simSet ξ q.1).card : ℝ≥0∞) := by
          rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) : ℝ≥0∞) :=
          mul_le_mul_of_nonneg_left (Nat.cast_le.2 (card_simSet_le ξ _)) zero_le
      _ ≤ ε := inv_card_bitVec_mul_two_pow.le

/-! ## Coordinates -/

/-- The record coordinates that the value of a node reads. -/
def deps : Name → Finset Name
  | src k => {src k}
  | ci k t => if h : t.val = 0 then {src k} else {ch k ⟨t.val - 1, by omega⟩}
  | ch k t => {ch k t}
  | cv k t => {ch k t}
  | rc => Finset.univ.image fun k => ch k 31
  | rh => {rh}

theorem deps_ci_zero (k : Fin 32) (t : Fin 32) (ht : t.val = 0) : deps (ci k t) = {src k} := by
  simp only [deps, dif_pos ht]

theorem deps_ci_succ (k : Fin 32) (t : Fin 32) (ht : ¬ t.val = 0) :
    deps (ci k t) = {ch k ⟨t.val - 1, by omega⟩} := by
  simp only [deps, dif_neg ht]

theorem child_src_ci (k : Fin 32) (t : Fin 32) (ht : t.val = 0) : child (src k) = some (ci k t) := by
  have e : t = 0 := Fin.ext ht
  subst e
  rfl

theorem child_cv_ci (k : Fin 32) (t : Fin 32) (ht : ¬ t.val = 0) :
    child (cv k ⟨t.val - 1, by omega⟩) = some (ci k t) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]
  simp only [Option.some.injEq, Name.ci.injEq, true_and, Fin.ext_iff]
  omega

theorem child_cv_31 (k : Fin 32) : child (cv k 31) = some rc := rfl

/-- Resample a source. -/
def updSrc (ξ : Rec) (k : Fin 32) (b : BitVec (chainBits k)) : Rec :=
  (Function.update ξ.1 (src k).fin (b.cast (graph_len_fin (src k)).symm), ξ.2)

/-- Resample a hash output. -/
def updHash (ξ : Rec) (s : Name) (b : BitVec 256) : Rec := (ξ.1, Function.update ξ.2 s.fin b)

theorem updHash_snd_self (ξ : Rec) (s : Name) (b : BitVec 256) : (updHash ξ s b).2 s.fin = b :=
  Function.update_self _ _ _

theorem updHash_snd_ne (ξ : Rec) (s : Name) (b : BitVec 256) {n : Name} (h : n ≠ s) :
    (updHash ξ s b).2 n.fin = ξ.2 n.fin := by
  simp only [updHash]
  exact Function.update_of_ne (fun e => h (Name.fin_injective e)) _ _

theorem updSrc_snd (ξ : Rec) (k : Fin 32) (b : BitVec (chainBits k)) : (updSrc ξ k b).2 = ξ.2 := rfl

theorem val_updHash_of_not_mem_deps (ξ : Rec) (s : Name) (b : BitVec 256) (n : Name)
    (h : s ∉ deps n) : val (updHash ξ s b) n = val ξ n := by
  cases n with
  | src k =>
    rw [val_src, val_src]
    rfl
  | ci k t =>
    by_cases ht : t.val = 0
    · rw [val_ci_zero _ k t ht, val_ci_zero _ k t ht, val_src, val_src]
      rfl
    · rw [deps_ci_succ k t ht, Finset.mem_singleton] at h
      rw [val_ci_succ _ k t ht, val_ci_succ _ k t ht, updHash_snd_ne _ _ _ (Ne.symm h)]
  | ch k t =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_ch, val_ch, updHash_snd_ne _ _ _ (Ne.symm h)]
  | cv k t =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_cv, val_cv, updHash_snd_ne _ _ _ (Ne.symm h)]
  | rc =>
    simp only [deps, Finset.mem_image, Finset.mem_univ, true_and, not_exists] at h
    rw [val_rc, val_rc]
    exact congrArg rootCat (funext fun k => by rw [updHash_snd_ne _ _ _ (h k)])
  | rh =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_rh, val_rh, updHash_snd_ne _ _ _ (Ne.symm h)]

theorem val_updSrc_src_of_ne (ξ : Rec) (k : Fin 32) (b : BitVec (chainBits k)) {k' : Fin 32} (h : ¬ k = k') :
    val (updSrc ξ k b) (src k') = val ξ (src k') := by
  have e : (updSrc ξ k b).1 (src k').fin = ξ.1 (src k').fin :=
    Function.update_of_ne (fun e => h (Name.src.inj (Name.fin_injective e)).symm) _ _
  rw [val_src, val_src, e]

theorem val_updSrc_of_not_mem_deps (ξ : Rec) (k : Fin 32) (b : BitVec (chainBits k)) (n : Name)
    (h : src k ∉ deps n) : val (updSrc ξ k b) n = val ξ n := by
  cases n with
  | src k' =>
    simp only [deps, Finset.mem_singleton, Name.src.injEq] at h
    exact val_updSrc_src_of_ne ξ k b h
  | ci k' t =>
    by_cases ht : t.val = 0
    · rw [deps_ci_zero k' t ht, Finset.mem_singleton, Name.src.injEq] at h
      rw [val_ci_zero _ k' t ht, val_ci_zero _ k' t ht, val_updSrc_src_of_ne ξ k b h]
    · rw [val_ci_succ _ k' t ht, val_ci_succ _ k' t ht, updSrc_snd]
  | ch k t => rw [val_ch, val_ch, updSrc_snd]
  | cv k t => rw [val_cv, val_cv, updSrc_snd]
  | rc => rw [val_rc, val_rc, updSrc_snd]
  | rh => rw [val_rh, val_rh, updSrc_snd]

theorem val_updSrc_self (ξ : Rec) (k : Fin 32) (b : BitVec (chainBits k)) :
    val (updSrc ξ k b) (src k) = b := by
  have e : (updSrc ξ k b).1 (src k).fin = b.cast (graph_len_fin (src k)).symm :=
    Function.update_self _ _ _
  rw [val_src, e]
  exact cast_cast_eq _ _ _

theorem snd_updHash_of_ne (ξ : Rec) (s : Name) (b : BitVec 256) (n : Name) (h : n ≠ s) :
    (updHash ξ s b).2 n.fin = ξ.2 n.fin :=
  updHash_snd_ne ξ s b h

theorem snd_updHash_self (ξ : Rec) (s : Name) (b : BitVec 256) :
    (updHash ξ s b).2 s.fin = b :=
  updHash_snd_self ξ s b

theorem snd_updSrc (ξ : Rec) (k : Fin 32) (b : BitVec (chainBits k)) : (updSrc ξ k b).2 = ξ.2 := rfl

/-! ## The coordinate that randomizes the input of a hash node -/

/-- The coordinate resampled to randomize the input of a hash node (junk for other nodes). -/
def coordOf : Name → Name
  | ch k t => if h : t.val = 0 then src k else ch k ⟨t.val - 1, by omega⟩
  | rh => ch 0 31
  | n => n

theorem coordOf_ne_rh (h : Name) (hh : h.cost ≠ 0) : coordOf h ≠ rh := by
  cases h
  case ch k t =>
    simp only [coordOf]
    split_ifs <;> simp
  case rh => simp [coordOf]
  all_goals exact absurd rfl hh

/-- The coordinate of a hash node lies at most two steps below its parent. -/
theorem coordOf_below {h p : Name} (hp : hashParent h = some p) :
    coordOf h = p ∨ child (coordOf h) = some p ∨ ∃ m, child (coordOf h) = some m ∧ child m = some p := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · rename_i k t
    simp only [coordOf]
    split_ifs with ht
    · exact Or.inr (Or.inl (child_src_ci k t ht))
    · exact Or.inr (Or.inr ⟨cv k ⟨t.val - 1, by omega⟩, rfl, child_cv_ci k t ht⟩)
  · exact Or.inr (Or.inr ⟨cv 0 31, rfl, rfl⟩)

/-- The low 192 bits of the root input are the low 192 bits of the top of chain `0`. -/
theorem setWidth_cast {n m k : ℕ} (h : n = m) (x : BitVec n) :
    (x.cast h).setWidth k = x.setWidth k := by
  subst h; rfl

theorem low192_lowCat (c : ℕ → BitVec 256) : ∀ j, (lowCat c j).setWidth 192 = lo192 (c 0)
  | 0 => BitVec.setWidth_eq _
  | j + 1 => by
    rw [lowCat, setWidth_cast, BitVec.setWidth_append, dif_pos (by omega), low192_lowCat c j]

theorem low192_rootCat (c : Fin 32 → BitVec 256) : (rootCat c).setWidth 192 = lo192 (c 0) := by
  unfold rootCat
  rw [setWidth_cast, low192_lowCat]
  rfl

/-- A filter whose members all have the same low 192 bits has at most `2 ^ 64` elements. -/
theorem card_filter_le_of_imp_lo (p : BitVec 256 → Prop) [DecidablePred p] (a : BitVec 192)
    (hp : ∀ b, p b → lo192 b = a) : (Finset.univ.filter p).card ≤ 2 ^ 64 :=
  le_trans (Finset.card_le_card fun b hb => Finset.mem_filter.2
    ⟨Finset.mem_univ _, hp b (Finset.mem_filter.1 hb).2⟩) (card_filter_lo192_le' a)

/-- Resampling the top of chain `0` moves the root input through its low 192 bits. -/
theorem card_updHash_rc_le (ξ : Rec) (u : BitVec rc.len) :
    (Finset.univ.filter fun b : BitVec 256 => val (updHash ξ (coordOf rh) b) rc = u).card ≤
      2 ^ 64 := by
  refine card_filter_le_of_imp_lo _ (u.setWidth 192) fun b hb => ?_
  have e := congrArg (fun x : BitVec rc.len => x.setWidth 192) hb
  rw [val_rc] at e
  have l := low192_rootCat (fun k => (updHash ξ (coordOf rh) b).2 (ch k 31).fin)
  have e2 : lo192 ((updHash ξ (coordOf rh) b).2 (ch 0 31).fin) = u.setWidth 192 := l.symm.trans e
  change lo192 ((updHash ξ (ch 0 31) b).2 (ch 0 31).fin) = _ at e2
  rwa [updHash_snd_self] at e2

/-- A filter whose members all have the same truncation has at most `2 ^ 128` elements. -/
theorem card_filter_le_of_imp (k : Fin 32) (p : BitVec 256 → Prop) [DecidablePred p] (a : BitVec (chainBits k))
    (hp : ∀ b, p b → trunc k b = a) : (Finset.univ.filter p).card ≤ 2 ^ 128 :=
  le_trans (Finset.card_le_card fun b hb => Finset.mem_filter.2
    ⟨Finset.mem_univ _, hp b (Finset.mem_filter.1 hb).2⟩) ((card_filter_trunc_le' k a).trans (by norm_num))

/-- Resampling the coordinate of a hash node makes its input hit any given value with
probability at most `2 ^ (-128)`: hash coordinates. -/
theorem card_updHash_input_le {h p : Name} (hp : hashParent h = some p) (ξ : Rec)
    (hs : ∀ k, coordOf h ≠ src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 256 => val (updHash ξ (coordOf h) b) p = u).card ≤ 2 ^ 128 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · -- `ch k t`
    rename_i k t
    have ht : ¬ t.val = 0 := fun ht => hs k (by simp [coordOf, ht])
    have e1 : coordOf (ch k t) = ch k ⟨t.val - 1, by omega⟩ := by simp [coordOf, ht]
    rw [e1]
    refine card_filter_le_of_imp k _ u fun b hb => ?_
    rw [val_ci_succ _ k t ht, updHash_snd_self] at hb
    exact hb
  · -- `rh`: the low 192 bits of the root input are those of the resampled top of chain `0`
    exact (card_updHash_rc_le ξ u).trans (by norm_num)

/-- Source coordinates. -/
theorem card_updSrc_input_le {h p : Name} (hp : hashParent h = some p) (ξ : Rec) {k : Fin 32}
    (hs : coordOf h = src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec (chainBits k) => val (updSrc ξ k b) p = u).card ≤ 1 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp only [coordOf] at hs
  · rename_i k' t
    by_cases ht : t.val = 0
    · rw [dif_pos ht] at hs
      obtain rfl : k = k' := (Name.src.inj hs).symm
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, val_ci_zero _ k t ht,
        val_updSrc_self] at ha hb
      exact ha.trans hb.symm
    · rw [dif_neg ht] at hs
      exact absurd hs (by simp)
  all_goals exact absurd hs (by simp)

end Forest

end OptimalOTS
