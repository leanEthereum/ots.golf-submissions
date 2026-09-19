import Submissions.UpperCompressions.Tree
import Submissions.UpperCompressions.Keygen
import Submissions.UpperCompressions.SignIdx

/-!
# Values of the concrete scheme

For a record `ξ : Rec` (sources and hash outputs), `val ξ n` is the value of node `n` in the
honest evaluation `graph.evalRec ξ`.  This file gives the explicit formulas (`val_src`, …,
`val_rh`), describes the keygen cache (`kc ξ`) through the keygen points `pointOf ξ h p` of the
hash nodes, splits it into the exposed and hidden parts relative to a disclosure set
(`fExp`, `fHid`), defines the event `Spr` (a cached answer at a non-keygen point that begins with
an honest value), and records which record coordinates each value depends on (`deps`), with the
two coordinate updates `updSrc` and `updHash`.

The oracle has no labels.  A keygen point is the bare input `⟨p.len, val ξ p⟩` of a hash node; the
hash node is read back from the tweak in its 16 high bits (`tagNat_pointOf`, `tagging`), and a
keygen point never has the length of an index query (`pointOf_ne_encQuery`).
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

theorem trunc_cast {n m : ℕ} (h : n = m) (x : BitVec n) : trunc (x.cast h) = trunc x := by
  subst h; rfl

theorem trunc_trunc {n : ℕ} (x : BitVec n) : trunc (trunc x) = trunc x := BitVec.setWidth_eq _

theorem cast_cast_eq {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x := by
  subst h₁; rfl

/-- The node equation of the concrete graph, with the kind computed by `kindOf`. -/
theorem evalRec_apply_fin (ξ : Rec) (n : Name) :
    graph.evalRec ξ n.fin =
      (kindOf n.fin n (ofFin_fin n)).value (graph.evalRec ξ) (ξ.1 n.fin) (ξ.2 n.fin) := by
  have := Graph.evalRec_apply graph ξ n.fin
  rwa [graph_kind_fin] at this

theorem trunc_evalRec (ξ : Rec) (n : Name) : trunc (graph.evalRec ξ n.fin) = trunc (val ξ n) := by
  unfold val
  exact (trunc_cast _ _).symm

theorem val_src (ξ : Rec) (k : Fin 54) : val ξ (src k) = (ξ.1 (src k).fin).cast (graph_len_fin _) := by
  unfold val
  rw [evalRec_apply_fin]
  rfl

theorem trunc_eq_self (x : BitVec 128) : trunc x = x := BitVec.setWidth_eq _

/-- Truncation loses nothing on a value of 128 bits (e.g. the value of `prev k t`). -/
theorem trunc_injective_of_len {w : ℕ} (hw : w = 128) :
    Function.Injective (trunc : BitVec w → BitVec 128) := by
  subst hw
  intro x y e
  rwa [trunc_eq_self, trunc_eq_self] at e

/-- The input of the chain hash `ch k t`: its tweak, then the value of `prev k t`. -/
theorem val_ci (ξ : Rec) (k : Fin 54) (t : Fin 14) :
    val ξ (ci k t) = tw (ch k t) ++ trunc (val ξ (prev k t)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw (ch k t) ++ trunc (graph.evalRec ξ (prev k t).fin) = _
  rw [trunc_evalRec]
  rfl

theorem val_ch (ξ : Rec) (k : Fin 54) (t : Fin 14) : val ξ (ch k t) = ξ.2 (ch k t).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem trunc_val_ch (ξ : Rec) (k : Fin 54) (t : Fin 14) :
    trunc (graph.evalRec ξ (ch k t).fin) = trunc (ξ.2 (ch k t).fin) := by
  rw [trunc_evalRec, val_ch]
  rfl

theorem val_cv (ξ : Rec) (k : Fin 54) (t : Fin 14) : val ξ (cv k t) = trunc (ξ.2 (ch k t).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show trunc (graph.evalRec ξ (ch k t).fin) = _
  exact trunc_val_ch ξ k t

theorem trunc_val_cv (ξ : Rec) (k : Fin 54) (t : Fin 14) :
    trunc (graph.evalRec ξ (cv k t).fin) = trunc (ξ.2 (ch k t).fin) := by
  rw [trunc_evalRec, val_cv]
  exact trunc_trunc _

/-- The first chain input reads the source. -/
theorem val_ci_zero (ξ : Rec) (k : Fin 54) (t : Fin 14) (ht : t.val = 0) :
    val ξ (ci k t) = tw (ch k t) ++ val ξ (src k) := by
  have e : prev k t = src k := by simp [Name.prev, ht]
  rw [val_ci, e]
  exact congrArg (tw (ch k t) ++ ·) (trunc_eq_self _)

/-- A later chain input reads the previous chain hash. -/
theorem val_ci_succ (ξ : Rec) (k : Fin 54) (t : Fin 14) (ht : ¬ t.val = 0) :
    val ξ (ci k t) = tw (ch k t) ++ trunc (ξ.2 (ch k ⟨t.val - 1, by omega⟩).fin) := by
  have e : prev k t = cv k ⟨t.val - 1, by omega⟩ := by simp [Name.prev, ht]
  rw [val_ci, e, val_cv]
  exact congrArg (tw (ch k t) ++ ·) (trunc_trunc _)

theorem val_gc (ξ : Rec) (j : Fin 18) :
    val ξ (gc j) = tw (gh j) ++ cat3 (trunc (ξ.2 (ch (chainOf j 0) 13).fin))
      (trunc (ξ.2 (ch (chainOf j 1) 13).fin)) (trunc (ξ.2 (ch (chainOf j 2) 13).fin)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw (gh j) ++ cat3 (trunc (graph.evalRec ξ (cv (chainOf j 0) 13).fin))
    (trunc (graph.evalRec ξ (cv (chainOf j 1) 13).fin))
    (trunc (graph.evalRec ξ (cv (chainOf j 2) 13).fin)) = _
  rw [trunc_val_cv, trunc_val_cv, trunc_val_cv]

theorem val_gh (ξ : Rec) (j : Fin 18) : val ξ (gh j) = ξ.2 (gh j).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem trunc_val_gh (ξ : Rec) (j : Fin 18) :
    trunc (graph.evalRec ξ (gh j).fin) = trunc (ξ.2 (gh j).fin) := by
  rw [trunc_evalRec, val_gh]
  rfl

theorem val_gv (ξ : Rec) (j : Fin 18) : val ξ (gv j) = trunc (ξ.2 (gh j).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show trunc (graph.evalRec ξ (gh j).fin) = _
  exact trunc_val_gh ξ j

theorem trunc_val_gv (ξ : Rec) (j : Fin 18) :
    trunc (graph.evalRec ξ (gv j).fin) = trunc (ξ.2 (gh j).fin) := by
  rw [trunc_evalRec, val_gv]
  exact trunc_trunc _

theorem val_ec (ξ : Rec) (l : Fin 6) :
    val ξ (ec l) = tw (eh l) ++ cat3 (trunc (ξ.2 (gh (groupOf l 0)).fin))
      (trunc (ξ.2 (gh (groupOf l 1)).fin)) (trunc (ξ.2 (gh (groupOf l 2)).fin)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw (eh l) ++ cat3 (trunc (graph.evalRec ξ (gv (groupOf l 0)).fin))
    (trunc (graph.evalRec ξ (gv (groupOf l 1)).fin))
    (trunc (graph.evalRec ξ (gv (groupOf l 2)).fin)) = _
  rw [trunc_val_gv, trunc_val_gv, trunc_val_gv]

theorem val_eh (ξ : Rec) (l : Fin 6) : val ξ (eh l) = ξ.2 (eh l).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem trunc_val_eh (ξ : Rec) (l : Fin 6) :
    trunc (graph.evalRec ξ (eh l).fin) = trunc (ξ.2 (eh l).fin) := by
  rw [trunc_evalRec, val_eh]
  rfl

theorem val_ev (ξ : Rec) (l : Fin 6) : val ξ (ev l) = trunc (ξ.2 (eh l).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show trunc (graph.evalRec ξ (eh l).fin) = _
  exact trunc_val_eh ξ l

theorem trunc_val_ev (ξ : Rec) (l : Fin 6) :
    trunc (graph.evalRec ξ (ev l).fin) = trunc (ξ.2 (eh l).fin) := by
  rw [trunc_evalRec, val_ev]
  exact trunc_trunc _

theorem val_rc (ξ : Rec) : val ξ rc = tw rh ++ cat6 fun l => trunc (ξ.2 (eh l).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw rh ++ cat6 (fun l => trunc (graph.evalRec ξ (ev l).fin)) = _
  exact congrArg (fun a => tw rh ++ cat6 a) (funext fun l => trunc_val_ev ξ l)

theorem val_rh (ξ : Rec) : val ξ rh = ξ.2 rh.fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

/-- The public key of a record: the first 128 bits of the root. -/
def pkOf (ξ : Rec) : BitVec 128 := trunc (ξ.2 rh.fin)

/-! ## Hash nodes and keygen points -/

/-- The node whose value a hash node hashes: its tweaked input. -/
def hashParent : Name → Option Name
  | ch k t => some (ci k t)
  | gh j => some (gc j)
  | eh l => some (ec l)
  | rh => some rc
  | _ => none

theorem hashParent_isSome_iff (h : Name) : (hashParent h).isSome ↔ h.cost ≠ 0 := by
  cases h <;> simp [hashParent, Name.cost]

theorem cost_ne_zero_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.cost ≠ 0 :=
  (hashParent_isSome_iff h).1 (by rw [hp]; rfl)

theorem child_hashParent {h p : Name} (hp : hashParent h = some p) : child p = some h := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  all_goals rfl

/-- The input of a hash node has length 144 (chains), 400 (groups, subtrees) or 784 (root). -/
theorem len_hashParent_cases {h p : Name} (hp : hashParent h = some p) :
    p.len = 144 ∨ p.len = 400 ∨ p.len = 784 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp [Name.len]

/-- The input of a hash node never has the length of an index query. -/
theorem len_hashParent_ne_enc {h p : Name} (hp : hashParent h = some p) :
    p.len ≠ msgBits + nonceBits := by
  have e : msgBits + nonceBits = 384 := rfl
  rw [e]
  rcases len_hashParent_cases hp with e | e | e <;> omega

/-- The keygen point of the hash node `h` with parent `p`: the bare input of `h`.  The hash node
is not written next to the input (the oracle has no labels); it is read back from the tweak
(`tagNat_pointOf`). -/
def pointOf (ξ : Rec) (_h p : Name) : Query := ⟨p.len, val ξ p⟩

/-- The value of the parent of a hash node starts with the tweak of that hash node. -/
theorem tagNat_val {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    tagNat ⟨p.len, val ξ p⟩ = h.idx := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · rw [val_ci]; exact tagNat_tw_append (n := 128) _ _
  · rw [val_gc]; exact tagNat_tw_append (n := 384) _ _
  · rw [val_ec]; exact tagNat_tw_append (n := 384) _ _
  · rw [val_rc]; exact tagNat_tw_append (n := 768) _ _

/-- A keygen point carries the index of its hash node. -/
theorem tagNat_pointOf {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    tagNat (pointOf ξ h p) = h.idx :=
  tagNat_val hp ξ

theorem pointOf_inj_left {ξ ξ' : Rec} {h h' p p' : Name} (hp : hashParent h = some p)
    (hp' : hashParent h' = some p') (e : pointOf ξ h p = pointOf ξ' h' p') : h = h' := by
  apply Name.idx_injective
  rw [← tagNat_pointOf hp ξ, ← tagNat_pointOf hp' ξ', e]

theorem pointOf_inj_input {ξ ξ' : Rec} {h p : Name} (e : pointOf ξ h p = pointOf ξ' h p) :
    val ξ p = val ξ' p := by
  simp only [pointOf, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
  exact e

/-- A keygen point is not an index query: its length is 144, 400 or 784, never 384. -/
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
  case gh j => exact congrArg some (sigma_val ξ (gc j))
  case eh l => exact congrArg some (sigma_val ξ (ec l))
  case rh => exact congrArg some (sigma_val ξ rc)

/-! ## The tagging of the concrete graph -/

/-- The hash node a query belongs to: the node whose index is written in its 16 high bits. -/
def tagOf (q : Query) : Option (Fin N) := if h : tagNat q < N then some ⟨tagNat q, h⟩ else none

theorem tagOf_eq_some_of_tagNat {q : Query} {h : Name} (e : tagNat q = h.idx) :
    tagOf q = some h.fin := by
  unfold tagOf
  rw [dif_pos (by rw [e]; exact h.idx_lt)]
  exact congrArg some (Fin.ext e)

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
  case gh j => exact ⟨gc j, rfl, (NodeKind.hash.inj hk).symm⟩
  case eh l => exact ⟨ec l, rfl, (NodeKind.hash.inj hk).symm⟩
  case rh => exact ⟨rc, rfl, (NodeKind.hash.inj hk).symm⟩

/-- The input of a hash node carries its tweak, in every assignment. -/
theorem tagNat_detVal_of_hashParent {h p : Name} (hp : hashParent h = some p) (x : Asg) :
    tagNat ⟨p.len, detVal p x⟩ = h.idx :=
  tagNat_detVal (child_hashParent hp) (cost_ne_zero_of_hashParent hp) x

/-- The tagging of the concrete graph: every hash input starts with the index of its hash node. -/
def tagging : graph.Tagging where
  tag q := if h : tagNat q < N then some ⟨tagNat q, h⟩ else none
  tag_parent := by
    intro v q hq hl hk
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨ofFin v, fin_ofFin v⟩
    obtain ⟨p, hp, rfl⟩ := graph_kind_eq_hash hk
    obtain ⟨ps, hps, hf, hkp⟩ := graph_kind_hashParent hp
    refine ⟨ps, hps, _, hf, hkp, fun x => ?_⟩
    exact tagOf_eq_some_of_tagNat
      (tagNat_cast_detVal (child_hashParent hp) (cost_ne_zero_of_hashParent hp) x _)

/-- The cache written by key generation. -/
def kc (ξ : Rec) : Cache := graph.keygenCache ξ

theorem kc_apply_iff (ξ : Rec) (q : Query) (w : BitVec 256) :
    kc ξ q = some w ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p ∧ w = ξ.2 h.fin := by
  refine (Graph.keygenCache_apply_iff graph tagging ξ q w).trans ?_
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
    obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hw
    exact ⟨h, p, hp, hq⟩
  · rintro ⟨h, p, hp, hq⟩
    exact ⟨_, (kc_apply_iff ξ q _).2 ⟨h, p, hp, hq, rfl⟩⟩

/-- The keygen cache holds no index query. -/
theorem kc_enc (ξ : Rec) (u : EncInput) : kc ξ (encQuery u) = none := by
  rcases hk : kc ξ (encQuery u) with _ | w
  · rfl
  · obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ _ w).1 hk
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

/-- The exposed part of the keygen cache. -/
def fExp (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p then kc ξ q else none

/-- The hidden part of the keygen cache. -/
def fHid (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p then kc ξ q else none

theorem extend_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.extend (fExp A? ξ) (fHid A? ξ) = kc ξ := by
  funext q
  simp only [Cache.extend_apply, fExp, fHid]
  by_cases h1 : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rw [if_pos h1]
    obtain ⟨h, p, hp, -, hq⟩ := h1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩)
    rw [hw]
    rfl
  · rw [if_neg h1, Option.none_or]
    by_cases h2 : ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p
    · rw [if_pos h2]
    · rw [if_neg h2]
      rcases hk : kc ξ q with _ | w
      · rfl
      · exfalso
        obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
        by_cases he : Exposed A? h
        · exact h1 ⟨h, p, hp, he, hq⟩
        · exact h2 ⟨h, p, hp, he, hq⟩

theorem disjoint_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.Disjoint (fExp A? ξ) (fHid A? ξ) := by
  intro q hq
  simp only [fHid] at hq
  split_ifs at hq with h2
  · obtain ⟨h, p, hp, he, hq⟩ := h2
    simp only [fExp]
    rw [if_neg]
    rintro ⟨h', p', hp', he', hq'⟩
    rw [hq] at hq'
    obtain rfl := pointOf_inj_left hp hp' hq'
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
      obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
      exact hc ⟨h, p, hp, not_exposed_none h, hq⟩

theorem fExp_none (ξ : Rec) : fExp none ξ = ∅ := by
  funext q
  simp only [fExp]
  rw [if_neg]
  · rfl
  · rintro ⟨h, -, -, he, -⟩
    exact not_exposed_none h he

theorem fExp_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fExp A? ξ (encQuery u) = none := by
  simp only [fExp]
  rw [if_neg]
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

/-- Some cached answer, at a string carrying the tweak of a hash node but different from the
honest input of that node, begins with the honest output of that node.  The tweak condition makes
a query count for one hash node only: without labels, a string of length `p.len` could otherwise
be a spurious preimage for every hash node with that input length. -/
def Spr (c : Cache) (ξ : Rec) : Prop :=
  ∃ h p, hashParent h = some p ∧ ∃ u : BitVec p.len, u ≠ val ξ p ∧ tagNat ⟨p.len, u⟩ = h.idx ∧
    ∃ w, c ⟨p.len, u⟩ = some w ∧ trunc w = trunc (ξ.2 h.fin)

theorem Spr.mono {c c' : Cache} (h : Cache.Sub c c') {ξ : Rec} (hs : Spr c ξ) :
    Spr c' ξ := by
  obtain ⟨hn, p, hp, u, hu, htag, w, hw, ht⟩ := hs
  exact ⟨hn, p, hp, u, hu, htag, w, h _ _ hw, ht⟩

/-- Caching an index query does not change `Spr`: no hash input has its length. -/
theorem spr_cacheQuery_enc (c : Cache) (ξ : Rec) (u : EncInput)
    (w : BitVec 256) : Spr (c.cacheQuery (encQuery u) w) ξ ↔ Spr c ξ := by
  have key : ∀ (h p : Name), hashParent h = some p → ∀ u' : BitVec p.len,
      c.cacheQuery (encQuery u) w ⟨p.len, u'⟩ = c ⟨p.len, u'⟩ :=
    fun h p hp u' => QueryCache.cacheQuery_of_ne _ _ (mk_ne_encQuery hp u' u)
  constructor
  · rintro ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
    rw [key h p hp] at hw
    exact ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
  · rintro ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
    refine ⟨h, p, hp, u', hu, htag, w', ?_, ht⟩
    rw [key h p hp]
    exact hw

/-- An entry of an overlay is an entry of one of the two caches. -/
theorem spr_of_extend {c f : Cache} {ξ : Rec} (hs : Spr (Cache.extend c f) ξ) :
    Spr c ξ ∨ Spr f ξ := by
  obtain ⟨h, p, hp, u, hu, htag, w, hw, ht⟩ := hs
  rw [Cache.extend_apply, Option.or_eq_some_iff] at hw
  rcases hw with hw | ⟨-, hw⟩
  · exact Or.inl ⟨h, p, hp, u, hu, htag, w, hw, ht⟩
  · exact Or.inr ⟨h, p, hp, u, hu, htag, w, hw, ht⟩

theorem not_spr_kc (ξ : Rec) : ¬ Spr (kc ξ) ξ := by
  rintro ⟨h, p, hp, u, hu, htag, w, hw, -⟩
  obtain ⟨h', p', hp', hq, -⟩ := (kc_apply_iff ξ _ w).1 hw
  have hh : h = h' := by
    apply Name.idx_injective
    rw [← htag, hq, tagNat_pointOf hp' ξ]
  subst hh
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  exact hu (eq_of_heq (Sigma.mk.inj_iff.1 hq).2)

theorem sub_fExp_kc (A? : Option (Finset Name)) (ξ : Rec) : Cache.Sub (fExp A? ξ) (kc ξ) := by
  intro q w hw
  simp only [fExp] at hw
  by_cases hc : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rwa [if_pos hc] at hw
  · rw [if_neg hc] at hw
    cases hw

theorem not_spr_fExp (A? : Option (Finset Name)) (ξ : Rec) : ¬ Spr (fExp A? ξ) ξ :=
  fun hs => not_spr_kc ξ (hs.mono (sub_fExp_kc A? ξ))

theorem not_spr_empty (ξ : Rec) : ¬ Spr ∅ ξ := by
  rintro ⟨h, p, hp, u, hu, -, w, hw, -⟩
  simp at hw

/-- `ε = 2 ^ (-128)`. -/
def ε : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 128)⁻¹

/-- At most `2 ^ 128` values of `256` bits have a given truncation. -/
theorem card_filter_trunc_le (a : BitVec 128) :
    (Finset.univ.filter fun w : BitVec 256 => trunc w = a).card ≤ 2 ^ 128 := by
  have key : (Finset.univ.filter fun w : BitVec 256 => trunc w = a).card ≤
      (Finset.univ : Finset (BitVec 128)).card := by
    refine Finset.card_le_card_of_injOn (fun w => (w >>> 128).setWidth 128)
      (fun _ _ => Finset.mem_univ _) ?_
    intro w hw w' hw' e
    rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
    have hlow : ∀ i, i < 128 → w.getLsbD i = w'.getLsbD i := by
      intro i hi
      have := congrArg (fun x : BitVec 128 => x.getLsbD i) (hw.2.trans hw'.2.symm)
      simpa [trunc, BitVec.getLsbD_setWidth, hi] using this
    have hhigh : ∀ i, 128 ≤ i → i < 256 → w.getLsbD i = w'.getLsbD i := by
      intro i hi1 hi2
      have := congrArg (fun x : BitVec 128 => x.getLsbD (i - 128)) e
      have h1 : i - 128 < 128 := by omega
      have h2 : 128 + (i - 128) = i := by omega
      simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h1, h2] using this
    apply BitVec.eq_of_getLsbD_eq
    intro i hi2
    by_cases hi : i < 128
    · exact hlow i hi
    · exact hhigh i (by omega) hi2
  rw [Finset.card_univ, Fintype.card_bitVec] at key
  exact key

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
    -- a new `Spr` entry sits at `q`, so it belongs to the hash node written in the tweak of `q`
    have key : ∀ w, Spr (c.cacheQuery q w) ξ →
        ∃ h : Name, tagNat q = h.idx ∧ trunc w = trunc (ξ.2 h.fin) := by
      rintro w ⟨h, p, hp, u, hu, htag, w', hw', ht⟩
      by_cases hqq : (⟨p.len, u⟩ : Query) = q
      · subst hqq
        rw [QueryCache.cacheQuery_self] at hw'
        obtain rfl := Option.some.inj hw'
        exact ⟨h, htag, ht⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hw'
        exact (hs ⟨h, p, hp, u, hu, htag, w', hw', ht⟩).elim
    by_cases hex : ∃ h₀ : Name, tagNat q = h₀.idx
    · obtain ⟨h₀, hq₀⟩ := hex
      have key' : ∀ w, Spr (c.cacheQuery q w) ξ → trunc w = trunc (ξ.2 h₀.fin) := by
        intro w hw
        obtain ⟨h, hq', ht⟩ := key w hw
        have : h₀ = h := Name.idx_injective (hq₀.symm.trans hq')
        subst this
        exact ht
      calc ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if Spr (c.cacheQuery q w) ξ then 1 else 0)
          ≤ ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if trunc w = trunc (ξ.2 h₀.fin) then 1 else 0) := by
            refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ zero_le
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd (key' w h1) h2
            · exact zero_le_one
            · exact le_rfl
        _ = (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun w : BitVec 256 => trunc w = trunc (ξ.2 h₀.fin)).card :
              ℝ≥0∞) := by
            rw [← Finset.mul_sum, Finset.sum_boole]
        _ ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) : ℝ≥0∞) :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.2 (card_filter_trunc_le _)) zero_le
        _ = ε := inv_card_bitVec_mul_two_pow
    · have hno : ∀ w, ¬ Spr (c.cacheQuery q w) ξ := fun w hw => by
        obtain ⟨h, hq', -⟩ := key w hw
        exact hex ⟨h, hq'⟩
      rw [Finset.sum_eq_zero fun w _ => by rw [if_neg (hno w), mul_zero]]
      exact zero_le

/-! ## Coordinates -/

/-- The record coordinates that the value of a node reads. -/
def deps : Name → Finset Name
  | src k => {src k}
  | ci k t => if h : t.val = 0 then {src k} else {ch k ⟨t.val - 1, by omega⟩}
  | ch k t => {ch k t}
  | cv k t => {ch k t}
  | gc j => {ch (chainOf j 0) 13, ch (chainOf j 1) 13, ch (chainOf j 2) 13}
  | gh j => {gh j}
  | gv j => {gh j}
  | ec l => {gh (groupOf l 0), gh (groupOf l 1), gh (groupOf l 2)}
  | eh l => {eh l}
  | ev l => {eh l}
  | rc => Finset.univ.image eh
  | rh => {rh}

theorem deps_ci_zero (k : Fin 54) (t : Fin 14) (ht : t.val = 0) : deps (ci k t) = {src k} := by
  simp only [deps, dif_pos ht]

theorem deps_ci_succ (k : Fin 54) (t : Fin 14) (ht : ¬ t.val = 0) :
    deps (ci k t) = {ch k ⟨t.val - 1, by omega⟩} := by
  simp only [deps, dif_neg ht]

theorem child_src_ci (k : Fin 54) (t : Fin 14) (ht : t.val = 0) : child (src k) = some (ci k t) := by
  have e : t = 0 := Fin.ext ht
  subst e
  rfl

theorem child_cv_ci (k : Fin 54) (t : Fin 14) (ht : ¬ t.val = 0) :
    child (cv k ⟨t.val - 1, by omega⟩) = some (ci k t) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]
  simp only [Option.some.injEq, Name.ci.injEq, true_and, Fin.ext_iff]
  omega

theorem chainOf_div (j : Fin 18) (a : Fin 3) : ((chainOf j a : Fin 54) : ℕ) / 3 = j := by
  simp only [chainOf]
  omega

theorem groupOf_div (l : Fin 6) (a : Fin 3) : ((groupOf l a : Fin 18) : ℕ) / 3 = l := by
  simp only [groupOf]
  omega

theorem child_cv_13 (k : Fin 54) : child (cv k 13) = some (gc ⟨k / 3, by omega⟩) := rfl

theorem child_cv_13_gc (j : Fin 18) (a : Fin 3) : child (cv (chainOf j a) 13) = some (gc j) := by
  rw [child_cv_13]
  exact congrArg some (congrArg gc (Fin.ext (chainOf_div j a)))

theorem child_gv_ec (l : Fin 6) (a : Fin 3) : child (gv (groupOf l a)) = some (ec l) := by
  show some (ec ⟨(groupOf l a : ℕ) / 3, by omega⟩) = some (ec l)
  exact congrArg some (congrArg ec (Fin.ext (groupOf_div l a)))

/-- Resample a source. -/
def updSrc (ξ : Rec) (k : Fin 54) (b : BitVec 128) : Rec :=
  (Function.update ξ.1 (src k).fin (b.cast (graph_len_fin (src k)).symm), ξ.2)

/-- Resample a hash output. -/
def updHash (ξ : Rec) (s : Name) (b : BitVec 256) : Rec := (ξ.1, Function.update ξ.2 s.fin b)

theorem updHash_snd_self (ξ : Rec) (s : Name) (b : BitVec 256) : (updHash ξ s b).2 s.fin = b :=
  Function.update_self _ _ _

theorem updHash_snd_ne (ξ : Rec) (s : Name) (b : BitVec 256) {n : Name} (h : n ≠ s) :
    (updHash ξ s b).2 n.fin = ξ.2 n.fin := by
  simp only [updHash]
  exact Function.update_of_ne (fun e => h (Name.fin_injective e)) _ _

theorem updSrc_snd (ξ : Rec) (k : Fin 54) (b : BitVec 128) : (updSrc ξ k b).2 = ξ.2 := rfl

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
  | gc j =>
    simp only [deps, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    obtain ⟨h0, h1, h2⟩ := h
    rw [val_gc, val_gc, updHash_snd_ne _ _ _ (Ne.symm h0), updHash_snd_ne _ _ _ (Ne.symm h1),
      updHash_snd_ne _ _ _ (Ne.symm h2)]
  | gh j =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_gh, val_gh, updHash_snd_ne _ _ _ (Ne.symm h)]
  | gv j =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_gv, val_gv, updHash_snd_ne _ _ _ (Ne.symm h)]
  | ec l =>
    simp only [deps, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    obtain ⟨h0, h1, h2⟩ := h
    rw [val_ec, val_ec, updHash_snd_ne _ _ _ (Ne.symm h0), updHash_snd_ne _ _ _ (Ne.symm h1),
      updHash_snd_ne _ _ _ (Ne.symm h2)]
  | eh l =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_eh, val_eh, updHash_snd_ne _ _ _ (Ne.symm h)]
  | ev l =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_ev, val_ev, updHash_snd_ne _ _ _ (Ne.symm h)]
  | rc =>
    simp only [deps, Finset.mem_image, Finset.mem_univ, true_and, not_exists] at h
    rw [val_rc, val_rc]
    exact congrArg (fun a => tw rh ++ cat6 a)
      (funext fun l => by rw [updHash_snd_ne _ _ _ (h l)])
  | rh =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_rh, val_rh, updHash_snd_ne _ _ _ (Ne.symm h)]

theorem val_updSrc_src_of_ne (ξ : Rec) (k : Fin 54) (b : BitVec 128) {k' : Fin 54} (h : ¬ k = k') :
    val (updSrc ξ k b) (src k') = val ξ (src k') := by
  have e : (updSrc ξ k b).1 (src k').fin = ξ.1 (src k').fin :=
    Function.update_of_ne (fun e => h (Name.src.inj (Name.fin_injective e)).symm) _ _
  rw [val_src, val_src, e]

theorem val_updSrc_of_not_mem_deps (ξ : Rec) (k : Fin 54) (b : BitVec 128) (n : Name)
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
  | gc j => rw [val_gc, val_gc, updSrc_snd]
  | gh j => rw [val_gh, val_gh, updSrc_snd]
  | gv j => rw [val_gv, val_gv, updSrc_snd]
  | ec l => rw [val_ec, val_ec, updSrc_snd]
  | eh l => rw [val_eh, val_eh, updSrc_snd]
  | ev l => rw [val_ev, val_ev, updSrc_snd]
  | rc => rw [val_rc, val_rc, updSrc_snd]
  | rh => rw [val_rh, val_rh, updSrc_snd]

theorem val_updSrc_self (ξ : Rec) (k : Fin 54) (b : BitVec 128) :
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

theorem snd_updSrc (ξ : Rec) (k : Fin 54) (b : BitVec 128) : (updSrc ξ k b).2 = ξ.2 := rfl

/-! ## The coordinate that randomizes the input of a hash node -/

/-- The coordinate resampled to randomize the input of a hash node (junk for other nodes). -/
def coordOf : Name → Name
  | ch k t => if h : t.val = 0 then src k else ch k ⟨t.val - 1, by omega⟩
  | gh j => ch (chainOf j 2) 13
  | eh l => gh (groupOf l 2)
  | rh => eh 5
  | n => n

theorem coordOf_ne_rh (h : Name) (hh : h.cost ≠ 0) : coordOf h ≠ rh := by
  cases h
  case ch k t =>
    simp only [coordOf]
    split_ifs <;> simp
  case gh j => simp [coordOf]
  case eh l => simp [coordOf]
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
  · exact Or.inr (Or.inr ⟨cv (chainOf _ 2) 13, rfl, child_cv_13_gc _ 2⟩)
  · exact Or.inr (Or.inr ⟨gv (groupOf _ 2), rfl, child_gv_ec _ 2⟩)
  · exact Or.inr (Or.inr ⟨ev 5, rfl, rfl⟩)

theorem trunc_cat3 (x y z : BitVec 128) : trunc (cat3 x y z) = z := by
  unfold cat3
  rw [trunc_cast]
  unfold trunc
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

theorem trunc_cat6 (a : Fin 6 → BitVec 128) : trunc (cat6 a) = a 5 := by
  unfold cat6
  rw [trunc_cast]
  unfold trunc
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

/-- The tweak sits in the high bits: it does not change the 128 low bits of a payload of at least
128 bits. -/
theorem trunc_tw_append {n : ℕ} (hn : 128 ≤ n) (a : BitVec 16) (x : BitVec n) :
    trunc (a ++ x) = trunc x := by
  unfold trunc
  rw [BitVec.setWidth_append, dif_pos hn]

/-- The low 128 bits of a tweaked hash input are those of its payload. -/
theorem trunc_of_tw_append_eq {n : ℕ} (hn : 128 ≤ n) {a : BitVec 16} {x : BitVec n}
    {u : BitVec (16 + n)} (e : a ++ x = u) : trunc u = trunc x := by
  subst e
  exact trunc_tw_append hn a x

/-- A chain input: the payload is the low 128 bits. -/
theorem trunc_of_tw_eq {a : BitVec 16} {x : BitVec 128} {u : BitVec 144} (e : a ++ x = u) :
    trunc u = x :=
  (trunc_of_tw_append_eq (n := 128) le_rfl e).trans (trunc_eq_self x)

/-- A tweaked concatenation of three values: the low 128 bits are the last value. -/
theorem trunc_of_tw_cat3_eq {a : BitVec 16} {x y z : BitVec 128} {u : BitVec 400}
    (e : a ++ cat3 x y z = u) : trunc u = z :=
  (trunc_of_tw_append_eq (n := 384) (by norm_num) e).trans (trunc_cat3 x y z)

/-- A tweaked concatenation of six values: the low 128 bits are the last value. -/
theorem trunc_of_tw_cat6_eq {a : BitVec 16} {b : Fin 6 → BitVec 128} {u : BitVec 784}
    (e : a ++ cat6 b = u) : trunc u = b 5 :=
  (trunc_of_tw_append_eq (n := 768) (by norm_num) e).trans (trunc_cat6 b)

/-- A filter whose members all have the same truncation has at most `2 ^ 128` elements. -/
theorem card_filter_le_of_imp (p : BitVec 256 → Prop) [DecidablePred p] (a : BitVec 128)
    (hp : ∀ b, p b → trunc b = a) : (Finset.univ.filter p).card ≤ 2 ^ 128 :=
  le_trans (Finset.card_le_card fun b hb => Finset.mem_filter.2
    ⟨Finset.mem_univ _, hp b (Finset.mem_filter.1 hb).2⟩) (card_filter_trunc_le a)

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
    refine card_filter_le_of_imp _ (trunc u) fun b hb => ?_
    rw [val_ci_succ _ k t ht] at hb
    have := trunc_of_tw_eq hb
    exact (this.trans (congrArg trunc (updHash_snd_self _ _ _))).symm
  · -- `gh j`
    refine card_filter_le_of_imp _ (trunc u) fun b hb => ?_
    rw [val_gc] at hb
    have := trunc_of_tw_cat3_eq hb
    exact (this.trans (congrArg trunc (updHash_snd_self _ _ _))).symm
  · -- `eh l`
    refine card_filter_le_of_imp _ (trunc u) fun b hb => ?_
    rw [val_ec] at hb
    have := trunc_of_tw_cat3_eq hb
    exact (this.trans (congrArg trunc (updHash_snd_self _ _ _))).symm
  · -- `rh`
    refine card_filter_le_of_imp _ (trunc u) fun b hb => ?_
    rw [val_rc] at hb
    have := trunc_of_tw_cat6_eq hb
    exact (this.trans (congrArg trunc (updHash_snd_self _ _ _))).symm

/-- Source coordinates. -/
theorem card_updSrc_input_le {h p : Name} (hp : hashParent h = some p) (ξ : Rec) {k : Fin 54}
    (hs : coordOf h = src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 128 => val (updSrc ξ k b) p = u).card ≤ 1 := by
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
      exact (append_inj (n := 128) (ha.trans hb.symm)).2
    · rw [dif_neg ht] at hs
      exact absurd hs (by simp)
  all_goals exact absurd hs (by simp)

end Forest

end OptimalOTS
