import Submissions.UpperRiscv.Values
import Submissions.UpperRiscv.Reconstruct

/-!
# From an accepted forgery to a bad event

Let the verifier reconstruct the root from values `given` at the disclosure set `A'` and obtain the
assignment `y`, all answers being recorded in the cache `d` (`Graph.ReconEqs`), and accept:
the first 128 bits of `y` at the root are the public key of the honest record `ξ`.

* `up` (the walk in the proof of the paper's Section 7.3): if `y` differs from the honest values at a
  non-hash node visited by the reconstruction, some recorded answer at a non-keygen point begins
  with an honest value (`Spr d ξ`).
* `events_none`: if nothing was exposed, then `Spr d ξ` or the root's keygen point was queried.
* `events_ne`: if the signature revealed the cut `A ≠ A'` of the same cost, then `Spr d ξ` or a
  keygen point hidden at `A` was queried.
* `events_same`: if `A' = A` and the supplied values differ from the honest ones, `Spr d ξ`.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

/-- The verifier's value at a node. -/
def yv (y : graph.Assignment) (n : Name) : BitVec n.len := (y n.fin).cast (graph_len_fin n)

/-! ## Bit-vector helpers -/

theorem sigma_cast {a b : ℕ} (h : a = b) (x : BitVec a) :
    (⟨a, x⟩ : Σ k : ℕ, BitVec k) = ⟨b, x.cast h⟩ := by subst h; rfl

theorem trunc_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) : trunc (x.cast h) = trunc x := by
  subst h; rfl

theorem trunc_128 (x : BitVec 128) : trunc x = x := BitVec.setWidth_eq x

theorem trunc_eq_cast {m : ℕ} (h : m = 128) (x : BitVec m) : trunc x = x.cast h := by
  subst h; exact BitVec.setWidth_eq x

theorem cast_injective {n m : ℕ} (h : n = m) {x y : BitVec n} (e : x.cast h = y.cast h) :
    x = y := by
  subst h; simpa using e

/-- Both halves of a concatenation are determined by it (as `append_inj` of `Names.lean`). -/
theorem bv_append_inj {n m : ℕ} {x x' : BitVec n} {y y' : BitVec m} (h : x ++ y = x' ++ y') :
    x = x' ∧ y = y' := by
  have key : ∀ i, (x ++ y).getLsbD i = (x' ++ y').getLsbD i := fun i => by rw [h]
  simp only [BitVec.getLsbD_append] at key
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := key (i + m)
    simp only [show ¬ (i + m < m) by omega, if_false, Nat.add_sub_cancel] at this
    exact this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := key i
    simpa [hi] using this

theorem rootAcc_inj {c c' : ℕ → BitVec 128} :
    ∀ j, rootAcc c j = rootAcc c' j → ∀ i ≤ j, c i = c' i
  | 0, h, i, hi => by
    obtain rfl : i = 0 := by omega
    exact h
  | j + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := bv_append_inj (cast_injective _ h)
    rcases Nat.lt_or_ge i (j + 1) with lt | ge
    · exact rootAcc_inj j h2 i (by omega)
    · obtain rfl : i = j + 1 := by omega
      exact (bv_append_inj h1).1

theorem rootCat_inj {a b : Fin 32 → BitVec 128} (h : rootCat a = rootCat b) : a = b := by
  unfold rootCat at h
  have key := rootAcc_inj 31 (cast_injective _ h)
  funext k
  have := key k.val (by omega)
  simpa [topFun, k.isLt] using this

/-! ## Names -/

theorem cost_eq_zero_of_len {n : Name} (h : n.len = 128) : n.cost = 0 := by
  cases n <;> first | rfl | (simp [Name.len] at h)

theorem len_eq_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.len = 256 := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp <;> rfl

theorem hashParent_cases {h p : Name} (hp : hashParent h = some p) :
    h = rh ∨ ∃ v, hashOf v = some h := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp
  · exact Or.inr ⟨cv _ _, rfl⟩
  · exact Or.inl rfl

/-- The input of a hash node is a deterministic node. -/
theorem cost_hashParent {h p : Name} (hp : hashParent h = some p) : p.cost = 0 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;> rfl

theorem hashParent_ne_src {h p : Name} (hp : hashParent h = some p) (k : Fin 32) : p ≠ src k := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact fun e => nomatch e

theorem hashParent_of_hashOf {v h : Name} (hh : hashOf v = some h) : ∃ p, hashParent h = some p := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh <;>
    exact ⟨_, rfl⟩

theorem cost_of_hashOf {v h : Name} (hh : hashOf v = some h) : v.cost = 0 := by
  cases v <;> simp only [hashOf, reduceCtorEq] at hh <;> rfl

theorem prev_succ (k : Fin 32) (t : Fin 15) (ht : t.val < 14) :
    prev k ⟨t.val + 1, by omega⟩ = cv k t := by
  simp [prev]

theorem val_rc' (ξ : Rec) : val ξ rc = rootCat fun k => val ξ (cv k 14) := by
  rw [val_rc]
  exact congrArg rootCat (funext fun k => (val_cv ξ k 14).symm)

theorem val_of_hashOf (ξ : Rec) {v h : Name} (hh : hashOf v = some h) :
    trunc (val ξ v) = trunc (ξ.2 h.fin) := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh
  · rw [val_cv]; exact trunc_128 _

/-! ## The kinds of the nodes -/

theorem graph_kind_hash {h p : Name} (hp : hashParent h = some p) :
    ∃ (hlt : p.fin < h.fin) (hl : graph.len h.fin = hashBits),
      graph.kind h.fin = .hash p.fin hlt hl := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact ⟨_, _, rfl⟩

theorem graph_kind_det {n : Name} (hc : n.cost = 0) (hs : ∀ k, n ≠ src k) :
    ∃ (hlt : ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, w < n.fin)
      (hf : ∀ x y : Asg, (∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, x w = y w) →
        (detVal n x).cast (graph_len_fin n).symm = (detVal n y).cast (graph_len_fin n).symm),
      graph.kind n.fin = .det ((Name.parents n).map nameEquiv.toEmbedding) hlt
        (fun x => (detVal n x).cast (graph_len_fin n).symm) hf := by
  rw [graph_kind_fin]
  cases n
  · exact absurd rfl (hs _)
  all_goals first | exact ⟨_, _, rfl⟩ | (simp [Name.cost] at hc)

/-! ## The reconstruction equations in terms of names -/

section Recon

variable {A : Finset Name} {d : Cache} {given y : graph.Assignment}

theorem yv_mem (hy : graph.ReconEqs d (fins A) given y) {n : Name} (hn : n ∈ A) :
    yv y n = (given n.fin).cast (graph_len_fin n) := by
  unfold yv
  rw [(hy n.fin).1 ((mem_fins A n).mpr hn)]

theorem recon_evaluated (hy : graph.ReconEqs d (fins A) given y) {n : Name}
    (he : Evaluated A n) :
    (∀ p hp hl, graph.kind n.fin = .hash p hp hl →
        ∃ w, d ⟨graph.len p, y p⟩ = some w ∧ y n.fin = w.cast hl.symm) ∧
      (∀ ps hlt f hf, graph.kind n.fin = .det ps hlt f hf → y n.fin = f y) ∧
      (graph.kind n.fin = .source → y n.fin = 0) :=
  (hy n.fin).2.2 (fun h => he.1 ((mem_fins A n).mp h)) ((visited_iff A n).mpr he.2)

/-- The hash equation at an evaluated hash node. -/
theorem yv_hash (hy : graph.ReconEqs d (fins A) given y) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) :
    ∃ w, d ⟨p.len, yv y p⟩ = some w ∧ trunc w = trunc (yv y h) := by
  obtain ⟨hlt, hl, hk⟩ := graph_kind_hash hp
  obtain ⟨w, hw, hyw⟩ := (recon_evaluated hy he).1 _ _ _ hk
  refine ⟨w, ?_, ?_⟩
  · rw [sigma_cast (graph_len_fin p) (y p.fin)] at hw
    exact hw
  · unfold yv
    rw [trunc_cast_eq, hyw, trunc_cast_eq]

/-- The value of an evaluated deterministic node. -/
theorem yv_det (hy : graph.ReconEqs d (fins A) given y) {n : Name} (he : Evaluated A n)
    (hc : n.cost = 0) (hs : ∀ k, n ≠ src k) : yv y n = detVal n y := by
  obtain ⟨hlt, hf, hk⟩ := graph_kind_det hc hs
  have := (recon_evaluated hy he).2.1 _ _ _ _ hk
  unfold yv
  rw [this]
  simp

theorem yv_cv (hy : graph.ReconEqs d (fins A) given y) {k : Fin 32} {t : Fin 15}
    (he : Evaluated A (cv k t)) : yv y (cv k t) = trunc (yv y (ch k t)) := by
  rw [yv_det hy he rfl (by simp)]
  show trunc (y _) = _
  unfold yv
  rw [trunc_cast_eq]

/-- The input of a chain hash: the value before it, then its header. -/
theorem yv_ci (hy : graph.ReconEqs d (fins A) given y) {k : Fin 32} {t : Fin 15}
    (he : Evaluated A (ci k t)) : yv y (ci k t) = trunc (yv y (prev k t)) ++ hdr k t := by
  rw [yv_det hy he rfl (by simp)]
  show trunc (y (prev k t).fin) ++ hdr k t = _
  unfold yv
  rw [trunc_cast_eq]

theorem yv_rc (hy : graph.ReconEqs d (fins A) given y) (he : Evaluated A rc) :
    yv y rc = rootCat fun k => yv y (cv k 14) := by
  rw [yv_det hy he rfl (by simp)]
  show rootCat (fun k => trunc (y (cv k 14).fin)) = _
  exact congrArg rootCat (funext fun k => trunc_eq_cast (graph_len_fin (cv k 14)) _)

theorem yv_of_hashOf (hy : graph.ReconEqs d (fins A) given y) {v h : Name}
    (hh : hashOf v = some h) (he : Evaluated A v) : trunc (yv y v) = trunc (yv y h) := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh
  · rw [yv_cv hy he]; exact trunc_128 _

/-- A forged chain input differs from the honest one as soon as the value before it does. -/
theorem yv_ci_ne (hy : graph.ReconEqs d (fins A) given y) {k : Fin 32} {t : Fin 15}
    (he : Evaluated A (ci k t)) {ξ : Rec} (hne : yv y (prev k t) ≠ val ξ (prev k t)) :
    yv y (ci k t) ≠ val ξ (ci k t) := by
  intro heq
  rw [yv_ci hy he, val_ci] at heq
  exact hne (trunc_injective_of_len (Name.len_prev k t) (append_inj heq).1)

/-- The input of an evaluated hash node is evaluated: it is not in the cut (its length is not
128), and everything above it is the hash node or above the hash node. -/
theorem evaluated_hashParent (hA : IsCut A) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) : Evaluated A p := by
  refine ⟨fun hm => ?_, fun m hm => ?_⟩
  · have h128 := hA.values p hm
    rcases len_hashParent_cases hp with e | e <;> omega
  · rw [above_of_child (child_hashParent hp)] at hm
    rcases hm with rfl | hm
    · exact he.1
    · exact he.2 m hm

/-- The forged input of an evaluated hash node is its deterministic function of the forged
assignment. -/
theorem yv_hashParent (hA : IsCut A) (hy : graph.ReconEqs d (fins A) given y) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) : yv y p = detVal p y :=
  yv_det hy (evaluated_hashParent hA hp he) (cost_hashParent hp) (hashParent_ne_src hp)

/-- The forged input of an evaluated hash node carries the tag of that node. -/
theorem tagNat_yv (hA : IsCut A) (hy : graph.ReconEqs d (fins A) given y) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) : tagNat ⟨p.len, yv y p⟩ = h.idx := by
  rw [yv_hashParent hA hy hp he]
  exact tagNat_detVal_of_hashParent hp y

end Recon

/-! ## The walk -/

/-- One step of the walk through a hash node: `v` feeds the hash node `h`. -/
theorem hash_step {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : trunc (yv y rh) = pkOf ξ) {v h : Name} (hch : child v = some h)
    (hhp : hashParent h = some v) (hv : ∀ m, Above m v → m ∉ A)
    (hne : yv y v ≠ val ξ v)
    (ih : ∀ v', height v' < height v → (∀ m, Above m v' → m ∉ A) → v'.cost = 0 →
      yv y v' ≠ val ξ v' → Spr d ξ) : Spr d ξ := by
  have h256 : h.len = 256 := len_eq_of_hashParent hhp
  have hhA : h ∉ A := fun hm => by have := hA.values h hm; omega
  have hhE : Evaluated A h := ⟨hhA, fun m hm => hv m (Above.step hch hm)⟩
  obtain ⟨w, hd, hw⟩ := yv_hash hy hhp hhE
  by_cases hsp : trunc w = trunc (ξ.2 h.fin)
  · exact ⟨h, v, hhp, yv y v, hne, tagNat_yv hA hy hhp hhE, w, hd, hsp⟩
  · rcases hashParent_cases hhp with rfl | ⟨v', hv'⟩
    · exfalso
      apply hsp
      rw [hw]
      exact hacc
    · have hcv' : child h = some v' := child_hashOf hv'
      have hv'E : Evaluated A v' :=
        ⟨hv v' (Above.step hch (Above.child hcv')),
          fun m hm => hv m (Above.step hch (Above.step hcv' hm))⟩
      refine ih v' ?_ hv'E.2 (cost_of_hashOf hv') ?_
      · have h1 := height_child hch
        have h2 := height_child hcv'
        omega
      · intro heq
        apply hsp
        rw [hw, ← yv_of_hashOf hy hv' hv'E, heq, val_of_hashOf ξ hv']

/-- **The walk.** -/
theorem up {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : trunc (yv y rh) = pkOf ξ) {v : Name} (hv : ∀ m, Above m v → m ∉ A)
    (hvh : v.cost = 0) (hne : yv y v ≠ val ξ v) : Spr d ξ := by
  suffices ∀ n, ∀ v, height v = n → (∀ m, Above m v → m ∉ A) → v.cost = 0 →
      yv y v ≠ val ξ v → Spr d ξ from this _ v rfl hv hvh hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv hvh hne
    have ih' : ∀ v', height v' < height v → (∀ m, Above m v' → m ∉ A) → v'.cost = 0 →
        yv y v' ≠ val ξ v' → Spr d ξ :=
      fun v' hlt => ih (height v') (by omega) v' rfl
    cases v with
    | src k =>
      have hch : child (src k) = some (ci k 0) := rfl
      have hcE : Evaluated A (ci k 0) :=
        ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
      refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
      exact yv_ci_ne hy hcE hne
    | ci k t =>
      exact hash_step hA hy hacc (h := ch k t) rfl rfl hv hne ih'
    | cv k t =>
      by_cases ht : t.val = 14
      · have ht' : t = 14 := Fin.ext ht
        subst ht'
        have hch : child (cv k 14) = some rc := rfl
        have hcE : Evaluated A rc :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        intro heq
        rw [yv_rc hy hcE, val_rc'] at heq
        exact hne (congrFun (rootCat_inj heq) k)
      · have hch : child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by simp [Name.child, ht]
        have hcE : Evaluated A (ci k ⟨t.val + 1, by omega⟩) :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        refine yv_ci_ne hy hcE ?_
        rw [prev_succ k t (by omega)]
        exact hne
    | rc =>
      exact hash_step hA hy hacc (h := rh) rfl rfl hv hne ih'
    | ch k t => exact absurd hvh (by simp [Name.cost])
    | rh => exact absurd hvh (by simp [Name.cost])

/-! ## The events -/

/-- Signing failed: everything is hidden. -/
theorem events_none {A' : Finset Name} (hA' : IsCut A') {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A') given y)
    (hacc : trunc (yv y rh) = pkOf ξ) : Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  have hrE : Evaluated A' rh := ⟨hA'.rh_not_mem, fun m hm => absurd hm (not_above_rh m)⟩
  obtain ⟨w, hd, -⟩ := yv_hash hy (p := rc) rfl hrE
  by_cases hne : yv y rc = val ξ rc
  · right
    refine ⟨⟨rc.len, yv y rc⟩, ?_, by rw [hd]; rfl⟩
    rw [kc_isSome_iff]
    exact ⟨rh, rc, rfl, by rw [hne]; rfl⟩
  · left
    refine up hA' hy hacc (v := rc) ?_ rfl hne
    intro m hm
    rw [above_of_child (show child rc = some rh from rfl)] at hm
    rcases hm with rfl | hm
    · exact hA'.rh_not_mem
    · exact absurd hm (not_above_rh m)

/-- The forgery uses a different disclosure set of the same cost. -/
theorem events_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hcost : ∑ n ∈ evaluatedSet A, n.cost = ∑ n ∈ evaluatedSet A', n.cost) (hne : A ≠ A')
    {ξ : Rec} {d : Cache} {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y) (hacc : trunc (yv y rh) = pkOf ξ) :
    Spr d ξ ∨ Cache.Hits d (fHid (some A) ξ) := by
  obtain ⟨v, hvA, hvE⟩ := exists_mem_evaluated_of_ne hA hA' hcost hne
  have hlen : v.len = 128 := hA.values v hvA
  have hns : ∀ k, v ≠ src k := by
    intro k hk
    subst hk
    rcases hA'.covers k with h | ⟨m, hmA', hm⟩
    · exact hvE.1 h
    · exact hvE.2 m hm hmA'
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((hashOf_isSome_iff v).mpr ⟨hlen, hns⟩)
  have hch : child h = some v := child_hashOf hh
  have hhA' : h ∉ A' := fun hm => by
    have := hA'.values h hm
    rw [len_of_hashOf hh] at this
    omega
  have hhE : Evaluated A' h := by
    refine ⟨hhA', fun m hm => ?_⟩
    rw [above_of_child hch] at hm
    rcases hm with rfl | hm
    · exact hvE.1
    · exact hvE.2 m hm
  obtain ⟨p, hhp⟩ := hashParent_of_hashOf hh
  by_cases hvne : yv y v = val ξ v
  · obtain ⟨w, hd, hw⟩ := yv_hash hy hhp hhE
    have htr : trunc w = trunc (ξ.2 h.fin) := by
      rw [hw, ← yv_of_hashOf hy hh hvE, hvne, val_of_hashOf ξ hh]
    by_cases hpne : yv y p = val ξ p
    · right
      refine ⟨⟨p.len, yv y p⟩, ?_, by rw [hd]; rfl⟩
      rw [fHid_isSome_some_iff]
      exact ⟨h, p, hhp, hA.not_evaluated_hashOf hvA hh, by rw [hpne]; rfl⟩
    · left
      exact ⟨h, p, hhp, yv y p, hpne, tagNat_yv hA' hy hhp hhE, w, hd, htr⟩
  · left
    exact up hA' hy hacc hvE.2 (cost_of_hashOf hh) hvne

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- `encode` only reads the values on the set. -/
theorem encode_congr (G : Graph) (A : Finset (Fin G.size))
    {x x' : G.Assignment} (h : ∀ v ∈ A, x v = x' v) : G.encode A x = G.encode A x' := by
  unfold Graph.encode
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_filter, decide_eq_true_iff] at hv
  rw [h v hv.2]

attribute [local semireducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- The forgery uses the signed disclosure set with different values. -/
theorem events_same {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {x' : List Bool} {y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A) (graph.decode (fins A) x') y)
    (hacc : trunc (yv y rh) = pkOf ξ) (hlen : x'.length = graph.revealBits (fins A))
    (hne : x' ≠ graph.encode (fins A) (graph.evalRec ξ)) : Spr d ξ := by
  have hex : ∃ a ∈ A, graph.decode (fins A) x' a.fin ≠ graph.evalRec ξ a.fin := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← graph.encode_decode (fins A) x' hlen]
    apply encode_congr
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact hcon a ha
  obtain ⟨a, ha, hne'⟩ := hex
  have hcost : a.cost = 0 := cost_eq_zero_of_len (hA.values a ha)
  refine up hA hy hacc (hA.antichain a ha) hcost ?_
  intro heq
  apply hne'
  rw [yv_mem hy ha] at heq
  unfold val at heq
  exact cast_injective _ heq

end Forest

end OptimalOTS
