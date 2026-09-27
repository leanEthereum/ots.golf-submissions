import Submissions.UpperRiscv.Values
import Submissions.UpperRiscv.Reconstruct

/-!
# From an accepted forgery to a bad event

Let the verifier reconstruct the root from values `given` at the disclosure set `A'` and obtain the
assignment `y`, all answers being recorded in the cache `d` (`Graph.ReconEqs`), and accept:
the first 128 bits of `y` at the root are the public key of the honest record `ξ`.

* `up` (the walk in the proof of the paper's Section 7.3): if `y` differs from the honest values,
  on the bits the graph reads (`Dif`), at a non-hash node visited by the reconstruction, some
  recorded answer at a non-keygen point simulates an honest output (`Spr d ξ`).
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

theorem trunc_cast_eq (k : Fin 33) {a b : ℕ} (h : a = b) (x : BitVec a) : trunc k (x.cast h) = trunc k x := by
  subst h; rfl

theorem trunc_state (k : Fin 33) (x : BitVec (chainBits k)) : trunc k x = x := trunc_eq_self k x

theorem trunc_src (k : Fin 33) (x : BitVec (src k).len) : trunc k x = x := trunc_eq_self k x

theorem cast_injective {n m : ℕ} (h : n = m) {x y : BitVec n} (e : x.cast h = y.cast h) :
    x = y := by
  subst h; simpa using e

/-- Both halves of a concatenation are determined by it. -/
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

/-! ## Names -/

theorem cost_eq_zero_of_len {n : Name} (h : n.len = 192) : n.cost = 0 := by
  cases n <;> first | rfl | (simp [Name.len] at h)

theorem len_eq_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.len = 256 := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp <;> rfl

/-- The input of a hash node is a deterministic node. -/
theorem cost_hashParent {h p : Name} (hp : hashParent h = some p) : p.cost = 0 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;> rfl

theorem hashParent_ne_src {h p : Name} (hp : hashParent h = some p) (k : Fin 33) : p ≠ src k := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact fun e => nomatch e

theorem prev_zero (k : Fin 33) : prev k 0 = src k := by
  simp [prev]

theorem prev_succ (k : Fin 33) (t : Fin 32) (ht : t.val < 31) :
    prev k ⟨t.val + 1, by omega⟩ = cv k t := by
  simp [prev]

theorem prev_of_ne_zero (k : Fin 33) (t : Fin 32) (ht : ¬ t.val = 0) :
    prev k t = cv k ⟨t.val - 1, by omega⟩ := by
  simp [prev, ht]

theorem hashOf_of_ne_zero (k : Fin 33) (t : Fin 32) (ht : ¬ t.val = 0) :
    hashOf (ci k t) = some (ch k ⟨t.val - 1, by omega⟩) := by
  simp [hashOf, ht]

theorem child_cv_of_ne (k : Fin 33) (t : Fin 32) (ht : ¬ t.val = 31) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp [Name.child, ht]

theorem child_cv_top (k : Fin 33) (t : Fin 32) (ht : t.val = 31) : child (cv k t) = some (tp k) := by
  simp [Name.child, ht]

theorem val_tp' (ξ : Rec) (k : Fin 33) : val ξ (tp k) = topSlice k (val ξ (cv k 31)) := by
  rw [val_tp, val_cv]

theorem val_rc' (ξ : Rec) : val ξ rc = rootRegion fun k => val ξ (tp k) := by
  rw [val_rc]
  exact congrArg rootRegion (funext fun k => (val_tp ξ k).symm)

/-- A cut holds only chain inputs and tops. -/
theorem IsCut.not_mem_of {A : Finset Name} (hA : IsCut A) (n : Name) (hci : ∀ k t, n ≠ ci k t)
    (htp : ∀ k, n ≠ tp k) : n ∉ A := by
  intro hn
  rcases hA.values n hn with ⟨k, t, rfl⟩ | ⟨k, rfl⟩
  · exact hci k t rfl
  · exact htp k rfl

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
    ∃ w, d ⟨p.len, yv y p⟩ = some w ∧ yv y h = w.cast (len_eq_of_hashParent hp).symm := by
  obtain ⟨hlt, hl, hk⟩ := graph_kind_hash hp
  obtain ⟨w, hw, hyw⟩ := (recon_evaluated hy he).1 _ _ _ hk
  refine ⟨w, ?_, ?_⟩
  · rw [sigma_cast (graph_len_fin p) (y p.fin)] at hw
    exact hw
  · unfold yv
    rw [hyw]
    rfl

theorem yv_hash_ch (hy : graph.ReconEqs d (fins A) given y) {k : Fin 33} {t : Fin 32}
    (he : Evaluated A (ch k t)) :
    ∃ w : BitVec 256, d ⟨chainBits k, yv y (ci k t)⟩ = some w ∧ yv y (ch k t) = w := by
  obtain ⟨w, hd, hw⟩ := yv_hash hy (h := ch k t) (p := ci k t) rfl he
  exact ⟨w, hd, hw⟩

theorem yv_hash_rh (hy : graph.ReconEqs d (fins A) given y) (he : Evaluated A rh) :
    ∃ w : BitVec 256, d ⟨6400, yv y rc⟩ = some w ∧ yv y rh = w := by
  obtain ⟨w, hd, hw⟩ := yv_hash hy (h := rh) (p := rc) rfl he
  exact ⟨w, hd, hw⟩

/-- The value of an evaluated deterministic node. -/
theorem yv_det (hy : graph.ReconEqs d (fins A) given y) {n : Name} (he : Evaluated A n)
    (hc : n.cost = 0) (hs : ∀ k, n ≠ src k) : yv y n = detVal n y := by
  obtain ⟨hlt, hf, hk⟩ := graph_kind_det hc hs
  have := (recon_evaluated hy he).2.1 _ _ _ _ hk
  unfold yv
  rw [this]
  simp

theorem yv_cv (hy : graph.ReconEqs d (fins A) given y) {k : Fin 33} {t : Fin 32}
    (he : Evaluated A (cv k t)) : yv y (cv k t) = yv y (ch k t) := by
  rw [yv_det hy he rfl (by simp)]
  rfl

/-- The input of a chain hash: the truncated value before it. -/
theorem yv_ci (hy : graph.ReconEqs d (fins A) given y) {k : Fin 33} {t : Fin 32}
    (he : Evaluated A (ci k t)) : yv y (ci k t) = trunc k (yv y (prev k t)) := by
  rw [yv_det hy he rfl (by simp)]
  show trunc k (y (prev k t).fin) = _
  unfold yv
  rw [trunc_cast_eq]

theorem yv_tp (hy : graph.ReconEqs d (fins A) given y) {k : Fin 33} (he : Evaluated A (tp k)) :
    yv y (tp k) = topSlice k (yv y (cv k 31)) := by
  rw [yv_det hy he rfl (by simp)]
  rfl

theorem yv_rc (hy : graph.ReconEqs d (fins A) given y) (he : Evaluated A rc) :
    yv y rc = rootRegion fun k => yv y (tp k) := by
  rw [yv_det hy he rfl (by simp)]
  rfl

end Recon

/-! ## The walk -/

/-- The forged value at a node differs from the honest one on the bits the graph reads from it:
all of them at a source, a chain input, a top or the root input; the next state slice at a chain
value below the last level; the root slot at the last level. -/
def Dif (ξ : Rec) : (v : Name) → BitVec v.len → Prop
  | cv k t, x => if t.val = 31 then topSlice k x ≠ topSlice k (val ξ (cv k t)) else
      trunc k x ≠ trunc k (val ξ (cv k t))
  | v, x => x ≠ val ξ v

theorem dif_src {ξ : Rec} {k : Fin 33} {x : BitVec (src k).len} (h : x ≠ val ξ (src k)) :
    Dif ξ (src k) x := h

theorem dif_ci {ξ : Rec} {k : Fin 33} {t : Fin 32} {x : BitVec (ci k t).len}
    (h : x ≠ val ξ (ci k t)) : Dif ξ (ci k t) x := h

theorem dif_rc {ξ : Rec} {x : BitVec rc.len} (h : x ≠ val ξ rc) : Dif ξ rc x := h

theorem dif_cv_of_lt {ξ : Rec} {k : Fin 33} {t : Fin 32} (ht : ¬ t.val = 31)
    {x : BitVec (cv k t).len} : Dif ξ (cv k t) x ↔ trunc k x ≠ trunc k (val ξ (cv k t)) := by
  show (if t.val = 31 then _ else _) ↔ _
  rw [if_neg ht]

theorem dif_cv_top {ξ : Rec} {k : Fin 33} {t : Fin 32} (ht : t.val = 31)
    {x : BitVec (cv k t).len} : Dif ξ (cv k t) x ↔ topSlice k x ≠ topSlice k (val ξ (cv k t)) := by
  show (if t.val = 31 then _ else _) ↔ _
  rw [if_pos ht]

theorem sim_ch_of_lo192 {ξ : Rec} {k : Fin 33} {t : Fin 32} (ht : t.val = 31) {w : BitVec 256}
    (hs : topSlice k w = topSlice k (ξ.2 (ch k t).fin)) : sim ξ (ch k t) w := by
  simpa [sim, ht] using hs

/-- **The walk.** -/
theorem up {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : trunc128 (yv y rh) = pkOf ξ) {v : Name} (hv : ∀ m, Above m v → m ∉ A)
    (hvh : v.cost = 0) (hne : Dif ξ v (yv y v)) : Spr d ξ := by
  suffices ∀ n, ∀ v, height v = n → (∀ m, Above m v → m ∉ A) → v.cost = 0 →
      Dif ξ v (yv y v) → Spr d ξ from this _ v rfl hv hvh hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv hvh hne
    have ih' : ∀ v', height v' < height v → (∀ m, Above m v' → m ∉ A) → v'.cost = 0 →
        Dif ξ v' (yv y v') → Spr d ξ :=
      fun v' hlt => ih (height v') (by omega) v' rfl
    cases v with
    | src k =>
      have hch : child (src k) = some (ci k 0) := rfl
      have hcE : Evaluated A (ci k 0) :=
        ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
      refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
      refine dif_ci ?_
      rw [yv_ci hy hcE, val_ci_zero ξ k 0 rfl, prev_zero, trunc_src]
      exact hne
    | ci k t =>
      -- through the hash node `ch k t`
      have hch : child (ci k t) = some (ch k t) := rfl
      have hhE : Evaluated A (ch k t) :=
        ⟨hA.not_mem_of _ (by simp) (by simp), fun m hm => hv m (Above.step hch hm)⟩
      obtain ⟨w, hd, hw⟩ := yv_hash_ch hy hhE
      by_cases hsim : sim ξ (ch k t) w
      · exact Or.inl ⟨ch k t, ci k t, rfl, yv y (ci k t), hne, w, hd, hsim⟩
      · have hch' : child (ch k t) = some (cv k t) := rfl
        have hcE : Evaluated A (cv k t) :=
          ⟨hA.not_mem_of _ (by simp) (by simp),
            fun m hm => hv m (Above.step hch (Above.step hch' hm))⟩
        refine ih' _ ?_ hcE.2 rfl ?_
        · have h1 := height_child hch
          have h2 := height_child hch'
          omega
        · have e3 : yv y (cv k t) = w := (yv_cv hy hcE).trans hw
          by_cases ht : t.val = 31
          · rw [dif_cv_top ht, val_cv, e3]
            exact fun e => hsim (sim_ch_of_lo192 ht e)
          · rw [dif_cv_of_lt ht, val_cv, e3]
            exact fun e => hsim (sim_ch_of_trunc ht e)
    | cv k t =>
      by_cases ht : t.val = 31
      · have hch : child (cv k t) = some (tp k) := child_cv_top k t ht
        have hcE : Evaluated A (tp k) :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        show yv y (tp k) ≠ val ξ (tp k)
        have ht' : t = 31 := Fin.ext ht
        subst ht'
        rw [yv_tp hy hcE, val_tp']
        exact (dif_cv_top rfl).1 hne
      · have hch : child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := child_cv_of_ne k t ht
        have hcE : Evaluated A (ci k ⟨t.val + 1, by omega⟩) :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        refine dif_ci ?_
        rw [yv_ci hy hcE, val_ci, prev_succ k t (by omega)]
        exact (dif_cv_of_lt ht).1 hne
    | tp k =>
      have hch : child (tp k) = some rc := rfl
      have hcE : Evaluated A rc :=
        ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
      refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
      refine dif_rc fun heq => ?_
      rw [yv_rc hy hcE, val_rc'] at heq
      exact hne (congrFun (rootRegion_injective heq) k)
    | rc =>
      have hch : child rc = some rh := rfl
      have hhE : Evaluated A rh :=
        ⟨hA.not_mem_of _ (by simp) (by simp), fun m hm => hv m (Above.step hch hm)⟩
      obtain ⟨w, hd, hw⟩ := yv_hash_rh hy hhE
      by_cases hsim : sim ξ rh w
      · exact Or.inl ⟨rh, rc, rfl, yv y rc, hne, w, hd, hsim⟩
      · exfalso
        apply hsim
        rw [sim_rh_iff, ← hw]
        exact hacc
    | ch k t => exact absurd hvh (by simp [Name.cost])
    | rh => exact absurd hvh (by simp [Name.cost])

/-! ## The events -/

/-- Signing failed: everything is hidden. -/
theorem events_none {A' : Finset Name} (hA' : IsCut A') {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A') given y)
    (hacc : trunc128 (yv y rh) = pkOf ξ) : Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  have hrE : Evaluated A' rh := ⟨hA'.rh_not_mem, fun m hm => absurd hm (not_above_rh m)⟩
  obtain ⟨w, hd, -⟩ := yv_hash_rh hy hrE
  by_cases hne : yv y rc = val ξ rc
  · right
    refine ⟨⟨6400, yv y rc⟩, ?_, by rw [hd]; rfl⟩
    rw [kc_isSome_iff]
    exact ⟨rh, rc, rfl, by rw [hne]; rfl⟩
  · left
    refine up hA' hy hacc (v := rc) ?_ rfl (dif_rc hne)
    intro m hm
    rw [above_of_child (show child rc = some rh from rfl)] at hm
    rcases hm with rfl | hm
    · exact hA'.rh_not_mem
    · exact absurd hm (not_above_rh m)

/-- A cut node evaluated at another cut is not at the bottom of its chain. -/
theorem ne_zero_of_evaluated {A' : Finset Name} (hA' : IsCut A') {k : Fin 33} {t : Fin 32}
    (hvE : Evaluated A' (ci k t)) : ¬ t.val = 0 := by
  intro ht
  obtain rfl : t = 0 := Fin.ext ht
  rcases hA'.covers k with h | ⟨m, hmA', hm⟩
  · rcases hA'.values _ h with ⟨_, _, e⟩ | ⟨_, e⟩ <;> cases e
  · rw [above_of_child (show child (src k) = some (ci k 0) from rfl)] at hm
    rcases hm with rfl | hm
    · exact hvE.1 hmA'
    · exact hvE.2 m hm hmA'

/-- The forgery uses a different disclosure set of the same cost. -/
theorem events_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hcost : ∑ n ∈ evaluatedSet A, n.cost = ∑ n ∈ evaluatedSet A', n.cost) (hne : A ≠ A')
    {ξ : Rec} {d : Cache} {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y) (hacc : trunc128 (yv y rh) = pkOf ξ) :
    Spr d ξ ∨ Cache.Hits d (fHid (some A) ξ) := by
  obtain ⟨v, hvA, hvE⟩ := exists_mem_evaluated_of_ne hA hA' hcost hne
  rcases hA.values v hvA with ⟨k, t, rfl⟩ | ⟨k, rfl⟩
  swap
  · -- a revealed cap top, evaluated by the forgery through `ch k 31`
    have hcv : child (cv k 31) = some (tp k) := rfl
    have hcvE : Evaluated A' (cv k 31) := by
      refine ⟨hA'.not_mem_of _ (by simp) (by simp), fun m hm => ?_⟩
      rw [above_of_child hcv] at hm
      rcases hm with rfl | hm
      · exact hvE.1
      · exact hvE.2 m hm
    have hhE : Evaluated A' (ch k 31) := by
      refine ⟨hA'.not_mem_of _ (by simp) (by simp), fun m hm => ?_⟩
      rw [above_of_child (show child (ch k 31) = some (cv k 31) from rfl)] at hm
      rcases hm with rfl | hm
      · exact hcvE.1
      · exact hcvE.2 m hm
    by_cases hvne : yv y (tp k) = val ξ (tp k)
    · obtain ⟨w, hd, hw⟩ := yv_hash_ch hy hhE
      have htr : topSlice k w = topSlice k (ξ.2 (ch k 31).fin) := by
        have f3 : yv y (cv k 31) = w := (yv_cv hy hcvE).trans hw
        have := hvne
        rw [yv_tp hy hvE, val_tp', f3, val_cv] at this
        exact this
      have hsim : sim ξ (ch k 31) w := sim_ch_of_lo192 rfl htr
      by_cases hpne : yv y (ci k 31) = val ξ (ci k 31)
      · right
        refine ⟨⟨chainBits k, yv y (ci k 31)⟩, ?_, by rw [hd]; rfl⟩
        rw [fHid_isSome_some_iff]
        exact ⟨ch k 31, ci k 31, rfl, hA.not_evaluated_hashOf hvA rfl, by rw [hpne]; rfl⟩
      · left
        exact Or.inl ⟨ch k 31, ci k 31, rfl, yv y (ci k 31), hpne, w, hd, hsim⟩
    · left
      exact up hA' hy hacc hvE.2 rfl hvne
  have ht0 : ¬ t.val = 0 := ne_zero_of_evaluated hA' hvE
  -- the hash node feeding the cut node, and its value node
  have hlt := t.isLt
  obtain ⟨t', ht'⟩ : ∃ t' : Fin 32, t'.val + 1 = t.val := ⟨⟨t.val - 1, by omega⟩, by show t.val - 1 + 1 = t.val; omega⟩
  have e1 : (⟨t.val - 1, by omega⟩ : Fin 32) = t' := Fin.ext (by simp only; omega)
  have e2 : (⟨t'.val + 1, by omega⟩ : Fin 32) = t := Fin.ext ht'
  have hh : hashOf (ci k t) = some (ch k t') := by rw [hashOf_of_ne_zero k t ht0, e1]
  have hprev : prev k t = cv k t' := by rw [prev_of_ne_zero k t ht0, e1]
  have hcv : child (cv k t') = some (ci k t) := by
    rw [child_cv_of_ne k t' (by omega), e2]
  have hcvE : Evaluated A' (cv k t') := by
    refine ⟨hA'.not_mem_of (cv k t') (by simp) (by simp), fun m hm => ?_⟩
    rw [above_of_child hcv] at hm
    rcases hm with rfl | hm
    · exact hvE.1
    · exact hvE.2 m hm
  have hhE : Evaluated A' (ch k t') := by
    refine ⟨hA'.not_mem_of (ch k t') (by simp) (by simp), fun m hm => ?_⟩
    rw [above_of_child (show child (ch k t') = some (cv k t') from rfl)] at hm
    rcases hm with rfl | hm
    · exact hcvE.1
    · exact hcvE.2 m hm
  by_cases hvne : yv y (ci k t) = val ξ (ci k t)
  · obtain ⟨w, hd, hw⟩ := yv_hash_ch hy hhE
    have htr : trunc k w = trunc k (ξ.2 (ch k t').fin) := by
      have f1 : yv y (ci k t) = trunc k (yv y (cv k t')) := by rw [yv_ci hy hvE, hprev]
      have f2 : val ξ (ci k t) = trunc k (val ξ (cv k t')) := by rw [val_ci, hprev]
      have f3 : yv y (cv k t') = w := (yv_cv hy hcvE).trans hw
      have := hvne
      rw [f1, f2, f3, val_cv] at this
      exact this
    have hsim : sim ξ (ch k t') w := sim_ch_of_trunc (by omega) htr
    by_cases hpne : yv y (ci k t') = val ξ (ci k t')
    · right
      refine ⟨⟨chainBits k, yv y (ci k t')⟩, ?_, by rw [hd]; rfl⟩
      rw [fHid_isSome_some_iff]
      exact ⟨ch k t', ci k t', rfl, hA.not_evaluated_hashOf hvA hh, by rw [hpne]; rfl⟩
    · left
      exact Or.inl ⟨ch k t', ci k t', rfl, yv y (ci k t'), hpne, w, hd, hsim⟩
  · left
    exact up hA' hy hacc hvE.2 rfl (dif_ci hvne)

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
    (hacc : trunc128 (yv y rh) = pkOf ξ) (hlen : x'.length = graph.revealBits (fins A))
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
  have hneq : yv y a ≠ val ξ a := by
    intro heq
    apply hne'
    rw [yv_mem hy ha] at heq
    unfold val at heq
    exact cast_injective _ heq
  rcases hA.values a ha with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · exact up hA hy hacc (hA.antichain _ ha) rfl hneq
  · exact up hA hy hacc (hA.antichain _ ha) rfl hneq

end Forest

end OptimalOTS
