import Submissions.UpperRiscvHint.Values
import Submissions.UpperRiscvHint.Reconstruct

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

theorem trunc_cast_eq (k : Fin 32) {a b : ℕ} (h : a = b) (x : BitVec a) : trunc k (x.cast h) = trunc k x := by
  subst h; rfl

theorem trunc_state (k : Fin 32) (x : BitVec (chainBits k)) : trunc k x = x := trunc_eq_self k x

theorem trunc_src (k : Fin 32) (x : BitVec (src k).len) : trunc k x = x := trunc_eq_self k x

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

theorem slotCat_inj {a b : (k : Fin 32) → BitVec (topBits k)} :
    ∀ s, slotCat a s = slotCat b s → ∀ j ≤ s, a (slotChain j) = b (slotChain j)
  | 0, h, j, hj => by
    obtain rfl : j = 0 := by omega
    exact h
  | s + 1, h, j, hj => by
    obtain ⟨h1, h2⟩ := bv_append_inj (x := a (slotChain (s + 1))) (y := slotCat a s) h
    rcases Nat.lt_or_ge j (s + 1) with lt | ge
    · exact slotCat_inj s h2 j (by omega)
    · obtain rfl : j = s + 1 := by omega
      exact h1

/-- The root slot of chain `k`. -/
def slotOf (k : Fin 32) : ℕ := if k.val < 16 then 2 * k.val else 2 * (k.val - 16) + 1

theorem slotChain_slotOf (k : Fin 32) : slotChain (slotOf k) = k := by
  apply Fin.ext
  simp only [slotChain, slotOf]
  split_ifs <;> omega

/-- The root input determines every top. -/
theorem rootCat_inj {a b : (k : Fin 32) → BitVec (topBits k)} (h : rootCat a = rootCat b) :
    a = b := by
  unfold rootCat at h
  funext k
  have key := slotCat_inj 31 (cast_injective _ h) (slotOf k) (by unfold slotOf; split_ifs <;> omega)
  rwa [slotChain_slotOf] at key

/-! ## Names -/

theorem cost_eq_zero_of_len {n : Name} (h : n.len = 192) : n.cost = 0 := by
  cases n <;> first | rfl | (simp [Name.len] at h)

theorem len_eq_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.len = 256 := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp <;> rfl

/-- The input of a hash node is a deterministic node. -/
theorem cost_hashParent {h p : Name} (hp : hashParent h = some p) : p.cost = 0 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;> rfl

theorem hashParent_ne_src {h p : Name} (hp : hashParent h = some p) (k : Fin 32) : p ≠ src k := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact fun e => nomatch e

theorem prev_zero (k : Fin 32) : prev k 0 = src k := by
  simp [prev]

theorem prev_succ (k : Fin 32) (t : Fin 32) (ht : t.val < 31) :
    prev k ⟨t.val + 1, by omega⟩ = cv k t := by
  simp [prev]

theorem prev_of_ne_zero (k : Fin 32) (t : Fin 32) (ht : ¬ t.val = 0) :
    prev k t = cv k ⟨t.val - 1, by omega⟩ := by
  simp [prev, ht]

theorem hashOf_of_ne_zero (k : Fin 32) (t : Fin 32) (ht : ¬ t.val = 0) :
    hashOf (ci k t) = some (ch k ⟨t.val - 1, by omega⟩) := by
  simp [hashOf, ht]

theorem child_cv_of_ne (k : Fin 32) (t : Fin 32) (ht : ¬ t.val = 31) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp [Name.child, ht]

theorem child_cv_top (k : Fin 32) (t : Fin 32) (ht : t.val = 31) :
    child (cv k t) = some (top k) := by
  simp [Name.child, ht]

theorem val_top' (ξ : Rec) (k : Fin 32) : val ξ (top k) = topOf k (val ξ (cv k 31)) := by
  rw [val_top, val_cv]

theorem val_rc' (ξ : Rec) : val ξ rc = rootCat fun k => val ξ (top k) := by
  rw [val_rc]
  exact congrArg rootCat (funext fun k => (val_top ξ k).symm)

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

theorem yv_hash_ch (hy : graph.ReconEqs d (fins A) given y) {k : Fin 32} {t : Fin 32}
    (he : Evaluated A (ch k t)) :
    ∃ w : BitVec 256, d ⟨chainBits k, yv y (ci k t)⟩ = some w ∧ yv y (ch k t) = w := by
  obtain ⟨w, hd, hw⟩ := yv_hash hy (h := ch k t) (p := ci k t) rfl he
  exact ⟨w, hd, hw⟩

theorem yv_hash_rh (hy : graph.ReconEqs d (fins A) given y) (he : Evaluated A rh) :
    ∃ w : BitVec 256, d ⟨7104, yv y rc⟩ = some w ∧ yv y rh = w := by
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

theorem yv_cv (hy : graph.ReconEqs d (fins A) given y) {k : Fin 32} {t : Fin 32}
    (he : Evaluated A (cv k t)) : yv y (cv k t) = yv y (ch k t) := by
  rw [yv_det hy he rfl (by simp)]
  rfl

/-- The input of a chain hash: the truncated value before it. -/
theorem yv_ci (hy : graph.ReconEqs d (fins A) given y) {k : Fin 32} {t : Fin 32}
    (he : Evaluated A (ci k t)) : yv y (ci k t) = trunc k (yv y (prev k t)) := by
  rw [yv_det hy he rfl (by simp)]
  show trunc k (y (prev k t).fin) = _
  unfold yv
  rw [trunc_cast_eq]

theorem yv_top (hy : graph.ReconEqs d (fins A) given y) {k : Fin 32} (he : Evaluated A (top k)) :
    yv y (top k) = topOf k (yv y (cv k 31)) := by
  rw [yv_det hy he rfl (by simp)]
  rfl

theorem yv_rc (hy : graph.ReconEqs d (fins A) given y) (he : Evaluated A rc) :
    yv y rc = rootCat fun k => yv y (top k) := by
  rw [yv_det hy he rfl (by simp)]
  rfl

end Recon

/-! ## The walk -/

/-- The forged value at a node differs from the honest one on the bits the graph reads from it:
all of them at a source, a chain input, a top or the root input; the next state at a chain value
below the last level; the committed top at the last level. -/
def Dif (ξ : Rec) : (v : Name) → BitVec v.len → Prop
  | cv k t, x => if t.val = 31 then topOf k x ≠ topOf k (val ξ (cv k t)) else
      trunc k x ≠ trunc k (val ξ (cv k t))
  | v, x => x ≠ val ξ v

theorem dif_src {ξ : Rec} {k : Fin 32} {x : BitVec (src k).len} (h : x ≠ val ξ (src k)) :
    Dif ξ (src k) x := h

theorem dif_ci {ξ : Rec} {k : Fin 32} {t : Fin 32} {x : BitVec (ci k t).len}
    (h : x ≠ val ξ (ci k t)) : Dif ξ (ci k t) x := h

theorem dif_top {ξ : Rec} {k : Fin 32} {x : BitVec (top k).len} (h : x ≠ val ξ (top k)) :
    Dif ξ (top k) x := h

theorem dif_rc {ξ : Rec} {x : BitVec rc.len} (h : x ≠ val ξ rc) : Dif ξ rc x := h

theorem dif_of_revealable {ξ : Rec} {a : Name} (ha : Revealable a) {x : BitVec a.len}
    (h : x ≠ val ξ a) : Dif ξ a x := by
  cases a with
  | ci _ _ => exact h
  | top _ => exact h
  | src _ | ch _ _ | cv _ _ | rc | rh => exact (ha : False).elim

theorem dif_cv_of_lt {ξ : Rec} {k : Fin 32} {t : Fin 32} (ht : ¬ t.val = 31)
    {x : BitVec (cv k t).len} : Dif ξ (cv k t) x ↔ trunc k x ≠ trunc k (val ξ (cv k t)) := by
  show (if t.val = 31 then _ else _) ↔ _
  rw [if_neg ht]

theorem dif_cv_top {ξ : Rec} {k : Fin 32} {t : Fin 32} (ht : t.val = 31)
    {x : BitVec (cv k t).len} : Dif ξ (cv k t) x ↔ topOf k x ≠ topOf k (val ξ (cv k t)) := by
  show (if t.val = 31 then _ else _) ↔ _
  rw [if_pos ht]

theorem sim_ch_of_topOf {ξ : Rec} {k : Fin 32} {t : Fin 32} (ht : t.val = 31) {w : BitVec 256}
    (hs : topOf k w = topOf k (ξ.2 (ch k t).fin)) : sim ξ (ch k t) w := by
  simpa [sim, ht] using hs

/-- **The walk.** -/
theorem up {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : flipHi (trunc128 (yv y rh)) = pkOf ξ) {v : Name} (hv : ∀ m, Above m v → m ∉ A)
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
    have notMem_of_len : ∀ m, ¬ m.len ≤ 192 → m ∉ A := fun m hm hmA => hm (hA.len_le hmA)
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
        ⟨notMem_of_len _ (by simp [Name.len]), fun m hm => hv m (Above.step hch hm)⟩
      obtain ⟨w, hd, hw⟩ := yv_hash_ch hy hhE
      by_cases hsim : sim ξ (ch k t) w
      · exact ⟨ch k t, ci k t, rfl, yv y (ci k t), hne, w, hd, hsim⟩
      · have hch' : child (ch k t) = some (cv k t) := rfl
        have hcE : Evaluated A (cv k t) :=
          ⟨notMem_of_len _ (by simp [Name.len]),
            fun m hm => hv m (Above.step hch (Above.step hch' hm))⟩
        refine ih' _ ?_ hcE.2 rfl ?_
        · have h1 := height_child hch
          have h2 := height_child hch'
          omega
        · have e3 : yv y (cv k t) = w := (yv_cv hy hcE).trans hw
          by_cases ht : t.val = 31
          · rw [dif_cv_top ht, val_cv, e3]
            exact fun e => hsim (sim_ch_of_topOf ht e)
          · rw [dif_cv_of_lt ht, val_cv, e3]
            exact fun e => hsim (sim_ch_of_trunc ht e)
    | cv k t =>
      by_cases ht : t.val = 31
      · have ht' : t = 31 := Fin.ext ht
        subst ht'
        have hch : child (cv k 31) = some (top k) := rfl
        have hcE : Evaluated A (top k) :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        refine dif_top fun heq => ?_
        rw [yv_top hy hcE, val_top'] at heq
        exact (dif_cv_top rfl).1 hne heq
      · have hch : child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := child_cv_of_ne k t ht
        have hcE : Evaluated A (ci k ⟨t.val + 1, by omega⟩) :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        refine dif_ci ?_
        rw [yv_ci hy hcE, val_ci, prev_succ k t (by omega)]
        exact (dif_cv_of_lt ht).1 hne
    | top k =>
      have hch : child (top k) = some rc := rfl
      have hcE : Evaluated A rc :=
        ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
      refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
      refine dif_rc fun heq => ?_
      rw [yv_rc hy hcE, val_rc'] at heq
      exact hne (congrFun (rootCat_inj heq) k)
    | rc =>
      have hch : child rc = some rh := rfl
      have hhE : Evaluated A rh :=
        ⟨notMem_of_len _ (by simp [Name.len]), fun m hm => hv m (Above.step hch hm)⟩
      obtain ⟨w, hd, hw⟩ := yv_hash_rh hy hhE
      by_cases hsim : sim ξ rh w
      · exact ⟨rh, rc, rfl, yv y rc, hne, w, hd, hsim⟩
      · exfalso
        apply hsim
        rw [sim_rh_iff, ← hw]
        exact flipHi_injective hacc
    | ch k t => exact absurd hvh (by simp [Name.cost])
    | rh => exact absurd hvh (by simp [Name.cost])

/-! ## The events -/

/-- Signing failed: everything is hidden. -/
theorem events_none {A' : Finset Name} (hA' : IsCut A') {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A') given y)
    (hacc : flipHi (trunc128 (yv y rh)) = pkOf ξ) : Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  have hrE : Evaluated A' rh := ⟨hA'.rh_not_mem, fun m hm => absurd hm (not_above_rh m)⟩
  obtain ⟨w, hd, -⟩ := yv_hash_rh hy hrE
  by_cases hne : yv y rc = val ξ rc
  · right
    refine ⟨⟨7104, yv y rc⟩, ?_, by rw [hd]; rfl⟩
    rw [kc_isSome_iff]
    exact ⟨rh, rc, rfl, by rw [hne]; rfl⟩
  · left
    refine up hA' hy hacc (v := rc) ?_ rfl (dif_rc hne)
    intro m hm
    rw [above_of_child (show child rc = some rh from rfl)] at hm
    rcases hm with rfl | hm
    · exact hA'.rh_not_mem
    · exact absurd hm (not_above_rh m)

/-- A chain hash evaluated by the verifier but hidden at the signed cut, whose recorded answer
simulates the honest one: its input is a hidden keygen point or a fresh preimage. -/
theorem hit_or_spr {A A' : Finset Name} {ξ : Rec} {d : Cache} {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y) {k : Fin 32} {t : Fin 32}
    (hhE : Evaluated A' (ch k t)) (hnE : ¬ Evaluated A (ch k t))
    (hsim : sim ξ (ch k t) (yv y (ch k t))) : Spr d ξ ∨ Cache.Hits d (fHid (some A) ξ) := by
  obtain ⟨w, hd, hw⟩ := yv_hash_ch hy hhE
  rw [hw] at hsim
  by_cases hpne : yv y (ci k t) = val ξ (ci k t)
  · right
    refine ⟨⟨chainBits k, yv y (ci k t)⟩, ?_, by rw [hd]; rfl⟩
    rw [fHid_isSome_some_iff]
    exact ⟨ch k t, ci k t, rfl, hnE, by rw [hpne]; rfl⟩
  · left
    exact ⟨ch k t, ci k t, rfl, yv y (ci k t), hpne, w, hd, hsim⟩

/-- The forgery uses a different disclosure set of the same cost. -/
theorem events_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hcost : ∑ n ∈ evaluatedSet A, n.cost = ∑ n ∈ evaluatedSet A', n.cost) (hne : A ≠ A')
    {ξ : Rec} {d : Cache} {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y) (hacc : flipHi (trunc128 (yv y rh)) = pkOf ξ) :
    Spr d ξ ∨ Cache.Hits d (fHid (some A) ξ) := by
  obtain ⟨v, hvA, hvE⟩ := exists_mem_evaluated_of_ne hA hA' hcost hne
  have hrev := hA.values v hvA
  by_cases hvne : yv y v = val ξ v
  swap
  · exact Or.inl (up hA' hy hacc hvE.2 hrev.cost_eq (dif_of_revealable hrev hvne))
  -- the hash node below the revealed node, and the value node between them
  obtain ⟨h, hh⟩ := hA'.exists_hashOf hrev hvE
  have hnE := hA.not_evaluated_hashOf hvA hh
  obtain ⟨c, hhc, hcv, hcl⟩ := child_hashOf hh
  have notMem_of_len : ∀ m, ¬ m.len ≤ 192 → m ∉ A' := fun m hm hmA => hm (hA'.len_le hmA)
  have hcE : Evaluated A' c := ⟨notMem_of_len _ (by omega), fun m hm => by
    rw [above_of_child hcv] at hm
    rcases hm with rfl | hm
    · exact hvE.1
    · exact hvE.2 m hm⟩
  have hhE : Evaluated A' h :=
    ⟨notMem_of_len _ (by rw [len_of_hashOf hh]; omega), fun m hm => by
      rw [above_of_child hhc] at hm
      rcases hm with rfl | hm
      · exact hcE.1
      · exact hcE.2 m hm⟩
  cases v with
  | ci k t =>
    have ht0 : ¬ t.val = 0 := fun ht => by simp [hashOf, ht] at hh
    rw [hashOf_of_ne_zero k t ht0, Option.some.injEq] at hh
    subst hh
    simp only [Name.child, Option.some.injEq] at hhc
    subst hhc
    refine hit_or_spr hy hhE hnE (sim_ch_of_trunc (by show t.val - 1 ≠ 31; omega) ?_)
    rw [← yv_cv hy hcE, ← val_cv]
    have e := hvne
    rw [yv_ci hy hvE, val_ci, prev_of_ne_zero k t ht0] at e
    exact e
  | top k =>
    simp only [hashOf, Option.some.injEq] at hh
    subst hh
    simp only [Name.child, Option.some.injEq] at hhc
    subst hhc
    refine hit_or_spr hy hhE hnE (sim_ch_of_topOf rfl ?_)
    rw [← yv_cv hy hcE, ← val_cv]
    have e := hvne
    rw [yv_top hy hvE, val_top'] at e
    exact e
  | src _ | ch _ _ | cv _ _ | rc | rh => exact (hrev : False).elim

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
    (hacc : flipHi (trunc128 (yv y rh)) = pkOf ξ) (hlen : x'.length = graph.revealBits (fins A))
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
  have hrev := hA.values a ha
  refine up hA hy hacc (hA.antichain _ ha) hrev.cost_eq (dif_of_revealable hrev ?_)
  intro heq
  apply hne'
  rw [yv_mem hy ha] at heq
  unfold val at heq
  exact cast_injective _ heq

end Forest

end OptimalOTS
