import Submissions.UpperRiscv.Values

/-!
# Hidden inputs are uniform

The input of a hidden hash node is a function of record coordinates that the public data (the
public key, the revealed values, the exposed keygen points) does not depend on.  Resampling one
such coordinate (`coordOf h`) leaves every record in the fiber of the public data and makes the
input hit any given value with probability at most `ε = 2 ^ (-128)`.

* `sum_updHash`, `sum_updSrc`: change of variables on a set closed under resampling;
* `HiddenCoord`: coordinates the public data does not depend on;
* `hits_charge_A`, `hits_charge_B`: for a fixed query point, at most an `ε` fraction of the
  records of a fiber have that point among their hidden keygen points.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

/-- The weight of a record. -/
def w : ℝ≥0∞ := (Fintype.card Rec : ℝ≥0∞)⁻¹

theorem sum_w : ∑ ξ : Rec, w = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, w]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- A set of records closed under resampling the coordinate `s`. -/
def ClosedAt (S : Finset Rec) (s : Name) : Prop :=
  match s with
  | src k => ∀ ξ ∈ S, ∀ b : BitVec 128, updSrc ξ k b ∈ S
  | _ => ∀ ξ ∈ S, ∀ b : BitVec 256, updHash ξ s b ∈ S

theorem closedAt_src (S : Finset Rec) (k : Fin 32) :
    ClosedAt S (src k) ↔ ∀ ξ ∈ S, ∀ b : BitVec 128, updSrc ξ k b ∈ S := Iff.rfl

theorem closedAt_of_ne_src (S : Finset Rec) {s : Name} (hs : ∀ k, s ≠ src k) :
    ClosedAt S s ↔ ∀ ξ ∈ S, ∀ b : BitVec 256, updHash ξ s b ∈ S := by
  cases s
  · exact absurd rfl (hs _)
  all_goals exact Iff.rfl

theorem bv_cast_cast {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x := by
  subst h₁; rfl

/-- Resampling a hash coordinate is an involution. -/
theorem updHash_updHash (ξ : Rec) (s : Name) (b : BitVec 256) :
    updHash (updHash ξ s b) s (ξ.2 s.fin) = ξ :=
  Prod.ext rfl (funext fun i => by
    show Function.update (Function.update ξ.2 s.fin b) s.fin (ξ.2 s.fin) i = ξ.2 i
    by_cases hi : i = s.fin
    · subst hi; exact Function.update_self ..
    · exact (Function.update_of_ne hi _ _).trans (Function.update_of_ne hi _ _))

/-- Resampling a source is an involution. -/
theorem updSrc_updSrc (ξ : Rec) (k : Fin 32) (b : BitVec 128) :
    updSrc (updSrc ξ k b) k ((ξ.1 (src k).fin).cast (graph_len_fin _)) = ξ :=
  Prod.ext (funext fun i => by
    show Function.update (Function.update ξ.1 (src k).fin (b.cast _)) (src k).fin
      (((ξ.1 (src k).fin).cast (graph_len_fin _)).cast (graph_len_fin _).symm) i = ξ.1 i
    by_cases hi : i = (src k).fin
    · subst hi; exact (Function.update_self ..).trans (bv_cast_cast _ _ _)
    · exact (Function.update_of_ne hi _ _).trans (Function.update_of_ne hi _ _)) rfl

theorem fst_updSrc_self (ξ : Rec) (k : Fin 32) (b : BitVec 128) :
    ((updSrc ξ k b).1 (src k).fin).cast (graph_len_fin _) = b := by
  show (Function.update ξ.1 (src k).fin (b.cast (graph_len_fin (src k)).symm) (src k).fin).cast
    (graph_len_fin (src k)) = b
  exact (congrArg (BitVec.cast (graph_len_fin (src k)))
    (Function.update_self (src k).fin (b.cast (graph_len_fin (src k)).symm) ξ.1)).trans
    (bv_cast_cast _ _ _)

/-- Change of variables: resampling a hash coordinate. -/
theorem sum_updHash (S : Finset Rec) (s : Name) (hs : ∀ k, s ≠ src k)
    (hS : ∀ ξ ∈ S, ∀ b : BitVec 256, updHash ξ s b ∈ S) (f : Rec → ℝ≥0∞) :
    ∑ ξ ∈ S, f ξ = ∑ ξ ∈ S, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ∑ b, f (updHash ξ s b) := by
  have key : ∑ ξ ∈ S, ∑ b, f (updHash ξ s b) = ∑ ξ ∈ S, ∑ _b : BitVec 256, f ξ := by
    calc ∑ ξ ∈ S, ∑ b, f (updHash ξ s b)
        = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 256)), f (updHash p.1 s p.2) :=
          (Finset.sum_product' S Finset.univ (fun ξ b => f (updHash ξ s b))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 256)), f p.1 := by
          refine Finset.sum_nbij' (fun p => (updHash p.1 s p.2, p.1.2 s.fin))
            (fun p => (updHash p.1 s p.2, p.1.2 s.fin)) ?_ ?_ ?_ ?_ ?_
          · intro p hp
            rw [Finset.mem_product] at hp ⊢
            exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
          · intro p hp
            rw [Finset.mem_product] at hp ⊢
            exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
          · intro p _
            exact Prod.ext (updHash_updHash _ _ _) (snd_updHash_self _ _ _)
          · intro p _
            exact Prod.ext (updHash_updHash _ _ _) (snd_updHash_self _ _ _)
          · intro p _
            rfl
      _ = ∑ ξ ∈ S, ∑ _b : BitVec 256, f ξ :=
          Finset.sum_product' S Finset.univ (fun ξ _ => f ξ)
  have hc0 : (Fintype.card (BitVec 256) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 256) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-- Change of variables: resampling a source. -/
theorem sum_updSrc (S : Finset Rec) (k : Fin 32)
    (hS : ∀ ξ ∈ S, ∀ b : BitVec 128, updSrc ξ k b ∈ S) (f : Rec → ℝ≥0∞) :
    ∑ ξ ∈ S, f ξ = ∑ ξ ∈ S, (Fintype.card (BitVec 128) : ℝ≥0∞)⁻¹ * ∑ b, f (updSrc ξ k b) := by
  have key : ∑ ξ ∈ S, ∑ b, f (updSrc ξ k b) = ∑ ξ ∈ S, ∑ _b : BitVec 128, f ξ := by
    calc ∑ ξ ∈ S, ∑ b, f (updSrc ξ k b)
        = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 128)), f (updSrc p.1 k p.2) :=
          (Finset.sum_product' S Finset.univ (fun ξ b => f (updSrc ξ k b))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 128)), f p.1 := by
          refine Finset.sum_nbij'
            (fun p => (updSrc p.1 k p.2, (p.1.1 (src k).fin).cast (graph_len_fin _)))
            (fun p => (updSrc p.1 k p.2, (p.1.1 (src k).fin).cast (graph_len_fin _))) ?_ ?_ ?_ ?_ ?_
          · intro p hp
            rw [Finset.mem_product] at hp ⊢
            exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
          · intro p hp
            rw [Finset.mem_product] at hp ⊢
            exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
          · intro p _
            exact Prod.ext (updSrc_updSrc _ _ _) (fst_updSrc_self _ _ _)
          · intro p _
            exact Prod.ext (updSrc_updSrc _ _ _) (fst_updSrc_self _ _ _)
          · intro p _
            rfl
      _ = ∑ ξ ∈ S, ∑ _b : BitVec 128, f ξ :=
          Finset.sum_product' S Finset.univ (fun ξ _ => f ξ)
  have hc0 : (Fintype.card (BitVec 128) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 128) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem card_bitVec_ennreal (n : ℕ) : (Fintype.card (BitVec n) : ℝ≥0∞) = 2 ^ n := by
  simp

theorem inv_card_mul_two_pow : (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 2 ^ 128 = ε := by
  have h0 : (2 : ℝ≥0∞) ^ 128 ≠ 0 := by simp
  have ht : (2 : ℝ≥0∞) ^ 128 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [card_bitVec_ennreal, ε, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add],
    ENNReal.mul_inv (Or.inl h0) (Or.inl ht), mul_assoc, ENNReal.inv_mul_cancel h0 ht, mul_one]

/-- On a set closed under resampling the coordinate of a hash node, its input hits any given
value with probability at most `ε`. -/
theorem sum_input_eq_le {h p : Name} (hp : hashParent h = some p) (S : Finset Rec)
    (hS : ClosedAt S (coordOf h)) (u : BitVec p.len) :
    ∑ ξ ∈ S, (if val ξ p = u then w else 0) ≤ ε * ∑ ξ ∈ S, w := by
  rw [Finset.mul_sum]
  by_cases hsrc : ∃ k, coordOf h = src k
  · obtain ⟨k, hk⟩ := hsrc
    rw [hk, closedAt_src] at hS
    rw [sum_updSrc S k hS (fun ξ => if val ξ p = u then w else 0)]
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updSrc_input_le hp ξ hk u
    have hle' : ((Finset.univ.filter fun b : BitVec 128 => val (updSrc ξ k b) p = u).card : ℝ≥0∞)
        ≤ 1 := by exact_mod_cast hle
    calc (Fintype.card (BitVec 128) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun b : BitVec 128 => val (updSrc ξ k b) p = u).card : ℝ≥0∞) * w)
        ≤ (Fintype.card (BitVec 128) : ℝ≥0∞)⁻¹ * (1 * w) := by gcongr
      _ = ε * w := by rw [one_mul, card_bitVec_ennreal, ε]
  · push Not at hsrc
    rw [closedAt_of_ne_src S hsrc] at hS
    rw [sum_updHash S (coordOf h) hsrc hS (fun ξ => if val ξ p = u then w else 0)]
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updHash_input_le hp ξ hsrc u
    have hle' : ((Finset.univ.filter fun b : BitVec 256 =>
        val (updHash ξ (coordOf h) b) p = u).card : ℝ≥0∞) ≤ 2 ^ 128 := by exact_mod_cast hle
    calc (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun b : BitVec 256 =>
            val (updHash ξ (coordOf h) b) p = u).card : ℝ≥0∞) * w)
        ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * (2 ^ 128 * w) := by gcongr
      _ = ε * w := by rw [← mul_assoc, inv_card_mul_two_pow]

/-! ## Hidden coordinates -/

/-- A coordinate the public data after signing at the cut `A` does not depend on: a node
strictly below the cut that is neither a cut node nor the hash node of a cut node. -/
def HiddenCoord (A : Finset Name) (s : Name) : Prop :=
  ¬ Evaluated A s ∧ s ∉ A ∧ ∀ a ∈ A, hashOf a ≠ some s

theorem len_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.len = 256 := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp <;> rfl

/-- A hash node lies strictly above its coordinate. -/
theorem above_coordOf {h p : Name} (hp : hashParent h = some p) : Above h (coordOf h) := by
  have hc := child_hashParent hp
  rcases coordOf_below hp with e | e | ⟨m, e1, e2⟩
  · rw [e]; exact Above.child hc
  · exact Above.step e (Above.child hc)
  · exact Above.step e1 (Above.step e2 (Above.child hc))

theorem coordOf_hiddenCoord {A : Finset Name} (hA : IsCut A) {h p : Name}
    (hp : hashParent h = some p) (hh : ¬ Evaluated A h) : HiddenCoord A (coordOf h) := by
  have hhA : h ∉ A := fun hm => by
    have := hA.values h hm
    rw [len_of_hashParent hp] at this
    omega
  obtain ⟨a, haA, hah⟩ : ∃ a ∈ A, Above a h := by
    by_contra hcon
    push Not at hcon
    exact hh ⟨hhA, fun m hm hmA => hcon m hmA hm⟩
  have hhs : Above h (coordOf h) := above_coordOf hp
  have has : Above a (coordOf h) := hah.trans hhs
  refine ⟨fun he => he.2 a has haA, fun hsA => hA.antichain _ hsA a has haA, fun a' ha' he => ?_⟩
  have hc : child (coordOf h) = some a' := child_hashOf he
  rw [above_of_child hc] at hhs
  rcases hhs with rfl | hhs
  · exact hhA ha'
  · exact hA.antichain a' ha' a (hah.trans hhs) haA

/-- If `s` is not in `A` and its child is evaluated, then `s` is evaluated. -/
theorem evaluated_of_child_res {A : Finset Name} {s n : Name} (hc : child s = some n) (hsA : s ∉ A)
    (hn : Evaluated A n) : Evaluated A s :=
  ⟨hsA, fun m hm => by
    rw [above_of_child hc] at hm
    rcases hm with rfl | hm
    · exact hn.1
    · exact hn.2 m hm⟩

/-- Every coordinate a node reads is the node itself, its hash node, the hash node of one of
its parents, or (for the first input of a chain, which reads a source) its parent. -/
theorem mem_deps_cases' {s n : Name} (h : s ∈ deps n) :
    s = n ∨ hashOf n = some s ∨ (∃ m, hashOf m = some s ∧ child m = some n) ∨
      (child s = some n ∧ n.len ≠ 128) := by
  cases n with
  | src k => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h
  | ci k t =>
    by_cases ht : t.val = 0
    · rw [deps_ci_zero k t ht, Finset.mem_singleton] at h
      subst h
      exact Or.inr (Or.inr (Or.inr ⟨child_src_ci k t ht, by simp [Name.len]⟩))
    · rw [deps_ci_succ k t ht, Finset.mem_singleton] at h
      subst h
      exact Or.inr (Or.inr (Or.inl ⟨cv k ⟨t.val - 1, by omega⟩, rfl, child_cv_ci k t ht⟩))
  | ch k t => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h
  | cv k t => simp only [deps, Finset.mem_singleton] at h; subst h; exact Or.inr (Or.inl rfl)
  | rc =>
    simp only [deps, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨k, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨cv k 14, rfl, rfl⟩))
  | rh => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h

/-- The child of a value node is not a 128-bit node. -/
theorem len_child_of_hashOf {m s n : Name} (hm : hashOf m = some s) (hc : child m = some n) :
    n.len ≠ 128 := by
  cases m <;> simp only [hashOf, reduceCtorEq] at hm
  · simp only [Name.child] at hc
    split_ifs at hc <;> simp only [Option.some.injEq] at hc <;> subst hc <;> simp [Name.len]

theorem not_mem_deps_of_hiddenCoord {A : Finset Name} (hA : IsCut A) {s n : Name}
    (hs : HiddenCoord A s) (hn : Evaluated A n ∨ n ∈ A) : s ∉ deps n := by
  intro hd
  obtain ⟨hsE, hsA, hsH⟩ := hs
  rcases mem_deps_cases' hd with rfl | hh | ⟨m, hm, hc⟩ | ⟨hc, hl⟩
  · rcases hn with hn | hn
    · exact hsE hn
    · exact hsA hn
  · rcases hn with hn | hn
    · exact hsE (evaluated_of_child_res (child_hashOf hh) hsA hn)
    · exact hsH n hn hh
  · have hcs : child s = some m := child_hashOf hm
    rcases hn with hn | hn
    · by_cases hmA : m ∈ A
      · exact hsH m hmA hm
      · exact hsE (evaluated_of_child_res hcs hsA (evaluated_of_child_res hc hmA hn))
    · exact len_child_of_hashOf hm hc (hA.values n hn)
  · rcases hn with hn | hn
    · exact hsE (evaluated_of_child_res hc hsA hn)
    · exact hl (hA.values n hn)

theorem hiddenCoord_ne_rh {A : Finset Name} {s : Name} (hs : HiddenCoord A s) : s ≠ rh := by
  rintro rfl
  exact hs.1 ⟨hs.2.1, fun m hm => absurd hm (not_above_rh m)⟩

/-! ## Invariance of the public data -/

/-- The revealed values at a disclosure set. -/
def revealed (A : Finset Name) (ξ : Rec) : List Bool := graph.encode (fins A) (graph.evalRec ξ)

theorem pkOf_updHash (ξ : Rec) {s : Name} (hs : s ≠ rh) (b : BitVec 256) :
    pkOf (updHash ξ s b) = pkOf ξ := by
  exact congrArg trunc (snd_updHash_of_ne ξ s b rh (Ne.symm hs))

theorem pkOf_updSrc (ξ : Rec) (k : Fin 32) (b : BitVec 128) : pkOf (updSrc ξ k b) = pkOf ξ := by
  unfold pkOf
  rw [snd_updSrc]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun a' ha' => h a' (by simp [ha'])]

/-- `encode` only reads the values on the encoded set. -/
theorem encode_congr_revealed {B : Finset (Fin graph.size)} {x x' : graph.Assignment}
    (h : ∀ v ∈ B, x v = x' v) : graph.encode B x = graph.encode B x' := by
  unfold Graph.encode
  apply flatMap_congr'
  intro v hv
  rw [List.mem_filter] at hv
  rw [h v (of_decide_eq_true hv.2)]

theorem evalRec_fin_congr {ξ ξ' : Rec} {a : Name} (h : val ξ a = val ξ' a) :
    graph.evalRec ξ a.fin = graph.evalRec ξ' a.fin := by
  unfold val at h
  simpa using congrArg (BitVec.cast (graph_len_fin a).symm) h

theorem revealed_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) : revealed A (updHash ξ s b) = revealed A ξ := by
  unfold revealed
  apply encode_congr_revealed
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v := ⟨ofFin v, fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins A a).mp hv
  exact evalRec_fin_congr
    (val_updHash_of_not_mem_deps ξ s b a (not_mem_deps_of_hiddenCoord hA hs (Or.inr haA)))

theorem revealed_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 32}
    (hs : HiddenCoord A (src k)) (b : BitVec 128) : revealed A (updSrc ξ k b) = revealed A ξ := by
  unfold revealed
  apply encode_congr_revealed
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v := ⟨ofFin v, fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins A a).mp hv
  exact evalRec_fin_congr
    (val_updSrc_of_not_mem_deps ξ k b a (not_mem_deps_of_hiddenCoord hA hs (Or.inr haA)))

theorem exposed_some_iff (A : Finset Name) (h : Name) : Exposed (some A) h ↔ Evaluated A h := by
  simp [Exposed]

/-- The parent of an evaluated hash node is evaluated or in the cut. -/
theorem evaluated_or_mem_of_child {A : Finset Name} {p h : Name} (hc : child p = some h)
    (he : Evaluated A h) : Evaluated A p ∨ p ∈ A := by
  by_cases hpA : p ∈ A
  · exact Or.inr hpA
  · exact Or.inl (evaluated_of_child_res hc hpA he)

theorem pointOf_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) : pointOf (updHash ξ s b) h p = pointOf ξ h p := by
  unfold pointOf
  rw [val_updHash_of_not_mem_deps _ _ _ _ (not_mem_deps_of_hiddenCoord hA hs
    (evaluated_or_mem_of_child (child_hashParent hp) he))]

theorem pointOf_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 32}
    (hs : HiddenCoord A (src k)) (b : BitVec 128) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) : pointOf (updSrc ξ k b) h p = pointOf ξ h p := by
  unfold pointOf
  rw [val_updSrc_of_not_mem_deps _ _ _ _ (not_mem_deps_of_hiddenCoord hA hs
    (evaluated_or_mem_of_child (child_hashParent hp) he))]

/-- The keygen cache at a keygen point. -/
theorem kc_pointOf (ξ : Rec) {h p : Name} (hp : hashParent h = some p) :
    kc ξ (pointOf ξ h p) = some (ξ.2 h.fin) :=
  (kc_apply_iff ξ _ _).mpr ⟨h, p, hp, rfl, rfl⟩

theorem fExp_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) : fExp (some A) (updHash ξ s b) = fExp (some A) ξ := by
  funext q
  have hpt : ∀ h p, hashParent h = some p → Exposed (some A) h →
      pointOf (updHash ξ s b) h p = pointOf ξ h p :=
    fun h p hp he => pointOf_updHash hA ξ hs b hp ((exposed_some_iff A h).mp he)
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf (updHash ξ s b) h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  simp only [fExp]
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p
  · rw [if_pos (hcond.mpr hq), if_pos hq]
    obtain ⟨h, p, hp, he, rfl⟩ := hq
    have hne : h ≠ s := fun e => hs.1 (e ▸ (exposed_some_iff A h).mp he)
    rw [kc_pointOf ξ hp, ← hpt h p hp he, kc_pointOf _ hp, snd_updHash_of_ne _ _ _ _ hne]
  · rw [if_neg (fun h' => hq (hcond.mp h')), if_neg hq]

theorem fExp_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 32}
    (hs : HiddenCoord A (src k)) (b : BitVec 128) : fExp (some A) (updSrc ξ k b) = fExp (some A) ξ := by
  funext q
  have hpt : ∀ h p, hashParent h = some p → Exposed (some A) h →
      pointOf (updSrc ξ k b) h p = pointOf ξ h p :=
    fun h p hp he => pointOf_updSrc hA ξ hs b hp ((exposed_some_iff A h).mp he)
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf (updSrc ξ k b) h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  simp only [fExp]
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p
  · rw [if_pos (hcond.mpr hq), if_pos hq]
    obtain ⟨h, p, hp, he, rfl⟩ := hq
    rw [kc_pointOf ξ hp, ← hpt h p hp he, kc_pointOf _ hp, snd_updSrc]
  · rw [if_neg (fun h' => hq (hcond.mp h')), if_neg hq]

/-! ## Fibers and charges -/

/-- The records with a given public key. -/
def fiberA (pk : BitVec 128) : Finset Rec := Finset.univ.filter fun ξ => pkOf ξ = pk

/-- The public data after signing at `A`. -/
abbrev Data := BitVec 128 × List Bool × Cache

/-- The public data of a record after signing at `A`. -/
def dataOf (A : Finset Name) (ξ : Rec) : Data := (pkOf ξ, revealed A ξ, fExp (some A) ξ)

/-- The records with given public data. -/
def fiberB (A : Finset Name) (d : Data) : Finset Rec := Finset.univ.filter fun ξ => dataOf A ξ = d

theorem fiberA_closedAt (pk : BitVec 128) {s : Name} (hs : s ≠ rh) : ClosedAt (fiberA pk) s := by
  by_cases hsrc : ∃ k, s = src k
  · obtain ⟨k, rfl⟩ := hsrc
    rw [closedAt_src]
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ξ hξ b
    rw [pkOf_updSrc]; exact hξ
  · push Not at hsrc
    rw [closedAt_of_ne_src _ hsrc]
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ξ hξ b
    rw [pkOf_updHash _ hs]; exact hξ

theorem dataOf_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) : dataOf A (updHash ξ s b) = dataOf A ξ := by
  simp only [dataOf, pkOf_updHash _ (hiddenCoord_ne_rh hs), revealed_updHash hA _ hs,
    fExp_updHash hA _ hs]

theorem dataOf_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 32}
    (hs : HiddenCoord A (src k)) (b : BitVec 128) : dataOf A (updSrc ξ k b) = dataOf A ξ := by
  simp only [dataOf, pkOf_updSrc, revealed_updSrc hA _ hs, fExp_updSrc hA _ hs]

theorem fiberB_closedAt {A : Finset Name} (hA : IsCut A) (d : Data) {s : Name}
    (hs : HiddenCoord A s) : ClosedAt (fiberB A d) s := by
  by_cases hsrc : ∃ k, s = src k
  · obtain ⟨k, rfl⟩ := hsrc
    rw [closedAt_src]
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ξ hξ b
    rw [dataOf_updSrc hA _ hs]; exact hξ
  · push Not at hsrc
    rw [closedAt_of_ne_src _ hsrc]
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ξ hξ b
    rw [dataOf_updHash hA _ hs]; exact hξ

/-- Before signing, every keygen point is hidden: a fixed query point is a keygen point of at
most an `ε` fraction of the records with a given public key. -/
theorem hits_charge_A (pk : BitVec 128) (q : Query) :
    ∑ ξ ∈ fiberA pk, (if (kc ξ q).isSome then w else 0) ≤ ε * ∑ ξ ∈ fiberA pk, w := by
  by_cases hex : ∃ h p, hashParent h = some p ∧ ∃ ξ₀ : Rec, q = pointOf ξ₀ h p
  · obtain ⟨h, p, hp, ξ₀, rfl⟩ := hex
    have key : ∀ ξ : Rec, (kc ξ (pointOf ξ₀ h p)).isSome ↔ val ξ p = val ξ₀ p := by
      intro ξ
      rw [kc_isSome_iff]
      constructor
      · rintro ⟨h', p', hp', e⟩
        obtain rfl := pointOf_inj_left hp hp' e
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact (pointOf_inj_input e).symm
      · intro hv
        exact ⟨h, p, hp, by simp only [pointOf, hv]⟩
    have hcost : h.cost ≠ 0 := (hashParent_isSome_iff h).mp (by rw [hp]; rfl)
    calc ∑ ξ ∈ fiberA pk, (if (kc ξ (pointOf ξ₀ h p)).isSome then w else 0)
        = ∑ ξ ∈ fiberA pk, (if val ξ p = val ξ₀ p then w else 0) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          by_cases hv : val ξ p = val ξ₀ p <;> simp [key, hv]
      _ ≤ _ := sum_input_eq_le hp _ (fiberA_closedAt pk (coordOf_ne_rh h hcost)) _
  · have hz : ∀ ξ : Rec, ¬ (kc ξ q).isSome := by
      intro ξ hk
      rw [kc_isSome_iff] at hk
      obtain ⟨h, p, hp, e⟩ := hk
      exact hex ⟨h, p, hp, ξ, e⟩
    have hsum : ∑ ξ ∈ fiberA pk, (if (kc ξ q).isSome then w else 0) = 0 :=
      Finset.sum_eq_zero fun ξ _ => if_neg (hz ξ)
    exact hsum.le.trans _root_.zero_le

/-- After signing at `A`, a fixed query point is a hidden keygen point of at most an `ε`
fraction of the records with given public data. -/
theorem hits_charge_B {A : Finset Name} (hA : IsCut A) (d : Data) (q : Query) :
    ∑ ξ ∈ fiberB A d, (if (fHid (some A) ξ q).isSome then w else 0) ≤
      ε * ∑ ξ ∈ fiberB A d, w := by
  by_cases hex : ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧ ∃ ξ₀ : Rec, q = pointOf ξ₀ h p
  · obtain ⟨h, p, hp, hh, ξ₀, rfl⟩ := hex
    have key : ∀ ξ : Rec, (fHid (some A) ξ (pointOf ξ₀ h p)).isSome ↔ val ξ p = val ξ₀ p := by
      intro ξ
      rw [fHid_isSome_some_iff]
      constructor
      · rintro ⟨h', p', hp', _, e⟩
        obtain rfl := pointOf_inj_left hp hp' e
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact (pointOf_inj_input e).symm
      · intro hv
        exact ⟨h, p, hp, hh, by simp only [pointOf, hv]⟩
    calc ∑ ξ ∈ fiberB A d, (if (fHid (some A) ξ (pointOf ξ₀ h p)).isSome then w else 0)
        = ∑ ξ ∈ fiberB A d, (if val ξ p = val ξ₀ p then w else 0) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          by_cases hv : val ξ p = val ξ₀ p <;> simp [key, hv]
      _ ≤ _ := sum_input_eq_le hp _ (fiberB_closedAt hA d (coordOf_hiddenCoord hA hp hh)) _
  · have hz : ∀ ξ : Rec, ¬ (fHid (some A) ξ q).isSome := by
      intro ξ hk
      rw [fHid_isSome_some_iff] at hk
      obtain ⟨h, p, hp, hh, e⟩ := hk
      exact hex ⟨h, p, hp, hh, ξ, e⟩
    have hsum : ∑ ξ ∈ fiberB A d, (if (fHid (some A) ξ q).isSome then w else 0) = 0 :=
      Finset.sum_eq_zero fun ξ _ => if_neg (hz ξ)
    exact hsum.le.trans _root_.zero_le

end Forest

end OptimalOTS
