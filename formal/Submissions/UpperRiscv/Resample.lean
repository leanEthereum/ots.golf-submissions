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
  | src k => ∀ ξ ∈ S, ∀ b : BitVec 192, updSrc ξ k b ∈ S
  | _ => ∀ ξ ∈ S, ∀ b : BitVec 256, updHash ξ s b ∈ S

theorem closedAt_src (S : Finset Rec) (k : Fin 28) :
    ClosedAt S (src k) ↔ ∀ ξ ∈ S, ∀ b : BitVec 192, updSrc ξ k b ∈ S := Iff.rfl

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
theorem updSrc_updSrc (ξ : Rec) (k : Fin 28) (b : BitVec 192) :
    updSrc (updSrc ξ k b) k ((ξ.1 (src k).fin).cast (graph_len_fin _)) = ξ :=
  Prod.ext (funext fun i => by
    show Function.update (Function.update ξ.1 (src k).fin (b.cast _)) (src k).fin
      (((ξ.1 (src k).fin).cast (graph_len_fin _)).cast (graph_len_fin _).symm) i = ξ.1 i
    by_cases hi : i = (src k).fin
    · subst hi; exact (Function.update_self ..).trans (bv_cast_cast _ _ _)
    · exact (Function.update_of_ne hi _ _).trans (Function.update_of_ne hi _ _)) rfl

theorem fst_updSrc_self (ξ : Rec) (k : Fin 28) (b : BitVec 192) :
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
theorem sum_updSrc (S : Finset Rec) (k : Fin 28)
    (hS : ∀ ξ ∈ S, ∀ b : BitVec 192, updSrc ξ k b ∈ S) (f : Rec → ℝ≥0∞) :
    ∑ ξ ∈ S, f ξ = ∑ ξ ∈ S, (Fintype.card (BitVec 192) : ℝ≥0∞)⁻¹ * ∑ b, f (updSrc ξ k b) := by
  have key : ∑ ξ ∈ S, ∑ b, f (updSrc ξ k b) = ∑ ξ ∈ S, ∑ _b : BitVec 192, f ξ := by
    calc ∑ ξ ∈ S, ∑ b, f (updSrc ξ k b)
        = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 192)), f (updSrc p.1 k p.2) :=
          (Finset.sum_product' S Finset.univ (fun ξ b => f (updSrc ξ k b))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 192)), f p.1 := by
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
      _ = ∑ ξ ∈ S, ∑ _b : BitVec 192, f ξ :=
          Finset.sum_product' S Finset.univ (fun ξ _ => f ξ)
  have hc0 : (Fintype.card (BitVec 192) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 192) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
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

/-- `ε₁ = 2 ^ (-192)`: the sharp per-node hit probability. -/
def ε₁ : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 192)⁻¹

theorem ε₁_le_ε : ε₁ ≤ ε := by
  unfold ε₁ ε
  exact ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by norm_num))

theorem inv_card_mul_two_pow_64 : (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 2 ^ 64 = ε₁ := by
  have h0 : (2 : ℝ≥0∞) ^ 64 ≠ 0 := by simp
  have ht : (2 : ℝ≥0∞) ^ 64 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [card_bitVec_ennreal, ε₁, show (2 : ℝ≥0∞) ^ 256 = 2 ^ 192 * 2 ^ 64 by rw [← pow_add],
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
    mul_assoc, ENNReal.inv_mul_cancel h0 ht, mul_one]

/-- A filter whose members all have the same truncation has at most `2 ^ 64` elements. -/
theorem card_filter_le_of_imp' (p : BitVec 256 → Prop) [DecidablePred p] (a : BitVec 192)
    (hp : ∀ b, p b → trunc b = a) : (Finset.univ.filter p).card ≤ 2 ^ 64 :=
  le_trans (Finset.card_le_card fun b hb => Finset.mem_filter.2
    ⟨Finset.mem_univ _, hp b (Finset.mem_filter.1 hb).2⟩) (card_filter_trunc_le' a)

/-- The sharp count: at most `2 ^ 64` resamplings of a hash coordinate give a chosen input. -/
theorem card_updHash_input_le' {h p : Name} (hp : hashParent h = some p) (ξ : Rec)
    (hs : ∀ k, coordOf h ≠ src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 256 => val (updHash ξ (coordOf h) b) p = u).card ≤ 2 ^ 64 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · rename_i k t
    have ht : ¬ t.val = 0 := fun ht => hs k (by simp [coordOf, ht])
    have e1 : coordOf (ch k t) = ch k ⟨t.val - 1, by omega⟩ := by simp [coordOf, ht]
    rw [e1]
    refine card_filter_le_of_imp' _ u fun b hb => ?_
    rw [val_ci_succ _ k t ht, updHash_snd_self] at hb
    exact hb
  · exact card_updHash_rc_le ξ u

/-- On a set closed under resampling the coordinate of a hash node, its input hits any given
value with probability at most `ε₁`. -/
theorem sum_input_eq_le' {h p : Name} (hp : hashParent h = some p) (S : Finset Rec)
    (hS : ClosedAt S (coordOf h)) (u : BitVec p.len) :
    ∑ ξ ∈ S, (if val ξ p = u then w else 0) ≤ ε₁ * ∑ ξ ∈ S, w := by
  rw [Finset.mul_sum]
  by_cases hsrc : ∃ k, coordOf h = src k
  · obtain ⟨k, hk⟩ := hsrc
    rw [hk, closedAt_src] at hS
    rw [sum_updSrc S k hS (fun ξ => if val ξ p = u then w else 0)]
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updSrc_input_le hp ξ hk u
    have hle' : ((Finset.univ.filter fun b : BitVec 192 => val (updSrc ξ k b) p = u).card : ℝ≥0∞)
        ≤ 1 := by exact_mod_cast hle
    calc (Fintype.card (BitVec 192) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun b : BitVec 192 => val (updSrc ξ k b) p = u).card : ℝ≥0∞) * w)
        ≤ (Fintype.card (BitVec 192) : ℝ≥0∞)⁻¹ * (1 * w) := by gcongr
      _ = ε₁ * w := by rw [one_mul, card_bitVec_ennreal, ε₁]
  · push Not at hsrc
    rw [closedAt_of_ne_src S hsrc] at hS
    rw [sum_updHash S (coordOf h) hsrc hS (fun ξ => if val ξ p = u then w else 0)]
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updHash_input_le' hp ξ hsrc u
    have hle' : ((Finset.univ.filter fun b : BitVec 256 =>
        val (updHash ξ (coordOf h) b) p = u).card : ℝ≥0∞) ≤ 2 ^ 64 := by exact_mod_cast hle
    calc (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun b : BitVec 256 =>
            val (updHash ξ (coordOf h) b) p = u).card : ℝ≥0∞) * w)
        ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * (2 ^ 64 * w) := by gcongr
      _ = ε₁ * w := by rw [← mul_assoc, inv_card_mul_two_pow_64]

/-- The same with the coarser `ε`. -/
theorem sum_input_eq_le {h p : Name} (hp : hashParent h = some p) (S : Finset Rec)
    (hS : ClosedAt S (coordOf h)) (u : BitVec p.len) :
    ∑ ξ ∈ S, (if val ξ p = u then w else 0) ≤ ε * ∑ ξ ∈ S, w :=
  (sum_input_eq_le' hp S hS u).trans (mul_le_mul' ε₁_le_ε le_rfl)

/-! ## Hidden coordinates -/

/-- A coordinate the public data after signing at the cut `A` does not depend on: a node
strictly below the cut that is neither a cut node nor read by a cut node. -/
def HiddenCoord (A : Finset Name) (s : Name) : Prop :=
  ¬ Evaluated A s ∧ s ∉ A ∧ ∀ a ∈ A, s ∉ deps a

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
    obtain ⟨_, _, e⟩ := hA.values h hm
    cases h <;> simp only [hashParent, reduceCtorEq] at hp <;> cases e
  obtain ⟨a, haA, hah⟩ : ∃ a ∈ A, Above a h := by
    by_contra hcon
    push Not at hcon
    exact hh ⟨hhA, fun m hm hmA => hcon m hmA hm⟩
  have hhs : Above h (coordOf h) := above_coordOf hp
  have has : Above a (coordOf h) := hah.trans hhs
  refine ⟨fun he => he.2 a has haA, fun hsA => hA.antichain _ hsA a has haA, fun a' ha' hd => ?_⟩
  -- a cut node reading the coordinate feeds the hash node `h`, which is then evaluated
  obtain ⟨k, t, rfl⟩ := hA.values a' ha'
  have hchild : child (ci k t) = some h := by
    cases h with
    | ch k' t' =>
      simp only [coordOf] at hd
      by_cases ht : t.val = 0
      · rw [deps_ci_zero k t ht, Finset.mem_singleton] at hd
        split_ifs at hd with ht'
        obtain rfl := Name.src.inj hd
        obtain rfl : t = 0 := Fin.ext ht
        obtain rfl : t' = 0 := Fin.ext ht'
        rfl
      · rw [deps_ci_succ k t ht, Finset.mem_singleton] at hd
        split_ifs at hd with ht'
        obtain ⟨e1, e2⟩ := Name.ch.inj hd
        have e3 : t' = t := Fin.ext (by have := Fin.ext_iff.mp e2; simp only at this; omega)
        subst e1; subst e3
        rfl
    | rh =>
      simp only [coordOf] at hd
      by_cases ht : t.val = 0
      · rw [deps_ci_zero k t ht, Finset.mem_singleton] at hd; cases hd
      · rw [deps_ci_succ k t ht, Finset.mem_singleton] at hd
        have e := (Name.ch.inj hd).2
        have := Fin.ext_iff.mp e
        simp only at this
        omega
    | src _ | ci _ _ | cv _ _ | rc => simp [hashParent] at hp
  exact hh ⟨hhA, fun m hm => hA.antichain (ci k t) ha' m (Above.step hchild hm)⟩

/-- If `s` is not in `A` and its child is evaluated, then `s` is evaluated. -/
theorem evaluated_of_child_res {A : Finset Name} {s n : Name} (hc : child s = some n) (hsA : s ∉ A)
    (hn : Evaluated A n) : Evaluated A s :=
  ⟨hsA, fun m hm => by
    rw [above_of_child hc] at hm
    rcases hm with rfl | hm
    · exact hn.1
    · exact hn.2 m hm⟩

/-- Every coordinate a node reads is the node itself, its own feeder, or two steps below it
through a value node. -/
theorem mem_deps_cases' {s n : Name} (h : s ∈ deps n) :
    s = n ∨ child s = some n ∨
      ∃ m, child s = some m ∧ child m = some n ∧ ∀ k t, m ≠ ci k t := by
  cases n with
  | src k => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h
  | ci k t =>
    by_cases ht : t.val = 0
    · rw [deps_ci_zero k t ht, Finset.mem_singleton] at h
      subst h
      exact Or.inr (Or.inl (child_src_ci k t ht))
    · rw [deps_ci_succ k t ht, Finset.mem_singleton] at h
      subst h
      exact Or.inr (Or.inr ⟨cv k ⟨t.val - 1, by omega⟩, rfl, child_cv_ci k t ht, fun _ _ e => by cases e⟩)
  | ch k t => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h
  | cv k t => simp only [deps, Finset.mem_singleton] at h; subst h; exact Or.inr (Or.inl rfl)
  | rc =>
    simp only [deps, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨k, rfl⟩ := h
    exact Or.inr (Or.inr ⟨cv k 31, rfl, rfl, fun _ _ e => by cases e⟩)
  | rh => simp only [deps, Finset.mem_singleton] at h; exact Or.inl h

theorem not_mem_deps_of_hiddenCoord {A : Finset Name} (hA : IsCut A) {s n : Name}
    (hs : HiddenCoord A s) (hn : Evaluated A n ∨ n ∈ A) : s ∉ deps n := by
  intro hd
  obtain ⟨hsE, hsA, hsD⟩ := hs
  rcases hn with hn | hn
  · rcases mem_deps_cases' hd with rfl | hc | ⟨m, hc1, hc2, hm⟩
    · exact hsE hn
    · exact hsE (evaluated_of_child_res hc hsA hn)
    · have hmA : m ∉ A := fun h => by obtain ⟨k, t, e⟩ := hA.values m h; exact hm k t e
      exact hsE (evaluated_of_child_res hc1 hsA (evaluated_of_child_res hc2 hmA hn))
  · exact hsD n hn hd

theorem hiddenCoord_ne_rh {A : Finset Name} {s : Name} (hs : HiddenCoord A s) : s ≠ rh := by
  rintro rfl
  exact hs.1 ⟨hs.2.1, fun m hm => absurd hm (not_above_rh m)⟩

/-! ## Invariance of the public data -/

/-- The revealed values at a disclosure set. -/
def revealed (A : Finset Name) (ξ : Rec) : List Bool := graph.encode (fins A) (graph.evalRec ξ)

theorem pkOf_updHash (ξ : Rec) {s : Name} (hs : s ≠ rh) (b : BitVec 256) :
    pkOf (updHash ξ s b) = pkOf ξ := by
  exact congrArg trunc128 (snd_updHash_of_ne ξ s b rh (Ne.symm hs))

theorem pkOf_updSrc (ξ : Rec) (k : Fin 28) (b : BitVec 192) : pkOf (updSrc ξ k b) = pkOf ξ := by
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
    (val_updHash_of_not_mem_deps ξ s b a (hs.2.2 a haA))

theorem revealed_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 28}
    (hs : HiddenCoord A (src k)) (b : BitVec 192) : revealed A (updSrc ξ k b) = revealed A ξ := by
  unfold revealed
  apply encode_congr_revealed
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v := ⟨ofFin v, fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins A a).mp hv
  exact evalRec_fin_congr
    (val_updSrc_of_not_mem_deps ξ k b a (hs.2.2 a haA))

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

theorem pointOf_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 28}
    (hs : HiddenCoord A (src k)) (b : BitVec 192) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) : pointOf (updSrc ξ k b) h p = pointOf ξ h p := by
  unfold pointOf
  rw [val_updSrc_of_not_mem_deps _ _ _ _ (not_mem_deps_of_hiddenCoord hA hs
    (evaluated_or_mem_of_child (child_hashParent hp) he))]

/-- The keygen cache at a keygen point of a good record. -/
theorem kc_pointOf {ξ : Rec} (hξ : DistinctRec ξ) {h p : Name} (hp : hashParent h = some p) :
    kc ξ (pointOf ξ h p) = some (ξ.2 h.fin) :=
  (kc_apply_iff hξ _ _).mpr ⟨h, p, hp, rfl, rfl⟩

theorem fExp_congr {A : Finset Name} {ξ ξ' : Rec}
    (hpt : ∀ h p, hashParent h = some p → Exposed (some A) h → pointOf ξ' h p = pointOf ξ h p)
    (hout : ∀ h, Exposed (some A) h → ξ'.2 h.fin = ξ.2 h.fin) :
    fExp (some A) ξ' = fExp (some A) ξ := by
  funext q
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ' h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩; exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p
  · have hq' := hcond.mpr hq
    unfold fExp
    rw [dif_pos hq', dif_pos hq]
    -- the chosen node is the same, and it is exposed
    have key : ∀ (P P' : Name → Prop) (e : P = P') (hP : ∃ x, P x) (hP' : ∃ x, P' x),
        Classical.choose hP = Classical.choose hP' := by
      intro P P' e hP hP'
      subst e
      rfl
    have hch : Classical.choose hq' = Classical.choose hq :=
      key (fun h => ∃ p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ' h p)
        (fun h => ∃ p, hashParent h = some p ∧ Exposed (some A) h ∧ q = pointOf ξ h p)
        (funext fun h => propext ⟨fun ⟨p, hp, he, hq⟩ => ⟨p, hp, he, hq.trans (hpt h p hp he)⟩,
          fun ⟨p, hp, he, hq⟩ => ⟨p, hp, he, hq.trans (hpt h p hp he).symm⟩⟩) hq' hq
    rw [hch]
    obtain ⟨p, hp, he, -⟩ := Classical.choose_spec hq
    rw [hout _ he]
  · rw [fExp_eq_none _ hq, fExp_eq_none _ (fun h => hq (hcond.mp h))]

theorem fExp_updHash {A : Finset Name} (hA : IsCut A) (ξ : Rec) {s : Name}
    (hs : HiddenCoord A s) (b : BitVec 256) : fExp (some A) (updHash ξ s b) = fExp (some A) ξ := by
  refine fExp_congr (fun h p hp he => pointOf_updHash hA ξ hs b hp ((exposed_some_iff A h).mp he))
    fun h he => ?_
  have hne : h ≠ s := fun e => hs.1 (e ▸ (exposed_some_iff A h).mp he)
  exact snd_updHash_of_ne _ _ _ _ hne

theorem fExp_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 28}
    (hs : HiddenCoord A (src k)) (b : BitVec 192) : fExp (some A) (updSrc ξ k b) = fExp (some A) ξ := by
  refine fExp_congr (fun h p hp he => pointOf_updSrc hA ξ hs b hp ((exposed_some_iff A h).mp he))
    fun h _ => rfl

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
    fExp_updHash hA ξ hs]

theorem dataOf_updSrc {A : Finset Name} (hA : IsCut A) (ξ : Rec) {k : Fin 28}
    (hs : HiddenCoord A (src k)) (b : BitVec 192) : dataOf A (updSrc ξ k b) = dataOf A ξ := by
  simp only [dataOf, pkOf_updSrc, revealed_updSrc hA _ hs, fExp_updSrc hA ξ hs]

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

theorem eq_pointOf_iff (ξ : Rec) (h p : Name) (u : BitVec p.len) :
    (⟨p.len, u⟩ : Query) = pointOf ξ h p ↔ val ξ p = u := by
  constructor
  · intro e
    exact (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  · intro hv
    show _ = (⟨p.len, val ξ p⟩ : Query)
    rw [hv]

theorem card_hashNodes_mul_ε₁_le : (897 : ℝ≥0∞) * ε₁ ≤ ε := by
  have h0 : (2 : ℝ≥0∞) ^ 64 ≠ 0 := by simp
  have ht : (2 : ℝ≥0∞) ^ 64 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : ε = (2 : ℝ≥0∞) ^ 64 * ε₁ := by
    rw [ε₁, ε, show (2 : ℝ≥0∞) ^ 192 = 2 ^ 64 * 2 ^ 128 by rw [← pow_add],
      ENNReal.mul_inv (Or.inl h0) (Or.inl ht), ← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul]
  rw [e]
  refine mul_le_mul' ?_ le_rfl
  exact_mod_cast (by norm_num : (897 : ℕ) ≤ 2 ^ 64)

/-- A fixed query is the point of at most one node per hash node in expectation: the union bound
over the hash nodes with the sharp per-node bound `ε₁`. -/
theorem sum_isPoint_le (S : Finset Rec) (q : Query)
    (hS : ∀ h p, hashParent h = some p → ClosedAt S (coordOf h)) :
    ∑ ξ ∈ S, (if ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p then w else 0) ≤
      ε * ∑ ξ ∈ S, w := by
  calc ∑ ξ ∈ S, (if ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p then w else 0)
      ≤ ∑ ξ ∈ S, ∑ h ∈ hashNodes,
          (if ∃ p, hashParent h = some p ∧ q = pointOf ξ h p then w else 0) := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        split_ifs with hex
        · obtain ⟨h, p, hp, hq⟩ := hex
          refine le_trans ?_ (Finset.single_le_sum (f := fun h =>
            if ∃ p, hashParent h = some p ∧ q = pointOf ξ h p then w else 0)
            (fun _ _ => zero_le) (mem_hashNodes.2 (by rw [hp]; rfl)))
          exact le_of_eq (if_pos ⟨p, hp, hq⟩).symm
        · exact zero_le
    _ = ∑ h ∈ hashNodes, ∑ ξ ∈ S,
          (if ∃ p, hashParent h = some p ∧ q = pointOf ξ h p then w else 0) := Finset.sum_comm
    _ ≤ ∑ _h ∈ hashNodes, ε₁ * ∑ ξ ∈ S, w := by
        refine Finset.sum_le_sum fun h hh => ?_
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (mem_hashNodes.1 hh)
        by_cases hq : ∃ u : BitVec p.len, q = ⟨p.len, u⟩
        · obtain ⟨u, rfl⟩ := hq
          have key : ∀ ξ : Rec, (∃ p', hashParent h = some p' ∧ (⟨p.len, u⟩ : Query) = pointOf ξ h p') ↔
              val ξ p = u := by
            intro ξ
            constructor
            · rintro ⟨p', hp', e⟩
              rw [hp] at hp'
              obtain rfl := Option.some.inj hp'
              exact (eq_pointOf_iff ξ h p u).1 e
            · intro hv
              exact ⟨p, hp, (eq_pointOf_iff ξ h p u).2 hv⟩
          calc ∑ ξ ∈ S, (if ∃ p', hashParent h = some p' ∧ (⟨p.len, u⟩ : Query) = pointOf ξ h p' then w else 0)
              = ∑ ξ ∈ S, (if val ξ p = u then w else 0) := by
                refine Finset.sum_congr rfl fun ξ _ => ?_
                by_cases hv : val ξ p = u
                · rw [if_pos ((key ξ).2 hv), if_pos hv]
                · rw [if_neg (fun h => hv ((key ξ).1 h)), if_neg hv]
            _ ≤ _ := sum_input_eq_le' hp S (hS h p hp) u
        · have hz : ∀ ξ : Rec, ¬ ∃ p', hashParent h = some p' ∧ q = pointOf ξ h p' := by
            rintro ξ ⟨p', hp', e⟩
            rw [hp] at hp'
            obtain rfl := Option.some.inj hp'
            exact hq ⟨val ξ p, e⟩
          rw [Finset.sum_eq_zero fun ξ _ => if_neg (hz ξ)]
          exact zero_le
    _ = 897 * ε₁ * ∑ ξ ∈ S, w := by
        rw [Finset.sum_const, card_hashNodes, nsmul_eq_mul, Nat.cast_ofNat, mul_assoc]
    _ ≤ ε * ∑ ξ ∈ S, w := mul_le_mul' card_hashNodes_mul_ε₁_le le_rfl

/-- Before signing, every keygen point is hidden: a fixed query point is a keygen point of at
most an `ε` fraction of the records with a given public key. -/
theorem hits_charge_A (pk : BitVec 128) (q : Query) :
    ∑ ξ ∈ fiberA pk, (if (kc ξ q).isSome then w else 0) ≤ ε * ∑ ξ ∈ fiberA pk, w := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_)) (sum_isPoint_le (fiberA pk) q ?_)
  · by_cases hk : (kc ξ q).isSome
    · rw [if_pos hk, if_pos ((kc_isSome_iff ξ q).1 hk)]
    · rw [if_neg hk, if_neg (fun h => hk ((kc_isSome_iff ξ q).2 h))]
  · intro h p hp
    exact fiberA_closedAt pk (coordOf_ne_rh h ((hashParent_isSome_iff h).mp (by rw [hp]; rfl)))

/-- After signing at `A`, a fixed query point is a hidden keygen point of at most an `ε`
fraction of the records with given public data. -/
theorem hits_charge_B {A : Finset Name} (hA : IsCut A) (d : Data) (q : Query) :
    ∑ ξ ∈ fiberB A d, (if (fHid (some A) ξ q).isSome then w else 0) ≤
      ε * ∑ ξ ∈ fiberB A d, w := by
  -- restrict the union to the hash nodes that are not evaluated at `A`
  have hsub : ∀ ξ, (fHid (some A) ξ q).isSome →
      ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧ q = pointOf ξ h p :=
    fun ξ h => (fHid_isSome_some_iff A ξ q).1 h
  calc ∑ ξ ∈ fiberB A d, (if (fHid (some A) ξ q).isSome then w else 0)
      ≤ ∑ ξ ∈ fiberB A d, ∑ h ∈ hashNodes.filter (fun h => ¬ Evaluated A h),
          (if ∃ p, hashParent h = some p ∧ q = pointOf ξ h p then w else 0) := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        split_ifs with hex
        · obtain ⟨h, p, hp, hh, hq⟩ := hsub ξ hex
          refine le_trans ?_ (Finset.single_le_sum (f := fun h =>
            if ∃ p, hashParent h = some p ∧ q = pointOf ξ h p then w else 0)
            (fun _ _ => zero_le) (Finset.mem_filter.2 ⟨mem_hashNodes.2 (by rw [hp]; rfl), hh⟩))
          exact le_of_eq (if_pos ⟨p, hp, hq⟩).symm
        · exact zero_le
    _ = ∑ h ∈ hashNodes.filter (fun h => ¬ Evaluated A h), ∑ ξ ∈ fiberB A d,
          (if ∃ p, hashParent h = some p ∧ q = pointOf ξ h p then w else 0) := Finset.sum_comm
    _ ≤ ∑ _h ∈ hashNodes.filter (fun h => ¬ Evaluated A h), ε₁ * ∑ ξ ∈ fiberB A d, w := by
        refine Finset.sum_le_sum fun h hh => ?_
        rw [Finset.mem_filter] at hh
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (mem_hashNodes.1 hh.1)
        have hclosed : ClosedAt (fiberB A d) (coordOf h) :=
          fiberB_closedAt hA d (coordOf_hiddenCoord hA hp hh.2)
        by_cases hq : ∃ u : BitVec p.len, q = ⟨p.len, u⟩
        · obtain ⟨u, rfl⟩ := hq
          have key : ∀ ξ : Rec, (∃ p', hashParent h = some p' ∧ (⟨p.len, u⟩ : Query) = pointOf ξ h p') ↔
              val ξ p = u := by
            intro ξ
            constructor
            · rintro ⟨p', hp', e⟩
              rw [hp] at hp'
              obtain rfl := Option.some.inj hp'
              exact (eq_pointOf_iff ξ h p u).1 e
            · intro hv
              exact ⟨p, hp, (eq_pointOf_iff ξ h p u).2 hv⟩
          calc ∑ ξ ∈ fiberB A d, (if ∃ p', hashParent h = some p' ∧ (⟨p.len, u⟩ : Query) = pointOf ξ h p' then w else 0)
              = ∑ ξ ∈ fiberB A d, (if val ξ p = u then w else 0) := by
                refine Finset.sum_congr rfl fun ξ _ => ?_
                by_cases hv : val ξ p = u
                · rw [if_pos ((key ξ).2 hv), if_pos hv]
                · rw [if_neg (fun h => hv ((key ξ).1 h)), if_neg hv]
            _ ≤ _ := sum_input_eq_le' hp _ hclosed u
        · have hz : ∀ ξ : Rec, ¬ ∃ p', hashParent h = some p' ∧ q = pointOf ξ h p' := by
            rintro ξ ⟨p', hp', e⟩
            rw [hp] at hp'
            obtain rfl := Option.some.inj hp'
            exact hq ⟨val ξ p, e⟩
          rw [Finset.sum_eq_zero fun ξ _ => if_neg (hz ξ)]
          exact zero_le
    _ ≤ ∑ _h ∈ hashNodes, ε₁ * ∑ ξ ∈ fiberB A d, w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => zero_le)
    _ = 897 * ε₁ * ∑ ξ ∈ fiberB A d, w := by
        rw [Finset.sum_const, card_hashNodes, nsmul_eq_mul, Nat.cast_ofNat, mul_assoc]
    _ ≤ ε * ∑ ξ ∈ fiberB A d, w := mul_le_mul' card_hashNodes_mul_ε₁_le le_rfl

end Forest

end OptimalOTS
