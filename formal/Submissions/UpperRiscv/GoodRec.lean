import Submissions.UpperRiscv.Resample

/-!
# Good records are the rule

A record is good (`GoodRec`) when its keygen points are pairwise distinct and no honest output
simulates another hash node with an input of the same length. Both failures are collision events
on at least 144 bits between two coordinates of the uniform record; the union bound over the
ordered pairs of hash nodes gives `δ = 2 · 1025² · 2⁻¹⁴⁴` (`sum_w_not_goodRec_le`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace Forest

open Name

/-! ## Generic resampling bounds -/

/-- Resampling a hash coordinate on a closed set: an event with at most `2 ^ 112` good values
of the coordinate has weight at most `ε₁`. -/
theorem sum_ind_le_of_card_updHash (s : Name) (hs : ∀ k, s ≠ src k) (S : Finset Rec)
    (hS : ∀ ξ ∈ S, ∀ b : BitVec 256, updHash ξ s b ∈ S) (f : Rec → Prop) [DecidablePred f]
    (hf : ∀ ξ, (Finset.univ.filter fun b : BitVec 256 => f (updHash ξ s b)).card ≤ 2 ^ 112) :
    ∑ ξ ∈ S, (if f ξ then w else 0) ≤ ε₁ * ∑ ξ ∈ S, w := by
  rw [Finset.mul_sum, sum_updHash S s hs hS (fun ξ => if f ξ then w else 0)]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hle' : ((Finset.univ.filter fun b : BitVec 256 => f (updHash ξ s b)).card : ℝ≥0∞) ≤
      2 ^ 112 := by exact_mod_cast hf ξ
  calc (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
        (((Finset.univ.filter fun b : BitVec 256 => f (updHash ξ s b)).card : ℝ≥0∞) * w)
      ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * (2 ^ 112 * w) := by gcongr
    _ = ε₁ * w := by rw [← mul_assoc, inv_card_mul_two_pow_112]

/-- Resampling a source on a closed set: an event with at most one good value of the source has
weight at most `ε₁`. -/
theorem sum_ind_le_of_card_updSrc (k : Fin 32) (S : Finset Rec)
    (hS : ∀ ξ ∈ S, ∀ b : BitVec (chainBits k), updSrc ξ k b ∈ S) (f : Rec → Prop) [DecidablePred f]
    (hf : ∀ ξ, (Finset.univ.filter fun b : BitVec (chainBits k) => f (updSrc ξ k b)).card ≤ 1) :
    ∑ ξ ∈ S, (if f ξ then w else 0) ≤ ε₁ * ∑ ξ ∈ S, w := by
  rw [Finset.mul_sum, sum_updSrc S k hS (fun ξ => if f ξ then w else 0)]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hle' : ((Finset.univ.filter fun b : BitVec (chainBits k) => f (updSrc ξ k b)).card : ℝ≥0∞) ≤
      1 := by exact_mod_cast hf ξ
  calc (Fintype.card (BitVec (chainBits k)) : ℝ≥0∞)⁻¹ *
        (((Finset.univ.filter fun b : BitVec (chainBits k) => f (updSrc ξ k b)).card : ℝ≥0∞) * w)
      ≤ (Fintype.card (BitVec (chainBits k)) : ℝ≥0∞)⁻¹ * (1 * w) := by gcongr
    _ ≤ ε₁ * w := by
        rw [one_mul]
        exact mul_le_mul' (inv_source_card_le k) le_rfl

theorem hashNode_ne_src {h p : Name} (hp : hashParent h = some p) (k : Fin 32) : h ≠ src k := by
  rintro rfl
  cases hp

/-! ## Distinct keygen points -/

/-- The coordinate of a hash node feeds no other hash node's input. -/
theorem coordOf_not_mem_deps {h p h' p' : Name} (hp : hashParent h = some p)
    (hp' : hashParent h' = some p') (hne : h ≠ h') : coordOf h ∉ deps p' := by
  intro hd
  cases h <;> cases h' <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp hp' <;>
    subst hp <;> subst hp'
  · rename_i k t k' t'
    simp only [coordOf, deps] at hd
    split_ifs at hd with ht ht' <;>
      simp only [Finset.mem_singleton, Name.src.injEq, Name.ch.injEq, reduceCtorEq,
        Fin.mk.injEq] at hd
    · subst hd
      exact hne (by congr 1; exact Fin.ext (by omega))
    · obtain ⟨rfl, h2⟩ := hd
      exact hne (by congr 1; exact Fin.ext (by omega))
  · rename_i k t
    simp only [coordOf, deps, Finset.mem_image, Finset.mem_univ, true_and] at hd
    obtain ⟨a, ha⟩ := hd
    split_ifs at ha with ht
    obtain ⟨-, h2⟩ := Name.ch.inj ha
    have h3 := Fin.ext_iff.1 h2
    have h4 : (31 : Fin 32).val = 31 := rfl
    have := t.isLt
    simp only at h3
    omega
  · rename_i k' t'
    simp only [coordOf, deps] at hd
    split_ifs at hd with ht'
    · simp only [Finset.mem_singleton, reduceCtorEq] at hd
    · rw [Finset.mem_singleton] at hd
      obtain ⟨-, h2⟩ := Name.ch.inj hd
      have h3 := Fin.ext_iff.1 h2
      have h4 : (31 : Fin 32).val = 31 := rfl
      have := t'.isLt
      simp only [Fin.val_mk] at h3
      omega
  · exact hne rfl

/-- The point of a hash node (a dummy query elsewhere). -/
def pt (ξ : Rec) (h : Name) : Query := ((hashParent h).map fun p => pointOf ξ h p).getD ⟨0, 0⟩

theorem pt_eq {ξ : Rec} {h p : Name} (hp : hashParent h = some p) : pt ξ h = pointOf ξ h p := by
  rw [pt, hp, Option.map_some, Option.getD_some]

theorem exists_pair_of_not_distinct {ξ : Rec} (hd : ¬ DistinctRec ξ) :
    ∃ h p h' p', hashParent h = some p ∧ hashParent h' = some p' ∧ h ≠ h' ∧
      pointOf ξ h p = pointOf ξ h' p' := by
  unfold DistinctRec Graph.Distinct at hd
  push Not at hd
  obtain ⟨v, v', q, hv, hv', hne⟩ := hd
  obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨ofFin v, fin_ofFin v⟩
  obtain ⟨h', rfl⟩ : ∃ h' : Name, h'.fin = v' := ⟨ofFin v', fin_ofFin v'⟩
  rw [graph_point_fin] at hv hv'
  rcases hpp : hashParent h with _ | p
  · rw [hpp] at hv; cases hv
  rcases hpp' : hashParent h' with _ | p'
  · rw [hpp'] at hv'; cases hv'
  rw [hpp, Option.map_some] at hv
  rw [hpp', Option.map_some] at hv'
  refine ⟨h, p, h', p', hpp, hpp', fun e => hne (congrArg Name.fin e), ?_⟩
  rw [Option.some.inj hv, Option.some.inj hv']

theorem card_pair_updHash_le {h p h' p' : Name} (hp : hashParent h = some p)
    (hp' : hashParent h' = some p') (hne : h ≠ h') (ξ : Rec) (hs : ∀ k, coordOf h ≠ src k) :
    (Finset.univ.filter fun b : BitVec 256 =>
      pointOf (updHash ξ (coordOf h) b) h p = pointOf (updHash ξ (coordOf h) b) h' p').card ≤
      2 ^ 112 := by
  have hinv : ∀ b, pointOf (updHash ξ (coordOf h) b) h' p' = pointOf ξ h' p' := fun b => by
    unfold pointOf
    rw [val_updHash_of_not_mem_deps _ _ _ _ (coordOf_not_mem_deps hp hp' hne)]
  by_cases hq : ∃ u : BitVec p.len, pointOf ξ h' p' = ⟨p.len, u⟩
  · obtain ⟨u, hu⟩ := hq
    refine le_trans (Finset.card_le_card fun b hb => ?_) (card_updHash_input_le' hp ξ hs u)
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hb.2
    rw [hinv, hu] at this
    exact (eq_pointOf_iff _ h p u).1 this.symm
  · refine le_trans (Finset.card_le_card (t := ∅) fun b hb => ?_) (by simp)
    rw [Finset.mem_filter] at hb
    exact absurd ⟨val (updHash ξ (coordOf h) b) p, (hinv b).symm.trans hb.2.symm⟩ hq

theorem card_pair_updSrc_le {h p h' p' : Name} (hp : hashParent h = some p)
    (hp' : hashParent h' = some p') (hne : h ≠ h') (ξ : Rec) {k : Fin 32} (hk : coordOf h = src k) :
    (Finset.univ.filter fun b : BitVec (chainBits k) =>
      pointOf (updSrc ξ k b) h p = pointOf (updSrc ξ k b) h' p').card ≤ 1 := by
  have hinv : ∀ b, pointOf (updSrc ξ k b) h' p' = pointOf ξ h' p' := fun b => by
    unfold pointOf
    rw [val_updSrc_of_not_mem_deps _ _ _ _ (hk ▸ coordOf_not_mem_deps hp hp' hne)]
  by_cases hq : ∃ u : BitVec p.len, pointOf ξ h' p' = ⟨p.len, u⟩
  · obtain ⟨u, hu⟩ := hq
    refine le_trans (Finset.card_le_card fun b hb => ?_) (card_updSrc_input_le hp ξ hk u)
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hb.2
    rw [hinv, hu] at this
    exact (eq_pointOf_iff _ h p u).1 this.symm
  · refine le_trans (Finset.card_le_card (t := ∅) fun b hb => ?_) (by simp)
    rw [Finset.mem_filter] at hb
    exact absurd ⟨val (updSrc ξ k b) p, (hinv b).symm.trans hb.2.symm⟩ hq

/-- Two distinct hash nodes share their keygen point with probability at most `ε₁`. -/
theorem sum_pair_le {h p h' p' : Name} (hp : hashParent h = some p)
    (hp' : hashParent h' = some p') (hne : h ≠ h') :
    ∑ ξ : Rec, (if pointOf ξ h p = pointOf ξ h' p' then w else 0) ≤ ε₁ := by
  by_cases hsrc : ∃ k, coordOf h = src k
  · obtain ⟨k, hk⟩ := hsrc
    refine le_trans (sum_ind_le_of_card_updSrc k Finset.univ (fun _ _ _ => by simp)
      (fun ξ => pointOf ξ h p = pointOf ξ h' p') fun ξ => card_pair_updSrc_le hp hp' hne ξ hk) ?_
    rw [sum_w, mul_one]
  · push Not at hsrc
    refine le_trans (sum_ind_le_of_card_updHash (coordOf h) hsrc Finset.univ
      (fun _ _ _ => by simp) (fun ξ => pointOf ξ h p = pointOf ξ h' p')
      fun ξ => card_pair_updHash_le hp hp' hne ξ hsrc) ?_
    rw [sum_w, mul_one]

theorem sum_w_not_distinct_le :
    ∑ ξ : Rec, (if ¬ DistinctRec ξ then w else 0) ≤ 1025 * 1025 * ε₁ := by
  calc ∑ ξ : Rec, (if ¬ DistinctRec ξ then w else 0)
      ≤ ∑ ξ : Rec, ∑ h ∈ hashNodes, ∑ h' ∈ hashNodes,
          (if h ≠ h' ∧ pt ξ h = pt ξ h' then w else 0) := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        by_cases hd : DistinctRec ξ
        · rw [if_neg (not_not.2 hd)]
          exact zero_le
        · rw [if_pos hd]
          obtain ⟨h, p, h', p', hp, hp', hne, he⟩ := exists_pair_of_not_distinct hd
          refine le_trans ?_ (Finset.single_le_sum (f := fun h => ∑ h' ∈ hashNodes,
            (if h ≠ h' ∧ pt ξ h = pt ξ h' then w else 0)) (fun _ _ => zero_le)
            (mem_hashNodes.2 (by rw [hp]; rfl)))
          refine le_trans ?_ (Finset.single_le_sum (f := fun h' =>
            (if h ≠ h' ∧ pt ξ h = pt ξ h' then w else 0)) (fun _ _ => zero_le)
            (mem_hashNodes.2 (by rw [hp']; rfl)))
          exact le_of_eq (if_pos ⟨hne, by rw [pt_eq hp, pt_eq hp', he]⟩).symm
    _ = ∑ h ∈ hashNodes, ∑ h' ∈ hashNodes, ∑ ξ : Rec,
          (if h ≠ h' ∧ pt ξ h = pt ξ h' then w else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ ≤ ∑ _h ∈ hashNodes, ∑ _h' ∈ hashNodes, ε₁ := by
        refine Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun h' hh' => ?_
        by_cases hne : h = h'
        · rw [Finset.sum_eq_zero fun ξ _ => if_neg fun hc => hc.1 hne]
          exact zero_le
        · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (mem_hashNodes.1 hh)
          obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.1 (mem_hashNodes.1 hh')
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_))
            (sum_pair_le hp hp' hne)
          by_cases he : pointOf ξ h p = pointOf ξ h' p'
          · rw [if_pos ⟨hne, by rw [pt_eq hp, pt_eq hp', he]⟩, if_pos he]
          · rw [if_neg (fun hc => he (by rw [← pt_eq hp, ← pt_eq hp']; exact hc.2)), if_neg he]
    _ = 1025 * 1025 * ε₁ := by
        rw [Finset.sum_const, Finset.sum_const, card_hashNodes, nsmul_eq_mul, nsmul_eq_mul,
          Nat.cast_ofNat, ← mul_assoc]

/-! ## No output collision -/

theorem sim_updHash_of_ne (ξ : Rec) {h s : Name} (hs : h ≠ s) (b w : BitVec 256) :
    sim (updHash ξ s b) h w ↔ sim ξ h w := by
  cases h <;> simp only [sim, snd_updHash_of_ne ξ s b _ hs]

theorem exists_pair_of_not_noOutCollision {ξ : Rec} (hd : ¬ NoOutCollision ξ) :
    ∃ h p h' p', hashParent h = some p ∧ hashParent h' = some p' ∧ h ≠ h' ∧ h ≠ rh ∧
      sim ξ h (ξ.2 h'.fin) := by
  unfold NoOutCollision at hd
  push Not at hd
  obtain ⟨h, p, h', p', hp, hp', hl, hne, hs⟩ := hd
  refine ⟨h, p, h', p', hp, hp', hne, ?_, hs⟩
  rintro rfl
  simp only [hashParent, Option.some.injEq] at hp
  subst hp
  exact hne (eq_rh_of_hashParent_len hp' hl.symm).symm

/-- The honest output of a hash node simulates another one with probability at most `ε₁`. -/
theorem sum_sim_pair_le {h p h' p' : Name} (hp : hashParent h = some p)
    (hp' : hashParent h' = some p') (hne : h ≠ h') (hh : h ≠ rh) :
    ∑ ξ : Rec, (if sim ξ h (ξ.2 h'.fin) then w else 0) ≤ ε₁ := by
  refine le_trans (sum_ind_le_of_card_updHash h' (hashNode_ne_src hp') Finset.univ
    (fun _ _ _ => by simp) (fun ξ => sim ξ h (ξ.2 h'.fin)) fun ξ => ?_) ?_
  · refine le_trans (Finset.card_le_card fun b hb => ?_) (card_filter_sim_le' ξ h hh)
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hb.2
    rw [updHash_snd_self] at this
    exact (sim_updHash_of_ne ξ hne b b).1 this
  · rw [sum_w, mul_one]

theorem sum_w_not_noOutCollision_le :
    ∑ ξ : Rec, (if ¬ NoOutCollision ξ then w else 0) ≤ 1025 * 1025 * ε₁ := by
  calc ∑ ξ : Rec, (if ¬ NoOutCollision ξ then w else 0)
      ≤ ∑ ξ : Rec, ∑ h ∈ hashNodes, ∑ h' ∈ hashNodes,
          (if h ≠ h' ∧ h ≠ rh ∧ sim ξ h (ξ.2 h'.fin) then w else 0) := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        by_cases hd : NoOutCollision ξ
        · rw [if_neg (not_not.2 hd)]
          exact zero_le
        · rw [if_pos hd]
          obtain ⟨h, p, h', p', hp, hp', hne, hh, hs⟩ := exists_pair_of_not_noOutCollision hd
          refine le_trans ?_ (Finset.single_le_sum (f := fun h => ∑ h' ∈ hashNodes,
            (if h ≠ h' ∧ h ≠ rh ∧ sim ξ h (ξ.2 h'.fin) then w else 0)) (fun _ _ => zero_le)
            (mem_hashNodes.2 (by rw [hp]; rfl)))
          refine le_trans ?_ (Finset.single_le_sum (f := fun h' =>
            (if h ≠ h' ∧ h ≠ rh ∧ sim ξ h (ξ.2 h'.fin) then w else 0)) (fun _ _ => zero_le)
            (mem_hashNodes.2 (by rw [hp']; rfl)))
          exact le_of_eq (if_pos ⟨hne, hh, hs⟩).symm
    _ = ∑ h ∈ hashNodes, ∑ h' ∈ hashNodes, ∑ ξ : Rec,
          (if h ≠ h' ∧ h ≠ rh ∧ sim ξ h (ξ.2 h'.fin) then w else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ ≤ ∑ _h ∈ hashNodes, ∑ _h' ∈ hashNodes, ε₁ := by
        refine Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun h' hh' => ?_
        by_cases hne : h = h'
        · rw [Finset.sum_eq_zero fun ξ _ => if_neg fun hc => hc.1 hne]
          exact zero_le
        by_cases hrh : h = rh
        · rw [Finset.sum_eq_zero fun ξ _ => if_neg fun hc => hc.2.1 hrh]
          exact zero_le
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (mem_hashNodes.1 hh)
        obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.1 (mem_hashNodes.1 hh')
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_))
          (sum_sim_pair_le hp hp' hne hrh)
        by_cases hs : sim ξ h (ξ.2 h'.fin)
        · rw [if_pos ⟨hne, hrh, hs⟩, if_pos hs]
        · rw [if_neg (fun hc => hs hc.2.2), if_neg hs]
    _ = 1025 * 1025 * ε₁ := by
        rw [Finset.sum_const, Finset.sum_const, card_hashNodes, nsmul_eq_mul, nsmul_eq_mul,
          Nat.cast_ofNat, ← mul_assoc]

/-! ## Good records -/

/-- The weight of the bad records. -/
def δ : ℝ≥0∞ := 2 * (1025 * 1025) * ε₁

theorem sum_w_not_goodRec_le : ∑ ξ : Rec, (if ¬ GoodRec ξ then w else 0) ≤ δ := by
  calc ∑ ξ : Rec, (if ¬ GoodRec ξ then w else 0)
      ≤ ∑ ξ : Rec, ((if ¬ DistinctRec ξ then w else 0) + (if ¬ NoOutCollision ξ then w else 0)) := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        by_cases hd : DistinctRec ξ
        · by_cases hn : NoOutCollision ξ
          · rw [if_neg (fun h => h ⟨hd, hn⟩)]
            exact zero_le
          · rw [if_pos (fun h => hn h.2), if_pos hn]
            exact le_add_left le_rfl
        · rw [if_pos (fun h => hd h.1), if_pos hd]
          exact le_add_right le_rfl
    _ = ∑ ξ : Rec, (if ¬ DistinctRec ξ then w else 0) +
          ∑ ξ : Rec, (if ¬ NoOutCollision ξ then w else 0) := Finset.sum_add_distrib
    _ ≤ 1025 * 1025 * ε₁ + 1025 * 1025 * ε₁ := add_le_add sum_w_not_distinct_le sum_w_not_noOutCollision_le
    _ = δ := by rw [δ]; ring

theorem sum_w_not_distinctRec_le : ∑ ξ : Rec, (if ¬ DistinctRec ξ then w else 0) ≤ δ := by
  refine sum_w_not_distinct_le.trans ?_
  rw [δ]
  calc (1025 : ℝ≥0∞) * 1025 * ε₁ = 1 * (1025 * 1025) * ε₁ := by ring
    _ ≤ 2 * (1025 * 1025) * ε₁ := by gcongr; norm_num

end Forest

end OptimalOTS
