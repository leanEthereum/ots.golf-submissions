import Submissions.UpperLeanIsa.FourChildCodec
import Submissions.UpperLeanIsa.SplitProfiles
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer.FourChildCodec
open scoped Classical

theorem mult_pos (u v : ℕ) (hv : v < cut u) : 0 < mult u v :=
  multS_pos (ushape_lt u) hv

theorem expanded_profile_sum (p : List MProfile) (F : ℕ → ℕ → ℕ) :
    ((p.flatMap fun x => List.replicate x.2.2 (x.1,x.2.1)).map
      fun x => x.2 * F x.1 x.2).sum = profileSumM p F := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, ih, profileSumM, List.map_cons, List.sum_cons, smul_eq_mul]
    rw [Nat.mul_assoc]

theorem profile_count {u : ℕ} (hu : u < 13) (F : ℕ → ℕ → ℕ) :
    ∑ v ∈ Finset.range (cut u), F (cost u v) (mult u v) =
      profileSumM (SplitDP.profile u) F := by
  have hs : ushape u = u := Nat.mod_eq_of_lt hu
  have ht := SplitTables.tables_ok u hu
  simp only [SplitTables.tableOK, Bool.and_eq_true] at ht
  have hm := (codec_facts hu).2.1
  calc
    _ = ∑ v ∈ Finset.range (cutS u),
        F (selected u v).1.sum (selected u v).2.2 := by
      simp only [cut, hs]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [cost, mult, hs, costS, tupS, if_pos (Finset.mem_range.mp hv), multS]
    _ = ((SplitTables.entries u).map fun e => e.2.2 * F e.1.sum e.2.2).sum := by
      have h := SplitTables.interval_sum (fun e => F e.1.sum e.2.2)
        (SplitTables.entries u) 0 ht.2
      simpa only [Nat.zero_add, hm, Finset.range_eq_Ico, selected] using h
    _ = (((SplitTables.entries u).map fun e => (e.1.sum,e.2.2)).map
        fun x => x.2 * F x.1 x.2).sum := by rw [List.map_map]; rfl
    _ = _ := by rw [SplitDP.profile_expand hu, expanded_profile_sum]

theorem compM_rec {n : ℕ} (hn : n < 13) (s w : ℕ) :
    compM cut cost mult (n + 1) s w =
      ((SplitDP.profile n).map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM cut cost mult n (s - x.1) (w / x.2.1) else 0).sum :=
  compM_succ_profile cut cost mult _ n (profile_count hn) s w

/-- This counts actual127-bit indices, not merely tuple profiles. -/
theorem card_weight_raw (w : ℕ) :
    (Finset.univ.filter fun I : Index =>
        params.Accepted I ∧ wprod I = w).card =
      ∑ s ∈ Finset.Ico 22 86, compM cut cost mult 13 s w := by
  rw [← card_windowM cut cost mult mult_pos]
  refine Finset.card_bij' (fun I hI => fun u => ⟨field u I, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepted_iff] at hI
      exact (not_dummy_iff I).mp hI.1.1 u u.isLt⟩)
    (fun c _ => indexOf (fun u => Fin.castLE (cut_le u u.isLt) (c u))) ?_ ?_ ?_ ?_
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepted_iff, gsum_eq, wprod] at hI ⊢
    exact ⟨hI.1.2.1, hI.1.2.2, hI.2⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepted_iff, gsum_eq, wprod] at hc ⊢
    simp only [field_indexOf, Fin.val_castLE]
    refine ⟨⟨(not_dummy_iff _).mpr fun u hu => ?_, hc.1, hc.2.1⟩, hc.2.2⟩
    have := field_indexOf (fun u => Fin.castLE (cut_le u u.isLt) (c u)) ⟨u, hu⟩
    simp only [Fin.val_castLE] at this
    rw [this]
    exact (c ⟨u, hu⟩).isLt
  · intro I _
    exact indexOf_fields I
  · intro c _
    funext u
    exact Fin.ext ((field_indexOf _ u).trans (Fin.val_castLE _ _))

end OptimalOTS.LeanIsaBaseline.Layer.FourChildCodec
