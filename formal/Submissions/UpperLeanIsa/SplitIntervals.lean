import Submissions.UpperLeanIsa.SplitTables

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitTables

def mass (es : List Entry) : ℕ := (es.map fun e => e.2.2).sum
def select (v : ℕ) : List Entry → Entry
  | [] => ([],0,0)
  | e :: es => if v < e.2.1 + e.2.2 then e else select v es

theorem interval_spec : ∀ (es : List Entry) (start v : ℕ),
    intervalsOK start es = true → start ≤ v → v < start + mass es →
    select v es ∈ es ∧ (select v es).2.1 ≤ v ∧
      v < (select v es).2.1 + (select v es).2.2
  | [], start, v, _, h1, h2 => by simp [mass] at h2; omega
  | e :: es, start, v, h, h1, h2 => by
    simp only [intervalsOK, Bool.and_eq_true, beq_iff_eq] at h
    simp only [mass, List.map_cons, List.sum_cons] at h2
    unfold select
    split_ifs with hv
    · exact ⟨List.mem_cons_self, by omega, hv⟩
    · have ht := interval_spec es (start + e.2.2) v h.2 (by omega) (by
        unfold mass; omega)
      exact ⟨List.mem_cons_of_mem _ ht.1, ht.2⟩

theorem interval_bounds : ∀ (es : List Entry) (start : ℕ),
    intervalsOK start es = true → ∀ e ∈ es,
      start ≤ e.2.1 ∧ e.2.1 + e.2.2 ≤ start + mass es
  | [], _, _, _, he => by simp at he
  | a :: es, start, h, e, he => by
    simp only [intervalsOK, Bool.and_eq_true, beq_iff_eq] at h
    simp only [mass, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp he with rfl | he
    · omega
    · have ht := interval_bounds es (start + a.2.2) h.2 e he
      unfold mass at ht
      omega

theorem select_eq : ∀ (es : List Entry) (start v : ℕ),
    intervalsOK start es = true → ∀ e ∈ es,
      e.2.1 ≤ v → v < e.2.1 + e.2.2 → select v es = e
  | [], _, _, _, _, he, _, _ => by simp at he
  | a :: es, start, v, h, e, he, h1, h2 => by
    simp only [intervalsOK, Bool.and_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.mp he with rfl | he
    · simp [select, h2]
    · have hb := interval_bounds es (start + a.2.2) h.2 e he
      rw [select, if_neg (by omega)]
      exact select_eq es (start + a.2.2) v h.2 e he h1 h2

/-- Summing over raw fields counts every decoded tuple once per alias. -/
theorem interval_sum (F : Entry → ℕ) : ∀ (es : List Entry) (start : ℕ),
    intervalsOK start es = true →
    ∑ v ∈ Finset.Ico start (start + mass es), F (select v es) =
      (es.map fun e => e.2.2 * F e).sum
  | [], start, _ => by simp [mass]
  | a :: es, start, h => by
    simp only [intervalsOK, Bool.and_eq_true, beq_iff_eq] at h
    have hmass : start + mass (a :: es) = start + a.2.2 + mass es := by
      simp [mass]; omega
    rw [hmass, ← Finset.sum_Ico_consecutive _ (by omega : start ≤ start + a.2.2)
      (Nat.le_add_right (start + a.2.2) (mass es))]
    have hfirst : ∑ v ∈ Finset.Ico start (start + a.2.2), F (select v (a :: es)) =
        a.2.2 * F a := by
      calc
        _ = ∑ _v ∈ Finset.Ico start (start + a.2.2), F a := by
          apply Finset.sum_congr rfl
          intro v hv
          have hv' := Finset.mem_Ico.mp hv
          rw [select, if_pos (by omega)]
        _ = a.2.2 * F a := by simp
    have htail : ∑ v ∈ Finset.Ico (start + a.2.2) (start + a.2.2 + mass es),
        F (select v (a :: es)) =
        ∑ v ∈ Finset.Ico (start + a.2.2) (start + a.2.2 + mass es),
          F (select v es) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hv' := Finset.mem_Ico.mp hv
      rw [select, if_neg (by omega)]
    rw [hfirst, htail, interval_sum F es (start + a.2.2) h.2]
    rfl

def tupleKey (u : ℕ) (t : List ℕ) : ℕ :=
  t.foldl (fun a b => a * 16 + b) (t.sum * 5 + zeroCount (t.take (visible u)))

def keysUp (u : ℕ) : List Entry → Bool
  | [] => true
  | [_] => true
  | a :: b :: es => tupleKey u a.1 < tupleKey u b.1 && keysUp u (b :: es)

theorem keysUp_lt (u : ℕ) : ∀ (es : List Entry), keysUp u es = true →
    ∀ i j, i < j → j < es.length →
    tupleKey u (es.getD i ([],0,0)).1 < tupleKey u (es.getD j ([],0,0)).1
  | [], _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | [_], _, i, j, hij, hj => by simp at hj; omega
  | a :: b :: es, h, i, j, hij, hj => by
    simp only [keysUp, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := keysUp_lt u (b :: es) h.2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : j < (b :: es).length := by simp only [List.length_cons] at hj ⊢; omega
    rw [List.getD_cons_succ]
    rcases i with _ | i
    · rw [List.getD_cons_zero]
      rcases j with _ | j
      · simpa using h.1
      · have := ih 0 (j + 1) (Nat.succ_pos j) hj'
        rw [List.getD_cons_zero] at this
        exact h.1.trans this
    · rw [List.getD_cons_succ]
      exact ih i j (by omega) hj'

theorem tuple_injective {u : ℕ} {es : List Entry} (h : keysUp u es = true)
    {a b : Entry} (ha : a ∈ es) (hb : b ∈ es) (hab : a.1 = b.1) : a = b := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, hf⟩ := List.mem_iff_getElem.mp hb
  have he' : es.getD i ([],0,0) = a := by rw [List.getD_eq_getElem _ _ hi]; exact he
  have hf' : es.getD j ([],0,0) = b := by rw [List.getD_eq_getElem _ _ hj]; exact hf
  have hij : i = j := by
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hn | hn
    · have := keysUp_lt u es h i j hn hj
      rw [he',hf',hab] at this
      exact (lt_irrefl _) this
    · have := keysUp_lt u es h j i hn hi
      rw [he',hf',hab] at this
      exact (lt_irrefl _) this
  rw [← he',← hf',hij]

end OptimalOTS.LeanIsaBaseline.Layer.SplitTables
