/-! Generic linear-scan certificates for literal `Nat` lists.

Kernel `decide` over `∀ t < n, P (l.getD t 0)` walks the list once per index, which is
quadratic. The helpers below state such facts as one structural pass over the list and transfer
them to the indexed form once, generically. -/

namespace OptimalOTS.LeanIsaBaseline.Layer.ListCert

/-- Strictly increasing, checked by one pass with raw `Nat.blt`. -/
def ascB : List Nat → Bool
  | a :: b :: l => Nat.blt a b && ascB (b :: l)
  | _ => true

theorem ascB_cons {a : Nat} {l : List Nat} (h : ascB (a :: l) = true) : ascB l = true := by
  match l, h with
  | [], _ => rfl
  | _ :: _, h => simp only [ascB, Bool.and_eq_true] at h; exact h.2

theorem ascB_head_lt {a : Nat} {l : List Nat} (h : ascB (a :: l) = true) :
    ∀ x ∈ l, a < x := by
  induction l generalizing a with
  | nil => intro x hx; cases hx
  | cons b l ih =>
    simp only [ascB, Bool.and_eq_true, Nat.blt_eq] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (ih h.2 x hx)

theorem ascB_pairwise : ∀ {l : List Nat}, ascB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | _ :: _, h => List.Pairwise.cons (ascB_head_lt h) (ascB_pairwise (ascB_cons h))

theorem ascB_nodup {l : List Nat} (h : ascB l = true) : l.Nodup :=
  (ascB_pairwise h).imp Nat.ne_of_lt

theorem ascB_getD : ∀ {l : List Nat}, ascB l = true →
    ∀ t, t + 1 < l.length → l.getD t 0 < l.getD (t + 1) 0
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: l, h, 0, _ => by
    simp only [ascB, Bool.and_eq_true, Nat.blt_eq] at h
    simpa using h.1
  | a :: b :: l, h, t + 1, ht => by
    have := ascB_getD (ascB_cons h) t (by simp at ht ⊢; omega)
    simpa using this

theorem getD_eq_getElem' {l : List Nat} {t : Nat} (h : t < l.length) : l.getD t 0 = l[t] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_of_all {p : Nat → Bool} {l : List Nat} (h : l.all p = true) :
    ∀ t < l.length, p (l.getD t 0) = true := by
  intro t ht
  rw [getD_eq_getElem' ht]
  exact List.all_eq_true.1 h _ (List.getElem_mem ht)

theorem getD_zipWith {f : Nat → Nat → Nat} {l₁ l₂ : List Nat} {t : Nat}
    (h₁ : t < l₁.length) (h₂ : t < l₂.length) :
    (List.zipWith f l₁ l₂).getD t 0 = f (l₁.getD t 0) (l₂.getD t 0) := by
  have h : t < (List.zipWith f l₁ l₂).length := by simp; omega
  rw [getD_eq_getElem' h, getD_eq_getElem' h₁, getD_eq_getElem' h₂,
    List.getElem_zipWith]

end OptimalOTS.LeanIsaBaseline.Layer.ListCert
