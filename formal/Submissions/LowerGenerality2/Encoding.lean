import Submissions.LowerGenerality2.Semantics

/-! Exact encoding and decoding of disclosed node values. -/

noncomputable section
open scoped Classical
namespace OptimalOTS.Encoding

open OptimalOTS.Dag


theorem testBit_foldr (l : List Bool) (i : ℕ) :
    (l.foldr (fun (b : Bool) (acc : ℕ) => b.toNat + 2 * acc) 0).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases i with _ | i
    · rw [Nat.testBit_zero]
      cases b <;> simp [Nat.add_mul_mod_self_left]
    · rw [Nat.testBit_succ, List.getD_cons_succ, ← ih i]
      congr 1
      cases b <;> simp <;> omega

theorem ofBits_toBits {n : ℕ} (x : BitVec n) : ofBits n (toBits x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, toBits]
  rw [testBit_foldr]
  simp [hi, List.getD_eq_getElem?_getD]

theorem length_toBits {n : ℕ} (x : BitVec n) : (toBits x).length = n := List.length_ofFn

theorem flatMap_split {n : ℕ} {β : Type} (f : Fin n → List β) (L : List (Fin n))
    (hL : L.Pairwise (· < ·)) (v : Fin n) (hv : v ∈ L) :
    L.flatMap f = (L.filter fun w => decide (w < v)).flatMap f ++ f v ++
      (L.filter fun w => decide (v < w)).flatMap f := by
  induction L with
  | nil => simp at hv
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    rcases List.mem_cons.1 hv with rfl | hv'
    · have h1 : (L.filter fun w => decide (w < v)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro w hw
        simpa using le_of_lt (hL.1 w hw)
      have h2 : (L.filter fun w => decide (v < w)) = L := by
        rw [List.filter_eq_self]
        intro w hw
        simpa using hL.1 w hw
      simp [List.filter_cons, h1, h2]
    · have hav : a < v := hL.1 v hv'
      rw [List.flatMap_cons, ih hL.2 hv']
      simp [List.filter_cons, hav, not_lt.2 hav.le]

section Generic

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable {G : Graph}

theorem length_encode (A : Finset (Fin G.size)) (x : G.Assignment) :
    (G.encode A x).length = G.revealBits A := by
  unfold Graph.encode Graph.revealBits
  rw [List.length_flatMap]
  simp only [length_toBits]
  rw [← List.sum_toFinset _ ((List.nodup_finRange _).filter _)]
  congr 1
  ext v
  simp

theorem decode_encode (A : Finset (Fin G.size)) (x : G.Assignment) (v : Fin G.size)
    (hv : v ∈ A) : G.decode A (G.encode A x) v = x v := by
  unfold Graph.decode Graph.encode
  have hL : ((List.finRange G.size).filter fun w => decide (w ∈ A)).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange _).filter _
  rw [flatMap_split _ _ hL v (by simp [hv])]
  have hoff : G.offset A v = ((((List.finRange G.size).filter fun w => decide (w ∈ A)).filter
      fun w => decide (w < v)).flatMap (fun w => toBits (x w))).length := by
    rw [List.length_flatMap]
    simp only [length_toBits]
    unfold Graph.offset
    rw [← List.sum_toFinset _ (((List.nodup_finRange _).filter _).filter _)]
    congr 1
    ext w
    simp [and_comm]
  rw [hoff, List.append_assoc, List.drop_left, List.take_left' (length_toBits _), ofBits_toBits]

end Generic

end OptimalOTS.Encoding
