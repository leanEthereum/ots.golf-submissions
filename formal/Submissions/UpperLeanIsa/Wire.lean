import Submissions.UpperLeanIsa.BasicProperties

/-! Fixed-width wire encoding, including both round trips. -/

namespace OptimalOTS.LeanIsaBaseline

theorem length_bits {n : ℕ} (x : BitVec n) : (toBits x).length = n :=
  List.length_ofFn

private theorem fold_bits_testBit (xs : List Bool) (i : ℕ) :
    (xs.foldr (fun (b : Bool) (a : ℕ) => b.toNat + 2 * a) 0).testBit i = xs.getD i false := by
  induction xs generalizing i with
  | nil => simp
  | cons b xs ih =>
    cases i with
    | zero => cases b <;> simp [Nat.testBit_zero]
    | succ i =>
      rw [List.foldr_cons, Nat.testBit_succ, List.getD_cons_succ, ← ih]
      congr 1
      cases b <;> simp
      omega

theorem ofBits_bits {n : ℕ} (x : BitVec n) : ofBits n (toBits x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, toBits]
  rw [fold_bits_testBit]
  simp [hi, List.getD_eq_getElem?_getD]

theorem bits_ofBits {n : ℕ} (xs : List Bool) (h : xs.length = n) :
    toBits (ofBits n xs) = xs := by
  apply List.ext_getElem
  · rw [length_bits, h]
  · intro i h₁ h₂
    rw [length_bits] at h₁
    simp only [toBits, List.getElem_ofFn, ofBits, BitVec.getLsbD_ofNat]
    rw [fold_bits_testBit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
    simp [h₁]

theorem slice_words {n w : ℕ} (xs : Fin n → BitVec w) (i : Fin n) :
    (((List.ofFn xs).flatMap toBits).drop (w * i.val)).take w = toBits (xs i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ, List.flatMap_cons]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero]
      exact List.take_left' (length_bits _)
    · simp only [Fin.val_succ]
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [show w + w * j.val = (toBits (xs 0)).length + w * j.val by rw [length_bits],
        List.drop_length_add_append]
      exact ih (fun j => xs j.succ) j

theorem decode_encode (xs : Words) : decode (encode xs) = xs := by
  funext i
  exact (congrArg (ofBits 128) (slice_words xs i)).trans (ofBits_bits (xs i))

theorem encode_injective : Function.Injective encode := by
  intro a b h
  exact (decode_encode a).symm.trans ((congrArg decode h).trans (decode_encode b))

theorem join_slices {α : Type} (w n : ℕ) (xs : List α) (h : xs.length = w * n) :
    (List.ofFn (fun i : Fin n => (xs.drop (w * i.val)).take w)).flatten = xs := by
  induction n generalizing xs with
  | zero =>
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    simp [this]
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero]
    have htail : (List.ofFn (fun i : Fin n => (xs.drop (w * i.succ.val)).take w)).flatten =
        xs.drop w := by
      convert ih (xs.drop w) (by simp only [List.length_drop, h, Nat.mul_succ]; omega) using 1
      congr 2
      funext i
      simp only [Fin.val_succ, List.drop_drop]
      congr 2
      simp only [Nat.mul_succ, Nat.add_comm]
    rw [htail, List.take_append_drop]

set_option maxRecDepth 4096 in
theorem encode_decode (bits : List Bool) (h : bits.length = 5504) :
    encode (decode bits) = bits := by
  have hlen (i : Fin 43) : ((bits.drop (128 * i.val)).take 128).length = 128 := by
    simp only [List.length_take, List.length_drop, h]
    have hi := i.isLt
    omega
  unfold encode decode
  rw [List.flatMap_def, List.map_ofFn]
  calc
    _ = (List.ofFn (fun i : Fin 43 => (bits.drop (128 * i.val)).take 128)).flatten :=
      congrArg List.flatten (congrArg List.ofFn (funext fun i => bits_ofBits _ (hlen i)))
    _ = bits := join_slices 128 43 bits h

end OptimalOTS.LeanIsaBaseline
