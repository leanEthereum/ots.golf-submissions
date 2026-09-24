import Submissions.UpperLeanIsa.LayerScheme
import Submissions.UpperLeanIsa.LayerBits

/-! Signature wire format of layer schemes: length and both decodings of `encode`. -/

open OracleSpec OracleComp

noncomputable section

namespace OptimalOTS.LeanIsaBaseline.Layer

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

theorem flatMap_length {n w : ℕ} (xs : Fin n → BitVec w) :
    ((List.ofFn xs).flatMap toBits).length = w * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatMap_cons, List.length_append, length_bits, ih]
    ring

theorem encode_length (xs : Fin numChains → Word) (η : Nonce) :
    (encode xs η).length = sigBits := by
  rw [encode, List.length_append, flatMap_length, length_bits]; rfl

theorem decodeWord_encode (xs : Fin numChains → Word) (η : Nonce) (k : Fin numChains) :
    decodeWord (encode xs η) k = xs k := by
  have hk : 128 * k.val + 128 ≤ ((List.ofFn xs).flatMap toBits).length := by
    rw [flatMap_length]; have := k.isLt; omega
  rw [decodeWord, encode, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega), slice_words, ofBits_bits]

theorem decodeNonce_encode (xs : Fin numChains → Word) (η : Nonce) :
    decodeNonce (encode xs η) = η := by
  have h : ((List.ofFn xs).flatMap toBits).length = 5376 := flatMap_length xs
  rw [decodeNonce, encode, ← h, List.drop_left, List.take_of_length_le (by rw [length_bits]),
    ofBits_bits]

/-- Verification rejects every string of the wrong length, on every path. -/
theorem verify_of_length_ne (P : Params) (pk : PublicKey) (m : Message) (bits : List Bool)
    (h : bits.length ≠ sigBits) : P.verify pk m bits = pure false := by
  rw [Params.verify, if_pos h]

theorem rejectsOversized (P : Params) : P.scheme.RejectsOversized maxSignatureBits := by
  intro pk m σ hσ
  change true ∉ support (P.verify pk m σ)
  rw [verify_of_length_ne P pk m σ (by unfold sigBits maxSignatureBits at *; omega)]
  simp

end OptimalOTS.LeanIsaBaseline.Layer
