import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanerVM.Parameters.Generator
import OptimalOTS.LeanIsaMachine
import Submissions.UpperLeanIsa.Correctness

/-!
# Constraint mathematics for the leanISA verifier

The machine program (design `NOTES.md`, §4 and §6) checks a Winternitz signature with
`MUL` / `XOR` / `SET` / `BLAKE2S` constraints along a dispatched path. This file proves, over plain
functions and values, the facts that turn those constraints into the scheme's fixed-table
verifier. Nothing here mentions the program or its execution, so the lemmas can be glued to any
layout.

1. `E` has characteristic two.
2. Chains: consecutive `BLAKE2S` outputs from position `e` compute `chainValue` (`chain_from`);
   `BLAKE2S` operands give `chainInput` and absorb inputs.
3. The absorb states compute `rootValue`.
4. The tie: the field sums of the shifted leaf words the leaves assert (`tieHi`, `tieLo`) are
   the message cells exactly when every leaf index `d k < 2 ^ fieldWidth k` is message field `k`
   (`tie_iff`), and the loader's cells (`inputWord_*`).
5. The checksum identity `Σ_{k<41} E k + 64 · (E 41 − 64) + E 42 = 5271` recovers the two
   offset checksum digits (`checksum_digits`), and the true digits satisfy it
   (`checksum_honest_sum`).
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord statementBits)

/-! ## 1. Characteristic two -/

/-- Addition in `E` is limb-wise `XOR`, so every word is its own negative. -/
theorem add_self_E (a : E) : a + a = 0 := by
  exact CharTwo.add_self_eq_zero a

/-- Addition in `K` is `XOR`. -/
theorem add_self_K (a : K) : a + a = 0 := BF64.add_self a

/-! ## 2. Chains -/

theorem chainValue_zero' (f : HashTable) (i j : ℕ) (x : Word) : chainValue f i j 0 x = x := by
  rfl

/-- One more chain step, appended at the end. -/
theorem chainValue_succ' (f : HashTable) (i j n : ℕ) (x : Word) :
    chainValue f i j (n + 1) x =
      (f ⟨896, chainInput i (j + n) (chainValue f i j n x)⟩).extractLsb' 0 128 := by
  rw [← chainValue_add f i j n 1 x]
  all_goals rfl

/-- A chain entered at position `e`: step `e` hashes `σ` (when `e < 127`), steps
`j ∈ (e, 126]` hash the previous output, and for `e = 127` the endpoint is `σ` itself. Then the
endpoint `x 127` is `chainValue f i e (127 - e) σ`. -/
theorem chain_from (f : HashTable) (i e : ℕ) (he : e ≤ 127) (σ : Word) (x : ℕ → Word)
    (hleaf : e < 127 → x (e + 1) = (f ⟨896, chainInput i e σ⟩).extractLsb' 0 128)
    (hbody : ∀ j, e < j → j ≤ 126 →
      x (j + 1) = (f ⟨896, chainInput i j (x j)⟩).extractLsb' 0 128)
    (h127 : e = 127 → x 127 = σ) :
    x 127 = chainValue f i e (127 - e) σ := by
  rcases Nat.lt_or_ge e 127 with hlt | hge
  · have key : ∀ n, e + n ≤ 126 → x (e + n + 1) = chainValue f i e (n + 1) σ := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [chainValue_succ', chainValue_zero', Nat.add_zero]
        exact hleaf hlt
      | succ n ih =>
        intro hn
        rw [chainValue_succ', ← ih (by omega), show e + (n + 1) = e + n + 1 by omega]
        exact hbody (e + n + 1) (by omega) (by omega)
    have h := key (126 - e) (by omega)
    rwa [show e + (126 - e) + 1 = 127 by omega, show 126 - e + 1 = 127 - e by omega] at h
  · obtain rfl : e = 127 := by omega
    rw [h127 rfl, Nat.sub_self, chainValue_zero']

/-! ### `BLAKE2S` operands as scheme queries -/

theorem zero_append_zero_128 : (0 : BitVec 128) ++ (0 : BitVec 128) = (0 : BitVec 256) := by
  exact BitVec.zero_append_zero

set_option exponentiation.threshold 512 in
theorem zero_append_three (y : BitVec 128) :
    (0 : BitVec 128) ++ (0 : BitVec 128) ++ (0 : BitVec 128) ++ y = y.setWidth 512 := by
  apply BitVec.eq_of_toNat_eq
  have h0 : (0 : BitVec 128).toNat = 0 := by
    rfl
  have hy := BitVec.toNat_lt_twoPow_of_le (by decide : 128 ≤ 512) (x := y)
  rw [BitVec.toNat_setWidth]
  simp only [BitVec.toNat_append, h0, Nat.zero_shiftLeft, Nat.zero_or]
  exact (Nat.mod_eq_of_lt hy).symm

/-- A chain step's `BLAKE2S`: message `(x, I_i, J_j, 0)`, zero chaining pair, metadata `1`,
queries exactly `chainInput i j x`. -/
theorem blake2sQuery_chain_gen (i j : ℕ) (m : Fin 4 → E) (cv0 cv1 md : E)
    (hm1 : cellBits (m 1) = BitVec.ofNat 128 i) (hm2 : cellBits (m 2) = BitVec.ofNat 128 j)
    (hm3 : cellBits (m 3) = 0) (hc0 : cellBits cv0 = 0) (hc1 : cellBits cv1 = 0)
    (hmd : cellBits md = 1) :
    blake2sQuery m cv0 cv1 md = chainInput i j (cellBits (m 0)) := by
  have hcv : cellBits cv1 ++ cellBits cv0 = (0 : BitVec 256) := by
    rw [hc0, hc1, zero_append_zero_128]
  have hblk : cellBits (m 3) ++ cellBits (m 2) ++ cellBits (m 1) ++ cellBits (m 0) =
      (0 : BitVec 128) ++ BitVec.ofNat 128 j ++ BitVec.ofNat 128 i ++ cellBits (m 0) := by
    rw [hm1, hm2, hm3]
  have key : hashInput (cellBits cv1 ++ cellBits cv0)
      (cellBits (m 3) ++ cellBits (m 2) ++ cellBits (m 1) ++ cellBits (m 0)) (cellBits md) =
      hashInput (0 : BitVec 256)
        ((0 : BitVec 128) ++ BitVec.ofNat 128 j ++ BitVec.ofNat 128 i ++ cellBits (m 0))
        (1 : BitVec 128) := by
    rw [hcv, hblk, hmd]
  exact key

/-- `blake2sQuery_chain_gen` for the literal operand vector the machine reads. -/
theorem blake2sQuery_chain (i j : ℕ) (x tagI tagJ z cv0 cv1 md : E)
    (hI : cellBits tagI = BitVec.ofNat 128 i) (hJ : cellBits tagJ = BitVec.ofNat 128 j)
    (hz : cellBits z = 0) (hc0 : cellBits cv0 = 0) (hc1 : cellBits cv1 = 0)
    (hmd : cellBits md = 1) :
    blake2sQuery ![x, tagI, tagJ, z] cv0 cv1 md = chainInput i j (cellBits x) :=
  blake2sQuery_chain_gen i j ![x, tagI, tagJ, z] cv0 cv1 md hI hJ hz hc0 hc1 hmd

/-- An absorb step's `BLAKE2S`: message `(x, 0, 0, 0)`, chaining pair `(cv0, cv1)`, metadata
`2 + r`, queries exactly the input of `absorb r (cv1 ++ cv0) x`. -/
theorem blake2sQuery_absorb_gen (r : ℕ) (m : Fin 4 → E) (cv0 cv1 md : E)
    (hm1 : cellBits (m 1) = 0) (hm2 : cellBits (m 2) = 0) (hm3 : cellBits (m 3) = 0)
    (hmd : cellBits md = BitVec.ofNat 128 (2 + r)) :
    blake2sQuery m cv0 cv1 md =
      hashInput (cellBits cv1 ++ cellBits cv0) ((cellBits (m 0)).setWidth 512)
        (BitVec.ofNat 128 (2 + r)) := by
  have hblk : cellBits (m 3) ++ cellBits (m 2) ++ cellBits (m 1) ++ cellBits (m 0) =
      (cellBits (m 0)).setWidth 512 := by
    rw [hm1, hm2, hm3, zero_append_three]
  have key : hashInput (cellBits cv1 ++ cellBits cv0)
      (cellBits (m 3) ++ cellBits (m 2) ++ cellBits (m 1) ++ cellBits (m 0)) (cellBits md) =
      hashInput (cellBits cv1 ++ cellBits cv0) ((cellBits (m 0)).setWidth 512)
        (BitVec.ofNat 128 (2 + r)) := by
    rw [hblk, hmd]
  exact key

/-- `blake2sQuery_absorb_gen` for the literal operand vector the machine reads. -/
theorem blake2sQuery_absorb (r : ℕ) (x z1 z2 z3 cv0 cv1 md : E)
    (h1 : cellBits z1 = 0) (h2 : cellBits z2 = 0) (h3 : cellBits z3 = 0)
    (hmd : cellBits md = BitVec.ofNat 128 (2 + r)) :
    blake2sQuery ![x, z1, z2, z3] cv0 cv1 md =
      hashInput (cellBits cv1 ++ cellBits cv0) ((cellBits x).setWidth 512)
        (BitVec.ofNat 128 (2 + r)) :=
  blake2sQuery_absorb_gen r ![x, z1, z2, z3] cv0 cv1 md h1 h2 h3 hmd

/-! ## 3. The root -/

theorem hi_append_lo (a : BitVec 256) : a.extractLsb' 128 128 ++ a.extractLsb' 0 128 = a := by
  have h := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := a) (start₁ := 0)
    (len₁ := 128) (start₂ := 128) (len₂ := 128) rfl
  exact h.trans BitVec.extractLsb'_eq_self

/-- The committed output pair of a `BLAKE2S` is the whole answer, high cell first. -/
theorem out_pair (lo hi : E) (ans : BitVec 256) (hlo : cellBits lo = ans.extractLsb' 0 128)
    (hhi : cellBits hi = ans.extractLsb' 128 128) : cellBits hi ++ cellBits lo = ans := by
  rw [hlo, hhi]
  exact hi_append_lo ans

/-- `rootValueFold` over `List.ofFn` is any state sequence satisfying the absorb recursion. -/
theorem rootValueFold_ofFn (f : HashTable) (n : ℕ) : ∀ (w : ℕ → Word) (c : ℕ → BitVec 256),
    (∀ k < n, c (k + 1) = f ⟨896, hashInput (c k) ((w k).setWidth 512)
      (BitVec.ofNat 128 (2 + (n - 1 - k)))⟩) →
    rootValueFold f (List.ofFn fun i : Fin n => w i) (c 0) = c n := by
  induction n with
  | zero =>
    intro w c _
    rfl
  | succ n ih =>
    intro w c hc
    have e0 : f ⟨896, hashInput (c 0) ((w 0).setWidth 512) (BitVec.ofNat 128 (2 + n))⟩ = c 1 := by
      have h := hc 0 (Nat.succ_pos n)
      rw [show n + 1 - 1 - 0 = n by omega, Nat.zero_add] at h
      exact h.symm
    have hrest := ih (fun k => w (k + 1)) (fun k => c (k + 1)) (fun k hk => by
      have h := hc (k + 1) (by omega)
      rw [show n + 1 - 1 - (k + 1) = n - 1 - k by omega] at h
      exact h)
    -- `hrest : rootValueFold f (List.ofFn fun i => w (↑i + 1)) (c 1) = c (n + 1)`
    simp only [Nat.zero_add] at hrest
    -- The list length sits inside the query index, and the answer's type depends on the query,
    -- so it cannot be rewritten under `f`. Generalise it instead (`subst`, not `rw`).
    have e0' : ∀ L : ℕ, L = n →
        (f ⟨896, hashInput (c 0) ((w 0).setWidth 512) (BitVec.ofNat 128 (2 + L))⟩ :
          BitVec 256) = c 1 := by
      intro L hL
      subst hL
      exact e0
    have key : (f ⟨896, hashInput (c 0) ((w 0).setWidth 512)
        (BitVec.ofNat 128 (2 + (List.ofFn fun i : Fin n => w ((i : ℕ) + 1)).length))⟩ :
          BitVec 256) = c 1 :=
      e0' _ List.length_ofFn
    rw [List.ofFn_succ]
    -- `Fin.val_zero` / `Fin.val_succ` are `rfl` lemmas, so `simp` applies them under `f`.
    simp only [rootValueFold, Fin.val_zero, Fin.val_succ]
    exact (congrArg (rootValueFold f (List.ofFn fun i : Fin n => w ((i : ℕ) + 1))) key).trans
      hrest

/-- Soundness of the root. States `(lo k, hi k)` start at zero; absorb `k` hashes endpoint
`e k` with metadata `2 + (42 - k)`; then `lo 43` holds `rootValue f xs`. -/
theorem root_sound (f : HashTable) (xs : Fin 43 → Word) (e lo hi : ℕ → E)
    (hxs : ∀ i : Fin 43, xs i = cellBits (e i))
    (hlo0 : cellBits (lo 0) = 0) (hhi0 : cellBits (hi 0) = 0)
    (hlo : ∀ k < 43, cellBits (lo (k + 1)) =
      (f ⟨896, hashInput (cellBits (hi k) ++ cellBits (lo k)) ((cellBits (e k)).setWidth 512)
        (BitVec.ofNat 128 (2 + (42 - k)))⟩).extractLsb' 0 128)
    (hhi : ∀ k < 43, cellBits (hi (k + 1)) =
      (f ⟨896, hashInput (cellBits (hi k) ++ cellBits (lo k)) ((cellBits (e k)).setWidth 512)
        (BitVec.ofNat 128 (2 + (42 - k)))⟩).extractLsb' 128 128) :
    cellBits (lo 43) = rootValue f xs := by
  have h0 : cellBits (hi 0) ++ cellBits (lo 0) = (0 : BitVec 256) := by
    rw [hhi0, hlo0, zero_append_zero_128]
  have hfold := rootValueFold_ofFn f 43 (fun k => cellBits (e k))
    (fun k => cellBits (hi k) ++ cellBits (lo k))
    (fun k hk => out_pair (lo (k + 1)) (hi (k + 1)) _ (hlo k hk) (hhi k hk))
  simp only [h0] at hfold
  have hxs' : xs = fun i : Fin 43 => cellBits (e i) := funext hxs
  have key : (rootValueFold f (List.ofFn xs) 0).extractLsb' 0 128 = cellBits (lo 43) := by
    rw [hxs', hfold, BitVec.extractLsb'_append_eq_right]
  exact key.symm

/-! ## 4. The tie and the loader -/

/-- `XOR` with a block above the low `n` bits is addition. -/
theorem xor_shiftLeft_eq_add {N a n : ℕ} (hN : N < 2 ^ n) : N ^^^ (a <<< n) = N + 2 ^ n * a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.add_comm N, Nat.testBit_two_pow_mul_add a hN j]
  by_cases hj : j < n
  · rw [if_pos hj, decide_eq_false (show ¬ (j ≥ n) by omega), Bool.false_and, Bool.xor_false]
  · have hNj : N.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num)
        (by omega)))
    rw [if_neg hj, decide_eq_true (show j ≥ n by omega), Bool.true_and, hNj, Bool.false_xor]

/-- `cellOfBits` turns `XOR` into field addition. -/
theorem cellOfBits_add (a b : BitVec 128) :
    cellOfBits a + cellOfBits b = cellOfBits (a ^^^ b) := by
  unfold cellOfBits
  rw [add_limbs, BitVec.extractLsb'_xor, BitVec.extractLsb'_xor]
  rfl

theorem cellOfBits_zero : cellOfBits 0 = 0 := by
  have h := cellOfBits_add 0 0
  rw [add_self_E, BitVec.xor_self] at h
  exact h.symm

/-! ### Mixed-radix packing

Fields `d q` of widths `w q`, little-endian: field `q` sits at bit offset `lsbOff w q`. -/

/-- The bit offset of little-endian field `n`: the total width of the fields below it. -/
def lsbOff (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => lsbOff w n + w n

/-- The fields `d 0 … d (n-1)` packed at their offsets. -/
def packLE (w d : ℕ → ℕ) (n : ℕ) : ℕ := ∑ q ∈ Finset.range n, 2 ^ lsbOff w q * d q

theorem lsbOff_mono (w : ℕ → ℕ) {p n : ℕ} (h : p ≤ n) : lsbOff w p ≤ lsbOff w n := by
  induction n with
  | zero =>
    obtain rfl : p = 0 := by omega
    exact le_rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact le_rfl
    · exact (ih (by omega)).trans (Nat.le_add_right _ _)

/-- Offsets of the fields from `a` on, counted from `a`. -/
theorem lsbOff_shift (w w' : ℕ → ℕ) (a : ℕ) (hw : ∀ q, w' q = w (a + q)) :
    ∀ n, lsbOff w a + lsbOff w' n = lsbOff w (a + n)
  | 0 => rfl
  | n + 1 => by
    have ih := lsbOff_shift w w' a hw n
    show lsbOff w a + (lsbOff w' n + w' n) = lsbOff w (a + n) + w (a + n)
    rw [hw n]
    omega

theorem packLE_lt (w d : ℕ → ℕ) : ∀ n, (∀ q < n, d q < 2 ^ w q) → packLE w d n < 2 ^ lsbOff w n
  | 0 => by
    intro _
    simp [packLE, lsbOff]
  | n + 1 => by
    intro hd
    have ih := packLE_lt w d n (fun q hq => hd q (by omega))
    have hn : d n + 1 ≤ 2 ^ w n := hd n (by omega)
    have h2 : 2 ^ lsbOff w n * (d n + 1) ≤ 2 ^ lsbOff w n * 2 ^ w n := Nat.mul_le_mul_left _ hn
    unfold packLE at ih ⊢
    rw [Finset.sum_range_succ, lsbOff, pow_add]
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega

theorem packLE_div (w d : ℕ → ℕ) (p : ℕ) : ∀ n, (∀ q < n, d q < 2 ^ w q) → p < n →
    packLE w d n / 2 ^ lsbOff w p % 2 ^ w p = d p
  | 0 => by
    intro _ h
    omega
  | n + 1 => by
    intro hd hp
    have hpos : 0 < 2 ^ lsbOff w p := by positivity
    unfold packLE
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge p n with hlt | hge
    · have hle : lsbOff w p + w p ≤ lsbOff w n := lsbOff_mono w (show p + 1 ≤ n by omega)
      have e : 2 ^ lsbOff w n * d n = 2 ^ lsbOff w p *
          (2 ^ w p * (2 ^ (lsbOff w n - (lsbOff w p + w p)) * d n)) := by
        rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add,
          show lsbOff w p + w p + (lsbOff w n - (lsbOff w p + w p)) = lsbOff w n by omega]
      rw [e, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
      exact packLE_div w d p n (fun q hq => hd q (by omega)) hlt
    · obtain rfl : p = n := by omega
      have hlt := packLE_lt w d p (fun q hq => hd q (by omega))
      unfold packLE at hlt
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_eq_of_lt (hd p (by omega))]

theorem packLE_digits (w : ℕ → ℕ) (N : ℕ) : ∀ n,
    packLE w (fun q => N / 2 ^ lsbOff w q % 2 ^ w q) n = N % 2 ^ lsbOff w n
  | 0 => by simp [packLE, lsbOff, Nat.mod_one]
  | n + 1 => by
    have ih := packLE_digits w N n
    unfold packLE at ih ⊢
    rw [Finset.sum_range_succ, ih, lsbOff, pow_add, Nat.mod_mul]

/-- Fields below the bound are the packed number's fields exactly. -/
theorem packLE_eq_iff (w d : ℕ → ℕ) (n c : ℕ) (hd : ∀ q < n, d q < 2 ^ w q)
    (hc : c < 2 ^ lsbOff w n) :
    packLE w d n = c ↔ ∀ q < n, d q = c / 2 ^ lsbOff w q % 2 ^ w q := by
  constructor
  · rintro rfl q hq
    exact (packLE_div w d q n hd hq).symm
  · intro h
    have e : packLE w d n = packLE w (fun q => c / 2 ^ lsbOff w q % 2 ^ w q) n :=
      Finset.sum_congr rfl fun q hq => by rw [h q (Finset.mem_range.mp hq)]
    rw [e, packLE_digits, Nat.mod_eq_of_lt hc]

/-- The field sum of the words `d q <<< lsbOff w q` is the word of the packed number. -/
theorem packLE_cells (w d : ℕ → ℕ) : ∀ n, (∀ q < n, d q < 2 ^ w q) →
    ∑ q ∈ Finset.range n, cellOfBits (BitVec.ofNat 128 (d q <<< lsbOff w q)) =
      cellOfBits (BitVec.ofNat 128 (packLE w d n))
  | 0 => by
    intro _
    rw [Finset.sum_range_zero]
    exact cellOfBits_zero.symm
  | n + 1 => by
    intro hd
    have ih := packLE_cells w d n (fun q hq => hd q (by omega))
    have hlt := packLE_lt w d n (fun q hq => hd q (by omega))
    rw [Finset.sum_range_succ, ih, cellOfBits_add, ← BitVec.ofNat_xor, xor_shiftLeft_eq_add hlt]
    unfold packLE
    rw [Finset.sum_range_succ]

/-! ### The message layout -/

/-- Cell 1's fields `40, 39, …, 20`, little-endian (and on through field 0). -/
def loWidth (q : ℕ) : ℕ := fieldWidth (40 - q)

/-- Cell 2's fields `19, 18, …, 0`, little-endian. -/
def hiWidth (q : ℕ) : ℕ := fieldWidth (19 - q)

theorem lsbOff_loWidth : ∀ q, q ≤ 40 → lsbOff loWidth q = fieldOff (40 - q)
  | 0 => fun _ => rfl
  | q + 1 => fun h => by
    have hs := fieldOff_succ (k := 40 - (q + 1)) (by omega)
    rw [show 40 - (q + 1) + 1 = 40 - q by omega] at hs
    show lsbOff loWidth q + fieldWidth (40 - q) = _
    rw [lsbOff_loWidth q (by omega), hs]

theorem lsbOff_loWidth_21 : lsbOff loWidth 21 = 128 := by
  rw [lsbOff_loWidth 21 (by norm_num)]
  rfl

theorem lsbOff_hiWidth (q : ℕ) : 128 + lsbOff hiWidth q = lsbOff loWidth (21 + q) := by
  rw [← lsbOff_loWidth_21]
  exact lsbOff_shift loWidth hiWidth 21 (fun q' => by
    unfold hiWidth loWidth
    congr 1
    omega) q

theorem lsbOff_hiWidth_of_le (q : ℕ) (hq : q ≤ 19) : 128 + lsbOff hiWidth q = fieldOff (19 - q) := by
  rw [lsbOff_hiWidth q, lsbOff_loWidth _ (by omega), show 40 - (21 + q) = 19 - q by omega]

theorem lsbOff_hiWidth_20 : lsbOff hiWidth 20 = 128 := by
  have h := lsbOff_hiWidth 20
  have h2 : lsbOff loWidth 41 = 256 := by
    show lsbOff loWidth 40 + fieldWidth (40 - 40) = 256
    rw [lsbOff_loWidth 40 le_rfl]
    rfl
  rw [h2] at h
  omega

/-- The in-cell bit offset of field `k`: fields `0 … 19` in cell 2, `20 … 40` in cell 1. -/
def fieldShift (k : ℕ) : ℕ := if k < 20 then fieldOff k - 128 else fieldOff k

/-- The tie word of leaf index `d k`: the field at its in-cell offset. -/
def tieWord (d : ℕ → ℕ) (k : ℕ) : E := cellOfBits (BitVec.ofNat 128 (d k <<< fieldShift k))

/-- The last field of each cell has in-cell offset 0, so its word is `posV (d k)`. -/
theorem tieWord_last (d : ℕ → ℕ) {k : ℕ} (hk : k = 19 ∨ k = 40) :
    tieWord d k = cellOfBits (BitVec.ofNat 128 (d k)) := by
  have h : fieldShift k = 0 := by rcases hk with rfl | rfl <;> rfl
  unfold tieWord
  rw [h, Nat.shiftLeft_zero]

/-- The field sum the tie ops of chains `0 … 19` assert equal to message cell 2. -/
noncomputable def tieHi (d : ℕ → ℕ) : E := ∑ k ∈ Finset.range 20, tieWord d k

/-- The field sum the tie ops of chains `20 … 40` assert equal to message cell 1. -/
noncomputable def tieLo (d : ℕ → ℕ) : E := ∑ k ∈ Finset.Ico 20 41, tieWord d k

theorem tieHi_eq (d : ℕ → ℕ) (hd : ∀ q < 20, d (19 - q) < 2 ^ hiWidth q) :
    tieHi d = cellOfBits (BitVec.ofNat 128 (packLE hiWidth (fun q => d (19 - q)) 20)) := by
  rw [← packLE_cells hiWidth (fun q => d (19 - q)) 20 hd]
  unfold tieHi
  refine (Finset.sum_range_reflect _ 20).symm.trans (Finset.sum_congr rfl fun q hq => ?_)
  have hq' := Finset.mem_range.mp hq
  have hs : fieldShift (19 - q) = lsbOff hiWidth q := by
    unfold fieldShift
    rw [if_pos (by omega)]
    have := lsbOff_hiWidth_of_le q (by omega)
    omega
  unfold tieWord
  rw [show 20 - 1 - q = 19 - q by omega, hs]

theorem tieLo_eq (d : ℕ → ℕ) (hd : ∀ q < 21, d (40 - q) < 2 ^ loWidth q) :
    tieLo d = cellOfBits (BitVec.ofNat 128 (packLE loWidth (fun q => d (40 - q)) 21)) := by
  rw [← packLE_cells loWidth (fun q => d (40 - q)) 21 hd]
  unfold tieLo
  rw [Finset.sum_Ico_eq_sum_range, show 41 - 20 = 21 from rfl]
  refine (Finset.sum_range_reflect _ 21).symm.trans (Finset.sum_congr rfl fun q hq => ?_)
  have hq' := Finset.mem_range.mp hq
  have hs : fieldShift (40 - q) = lsbOff loWidth q := by
    unfold fieldShift
    rw [if_neg (by omega), lsbOff_loWidth q (by omega)]
  unfold tieWord
  rw [show 20 + (21 - 1 - q) = 40 - q by omega, hs]

theorem cellOfBits_ofNat_inj {x : ℕ} {b : BitVec 128} (hx : x < 2 ^ 128) :
    cellOfBits (BitVec.ofNat 128 x) = cellOfBits b ↔ x = b.toNat := by
  constructor
  · intro h
    have hb := congrArg cellBits h
    rw [cellBits_cellOfBits, cellBits_cellOfBits] at hb
    rw [← hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  · intro h
    rw [h]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt b.isLt

theorem extract_hi_toNat (m : Message) : (m.extractLsb' 128 128).toNat = m.toNat / 2 ^ 128 := by
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by omega)

theorem extract_lo_toNat (m : Message) : (m.extractLsb' 0 128).toNat = m.toNat % 2 ^ 128 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- A cell-2 field read from the high cell's number. -/
theorem hi_field (N : ℕ) {q : ℕ} (hq : q < 20) :
    N / 2 ^ 128 / 2 ^ lsbOff hiWidth q % 2 ^ hiWidth q =
      N / 2 ^ fieldOff (19 - q) % 2 ^ fieldWidth (19 - q) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, lsbOff_hiWidth_of_le q (by omega)]
  rfl

/-- A cell-1 field read from the low cell's number. -/
theorem lo_field (N : ℕ) {q : ℕ} (hq : q < 21) :
    N % 2 ^ 128 / 2 ^ lsbOff loWidth q % 2 ^ loWidth q =
      N / 2 ^ fieldOff (40 - q) % 2 ^ fieldWidth (40 - q) := by
  have hle : lsbOff loWidth q + loWidth q ≤ 128 := by
    rw [← lsbOff_loWidth_21]
    exact lsbOff_mono loWidth (show q + 1 ≤ 21 by omega)
  have hdvd : 2 ^ (lsbOff loWidth q + loWidth q) ∣ 2 ^ 128 := pow_dvd_pow 2 hle
  rw [← Nat.mod_mul_right_div_self, ← pow_add, Nat.mod_mod_of_dvd _ hdvd, pow_add,
    Nat.mod_mul_right_div_self, lsbOff_loWidth q (by omega)]
  rfl

/-- **The tie.** For leaf indices `d k < 2 ^ fieldWidth k` (`k < 41`), the tie sums are the two
message cells exactly when each offset leaf `digitOff k + d k` is the message's digit `k`. -/
theorem tie_iff (m : Message) (d : ℕ → ℕ) (hd : ∀ k < 41, d k < 2 ^ fieldWidth k) :
    (tieHi d = cellOfBits (m.extractLsb' 128 128) ∧ tieLo d = cellOfBits (m.extractLsb' 0 128)) ↔
      ∀ k (hk : k < 41), digitOff k + d k = digit m ⟨k, by omega⟩ := by
  have hdh : ∀ q < 20, d (19 - q) < 2 ^ hiWidth q := fun q hq => hd _ (by omega)
  have hdl : ∀ q < 21, d (40 - q) < 2 ^ loWidth q := fun q hq => hd _ (by omega)
  have hm : m.toNat < 2 ^ 256 := m.isLt
  have hHi : m.toNat / 2 ^ 128 < 2 ^ lsbOff hiWidth 20 := by
    rw [lsbOff_hiWidth_20]
    omega
  have hLo : m.toNat % 2 ^ 128 < 2 ^ lsbOff loWidth 21 := by
    rw [lsbOff_loWidth_21]
    omega
  have hPh : packLE hiWidth (fun q => d (19 - q)) 20 < 2 ^ 128 :=
    lt_of_lt_of_eq (packLE_lt _ _ 20 hdh) (by rw [lsbOff_hiWidth_20])
  have hPl : packLE loWidth (fun q => d (40 - q)) 21 < 2 ^ 128 :=
    lt_of_lt_of_eq (packLE_lt _ _ 21 hdl) (by rw [lsbOff_loWidth_21])
  have hfield : ∀ k (hk : k < 41), digit m ⟨k, by omega⟩ =
      digitOff k + m.toNat / 2 ^ fieldOff k % 2 ^ fieldWidth k :=
    fun k hk => digit_of_lt m ⟨k, by omega⟩ hk
  rw [tieHi_eq d hdh, tieLo_eq d hdl, cellOfBits_ofNat_inj hPh, cellOfBits_ofNat_inj hPl,
    extract_hi_toNat, extract_lo_toNat, packLE_eq_iff _ _ 20 _ hdh hHi,
    packLE_eq_iff _ _ 21 _ hdl hLo]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    rw [hfield k hk]
    by_cases h : k < 20
    · have e := h1 (19 - k) (by omega)
      rw [hi_field _ (by omega), show 19 - (19 - k) = k by omega] at e
      rw [e]
    · have e := h2 (40 - k) (by omega)
      rw [lo_field _ (by omega), show 40 - (40 - k) = k by omega] at e
      rw [e]
  · intro h
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · have e := h (19 - q) (by omega)
      rw [hfield _ (by omega)] at e
      rw [hi_field _ hq]
      omega
    · have e := h (40 - q) (by omega)
      rw [hfield _ (by omega)] at e
      rw [lo_field _ hq]
      omega

/-- The tie accumulator after chain `k ≤ 39`: the partial sum of `tieHi` for `k < 20`, and of
`tieLo` from chain 20 on. -/
noncomputable def tieAcc (d : ℕ → ℕ) (k : ℕ) : E :=
  if k < 20 then ∑ i ∈ Finset.range (k + 1), tieWord d i
  else ∑ i ∈ Finset.Ico 20 (k + 1), tieWord d i

theorem tieAcc_zero (d : ℕ → ℕ) : tieAcc d 0 = tieWord d 0 := by
  unfold tieAcc
  rw [if_pos (by norm_num), Finset.sum_range_one]

theorem tieAcc_20 (d : ℕ → ℕ) : tieAcc d 20 = tieWord d 20 := by
  unfold tieAcc
  rw [if_neg (by norm_num), Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self,
    Finset.sum_empty, zero_add]

/-- Every middle tie op adds its word to the accumulator. -/
theorem tieAcc_succ (d : ℕ → ℕ) {k : ℕ} (h1 : 1 ≤ k) (h20 : k ≠ 20) :
    tieAcc d k = tieAcc d (k - 1) + tieWord d k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold tieAcc
  rw [Nat.add_sub_cancel]
  by_cases h : j + 1 < 20
  · rw [if_pos h, if_pos (by omega), Finset.sum_range_succ _ (j + 1)]
  · rw [if_neg h, if_neg (by omega), Finset.sum_Ico_succ_top (by omega)]

theorem tieHi_acc (d : ℕ → ℕ) : tieHi d = tieAcc d 18 + tieWord d 19 := by
  unfold tieAcc tieHi
  rw [if_pos (by norm_num), ← Finset.sum_range_succ]

theorem tieLo_acc (d : ℕ → ℕ) : tieLo d = tieAcc d 39 + tieWord d 40 := by
  unfold tieAcc tieLo
  rw [if_neg (by norm_num), ← Finset.sum_Ico_succ_top (by norm_num)]

/-- Accumulator cells obeying the tie ops of chains `0 … 40` close the message cells `c2`, `c1`
on the tie sums. -/
theorem tie_chain (d : ℕ → ℕ) (acc : ℕ → E) (c1 c2 : E)
    (h0 : acc 0 = tieWord d 0)
    (hmid : ∀ k, 1 ≤ k → k ≤ 39 → k ≠ 19 → k ≠ 20 → acc k = acc (k - 1) + tieWord d k)
    (h19 : c2 = acc 18 + tieWord d 19)
    (h20 : acc 20 = tieWord d 20)
    (h40 : c1 = acc 39 + tieWord d 40) :
    c2 = tieHi d ∧ c1 = tieLo d := by
  have hL : ∀ k, k ≤ 18 → acc k = tieAcc d k := by
    intro k
    induction k with
    | zero => intro _; rw [h0, tieAcc_zero]
    | succ k ih =>
      intro hk
      rw [hmid (k + 1) (by omega) (by omega) (by omega) (by omega),
        tieAcc_succ d (by omega) (by omega), Nat.add_sub_cancel, ih (by omega)]
  have hH : ∀ n, 20 + n ≤ 39 → acc (20 + n) = tieAcc d (20 + n) := by
    intro n
    induction n with
    | zero => intro _; rw [Nat.add_zero, h20, tieAcc_20]
    | succ n ih =>
      intro hn
      rw [hmid (20 + (n + 1)) (by omega) hn (by omega) (by omega),
        tieAcc_succ d (by omega) (by omega), show 20 + (n + 1) - 1 = 20 + n by omega,
        ih (by omega)]
  refine ⟨?_, ?_⟩
  · rw [h19, hL 18 le_rfl, tieHi_acc]
  · rw [h40, show (39 : ℕ) = 20 + 19 from rfl, hH 19 le_rfl, tieLo_acc]

/-! ### The loader -/

theorem take_drop_toBits {n : ℕ} (x : BitVec n) (s w : ℕ) (h : s + w ≤ n) :
    ((toBits x).drop s).take w = toBits (x.extractLsb' s w) := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, length_bits, length_bits]
    omega
  · intro i h₁ h₂
    have hiw : i < w := by
      rw [length_bits] at h₂
      exact h₂
    simp only [List.getElem_take, List.getElem_drop, toBits, List.getElem_ofFn,
      BitVec.getLsbD_extractLsb', decide_eq_true hiw, Bool.true_and]

/-- The loader's cell 1 holds message bits `0 … 127`. -/
theorem inputWord_one (pk : PublicKey) (m : Message) (σ : List Bool) :
    inputWord pk m σ 1 = cellOfBits (m.extractLsb' 0 128) := by
  have hpk : (toBits pk).length = 128 := length_bits pk
  have hm : (toBits m).length = 256 := length_bits m
  have hm1 : 128 ≤ (toBits m).length := by
    rw [hm]
    omega
  have hslice : ((toBits m).drop 0).take 128 = toBits (m.extractLsb' 0 128) :=
    take_drop_toBits m 0 128 (by show 0 + 128 ≤ 256; omega)
  rw [List.drop_zero] at hslice
  have h : ((statementBits pk m σ).drop (1 * 128)).take 128 = toBits (m.extractLsb' 0 128) := by
    unfold statementBits
    rw [Nat.one_mul]
    simp only [List.append_assoc]
    rw [List.drop_left' hpk, List.take_append_of_le_length hm1]
    exact hslice
  unfold inputWord
  rw [h, ofBits_bits]

/-- The loader's cell 2 holds message bits `128 … 255`. -/
theorem inputWord_two (pk : PublicKey) (m : Message) (σ : List Bool) :
    inputWord pk m σ 2 = cellOfBits (m.extractLsb' 128 128) := by
  have hpk : (toBits pk).length = 128 := length_bits pk
  have hm : (toBits m).length = 256 := length_bits m
  have hm1 : 128 ≤ (toBits m).length := by
    rw [hm]
    omega
  have hm2 : 128 ≤ ((toBits m).drop 128).length := by
    rw [List.length_drop, hm]
  have hslice : ((toBits m).drop 128).take 128 = toBits (m.extractLsb' 128 128) :=
    take_drop_toBits m 128 128 (by show 128 + 128 ≤ 256; omega)
  have h : ((statementBits pk m σ).drop (2 * 128)).take 128 =
      toBits (m.extractLsb' 128 128) := by
    unfold statementBits
    rw [show 2 * 128 = (toBits pk).length + 128 by omega]
    simp only [List.append_assoc]
    rw [List.drop_length_add_append, List.drop_append_of_le_length hm1,
      List.take_append_of_le_length hm2]
    exact hslice
  unfold inputWord
  rw [h, ofBits_bits]

theorem cellBits_zero_E : cellBits (0 : E) = 0 := by
  rw [← cellOfBits_zero, cellBits_cellOfBits]

/-- The loader's cell 0 holds the public key. -/
theorem inputWord_pk (pk : PublicKey) (msg : Message) (σ : List Bool) :
    inputWord pk msg σ 0 = cellOfBits pk := by
  have h : ((statementBits pk msg σ).drop (0 * 128)).take 128 = toBits pk := by
    unfold statementBits
    rw [Nat.zero_mul, List.drop_zero, List.append_assoc, List.append_assoc]
    exact List.take_left' (length_bits pk)
  unfold inputWord
  rw [h]
  exact congrArg cellOfBits (ofBits_bits pk)

/-- The loader's cell 3 holds the capped signature length. -/
theorem inputWord_len (pk : PublicKey) (msg : Message) (σ : List Bool) :
    inputWord pk msg σ 3 =
      cellOfBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1))) := by
  have hpre : (toBits pk ++ toBits msg).length = 3 * 128 := by
    rw [List.length_append, length_bits, length_bits]
    all_goals rfl
  have h : ((statementBits pk msg σ).drop (3 * 128)).take 128 =
      toBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1))) := by
    unfold statementBits
    rw [List.append_assoc, List.drop_left' hpre]
    exact List.take_left' (length_bits _)
  unfold inputWord
  rw [h, ofBits_bits]

/-- For a signature of the admitted length, cell `4 + i` holds the `i`-th revealed word. -/
theorem inputWord_sigDecode (pk : PublicKey) (msg : Message) (σ : List Bool)
    (hlen : σ.length = 5504) (i : Fin 43) :
    inputWord pk msg σ (4 + i.val) = cellOfBits (decode σ i) := by
  have hpre : (toBits pk ++ toBits msg ++
      toBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1)))).length = 512 := by
    rw [List.length_append, List.length_append, length_bits, length_bits, length_bits]
    all_goals rfl
  have htake : σ.take maxSignatureBits = σ :=
    List.take_of_length_le (by rw [hlen]; unfold maxSignatureBits; omega)
  unfold inputWord statementBits
  rw [show (4 + i.val) * 128 = 512 + 128 * i.val by omega, ← List.drop_drop, List.drop_left' hpre,
    htake]
  rfl

/-- The length cell pins the admitted length: `5504 < 5505`, so the capped length is exact. -/
theorem length_of_inputWord_len (pk : PublicKey) (msg : Message) (σ : List Bool)
    (h : inputWord pk msg σ 3 = cellOfBits (BitVec.ofNat 128 5504)) : σ.length = 5504 := by
  rw [inputWord_len] at h
  have hb := congrArg cellBits h
  rw [cellBits_cellOfBits, cellBits_cellOfBits] at hb
  have hn := congrArg BitVec.toNat hb
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hn
  unfold maxSignatureBits at hn
  have h1 : min σ.length (5504 + 1) < 2 ^ 128 := by
    have : min σ.length (5504 + 1) ≤ 5505 := Nat.min_le_right _ _
    have h2 : (5505 : ℕ) < 2 ^ 128 := by norm_num
    omega
  have h3 : (5504 : ℕ) < 2 ^ 128 := by norm_num
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3] at hn
  omega

/-! ## 5. Digits and the checksum -/

/-- Message field `k` as a number below `2 ^ fieldWidth k`. -/
theorem field_lt (m : Message) (k : ℕ) :
    m.toNat / 2 ^ fieldOff k % 2 ^ fieldWidth k < 2 ^ fieldWidth k :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A message digit is its field plus the digit offset. -/
theorem digitOff_le_digit (m : Message) (k : ℕ) (hk : k < 41) :
    digitOff k ≤ digit m ⟨k, by omega⟩ := by
  rw [digit_of_lt m ⟨k, by omega⟩ hk]
  exact Nat.le_add_right _ _

theorem checksum_hi_le (m : Message) : Checksum.wotsChecksumValue 128 (messageDigits m) / 64 ≤ 50 := by
  have := wotsChecksumValue_messageDigits_le m
  omega

/-- The checksum plus the message digits is `41 · 127`. -/
theorem checksum_add_digits (m : Message) (D : ℕ → ℕ)
    (hd : ∀ k (hk : k < 41), D k = digit m ⟨k, by omega⟩) :
    Checksum.wotsChecksumValue 128 (messageDigits m) + ∑ k ∈ Finset.range 41, D k = 5207 := by
  have hC : Checksum.wotsChecksumValue 128 (messageDigits m) =
      ∑ k ∈ Finset.range 41, (127 - D k) := by
    rw [wotsChecksumValue_messageDigits m, ← Fin.sum_univ_eq_sum_range (fun k => 127 - D k) 41]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hd k.val k.isLt]
    rfl
  rw [hC, ← Finset.sum_add_distrib]
  have h : ∀ k ∈ Finset.range 41, 127 - D k + D k = 127 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have := digit_le m ⟨k, by omega⟩
    rw [hd k hk']
    omega
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The checksum identity recovers the two offset checksum digits: if the message chains carry
the message digits, `64 ≤ E 41`, `64 ≤ E 42 < 128` and
`Σ_{k<41} E k + 64 · (E 41 − 64) + E 42 = 5271`, then `E 41` and `E 42` are digits 41 and 42. -/
theorem checksum_digits (m : Message) (D : ℕ → ℕ)
    (hd : ∀ k (hk : k < 41), D k = digit m ⟨k, by omega⟩) (h41 : 64 ≤ D 41) (h42 : 64 ≤ D 42)
    (h42' : D 42 < 128)
    (hsum : ∑ k ∈ Finset.range 41, D k + 64 * (D 41 - 64) + D 42 = 5271) :
    D 41 = digit m 41 ∧ D 42 = digit m 42 := by
  have hC := checksum_add_digits m D hd
  rw [digit_hi, digit_lo]
  omega

/-- The honest direction: the true digits satisfy the checksum identity. -/
theorem checksum_honest_sum (m : Message) (D : ℕ → ℕ)
    (hd : ∀ k (hk : k < 41), D k = digit m ⟨k, by omega⟩) :
    ∑ k ∈ Finset.range 41, D k +
      64 * (Checksum.wotsChecksumValue 128 (messageDigits m) / 64) +
      (64 + Checksum.wotsChecksumValue 128 (messageDigits m) % 64) = 5271 := by
  have hC := checksum_add_digits m D hd
  omega

end OptimalOTS.LeanIsaBaseline.Machine
