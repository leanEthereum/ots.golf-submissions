import OptimalOTS.Dag
import Submissions.UpperRiscv.Count

/-!
# Accepted indices

An index is the 128-bit prefix of the hash of message and nonce. It is accepted when its 32
nibbles sum to `target = 160`; every nibble value is allowed. The accepted indices are counted
exactly by `comp 32 160`, and there are more than `2 ^ 115` of them, so the signing loop of the
paper scheme succeeds with the same probability as before.
-/

namespace OptimalOTS

open OptimalOTS.Dag


/-- The digit sum of every accepted index. -/
def target : ℕ := 160

/-- Nibble `k` of `i`. -/
def nibble (i k : ℕ) : ℕ := i / 16 ^ k % 16

theorem nibble_lt (i k : ℕ) : nibble i k < 16 := Nat.mod_lt _ (by norm_num)

theorem nibble_zero (i : ℕ) : nibble i 0 = i % 16 := by simp [nibble]

theorem nibble_succ (i k : ℕ) : nibble i (k + 1) = nibble (i / 16) k := by
  rw [nibble, nibble, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- The number whose `n` low nibbles are `c 0, …, c (n - 1)`. -/
def ofNibbles (c : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, c k * 16 ^ k

theorem ofNibbles_zero (c : ℕ → ℕ) : ofNibbles c 0 = 0 := by simp [ofNibbles]

theorem ofNibbles_succ (c : ℕ → ℕ) (n : ℕ) :
    ofNibbles c (n + 1) = c 0 + 16 * ofNibbles (fun k => c (k + 1)) n := by
  unfold ofNibbles
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  simp only [pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem nibble_ofNibbles (c : ℕ → ℕ) (hc : ∀ k, c k < 16) :
    ∀ n j, j < n → nibble (ofNibbles c n) j = c j := by
  intro n
  induction n generalizing c with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rw [ofNibbles_succ]
    cases j with
    | zero => rw [nibble_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc 0)]
    | succ j =>
      rw [nibble_succ, Nat.add_mul_div_left _ _ (by norm_num : 0 < 16), Nat.div_eq_of_lt (hc 0),
        zero_add]
      exact ih (fun k => c (k + 1)) (fun k => hc (k + 1)) j (by omega)

theorem ofNibbles_lt (c : ℕ → ℕ) (hc : ∀ k, c k < 16) : ∀ n, ofNibbles c n < 16 ^ n := by
  intro n
  induction n generalizing c with
  | zero => simp [ofNibbles]
  | succ n ih =>
    rw [ofNibbles_succ, pow_succ]
    have := ih (fun k => c (k + 1)) (fun k => hc (k + 1))
    have h0 := hc 0
    omega

theorem ofNibbles_nibble (i : ℕ) : ∀ n, i < 16 ^ n → ofNibbles (nibble i) n = i := by
  intro n
  induction n generalizing i with
  | zero => intro hi; rw [ofNibbles_zero]; omega
  | succ n ih =>
    intro hi
    rw [ofNibbles_succ, nibble_zero]
    have e : (fun k => nibble i (k + 1)) = nibble (i / 16) := funext fun k => nibble_succ i k
    rw [e, ih (i / 16) (by rw [pow_succ] at hi; omega)]
    omega

/-- An index is accepted when its 32 nibbles sum to `target`. -/
def Accepted (i : ℕ) : Prop := ∑ k ∈ Finset.range 32, nibble i k = target

instance : DecidablePred Accepted := fun i => by unfold Accepted; infer_instance

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- The accepted indices below `2 ^ idxBits`. -/
def validSet : Finset ℕ := (Finset.range (2 ^ idxBits)).filter Accepted

/-- A valid index. -/
abbrev Idx : Type := {i : ℕ // i ∈ validSet}

/-- The number of valid indices. -/
def numValid : ℕ := (validSet).card

theorem mem_validSet {i : ℕ} : i ∈ validSet ↔ i < 2 ^ idxBits ∧ Accepted i := by
  simp [validSet]

theorem mem_validSet_lt {i : ℕ} (h : i ∈ validSet) : i < 2 ^ idxBits :=
  (mem_validSet.mp h).1

theorem mem_validSet_accepted {i : ℕ} (h : i ∈ validSet) : Accepted i :=
  (mem_validSet.mp h).2

theorem Idx.isLt (i : Idx) : i.val < 2 ^ idxBits := mem_validSet_lt i.2

theorem numValid_le : numValid ≤ 2 ^ idxBits := by
  unfold numValid validSet
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])

/-! ## Counting the accepted indices -/

/-- The digit tuples counted by `comp 32 target`. -/
def tuples : Finset (Fin 32 → Fin 16) := Finset.univ.filter fun c => ∑ k, (c k).val = target

theorem tuples_card : tuples.card = Forest.comp 32 target := Forest.card_comp 32 target

/-- The digits of an index. -/
def digitsOf (i : ℕ) (k : Fin 32) : Fin 16 := ⟨nibble i k, nibble_lt i k⟩

/-- The digit function of a tuple, extended by zero. -/
def digitFun (c : Fin 32 → Fin 16) (k : ℕ) : ℕ := if h : k < 32 then (c ⟨k, h⟩).val else 0

theorem digitFun_lt (c : Fin 32 → Fin 16) (k : ℕ) : digitFun c k < 16 := by
  unfold digitFun
  split_ifs with h
  · exact (c ⟨k, h⟩).isLt
  · norm_num

/-- The index with the given digits. -/
def indexOf (c : Fin 32 → Fin 16) : ℕ := ofNibbles (digitFun c) 32

theorem nibble_indexOf (c : Fin 32 → Fin 16) (k : Fin 32) : nibble (indexOf c) k = (c k).val := by
  rw [indexOf, nibble_ofNibbles _ (digitFun_lt c) 32 k k.isLt, digitFun, dif_pos k.isLt]

theorem idxBits_eq : 2 ^ idxBits = 16 ^ 32 := by norm_num [idxBits]

attribute [local irreducible] validSet tuples

theorem card_validSet : (validSet).card = Forest.comp 32 target := by
  rw [← tuples_card]
  refine Finset.card_bij' (fun i _ => digitsOf i) (fun c _ => indexOf c) ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨_, sum⟩ := mem_validSet.mp hi
    simp only [tuples, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← sum, ← Fin.sum_univ_eq_sum_range]
    rfl
  · intro c hc
    simp only [tuples, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine mem_validSet.mpr ⟨?_, ?_⟩
    · rw [idxBits_eq]
      exact ofNibbles_lt _ (digitFun_lt c) 32
    · show ∑ k ∈ Finset.range 32, nibble (indexOf c) k = target
      rw [← hc, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun k _ => nibble_indexOf c k
  · intro i hi
    obtain ⟨lt, _⟩ := mem_validSet.mp hi
    show ofNibbles (digitFun (digitsOf i)) 32 = i
    have agree : ∀ k ∈ Finset.range 32, digitFun (digitsOf i) k * 16 ^ k = nibble i k * 16 ^ k := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [digitFun, dif_pos hk', digitsOf]
    rw [ofNibbles, Finset.sum_congr rfl agree]
    rw [idxBits_eq] at lt
    exact ofNibbles_nibble i 32 lt
  · intro c _
    funext k
    apply Fin.ext
    show nibble (indexOf c) k = (c k).val
    rw [nibble_indexOf]

theorem comp_32_target : Forest.comp 32 target = 44383521204130784290044027201113527 := by
  show Forest.comp 32 160 = _
  rw [← Forest.compTable_getD 160 32 160 le_rfl]
  decide +kernel

theorem numValid_ge : 2 ^ 115 ≤ numValid := by
  rw [numValid, card_validSet, comp_32_target]
  norm_num

end OptimalOTS
