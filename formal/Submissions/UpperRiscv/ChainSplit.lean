import Submissions.UpperRiscv.Reader
import Submissions.UpperRiscv.MixedProgram

/-!
# Splitting a chain at its first hash

An expanding chain hashes its disclosed value once before its pair's cap is tested. Its node list
splits into the reader's prefix up to and including that first hash (`readNodes`) and the rest
(`suffixNodes`); a chain that does not expand runs all of its nodes after the test.
-/

open OracleComp
noncomputable section
open scoped Classical

namespace OptimalOTS.RiscvUpperForest.ForestVerifier

open OptimalOTS.Dag
open Forest Forest.Name

variable (index : RawIdx) (v : ℕ)

/-- The three nodes of level `t` of chain `k`, none beyond the last level. -/
def tripleN (k : Fin 33) (t : ℕ) : List Name :=
  if h : t < 32 then [ci k ⟨t, h⟩, ch k ⟨t, h⟩, cv k ⟨t, h⟩] else []

theorem chainNodes_eq (k : Fin 33) :
    chainNodes k = src k :: ((List.range 32).flatMap (tripleN k) ++ [tp k]) := by
  simp only [chainNodes, List.finRange, List.range, List.cons_append]
  rfl

theorem range_split (p : ℕ) (hp : p ≤ 32) :
    List.range 32 = List.range p ++ List.range' p (32 - p) := by
  have h := @List.range'_append_1 0 p (32 - p)
  rw [Nat.zero_add, Nat.add_sub_cancel' hp] at h
  rw [List.range_eq_range', List.range_eq_range', h]

/-- The source and the levels up to the disclosed one. -/
def readNodes (k : Fin 33) : List Name :=
  src k :: (List.range (pos index v k + 1)).flatMap (tripleN k)

/-- The levels above the disclosed one, then the top. -/
def suffixNodes (k : Fin 33) : List Name :=
  (List.range' (pos index v k + 1) (32 - (pos index v k + 1))).flatMap (tripleN k) ++ [tp k]

theorem chain_split_first (k : Fin 33) (h : pos index v k ≤ 31) :
    chainNodes k = readNodes index v k ++ suffixNodes index v k := by
  rw [chainNodes_eq, range_split (pos index v k + 1) (by omega), List.flatMap_append]
  simp only [readNodes, suffixNodes, List.cons_append, List.append_assoc]

theorem expands_not_cap' : ∀ k : Fin 33, RiscvMixedProgram.expands k.val = true → ¬ isCap k := by
  decide +kernel

/-- An expanding chain is revealed at most at its last input. -/
theorem pos_le_of_expands (k : Fin 33) (h : RiscvMixedProgram.expands k.val = true) :
    pos index v k ≤ 31 := by
  show (posV index v k).val ≤ 31
  rw [posV_val]
  unfold topPos
  rw [if_neg (expands_not_cap' k h)]
  omega

/-- The nodes run before the pair's cap test. -/
def entryNodes (k : Fin 33) : List Name :=
  if RiscvMixedProgram.expands k.val then readNodes index v k else []

/-- The nodes run after the pair's cap test. -/
def tableNodes (k : Fin 33) : List Name :=
  if RiscvMixedProgram.expands k.val then suffixNodes index v k else chainNodes k

theorem chain_entry_split (k : Fin 33) :
    chainNodes k = entryNodes index v k ++ tableNodes index v k := by
  unfold entryNodes tableNodes
  split_ifs with h
  · exact chain_split_first index v k (pos_le_of_expands index v k h)
  · rfl

end OptimalOTS.RiscvUpperForest.ForestVerifier
