import Submissions.UpperLeanIsa.Correctness
import Submissions.UpperLeanIsa.MachineProgram
import Submissions.UpperLeanIsa.ConstraintMath
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

/-!
# The honest leanISA prover

The honest prover queries the oracle exactly as the machine will: 255 chain steps per chain
(the positions below the digit hash the revealed word as dummies) and 34 root absorptions. It
then commits the image whose every cell is a pure function of the input and the answers.

This file collects the answers (`chainAnswers`, `rootAnswers`), gives their fixed-table
counterparts (`chainAnsF`, `rootAnsF`) and the value facts the soundness and completeness proofs
share: the honest chain ends at `chainValue`, and the root states fold to `rootValueFold`.
-/

namespace OptimalOTS.LeanIsaBaseline.Honest

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits eq_of_cellBits_eq blake2sQuery
  hashInput inputWord statementBits OracleCompressCells)
open OptimalOTS.LeanIsaBaseline.Machine

noncomputable section

/-! ## Sequential answer collection -/

/-- An answer table: the full 256-bit answer of step `j` at index `j`. -/
abbrev Answers := ℕ → BitVec 256

/-- The table `A` cut to its first `n` entries, zero above. -/
def cutAns (n : ℕ) (A : Answers) : Answers := fun j => if j < n then A j else 0

theorem cutAns_of_lt {n j : ℕ} (A : Answers) (h : j < n) : cutAns n A j = A j := if_pos h

/-- Ask `n` queries in order; the query of step `j` may read the answers of earlier steps. The
answer of step `j < n` is stored at index `j`, zero above. -/
def seqAnswers (q : ℕ → Answers → BitVec 896) : ℕ → OracleComp Spec Answers
  | 0 => pure (fun _ => 0)
  | n + 1 => do
    let A ← seqAnswers q n
    let a ← hash (q n A)
    pure (fun j => if j = n then a else A j)

/-- Under a fixed table, sequential collection returns the table's own answers, provided every
query reads only earlier answers. -/
theorem fixed_seqAnswers (f : HashTable) (q : ℕ → Answers → BitVec 896) (A : Answers)
    (hq : ∀ j (B : Answers), (∀ k < j, B k = A k) → q j B = q j A)
    (hA : ∀ j, A j = f ⟨896, q j A⟩) (n : ℕ) :
    simulateQ (unifFwdAnswerImpl f) (seqAnswers q n) = pure (cutAns n A) := by
  induction n with
  | zero =>
    simp only [seqAnswers, simulateQ_pure]
    congr 1
    all_goals
      funext j
      exact (if_neg (Nat.not_lt_zero j)).symm
  | succ n ih =>
    have hqn : q n (cutAns n A) = q n A := hq n _ (fun k hk => cutAns_of_lt A hk)
    simp only [seqAnswers, simulateQ_bind, simulateQ_pure, ih, pure_bind, fixed_hash]
    congr 1
    funext j
    by_cases hj : j = n
    · rw [hj]
      refine (if_pos rfl).trans ?_
      rw [hqn, ← hA n]
      exact (cutAns_of_lt A (Nat.lt_succ_self n)).symm
    · refine (if_neg hj).trans ?_
      show (if j < n then A j else 0) = (if j < n + 1 then A j else 0)
      by_cases hjn : j < n
      · rw [if_pos hjn, if_pos (show j < n + 1 by omega)]
      · rw [if_neg hjn, if_neg (show ¬ j < n + 1 by omega)]

/-! ## Chain answers -/

/-- The chain value `x_j` read off an answer table: `x_0 = σ`, and `x_{j+1}` is the low half of
answer `j`. -/
def xOf (σ : Word) (A : Answers) : ℕ → Word
  | 0 => σ
  | j + 1 => (A j).extractLsb' 0 128

theorem xOf_zero (σ : Word) (A : Answers) : xOf σ A 0 = σ := rfl

theorem xOf_succ (σ : Word) (A : Answers) (j : ℕ) :
    xOf σ A (j + 1) = (A j).extractLsb' 0 128 := rfl

theorem xOf_congr {σ : Word} {A B : Answers} {j : ℕ} (h : ∀ k < j, B k = A k) :
    xOf σ B j = xOf σ A j := by
  cases j with
  | zero => rfl
  | succ j => rw [xOf_succ, xOf_succ, h j (Nat.lt_succ_self j)]

theorem xOf_cutAns (σ : Word) (A : Answers) {n j : ℕ} (h : j ≤ n) :
    xOf σ (cutAns n A) j = xOf σ A j :=
  xOf_congr (fun k hk => cutAns_of_lt A (show k < n by omega))

/-- The word step `j` hashes: `σ` up to and including the digit `d`, `x_j` after it. -/
def inW (d : ℕ) (σ : Word) (A : Answers) (j : ℕ) : Word := if j ≤ d then σ else xOf σ A j

/-- The oracle input of chain `i`, step `j`. -/
def chainQ (i d : ℕ) (σ : Word) (j : ℕ) (A : Answers) : BitVec 896 :=
  chainInput i j (inW d σ A j)

theorem chainQ_congr {i d : ℕ} {σ : Word} {A B : Answers} {j : ℕ}
    (h : ∀ k < j, B k = A k) : chainQ i d σ j B = chainQ i d σ j A := by
  unfold chainQ inW
  rw [xOf_congr h]

/-- The honest machine's 255 queries on chain `i`, digit `d`, revealed word `σ`. -/
def chainAnswers (i d : ℕ) (σ : Word) : OracleComp Spec Answers :=
  seqAnswers (chainQ i d σ) 255

/-- The honest chain value `x_j` under a fixed table. -/
def chainXF (f : HashTable) (i d : ℕ) (σ : Word) : ℕ → Word
  | 0 => σ
  | j + 1 =>
    (f ⟨896, chainInput i j (if j ≤ d then σ else chainXF f i d σ j)⟩).extractLsb' 0 128

/-- The honest answer of step `j` under a fixed table. -/
def chainAnsF (f : HashTable) (i d : ℕ) (σ : Word) (j : ℕ) : BitVec 256 :=
  f ⟨896, chainInput i j (if j ≤ d then σ else chainXF f i d σ j)⟩

theorem chainXF_zero (f : HashTable) (i d : ℕ) (σ : Word) : chainXF f i d σ 0 = σ := rfl

theorem chainXF_succ (f : HashTable) (i d : ℕ) (σ : Word) (j : ℕ) :
    chainXF f i d σ (j + 1) =
      (f ⟨896, chainInput i j (if j ≤ d then σ else chainXF f i d σ j)⟩).extractLsb' 0 128 :=
  rfl

theorem xOf_chainAnsF (f : HashTable) (i d : ℕ) (σ : Word) (j : ℕ) :
    xOf σ (chainAnsF f i d σ) j = chainXF f i d σ j := by
  cases j with
  | zero => rfl
  | succ j => rfl

theorem chainAnsF_spec (f : HashTable) (i d : ℕ) (σ : Word) (j : ℕ) :
    chainAnsF f i d σ j = f ⟨896, chainQ i d σ j (chainAnsF f i d σ)⟩ := by
  unfold chainQ inW
  rw [xOf_chainAnsF, chainAnsF]

theorem fixed_chainAnswers (f : HashTable) (i d : ℕ) (σ : Word) :
    simulateQ (unifFwdAnswerImpl f) (chainAnswers i d σ) =
      pure (cutAns 255 (chainAnsF f i d σ)) :=
  fixed_seqAnswers f (chainQ i d σ) (chainAnsF f i d σ) (fun _ _ h => chainQ_congr h)
    (chainAnsF_spec f i d σ) 255

/-- From the digit on, the honest chain value is the verifier's chain value. -/
theorem chainXF_add_succ (f : HashTable) (i d : ℕ) (σ : Word) :
    ∀ n : ℕ, chainXF f i d σ (d + n + 1) = chainValue f i d (n + 1) σ
  | 0 => by
    rw [Nat.add_zero, chainXF_succ, if_pos (Nat.le_refl d)]
    all_goals rfl
  | n + 1 => by
    have ih := chainXF_add_succ f i d σ n
    have hn : ¬ d + n + 1 ≤ d := by omega
    rw [show d + (n + 1) + 1 = d + n + 1 + 1 by omega, chainXF_succ, if_neg hn, ih,
      ← chainValue_add f i d (n + 1) 1 σ, ← Nat.add_assoc]
    all_goals rfl

theorem chainXF_255 (f : HashTable) (i d : ℕ) (σ : Word) (hd : d ≤ 254) :
    chainXF f i d σ 255 = chainValue f i d (255 - d) σ := by
  have h := chainXF_add_succ f i d σ (254 - d)
  rwa [show d + (254 - d) + 1 = 255 by omega, show 254 - d + 1 = 255 - d by omega] at h

/-- Any sequence obeying the honest recursion is the honest chain. This is how soundness reads
the chain off the committed cells. -/
theorem eq_chainXF (f : HashTable) (i d : ℕ) (σ : Word) (X : ℕ → Word) (n : ℕ)
    (h0 : X 0 = σ)
    (hs : ∀ j < n, X (j + 1) =
      (f ⟨896, chainInput i j (if j ≤ d then σ else X j)⟩).extractLsb' 0 128) :
    ∀ j, j ≤ n → X j = chainXF f i d σ j := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    rw [hs j (by omega), ih (by omega), chainXF_succ]

/-- The word the endpoint cell holds: the last chain value, or `σ` when the digit is 255. -/
def endW (d : ℕ) (σ : Word) (A : Answers) : Word := if d ≤ 254 then xOf σ A 255 else σ

theorem endW_honest (f : HashTable) (i d : ℕ) (σ : Word) (hd : d ≤ 255) :
    endW d σ (cutAns 255 (chainAnsF f i d σ)) = chainValue f i d (255 - d) σ := by
  unfold endW
  by_cases h : d ≤ 254
  · rw [if_pos h, xOf_cutAns σ _ (Nat.le_refl 255), xOf_chainAnsF, chainXF_255 f i d σ h]
  · rw [if_neg h]
    obtain rfl : d = 255 := by omega
    simp only [Nat.sub_self, chainValue]

/-- The endpoint of a sequence obeying the honest recursion, as soundness reads it. -/
theorem end_of_recursion (f : HashTable) (i d : ℕ) (σ : Word) (X : ℕ → Word) (hd : d ≤ 255)
    (h0 : X 0 = σ)
    (hs : ∀ j < 255, X (j + 1) =
      (f ⟨896, chainInput i j (if j ≤ d then σ else X j)⟩).extractLsb' 0 128) :
    (if d ≤ 254 then X 255 else σ) = chainValue f i d (255 - d) σ := by
  by_cases h : d ≤ 254
  · rw [if_pos h, eq_chainXF f i d σ X 255 h0 hs 255 (Nat.le_refl 255), chainXF_255 f i d σ h]
  · rw [if_neg h]
    obtain rfl : d = 255 := by omega
    simp only [Nat.sub_self, chainValue]

/-! ## Root answers -/

/-- The absorb state before step `k`, read off the answers: zero, then the previous answer. -/
def stOf (R : Answers) : ℕ → BitVec 256
  | 0 => 0
  | k + 1 => R k

theorem stOf_congr {R R' : Answers} {k : ℕ} (h : ∀ t < k, R' t = R t) :
    stOf R' k = stOf R k := by
  cases k with
  | zero => rfl
  | succ k => exact h k (Nat.lt_succ_self k)

/-- The oracle input of absorb `k`: 33 - k words remain after it. -/
def rootQ (ends : ℕ → Word) (k : ℕ) (R : Answers) : BitVec 896 :=
  LeanIsa.hashInput (stOf R k) ((ends k).setWidth 512) (BitVec.ofNat 128 (2 + (33 - k)))

/-- The honest machine's 34 root absorptions. -/
def rootAnswers (ends : ℕ → Word) : OracleComp Spec Answers := seqAnswers (rootQ ends) 34

/-- The root state before absorb `k` under a fixed table. -/
def rootStF (f : HashTable) (ends : ℕ → Word) : ℕ → BitVec 256
  | 0 => 0
  | k + 1 => f ⟨896, LeanIsa.hashInput (rootStF f ends k) ((ends k).setWidth 512)
      (BitVec.ofNat 128 (2 + (33 - k)))⟩

/-- The honest answer of absorb `k` under a fixed table. -/
def rootAnsF (f : HashTable) (ends : ℕ → Word) (k : ℕ) : BitVec 256 := rootStF f ends (k + 1)

theorem stOf_rootAnsF (f : HashTable) (ends : ℕ → Word) (k : ℕ) :
    stOf (rootAnsF f ends) k = rootStF f ends k := by
  cases k with
  | zero => rfl
  | succ k => rfl

theorem rootStF_succ (f : HashTable) (ends : ℕ → Word) (k : ℕ) :
    rootStF f ends (k + 1) = f ⟨896, LeanIsa.hashInput (rootStF f ends k)
      ((ends k).setWidth 512) (BitVec.ofNat 128 (2 + (33 - k)))⟩ := rfl

theorem rootAnsF_spec (f : HashTable) (ends : ℕ → Word) (k : ℕ) :
    rootAnsF f ends k = f ⟨896, rootQ ends k (rootAnsF f ends)⟩ := by
  unfold rootQ
  rw [stOf_rootAnsF, rootAnsF, rootStF_succ]

theorem fixed_rootAnswers (f : HashTable) (ends : ℕ → Word) :
    simulateQ (unifFwdAnswerImpl f) (rootAnswers ends) = pure (cutAns 34 (rootAnsF f ends)) :=
  fixed_seqAnswers f (rootQ ends) (rootAnsF f ends)
    (fun _ _ h => by unfold rootQ; rw [stOf_congr h]) (rootAnsF_spec f ends) 34

theorem rootValueFold_cons (f : HashTable) (x : Word) (xs : List Word) (cv : BitVec 256) :
    rootValueFold f (x :: xs) cv = rootValueFold f xs
      (f ⟨896, LeanIsa.hashInput cv (x.setWidth 512) (BitVec.ofNat 128 (2 + xs.length))⟩) :=
  rfl

theorem rootValueFold_states_aux (f : HashTable) (ends : ℕ → Word) (S : ℕ → BitVec 256)
    (hS : ∀ k < 34, S (k + 1) = f ⟨896, LeanIsa.hashInput (S k) ((ends k).setWidth 512)
      (BitVec.ofNat 128 (2 + (33 - k)))⟩) :
    ∀ (n k : ℕ) (v : Fin n → Word), k + n = 34 → (∀ t : Fin n, v t = ends (k + t)) →
      rootValueFold f (List.ofFn v) (S k) = S 34
  | 0, k, v, h, _ => by
    obtain rfl : k = 34 := by omega
    simp only [List.ofFn_zero, rootValueFold]
  | n + 1, k, v, h, hv => by
    have hv0 : v 0 = ends k := hv 0
    have hlen : 2 + (List.ofFn fun t : Fin n => v t.succ).length = 2 + (33 - k) := by
      rw [List.length_ofFn]
      omega
    rw [List.ofFn_succ, rootValueFold_cons, hlen, hv0, ← hS k (by omega)]
    exact rootValueFold_states_aux f ends S hS n (k + 1) (fun t => v t.succ) (by omega)
      (fun t => by
        show v t.succ = ends (k + 1 + (t : ℕ))
        rw [hv t.succ, Fin.val_succ, show k + ((t : ℕ) + 1) = k + 1 + (t : ℕ) by omega])

/-- Root states obeying the absorb recursion end at the verifier's root fold. Shared by the
honest prover and by soundness. -/
theorem rootValueFold_states (f : HashTable) (w : Fin 34 → Word) (ends : ℕ → Word)
    (hw : ∀ t : Fin 34, w t = ends t) (S : ℕ → BitVec 256) (h0 : S 0 = 0)
    (hS : ∀ k < 34, S (k + 1) = f ⟨896, LeanIsa.hashInput (S k) ((ends k).setWidth 512)
      (BitVec.ofNat 128 (2 + (33 - k)))⟩) :
    rootValueFold f (List.ofFn w) 0 = S 34 := by
  have h := rootValueFold_states_aux f ends S hS 34 0 w rfl
    (fun t => by rw [Nat.zero_add]; exact hw t)
  rwa [h0] at h

theorem rootValue_states (f : HashTable) (w : Fin 34 → Word) (ends : ℕ → Word)
    (hw : ∀ t : Fin 34, w t = ends t) (S : ℕ → BitVec 256) (h0 : S 0 = 0)
    (hS : ∀ k < 34, S (k + 1) = f ⟨896, LeanIsa.hashInput (S k) ((ends k).setWidth 512)
      (BitVec.ofNat 128 (2 + (33 - k)))⟩) :
    rootValue f w = (S 34).extractLsb' 0 128 := by
  unfold rootValue
  rw [rootValueFold_states f w ends hw S h0 hS]

theorem rootValueFold_rootStF (f : HashTable) (w : Fin 34 → Word) (ends : ℕ → Word)
    (hw : ∀ t : Fin 34, w t = ends t) :
    rootValueFold f (List.ofFn w) 0 = rootStF f ends 34 :=
  rootValueFold_states f w ends hw (rootStF f ends) rfl (fun k _ => rootStF_succ f ends k)

/-! ## The cells the loader pins -/

theorem inputWord_zero (pk : PublicKey) (msg : Message) (σ : List Bool) :
    inputWord pk msg σ 0 = cellOfBits pk := by
  have h : ((statementBits pk msg σ).drop (0 * 128)).take 128 = toBits pk := by
    unfold statementBits
    rw [Nat.zero_mul, List.drop_zero, List.append_assoc, List.append_assoc]
    exact List.take_left' (length_bits pk)
  unfold inputWord
  rw [h]
  exact congrArg cellOfBits (ofBits_bits pk)

theorem inputWord_three (pk : PublicKey) (msg : Message) (σ : List Bool) :
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

/-- For a signature of the admitted length, cell `4 + i` holds the `i`-th 128-bit word. -/
theorem inputWord_sig (pk : PublicKey) (msg : Message) (σ : List Bool) (hlen : σ.length = 4352)
    (i : ℕ) :
    inputWord pk msg σ (4 + i) = cellOfBits (ofBits 128 ((σ.drop (128 * i)).take 128)) := by
  have hpre : (toBits pk ++ toBits msg ++
      toBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1)))).length = 512 := by
    rw [List.length_append, List.length_append, length_bits, length_bits, length_bits]
    all_goals rfl
  have htake : σ.take maxSignatureBits = σ :=
    List.take_of_length_le (by rw [hlen]; unfold maxSignatureBits; omega)
  unfold inputWord statementBits
  rw [show (4 + i) * 128 = 512 + 128 * i by omega, ← List.drop_drop, List.drop_left' hpre, htake]

theorem inputWord_decode (pk : PublicKey) (msg : Message) (σ : List Bool)
    (hlen : σ.length = 4352) (i : Fin 34) :
    inputWord pk msg σ (4 + i.val) = cellOfBits (decode σ i) :=
  inputWord_sig pk msg σ hlen i.val

/-- The length cell pins the admitted length: `4352 < 5505`, so the capped length is exact. -/
theorem length_of_inputWord_three (pk : PublicKey) (msg : Message) (σ : List Bool)
    (h : inputWord pk msg σ 3 = lenV) : σ.length = 4352 := by
  unfold lenV at h
  rw [inputWord_three] at h
  have hb := congrArg cellBits h
  rw [cellBits_cellOfBits, cellBits_cellOfBits] at hb
  have hn := congrArg BitVec.toNat hb
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hn
  unfold maxSignatureBits at hn
  have h1 : min σ.length (5504 + 1) < 2 ^ 128 := by
    have : min σ.length (5504 + 1) ≤ 5505 := Nat.min_le_right _ _
    have h2 : (5505 : ℕ) < 2 ^ 128 := by norm_num
    omega
  have h3 : (4352 : ℕ) < 2 ^ 128 := by norm_num
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3] at hn
  omega

/-! ## Honest cell values of one chain

`d` is the digit, `σ` the revealed word, `A` the chain's answer table. Each value is written
so that the instruction that checks it holds by definition or by a two-case split. -/

/-- Thermometer bit `t_j = [d ≤ j]`. -/
def thermo (d j : ℕ) : E := if d ≤ j then 1 else 0

/-- The previous thermometer bit `t_{j-1}`, with `t_{-1} = 0`. -/
def thermoPrev (d j : ℕ) : E := if d < j then 1 else 0

theorem thermoPrev_zero (d : ℕ) : thermoPrev d 0 = 0 := if_neg (Nat.not_lt_zero d)

theorem thermoPrev_succ (d j : ℕ) : thermoPrev d (j + 1) = thermo d j := by
  unfold thermoPrev thermo
  by_cases h : d ≤ j
  · rw [if_pos h, if_pos (show d < j + 1 by omega)]
  · rw [if_neg h, if_neg (show ¬ d < j + 1 by omega)]

theorem thermo_mul_self (d j : ℕ) : thermo d j = thermo d j * thermo d j := by
  unfold thermo
  by_cases h : d ≤ j
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul]

theorem thermoPrev_mul_thermo (d j : ℕ) : thermoPrev d j = thermoPrev d j * thermo d j := by
  unfold thermoPrev thermo
  by_cases h : d < j
  · rw [if_pos h, if_pos (show d ≤ j by omega), one_mul]
  · rw [if_neg h, zero_mul]

/-- The value `x_j` as a cell. -/
def xE (σ : Word) (A : Answers) (j : ℕ) : E := cellOfBits (xOf σ A j)

/-- `s_j = x_j + σ`. -/
def sE (σ : Word) (A : Answers) (j : ℕ) : E := xE σ A j + cellOfBits σ

/-- `u_j = t_{j-1} · s_j`. -/
def uE (d : ℕ) (σ : Word) (A : Answers) (j : ℕ) : E := thermoPrev d j * sE σ A j

/-- `in_j = σ + u_j`. -/
def inE (d : ℕ) (σ : Word) (A : Answers) (j : ℕ) : E := cellOfBits σ + uE d σ A j

/-- The low output cell of step `j`, which is `x_{j+1}`. -/
def lowE (A : Answers) (j : ℕ) : E := cellOfBits ((A j).extractLsb' 0 128)

/-- The high output cell of step `j`. -/
def highE (A : Answers) (j : ℕ) : E := cellOfBits ((A j).extractLsb' 128 128)

/-- A link product `t_j · w_j`. -/
def prodE (d : ℕ) (w : ℕ → E) (j : ℕ) : E := thermo d j * w j

/-- A link accumulator: `a_0` then `a_{j+1} = a_j + t_j · w_j`. -/
def accE (d : ℕ) (a0 : E) (w : ℕ → E) : ℕ → E
  | 0 => a0
  | j + 1 => accE d a0 w j + prodE d w j

theorem accE_zero (d : ℕ) (a0 : E) (w : ℕ → E) : accE d a0 w 0 = a0 := rfl

theorem accE_succ (d : ℕ) (a0 : E) (w : ℕ → E) (j : ℕ) :
    accE d a0 w (j + 1) = accE d a0 w j + prodE d w j := rfl

/-- Telescoping in characteristic two: an accumulator of thermometer-weighted differences
`w_j = V_j + V_{j+1}` has added `V_d + V_n` to its base once `n` has passed the digit. -/
theorem accE_telescope (d : ℕ) (a0 : E) (V w : ℕ → E) (hw : ∀ j, w j = V j + V (j + 1)) :
    ∀ n, accE d a0 w n = a0 + (if d ≤ n then V d + V n else 0)
  | 0 => by
    rw [accE_zero]
    by_cases h : d ≤ 0
    · rw [if_pos h, show d = 0 by omega, CharTwo.add_self_eq_zero, add_zero]
    · rw [if_neg h, add_zero]
  | n + 1 => by
    rw [accE_succ, accE_telescope d a0 V w hw n]
    unfold prodE thermo
    rw [hw n]
    by_cases h : d ≤ n
    · rw [if_pos h, if_pos h, if_pos (show d ≤ n + 1 by omega), one_mul]
      linear_combination (CharTwo.add_self_eq_zero (V n))
    · rw [if_neg h, if_neg h, zero_mul, add_zero, add_zero]
      by_cases h' : d = n + 1
      · rw [if_pos (show d ≤ n + 1 by omega), h', CharTwo.add_self_eq_zero, add_zero]
      · rw [if_neg (show ¬ d ≤ n + 1 by omega), add_zero]

/-- With base `V_n` and a digit `d ≤ n`, the accumulator ends at `V_d`. -/
theorem accE_telescope_end (d n : ℕ) (V w : ℕ → E) (hw : ∀ j, w j = V j + V (j + 1))
    (hd : d ≤ n) : accE d (V n) w n = V d := by
  rw [accE_telescope d (V n) V w hw n, if_pos hd]
  linear_combination (CharTwo.add_self_eq_zero (V n))

/-- A sequence obeying the accumulator recursion is the accumulator. -/
theorem eq_accE (d : ℕ) (w : ℕ → E) (a : ℕ → E) (n : ℕ)
    (hs : ∀ j < n, a (j + 1) = a j + thermo d j * w j) :
    ∀ j, j ≤ n → a j = accE d (a 0) w j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [hs j (by omega), ih (by omega), accE_succ, prodE]

/-- Endpoint temporaries: `e0 = x_255 + σ`, `e1 = t_254 · e0`, `end = σ + e1`. -/
def e0E (σ : Word) (A : Answers) : E := xE σ A 255 + cellOfBits σ

def e1E (d : ℕ) (σ : Word) (A : Answers) : E := thermo d 254 * e0E σ A

def endE (d : ℕ) (σ : Word) (A : Answers) : E := cellOfBits σ + e1E d σ A

theorem xE_succ (σ : Word) (A : Answers) (j : ℕ) : xE σ A (j + 1) = lowE A j := rfl

theorem xE_zero (σ : Word) (A : Answers) : xE σ A 0 = cellOfBits σ := rfl

/-- `σ + (x + σ) = x` in characteristic two. -/
theorem char2_cancel (a b : E) : a + (b + a) = b := by
  rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The mux: the hashed cell is `σ` up to the digit and `x_j` after it. -/
theorem inE_eq (d : ℕ) (σ : Word) (A : Answers) (j : ℕ) :
    inE d σ A j = cellOfBits (inW d σ A j) := by
  unfold inE uE sE inW thermoPrev xE
  by_cases h : j ≤ d
  · rw [if_neg (show ¬ d < j by omega), if_pos h, zero_mul, add_zero]
  · rw [if_pos (show d < j by omega), if_neg h, one_mul, char2_cancel]

/-- The endpoint cell holds `endW`. -/
theorem endE_eq (d : ℕ) (σ : Word) (A : Answers) : endE d σ A = cellOfBits (endW d σ A) := by
  unfold endE e1E e0E endW thermo xE
  by_cases h : d ≤ 254
  · rw [if_pos h, if_pos h, one_mul, char2_cancel]
  · rw [if_neg h, if_neg h, zero_mul, add_zero]


/-! ## Cell arithmetic -/

theorem isCanonical_cellOfBits (b : BitVec 128) : IsCanonical128 (cellOfBits b) := by
  show (E.ofLimbs (b.extractLsb' 0 64) (b.extractLsb' 64 64) 0).limb 2 = 0
  rw [limb_ofLimbs]
  all_goals rfl

theorem cellBits_zero : cellBits (0 : E) = 0 := by
  rw [← Machine.cellOfBits_zero, cellBits_cellOfBits]

theorem isCanonical_zero : IsCanonical128 (0 : E) := by
  rw [← Machine.cellOfBits_zero]
  exact isCanonical_cellOfBits 0

theorem cellOfBits_cellBits {x : E} (hx : IsCanonical128 x) : cellOfBits (cellBits x) = x :=
  eq_of_cellBits_eq (isCanonical_cellOfBits _) hx (cellBits_cellOfBits _)

/-! ## Constants of segment A -/

/-- The constant committed at cell `c < 8192`, laid out as `MachineProgram` sets it. -/
def hConst (c : ℕ) : E :=
  if c = 3 then lenV
  else if c = 50 then oneV
  else if c = 51 then fpcV
  else if 64 ≤ c ∧ c < 98 then chainIdV (c - 64)
  else if 100 ≤ c ∧ c < 134 then rootMdV (c - 100)
  else if 256 ≤ c ∧ c < 511 then posV (c - 256)
  else if 1024 ≤ c ∧ c < 5120 then wvV ((c - 1024) / 256) ((c - 1024) % 256)
  else if 5120 ≤ c ∧ c < 5375 then wuV (c - 5120)
  else if 5376 ≤ c ∧ c < 5631 then wuHiV (c - 5376)
  else if 5632 ≤ c ∧ c < 5887 then wuLoV (c - 5632)
  else if c = 5888 then ubHiV
  else if c = 5889 then ubLoV
  else if 5890 ≤ c ∧ c < 5906 then vbV (c - 5890)
  else 0

/-- The V weights and base of chain `i`. -/
def avW (i : ℕ) : ℕ → E := wvV (bytePos i)

def avBase (i : ℕ) : E := vbV (bytePos i)

/-- The U weights and base of chain `i`. -/
def auW (i j : ℕ) : E := if i < 32 then wuV j else if i = 32 then wuHiV j else wuLoV j

def auBase (i : ℕ) : E := if i < 32 then oneV else if i = 32 then ubHiV else ubLoV

/-! ## Link values -/

/-- `V_k` at byte position `p`. -/
def vV (p k : ℕ) : E := cellOfBits (BitVec.ofNat 128 (k <<< (8 * p)))

theorem wvV_eq (p j : ℕ) : wvV p j = vV p j + vV p (j + 1) :=
  cellOfBits_shift_xor j (j + 1) (8 * p)

theorem vbV_eq (p : ℕ) : vbV p = vV p 255 := rfl

/-- The exponent of `U_k` on chain `i`. -/
def uExp (i k : ℕ) : ℕ := if i < 32 then 255 - k else if i = 32 then 256 * k else k

/-- `U_k` on chain `i`. -/
def uV (i k : ℕ) : E := ofK (gpow (uExp i k))

theorem auW_eq (i j : ℕ) : auW i j = uV i j + uV i (j + 1) := by
  unfold auW uV uExp
  by_cases h1 : i < 32
  · rw [if_pos h1, if_pos h1, if_pos h1]
    try rfl
  · by_cases h2 : i = 32
    · rw [if_neg h1, if_neg h1, if_neg h1, if_pos h2, if_pos h2, if_pos h2]
      try rfl
    · rw [if_neg h1, if_neg h1, if_neg h1, if_neg h2, if_neg h2, if_neg h2]
      try rfl

theorem auBase_eq (i : ℕ) : auBase i = uV i 255 := by
  unfold auBase uV uExp
  by_cases h1 : i < 32
  · rw [if_pos h1, if_pos h1, Nat.sub_self, Machine.gpow_zero, oneV_eq_ofK]
  · by_cases h2 : i = 32
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
      try rfl
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      try rfl

/-- The honest `D_i` is `V_{d_i}`. -/
theorem accE_V (d : ℕ) (hd : d ≤ 255) (i : ℕ) : accE d (avBase i) (avW i) 255 = vV (bytePos i) d :=
  accE_telescope_end d 255 (vV (bytePos i)) (avW i) (fun j => wvV_eq (bytePos i) j) hd

/-- The honest `P_i` is `U_{d_i}`. -/
theorem accE_U (d : ℕ) (hd : d ≤ 255) (i : ℕ) : accE d (auBase i) (auW i) 255 = uV i d := by
  rw [auBase_eq]
  exact accE_telescope_end d 255 (uV i) (auW i) (fun j => auW_eq i j) hd

/-! ## Honest values -/

/-- The digit of chain `i`, natural-number indexed. -/
def dig (m : Message) (i : ℕ) : ℕ := if h : i < 34 then digit m ⟨i, h⟩ else 0

/-- The revealed word of chain `i`. -/
def sigW (bits : List Bool) (i : ℕ) : Word := ofBits 128 ((bits.drop (128 * i)).take 128)

/-- Chain `i`'s answer table. -/
def tabN (CA : Fin 34 → Answers) (i : ℕ) : Answers :=
  if h : i < 34 then CA ⟨i, h⟩ else fun _ => 0

theorem dig_fin (m : Message) (i : Fin 34) : dig m i.val = digit m i := by
  unfold dig
  rw [dif_pos i.isLt]

theorem dig_le (m : Message) (i : ℕ) : dig m i ≤ 255 := by
  unfold dig
  split
  · exact digit_le m _
  · exact Nat.zero_le _

theorem sigW_fin (bits : List Bool) (i : Fin 34) : sigW bits i.val = decode bits i := rfl

theorem tabN_fin (CA : Fin 34 → Answers) (i : Fin 34) : tabN CA i.val = CA i := by
  unfold tabN
  rw [dif_pos i.isLt]

/-- Honest `D_i` and `P_i`; they depend on the message only. -/
def dVal (m : Message) (i : ℕ) : E := accE (dig m i) (avBase i) (avW i) 255

def pVal (m : Message) (i : ℕ) : E := accE (dig m i) (auBase i) (auW i) 255

/-- The honest value of cell `r` of step `j` of chain `i`. -/
def stepVal (d : ℕ) (σ : Word) (A : Answers) (i j : ℕ) : ℕ → E
  | 0 => thermo d j
  | 1 => sE σ A j
  | 2 => uE d σ A j
  | 3 => inE d σ A j
  | 4 => lowE A j
  | 5 => highE A j
  | 6 => prodE d (avW i) j
  | 7 => accE d (avBase i) (avW i) (j + 1)
  | 8 => prodE d (auW i) j
  | _ => accE d (auBase i) (auW i) (j + 1)

/-- The honest value at offset `o` of chain `i`'s block. -/
def chainOffVal (d : ℕ) (σ : Word) (A : Answers) (i o : ℕ) : E :=
  if o < 2550 then stepVal d σ A i (o / 10) (o % 10)
  else if o = 2550 then e0E σ A
  else if o = 2551 then e1E d σ A
  else if o = 2552 then endE d σ A
  else 0

/-- The honest partial XOR of link half `h`: `Σ_{b ≤ s} D_{linkChain h b}`. -/
def linkAccV (m : Message) (h : ℕ) : ℕ → E
  | 0 => dVal m (linkChain h 0)
  | s + 1 => linkAccV m h s + dVal m (linkChain h (s + 1))

/-- The honest partial checksum product `Π_{i ≤ s} P_i`. -/
def prodAccV (m : Message) : ℕ → E
  | 0 => pVal m 0
  | s + 1 => prodAccV m s * pVal m (s + 1)

/-- The honest link temporary at `96000 + o`. -/
def tempVal (m : Message) (o : ℕ) : E :=
  if o < 32 then (if 1 ≤ o % 16 ∧ o % 16 < 15 then linkAccV m (o / 16) (o % 16) else 0)
  else if 101 ≤ o ∧ o < 132 then prodAccV m (o - 100)
  else 0

/-- The honest value at `97000 + o`: root states, then the halt cells. -/
def rootOffVal (RA : Answers) (o : ℕ) : E :=
  if 2 ≤ o ∧ o < 70 then
    (if o % 2 = 0 then lowE RA (o / 2 - 1) else highE RA (o / 2 - 1))
  else if o = 100 then oneV
  else if o = 101 then fpcV
  else 0

/-- The honest value at offset `o` of chain `i`. -/
def chainCellVal (m : Message) (bits : List Bool) (CA : Fin 34 → Answers) (i o : ℕ) : E :=
  chainOffVal (dig m i) (sigW bits i) (tabN CA i) i o

/-- The honest value of every cell. The loader overwrites cells `0 … 46`. -/
def cellVal (m : Message) (bits : List Bool) (CA : Fin 34 → Answers) (RA : Answers)
    (c : ℕ) : E :=
  if c < 8192 then hConst c
  else if c < 95232 then chainCellVal m bits CA ((c - 8192) / 2560) ((c - 8192) % 2560)
  else if c < 96000 then 0
  else if c < 97000 then tempVal m (c - 96000)
  else rootOffVal RA (c - 97000)

/-- The honest image over given answer tables. -/
def imageOf (_pk : PublicKey) (m : Message) (bits : List Bool) (CA : Fin 34 → Answers)
    (RA : Answers) : MemImage 17 :=
  fun c => cellVal m bits CA RA c.val

/-! ## The prover -/

/-- The endpoint words the honest prover absorbs. -/
def endsOf (m : Message) (bits : List Bool) (CA : Fin 34 → Answers) (k : ℕ) : Word :=
  endW (dig m k) (sigW bits k) (tabN CA k)

/-- The honest prover: query the chains as the machine will, then the root, then commit. -/
def prover (pk : PublicKey) (m : Message) (bits : List Bool) :
    OracleComp Spec (MemImage 17) := do
  let CA ← tabulate (fun i : Fin 34 => chainAnswers i.val (digit m i) (decode bits i))
  let RA ← rootAnswers (endsOf m bits CA)
  pure (imageOf pk m bits CA RA)

/-- The chain answer tables under a fixed table. -/
def chainTab (f : HashTable) (m : Message) (bits : List Bool) (i : Fin 34) : Answers :=
  cutAns 255 (chainAnsF f i.val (digit m i) (decode bits i))

/-- The root answer table under a fixed table. -/
def rootTab (f : HashTable) (m : Message) (bits : List Bool) : Answers :=
  cutAns 34 (rootAnsF f (endsOf m bits (chainTab f m bits)))

/-- The honest image under a fixed table. -/
def imageF (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) : MemImage 17 :=
  imageOf pk m bits (chainTab f m bits) (rootTab f m bits)

theorem fixed_prover (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) :
    simulateQ (unifFwdAnswerImpl f) (prover pk m bits) = pure (imageF f pk m bits) := by
  unfold prover imageF rootTab
  simp only [simulateQ_bind, simulateQ_pure]
  rw [fixed_tabulate f (fun i : Fin 34 => chainAnswers i.val (digit m i) (decode bits i))
      (chainTab f m bits) (fun i => fixed_chainAnswers f i.val (digit m i) (decode bits i)),
    pure_bind, fixed_rootAnswers f (endsOf m bits (chainTab f m bits)), pure_bind]

/-! ## Honest facts under a fixed table -/

theorem tabN_chainTab (f : HashTable) (m : Message) (bits : List Bool) {i : ℕ} (hi : i < 34) :
    tabN (chainTab f m bits) i = cutAns 255 (chainAnsF f i (dig m i) (sigW bits i)) := by
  have h1 : tabN (chainTab f m bits) i = chainTab f m bits ⟨i, hi⟩ := tabN_fin _ ⟨i, hi⟩
  have h2 : digit m ⟨i, hi⟩ = dig m i := (dig_fin m ⟨i, hi⟩).symm
  have h3 : decode bits ⟨i, hi⟩ = sigW bits i := rfl
  rw [h1]
  show cutAns 255 (chainAnsF f i (digit m ⟨i, hi⟩) (decode bits ⟨i, hi⟩)) = _
  rw [h2, h3]

/-- The honest endpoint word is the verifier's reconstructed word. -/
theorem endsOf_honest (f : HashTable) (m : Message) (bits : List Bool) (i : Fin 34) :
    endsOf m bits (chainTab f m bits) i.val = reconstructedWords f m bits i := by
  show endW (dig m i.val) (sigW bits i.val) (tabN (chainTab f m bits) i.val) =
    chainValue f i.val (digit m i) (255 - digit m i) (decode bits i)
  rw [tabN_chainTab f m bits i.isLt, endW_honest f i.val _ _ (dig_le m i.val), dig_fin,
    sigW_fin]

/-- The honest final root state is the verifier's root fold. -/
theorem rootTab_33 (f : HashTable) (m : Message) (bits : List Bool) :
    rootTab f m bits 33 = rootValueFold f (List.ofFn (reconstructedWords f m bits)) 0 := by
  unfold rootTab
  rw [cutAns_of_lt _ (show 33 < 34 by norm_num)]
  rw [rootValueFold_rootStF f (reconstructedWords f m bits) (endsOf m bits (chainTab f m bits))
    (fun t => (endsOf_honest f m bits t).symm)]
  try rfl

end

end OptimalOTS.LeanIsaBaseline.Honest
