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


/-- Above the statement (`38 · 128 = 4864` bits for an admitted signature) the loader pins zero:
cells `38 … 46`, in particular the zero pair `(zCell, zCell + 1)`. -/
theorem inputWord_of_ge_38 (pk : PublicKey) (msg : Message) (σ : List Bool)
    (hlen : σ.length = 4352) {i : ℕ} (hi : 38 ≤ i) : inputWord pk msg σ i = 0 := by
  have hl : (statementBits pk msg σ).length = 4864 := by
    unfold statementBits
    rw [List.length_append, List.length_append, List.length_append, length_bits, length_bits,
      length_bits, List.length_take, hlen]
    unfold maxSignatureBits pkBits msgBits
    omega
  have hd : (statementBits pk msg σ).drop (i * 128) = [] :=
    List.drop_eq_nil_of_le (by rw [hl]; omega)
  unfold inputWord
  rw [hd, List.take_nil]
  exact Machine.cellOfBits_zero

/-! ## Cell arithmetic -/

/-- The value `x_j` as a cell. -/
def xE (σ : Word) (A : Answers) (j : ℕ) : E := cellOfBits (xOf σ A j)

/-- The low output cell of step `j`, which is `x_{j+1}`. -/
def lowE (A : Answers) (j : ℕ) : E := cellOfBits ((A j).extractLsb' 0 128)

/-- The high output cell of step `j`. -/
def highE (A : Answers) (j : ℕ) : E := cellOfBits ((A j).extractLsb' 128 128)

theorem xE_succ (σ : Word) (A : Answers) (j : ℕ) : xE σ A (j + 1) = lowE A j := rfl

theorem xE_zero (σ : Word) (A : Answers) : xE σ A 0 = cellOfBits σ := rfl

/-- `σ + (x + σ) = x` in characteristic two. -/
theorem char2_cancel (a b : E) : a + (b + a) = b := by
  rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

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

/-- The honest tie accumulator of chain `k < 32`: the byte words `vV (bytePos i) d_i` of the
chains of `k`'s half up to and including `k` (cells 2 and 1 are the full sums, `accCell 15` and
`accCell 31`). -/
def accV (m : Message) (k : ℕ) : E :=
  ∑ i ∈ Finset.Ico (16 * (k / 16)) (k + 1), vV (bytePos i) (dig m i)

/-- The honest checksum-product exponent held by `gCell k`: `Σ_{i ≤ k} (s0 i + d_i + 1)` for
`k < 32`, and that sum over the 32 message chains plus `256 · d_32` for `k = 32`. -/
def gExp (m : Message) (k : ℕ) : ℕ :=
  if k < 32 then ∑ i ∈ Finset.range (k + 1), (s0 i + dig m i + 1)
  else (∑ i ∈ Finset.range 32, (s0 i + dig m i + 1)) + 256 * dig m 32

/-- The honest value at offset `o < 160` of chain `k`'s scratch block (§7): the unary and group
hints selecting leaf `d_k`, all node targets, and the leaf cells. -/
def scrVal (m : Message) (k o : ℕ) : E :=
  if o < 64 then
    (if k = 32 then (if o < 31 - dig m k then oneV else 0)
     else (if o < dig m k / 4 then oneV else 0))
  else if o < 128 then
    (if k = 32 then tgtV (rBase 32 + 7 * (o - 64 + 1)) else tgtV (rBase k + 46 * (o - 64 + 1)))
  else if o = 128 then (if 2 ≤ dig m k % 4 then oneV else 0)
  else if o = 129 then (if dig m k % 2 = 1 then oneV else 0)
  else if o = 130 then tgtV (gBase k (dig m k / 4) + 24)
  else if o = 131 then tgtV (gBase k (dig m k / 4) + 11 * (2 * (dig m k % 4 / 2) + 1) + 4)
  else if o = 132 then tgtV (s0 k + dig m k + 1)
  else if o = 133 then tgtV (s0 k + 255)
  else if o = 134 then tgtV (gExp m k)
  else if o = 135 then vV (bytePos k) (dig m k)
  else if o = 136 then accV m k
  else tgtV (256 * dig m k)

/-- The honest value at `7000 + o`: the root state pairs `S_{t+1}` (low cell at `o = 2t + 2`). -/
def rootVal (RA : Answers) (o : ℕ) : E :=
  if o % 2 = 0 then lowE RA (o / 2 - 1) else highE RA (o / 2 - 1)

/-- The honest value at offset `o < 512` of chain `k`'s word block: `x_{k,j}` at `o = 2j` (the
hashed word `inW`: `σ` up to the digit, the chain after it), `h_{k,j-1}` at `o = 2j + 1`. -/
def xVal (m : Message) (bits : List Bool) (CA : Fin 34 → Answers) (k o : ℕ) : E :=
  if o % 2 = 0 then cellOfBits (inW (dig m k) (sigW bits k) (tabN CA k) (o / 2))
  else highE (tabN CA k) (o / 2 - 1)

/-- The honest value of every cell. The loader overwrites cells `0 … 46`. -/
def cellVal (m : Message) (bits : List Bool) (CA : Fin 34 → Answers) (RA : Answers)
    (c : ℕ) : E :=
  if c < 400 then posV (c - 100)
  else if c = 400 then tgtV K0
  else if c < 1024 then 0
  else if c < 6464 then scrVal m ((c - 1024) / 160) ((c - 1024) % 160)
  else if c < 8192 then rootVal RA (c - 7000)
  else xVal m bits CA ((c - 8192) / 512) ((c - 8192) % 512)

/-- The honest image over given answer tables (`memLog = 16`). -/
def imageOf (_pk : PublicKey) (m : Message) (bits : List Bool) (CA : Fin 34 → Answers)
    (RA : Answers) : MemImage 16 :=
  fun c => cellVal m bits CA RA c.val

/-! ## The prover -/

/-- The endpoint words the honest prover absorbs. -/
def endsOf (m : Message) (bits : List Bool) (CA : Fin 34 → Answers) (k : ℕ) : Word :=
  endW (dig m k) (sigW bits k) (tabN CA k)

/-- The honest prover: query the chains as the machine will, then the root, then commit. -/
def prover (pk : PublicKey) (m : Message) (bits : List Bool) :
    OracleComp Spec (MemImage 16) := do
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
def imageF (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) : MemImage 16 :=
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


/-- The honest chain answer of step `j` is the table's answer to the step's query. -/
theorem chain_answer (f : HashTable) (i d : ℕ) (σ : Word) {j : ℕ} (hj : j < 255) :
    f ⟨896, chainInput i j (inW d σ (cutAns 255 (chainAnsF f i d σ)) j)⟩ =
      cutAns 255 (chainAnsF f i d σ) j := by
  have hq : chainQ i d σ j (cutAns 255 (chainAnsF f i d σ)) = chainQ i d σ j (chainAnsF f i d σ) :=
    chainQ_congr (i := i) (d := d) (σ := σ) (A := chainAnsF f i d σ)
      (B := cutAns 255 (chainAnsF f i d σ)) (j := j)
      (fun k hk => cutAns_of_lt _ (show k < 255 by omega))
  have hq' : chainInput i j (inW d σ (cutAns 255 (chainAnsF f i d σ)) j) =
      chainQ i d σ j (chainAnsF f i d σ) := hq
  rw [hq', cutAns_of_lt _ hj, chainAnsF_spec f i d σ j]

/-- The honest root answer of absorption `t` is the table's answer to its query. -/
theorem root_answer (f : HashTable) (ends : ℕ → Word) {t : ℕ} (ht : t < 34) :
    f ⟨896, rootQ ends t (cutAns 34 (rootAnsF f ends))⟩ = cutAns 34 (rootAnsF f ends) t := by
  have hq : rootQ ends t (cutAns 34 (rootAnsF f ends)) = rootQ ends t (rootAnsF f ends) := by
    unfold rootQ
    rw [stOf_congr (R := rootAnsF f ends) (R' := cutAns 34 (rootAnsF f ends)) (k := t)
      (fun s hs => cutAns_of_lt _ (show s < 34 by omega))]
  rw [hq, cutAns_of_lt _ ht, rootAnsF_spec f ends t]

end

end OptimalOTS.LeanIsaBaseline.Honest
