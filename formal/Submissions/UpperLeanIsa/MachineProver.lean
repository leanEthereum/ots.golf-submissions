import Submissions.UpperLeanIsa.MachineSound

/-!
# The honest HL-GROUP-3 prover

The honest prover queries the oracle exactly as the verifier does: the index, then for each chain
`k` its `d k` steps from the revealed word (`d = dg T (hxs T I)`, the digits of the index `I`),
then the nine root calls. It commits the image whose every cell is a pure function of the input
and those answers (`hcell`): the constants, the index pair, the tie patterns and accumulators, the
landing hints `H_f = g ^ ent f (xs f)`, `H'_f = H_f · g`, the landing products, the chain pairs
and the root states. Under a fixed table the prover is `imageF` (`fixed_prover`).
-/

namespace OptimalOTS.HLG3

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

variable (P : Params) (T : Tab)

/-! ## Answer collection -/

/-- The answers of `n` chain steps of chain `k` from position `j`, in order. -/
def chainAnsQ (k : Fin numChains) : ℕ → ℕ → Word → OracleComp Spec (ℕ → BitVec 256)
  | _, 0, _ => pure (fun _ => 0)
  | j, n + 1, x => do
    let a ← hash896 (P.chainInput k j x)
    let A ← chainAnsQ k (j + 1) n (P.slice k j a)
    pure (fun t => if t = 0 then a else A (t - 1))

/-- `chainAnsQ` under a fixed table. -/
def chainAnsF (f : HashTable) (k : Fin numChains) : ℕ → ℕ → Word → ℕ → BitVec 256
  | _, 0, _ => fun _ => 0
  | j, n + 1, x => fun t => if t = 0 then ans f (P.chainInput k j x) else
      chainAnsF f k (j + 1) n (P.slice k j (ans f (P.chainInput k j x))) (t - 1)

theorem fixed_chainAns (f : HashTable) (k : Fin numChains) (j n : ℕ) (x : Word) :
    simulateQ (unifFwdAnswerImpl f) (chainAnsQ P k j n x) = pure (chainAnsF P f k j n x) := by
  induction n generalizing j x with
  | zero => rfl
  | succ n ih =>
    rw [chainAnsQ, simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind, ih, pure_bind,
      simulateQ_pure]
    rfl

theorem chainValue_succ (f : HashTable) (P : Params) (k : Fin numChains) :
    ∀ t j x, chainValue f P k j (t + 1) x =
      P.slice k (j + t) (ans f (P.chainInput k (j + t) (chainValue f P k j t x))) := by
  intro t
  induction t with
  | zero => intro j x; rfl
  | succ t ih =>
    intro j x
    show chainValue f P k (j + 1) (t + 1) _ = _
    rw [ih, show j + 1 + t = j + (t + 1) by ring]
    rfl

theorem chainAnsF_spec (f : HashTable) (k : Fin numChains) :
    ∀ n j x t, t < n →
      chainAnsF P f k j n x t = ans f (P.chainInput k (j + t) (chainValue f P k j t x)) := by
  intro n
  induction n with
  | zero => intro j x t ht; omega
  | succ n ih =>
    intro j x t ht
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp only [chainAnsF]; rfl
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      simp only [chainAnsF, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [ih (j + 1) _ u (by omega), show j + 1 + u = j + (u + 1) by omega]
      rfl

/-- The answers of `n` root calls from call `r` and state `st`, in order. -/
def rootAnsQ (tp : Fin numChains → Word) : ℕ → ℕ → BitVec 256 → OracleComp Spec (ℕ → BitVec 256)
  | _, 0, _ => pure (fun _ => 0)
  | r, n + 1, st => do
    let a ← hash896 (P.rootInput tp r st)
    let A ← rootAnsQ tp (r + 1) n a
    pure (fun i => if i = 0 then a else A (i - 1))

/-- `rootAnsQ` under a fixed table. -/
def rootAnsF (f : HashTable) (tp : Fin numChains → Word) : ℕ → ℕ → BitVec 256 → ℕ → BitVec 256
  | _, 0, _ => fun _ => 0
  | r, n + 1, st => fun i => if i = 0 then ans f (P.rootInput tp r st) else
      rootAnsF f tp (r + 1) n (ans f (P.rootInput tp r st)) (i - 1)

theorem fixed_rootAns (f : HashTable) (tp : Fin numChains → Word) (r n : ℕ) (st : BitVec 256) :
    simulateQ (unifFwdAnswerImpl f) (rootAnsQ P tp r n st) = pure (rootAnsF P f tp r n st) := by
  induction n generalizing r st with
  | zero => rfl
  | succ n ih =>
    rw [rootAnsQ, simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind, ih, pure_bind,
      simulateQ_pure]
    rfl

theorem rootAnsF_spec (f : HashTable) (tp : Fin numChains → Word) :
    ∀ n r st i, i < n → rootAnsF P f tp r n st i = rootState f P tp r (i + 1) st := by
  intro n
  induction n with
  | zero => intro r st i hi; omega
  | succ n ih =>
    intro r st i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [rootAnsF]; rfl
    · obtain ⟨u, rfl⟩ : ∃ u, i = u + 1 := ⟨i - 1, by omega⟩
      simp only [rootAnsF, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [ih (r + 1) _ u (by omega)]
      rfl

/-! ## Honest values -/

/-- The index of the index answer `y0`. -/
def idxOf (y0 : BitVec 256) : Word := y0.extractLsb' 0 128

/-- The honest index vector of an index: the free digit, then the group fields. -/
def hxs (I : Word) (f : ℕ) : ℕ := if f = 0 then freeDigit (gcost T I) else field (f - 1) I

/-- Signature cell `k`. -/
def sigW (bits : List Bool) (k : ℕ) : Word := ofBits 128 ((bits.drop (128 * k)).take 128)

/-- The digit of chain `k` for the index answer `y0`. -/
def hd (y0 : BitVec 256) (k : ℕ) : ℕ := dg T (hxs T (idxOf y0)) k

/-- The chain top: the selected half of the last answer, or the revealed word. -/
def topOf (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (k : ℕ) : Word :=
  if hd T y0 k = 0 then sigW bits k else (A k (hd T y0 k - 1)).extractLsb' (128 * topOff k) 128

/-- The unused half of the last answer (zero for no step); low when the top uses the high half. -/
def hiOf (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (k : ℕ) : E :=
  if hd T y0 k = 0 then 0 else cellOfBits ((A k (hd T y0 k - 1)).extractLsb' (128 * (1 - topOff k)) 128)

/-- The tops as a vector. -/
def topsOfV (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) :
    Fin numChains → Word := fun k => topOf T bits y0 A k.val

/-- The low cell of an answer. -/
def loC (a : BitVec 256) : E := cellOfBits (a.extractLsb' 0 128)

/-- The high cell of an answer. -/
def hiC (a : BitVec 256) : E := cellOfBits (a.extractLsb' 128 128)

/-- The honest landing product before group `u`. -/
def gpV (I : Word) (u : ℕ) : E :=
  ofK (LeanIsaFieldRescale.initialProduct 87 (hxs T I 0) *
    LeanIsaFieldRescale.costFactor (∑ w ∈ Finset.range u, cost T w (hxs T I (w + 1))))

/-- The home chain of `XH` pair `i`. -/
def xhK (i : ℕ) : ℕ := [3, 4, 5, 6, 9, 10, 11, 14, 15, 16, 19, 20, 21, 24, 25, 26, 29, 30, 31, 34, 35, 36, 39, 40, 41].getD i 0

/-- The physical answer pair, placing the top at offset topOff k and the unused half beside it. -/
def topPair (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (k b : ℕ) : E :=
  if b = topOff k then cellOfBits (topOf T bits y0 A k) else hiOf T y0 A k

/-- The honest value of cell `c ≥ 47`, from the index answer `y0`, the chain answers `A` and the
root answers `RA`. -/
def hcell (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (RA : ℕ → BitVec 256)
    (c : ℕ) : E :=
  if c < 48 then 0
  else if c = 48 then oneV
  else if c = 49 then gV
  else if c = 50 then gpV T (idxOf y0) 13
  else if c < 68 then cV (c - 50)
  else if c = 68 then loC y0
  else if c = 69 then hiC y0
  else if c < 83 then fpat (c - 70) (hxs T (idxOf y0) (c - 70 + 1))
  else if c < 96 then 0
  else if c < 108 then natV (ofDigitsW gb (fun w => hxs T (idxOf y0) (w + 1)) (c - 96 + 1))
  else if c < 122 then ofK (gpow (ent (c - 108) (hxs T (idxOf y0) (c - 108))))
  else if c < 136 then ofK (gpow (ent (c - 122) (hxs T (idxOf y0) (c - 122)) + 1))
  else if c < 149 then gpV T (idxOf y0) (c - 136)
  else if c = 149 then hiOf T y0 A 38
  else if c = 150 then cellOfBits (topOf T bits y0 A 38)
  else if c < 153 then topPair T bits y0 A 37 (c - 151)
  else if c = 153 then cellOfBits (topOf T bits y0 A 0)
  else if c = 154 then hiOf T y0 A 0
  else if c = 183 then ofK (gpow (ent 14 (hxs T (idxOf y0) 1)))
  else if c = 184 then ofK (gpow (ent 14 (hxs T (idxOf y0) 1) + 1))
  else if c < 187 then
    let r := (c - 155) / 4
    let k := if (c - 155) % 4 < 2 then (if r = 0 then 1 else 5 * r + 2)
      else (if r = 0 then 2 else 5 * r + 3)
    topPair T bits y0 A k ((c - 155) % 2)
  else if c < 237 then topPair T bits y0 A (xhK ((c - 187) / 2)) ((c - 187) % 2)
  else if c < 255 then
    (if (c - 237) % 2 = 0 then loC (RA ((c - 237) / 2)) else hiC (RA ((c - 237) / 2)))
  else if c < 4096 then 0
  else if c < 5430 then
    (if (c - xcBase (bandIdx xcBase 42 c)) % 2 = 0
      then loC (A (bandIdx xcBase 42 c) ((c - xcBase (bandIdx xcBase 42 c)) / 2))
      else hiC (A (bandIdx xcBase 42 c) ((c - xcBase (bandIdx xcBase 42 c)) / 2)))
  else 0

/-- The honest image. -/
def imageOf (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256)
    (RA : ℕ → BitVec 256) : MemImage 16 := fun c => hcell T bits y0 A RA c.val

/-- The chain answer table of an index. -/
def chainTab (CA : Fin numChains → ℕ → BitVec 256) : ℕ → ℕ → BitVec 256 :=
  fun k t => if h : k < 42 then CA ⟨k, h⟩ t else 0

/-- **The honest prover.** Query the index, the chains, the root; commit the image. -/
def prover (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec (MemImage 16) := do
  let y0 ← hash896 (P.idxInput m (decodeNonce bits) pk)
  let CA ← tabulate (fun k : Fin numChains =>
    chainAnsQ P k (LEN k.val - 1 - hd T y0 k.val) (hd T y0 k.val) (sigW bits k.val))
  let RA ← rootAnsQ P (topsOfV T bits y0 (chainTab CA)) 0 9
    (Params.rootInit (topsOfV T bits y0 (chainTab CA)))
  pure (imageOf T bits y0 (chainTab CA) RA)

/-! ## The prover under a fixed table -/

section Fixed

variable (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

/-- The index answer. -/
def y0F : BitVec 256 := ans f (P.idxInput m (decodeNonce bits) pk)

/-- The chain answers. -/
def AF : ℕ → ℕ → BitVec 256 :=
  chainTab (fun k : Fin numChains => chainAnsF P f k (LEN k.val - 1 - hd T (y0F P f pk m bits) k.val)
    (hd T (y0F P f pk m bits) k.val) (sigW bits k.val))

/-- The root answers. -/
def RAF : ℕ → BitVec 256 :=
  rootAnsF P f (topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits)) 0 9
    (Params.rootInit (topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits)))

/-- The honest image under the table. -/
def imageF : MemImage 16 :=
  imageOf T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits)

theorem fixed_prover :
    simulateQ (unifFwdAnswerImpl f) (prover P T pk m bits) = pure (imageF P T f pk m bits) := by
  unfold prover imageF RAF AF y0F
  rw [simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind,
    fixed_tabulate f _ _ (fun k => fixed_chainAns P f k _ _ _), pure_bind, simulateQ_bind,
    fixed_rootAns, pure_bind, simulateQ_pure]

end Fixed

attribute [irreducible] hcell

end

end OptimalOTS.HLG3
