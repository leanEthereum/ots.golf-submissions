import Submissions.UpperLeanIsa.MachineSound

/-!
# The honest HL-FLAT-A prover

The honest prover queries the oracle exactly as the verifier does: the index, then for each chain
`k` its `d k` steps from the revealed word (`d = digits of the index`), then the ten root calls.
It commits the image whose every cell is a pure function of the input and those answers
(`hcell`): the constants, the index pair, the tie patterns and accumulators, the landing hints
`H_k = g ^ entryOf k (d k)`, `H'_k = H_k · g`, the landing products, the chain pairs and the root
states. Under a fixed table the prover is `imageF` (`fixed_prover`).
-/

namespace OptimalOTS.HLFlat

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

/-! ## Answer collection -/

/-- The answers of `n` chain steps of chain `k` from position `j`, in order. -/
def chainAnsQ (k : Fin numChains) : ℕ → ℕ → Word → OracleComp Spec (ℕ → BitVec 256)
  | _, 0, _ => pure (fun _ => 0)
  | j, n + 1, x => do
    let a ← hash896 (FP.chainInput k j x)
    let A ← chainAnsQ k (j + 1) n (a.extractLsb' 0 128)
    pure (fun t => if t = 0 then a else A (t - 1))

/-- `chainAnsQ` under a fixed table. -/
def chainAnsF (f : HashTable) (k : Fin numChains) : ℕ → ℕ → Word → ℕ → BitVec 256
  | _, 0, _ => fun _ => 0
  | j, n + 1, x => fun t => if t = 0 then ans f (FP.chainInput k j x) else
      chainAnsF f k (j + 1) n ((ans f (FP.chainInput k j x)).extractLsb' 0 128) (t - 1)

theorem fixed_chainAns (f : HashTable) (k : Fin numChains) (j n : ℕ) (x : Word) :
    simulateQ (unifFwdAnswerImpl f) (chainAnsQ k j n x) = pure (chainAnsF f k j n x) := by
  induction n generalizing j x with
  | zero => rfl
  | succ n ih =>
    rw [chainAnsQ, simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind, ih, pure_bind,
      simulateQ_pure]
    rfl

theorem chainValue_succ (f : HashTable) (P : Params) (k : Fin numChains) :
    ∀ t j x, chainValue f P k j (t + 1) x =
      (ans f (P.chainInput k (j + t) (chainValue f P k j t x))).extractLsb' 0 128 := by
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
      chainAnsF f k j n x t = ans f (FP.chainInput k (j + t) (chainValue f FP k j t x)) := by
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
    let a ← hash896 (FP.rootInput tp r st)
    let A ← rootAnsQ tp (r + 1) n a
    pure (fun i => if i = 0 then a else A (i - 1))

/-- `rootAnsQ` under a fixed table. -/
def rootAnsF (f : HashTable) (tp : Fin numChains → Word) : ℕ → ℕ → BitVec 256 → ℕ → BitVec 256
  | _, 0, _ => fun _ => 0
  | r, n + 1, st => fun i => if i = 0 then ans f (FP.rootInput tp r st) else
      rootAnsF f tp (r + 1) n (ans f (FP.rootInput tp r st)) (i - 1)

theorem fixed_rootAns (f : HashTable) (tp : Fin numChains → Word) (r n : ℕ) (st : BitVec 256) :
    simulateQ (unifFwdAnswerImpl f) (rootAnsQ tp r n st) = pure (rootAnsF f tp r n st) := by
  induction n generalizing r st with
  | zero => rfl
  | succ n ih =>
    rw [rootAnsQ, simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind, ih, pure_bind,
      simulateQ_pure]
    rfl

theorem rootAnsF_spec (f : HashTable) (tp : Fin numChains → Word) :
    ∀ n r st i, i < n → rootAnsF f tp r n st i = rootState f FP tp r (i + 1) st := by
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

/-- Digit `k` of the index `I`. -/
def dg (I : Word) (k : ℕ) : ℕ := digitW Flat.wid I.toNat k

/-- Signature cell `k`. -/
def sigW (bits : List Bool) (k : ℕ) : Word := ofBits 128 ((bits.drop (128 * k)).take 128)

/-- The index of the index answer `y0`. -/
def idxOf (y0 : BitVec 256) : Word := y0.extractLsb' 0 128

/-- The chain top of chain `k` (the last answer's low half, or the revealed word). -/
def topOf (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (k : ℕ) : Word :=
  if dg (idxOf y0) k = 0 then sigW bits k else (A k (dg (idxOf y0) k - 1)).extractLsb' 0 128

/-- The high half of chain `k`'s last answer (zero when it has no step). -/
def hiOf (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (k : ℕ) : E :=
  if dg (idxOf y0) k = 0 then 0 else cellOfBits ((A k (dg (idxOf y0) k - 1)).extractLsb' 128 128)

/-- The tops as a vector. -/
def topsOfV (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) :
    Fin numChains → Word := fun k => topOf bits y0 A k.val

/-- The low cell of an answer. -/
def loC (a : BitVec 256) : E := cellOfBits (a.extractLsb' 0 128)

/-- The high cell of an answer. -/
def hiC (a : BitVec 256) : E := cellOfBits (a.extractLsb' 128 128)

/-- The honest value of cell `c ≥ 47`, from the index answer `y0`, the chain answers `A` and the
root answers `RA`. -/
def hcell (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (RA : ℕ → BitVec 256)
    (c : ℕ) : E :=
  if c < 48 then 0
  else if c = 48 then oneV
  else if c = 49 then natV 10
  else if c = 50 then gV
  else if c = 51 then k0V
  else if c < 59 then natV (c - 49)
  else if c < 101 then frameV (c - 59)
  else if c = 101 then loC y0
  else if c = 102 then hiC y0
  else if c < 145 then fpat (c - 103) (dg (idxOf y0) (c - 103))
  else if c < 186 then natV (ofDigitsW Flat.wid (dg (idxOf y0)) (c - 144))
  else if c < 228 then ofK (gpow (entryOf (c - 186) (dg (idxOf y0) (c - 186))))
  else if c < 270 then ofK (gpow (entryOf (c - 228) (dg (idxOf y0) (c - 228)) + 1))
  else if c < 311 then
    ofK (gpow (∑ j ∈ Finset.range (c - 269), entryOf j (dg (idxOf y0) j)))
  else if c < 320 then 0
  else if c < 404 then
    (if (c - 320) % 2 = 0 then cellOfBits (topOf bits y0 A ((c - 320) / 2))
      else hiOf y0 A ((c - 320) / 2))
  else if c < 410 then 0
  else if c = 410 then cellOfBits (topOf bits y0 A 0)
  else if c = 411 then cellOfBits (topOf bits y0 A 1)
  else if c = 412 then hiOf y0 A 1
  else if c < 1024 then 0
  else if c < 2368 then
    (if (c - 1024) % 2 = 0 then loC (A ((c - 1024) / 32) ((c - 1024) % 32 / 2))
      else hiC (A ((c - 1024) / 32) ((c - 1024) % 32 / 2)))
  else if c < 2400 then 0
  else if c < 2420 then
    (if (c - 2400) % 2 = 0 then loC (RA ((c - 2400) / 2)) else hiC (RA ((c - 2400) / 2)))
  else 0

/-- The honest image. -/
def imageOf (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256)
    (RA : ℕ → BitVec 256) : MemImage 16 := fun c => hcell bits y0 A RA c.val

/-- The chain answer table of an index. -/
def chainTab (CA : Fin numChains → ℕ → BitVec 256) : ℕ → ℕ → BitVec 256 :=
  fun k t => if h : k < 42 then CA ⟨k, h⟩ t else 0

/-- **The honest prover.** Query the index, the chains, the root; commit the image. -/
def prover (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec (MemImage 16) := do
  let y0 ← hash896 (FP.idxInput m (decodeNonce bits) pk)
  let CA ← tabulate (fun k : Fin numChains =>
    chainAnsQ k (W k.val - 1 - dg (idxOf y0) k.val) (dg (idxOf y0) k.val) (sigW bits k.val))
  let RA ← rootAnsQ (topsOfV bits y0 (chainTab CA)) 0 10
    (Params.rootInit (topsOfV bits y0 (chainTab CA)))
  pure (imageOf bits y0 (chainTab CA) RA)

/-! ## The prover under a fixed table -/

section Fixed

variable (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

/-- The index answer. -/
def y0F : BitVec 256 := ans f (FP.idxInput m (decodeNonce bits) pk)

/-- The chain answers. -/
def AF : ℕ → ℕ → BitVec 256 :=
  chainTab (fun k : Fin numChains => chainAnsF f k (W k.val - 1 - dg (idxOf (y0F f pk m bits)) k.val)
    (dg (idxOf (y0F f pk m bits)) k.val) (sigW bits k.val))

/-- The root answers. -/
def RAF : ℕ → BitVec 256 :=
  rootAnsF f (topsOfV bits (y0F f pk m bits) (AF f pk m bits)) 0 10
    (Params.rootInit (topsOfV bits (y0F f pk m bits) (AF f pk m bits)))

/-- The honest image under the table. -/
def imageF : MemImage 16 := imageOf bits (y0F f pk m bits) (AF f pk m bits) (RAF f pk m bits)

theorem fixed_prover : simulateQ (unifFwdAnswerImpl f) (prover pk m bits) = pure (imageF f pk m bits) := by
  unfold prover imageF RAF AF y0F
  rw [simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind,
    fixed_tabulate f _ _ (fun k => fixed_chainAns f k _ _ _), pure_bind, simulateQ_bind,
    fixed_rootAns, pure_bind, simulateQ_pure]

end Fixed

attribute [irreducible] hcell

end

end OptimalOTS.HLFlat
