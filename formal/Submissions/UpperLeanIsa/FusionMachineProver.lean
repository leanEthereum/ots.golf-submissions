import Submissions.UpperLeanIsa.FusionMachineSound

/-!
# The honest fused prover

The prover computes the index and reconstructs chain tops in dependency order. It then queries
the chain steps again with that final context to collect both output halves, followed by three
root calls. Repeated queries share answers in the cached oracle. The resulting committed image
contains constants, index words, tie patterns, accumulators, landing hints and products, chain
pairs, and root states. Under a fixed table the prover is `imageF` (`fixed_prover`).
-/

namespace OptimalOTS.HLFusion

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.HLG3 (natV ans hash896 fixed_hash896 fixed_tabulate)
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

variable (P : Fusion.Params) (T : Tab)

/-! ## Answer collection -/

/-- The answers of `n` chain steps of chain `k` from position `j`, in order. -/
def chainAnsQ (ctx : Fusion.Tops) (k : Fin numChains) : ℕ → ℕ → Word → OracleComp Spec (ℕ → BitVec 256)
  | _, 0, _ => pure (fun _ => 0)
  | j, n + 1, x => do
    let a ← hash896 (P.chainInput ctx k j x)
    let A ← chainAnsQ ctx k (j + 1) n (P.codec.slice k j a)
    pure (fun t => if t = 0 then a else A (t - 1))

/-- `chainAnsQ` under a fixed table. -/
def chainAnsF (f : HashTable) (ctx : Fusion.Tops) (k : Fin numChains) : ℕ → ℕ → Word → ℕ → BitVec 256
  | _, 0, _ => fun _ => 0
  | j, n + 1, x => fun t => if t = 0 then ans f (P.chainInput ctx k j x) else
      chainAnsF f ctx k (j + 1) n (P.codec.slice k j (ans f (P.chainInput ctx k j x))) (t - 1)

theorem fixed_chainAns (f : HashTable) (ctx : Fusion.Tops) (k : Fin numChains) (j n : ℕ) (x : Word) :
    simulateQ (unifFwdAnswerImpl f) (chainAnsQ P ctx k j n x) = pure (chainAnsF P f ctx k j n x) := by
  induction n generalizing j x with
  | zero => rfl
  | succ n ih =>
    rw [chainAnsQ, simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind, ih, pure_bind,
      simulateQ_pure]
    rfl

theorem chainValue_succ (f : HashTable) (P : Fusion.Params) (ctx : Fusion.Tops) (k : Fin numChains) :
    ∀ t j x, P.chainValue f ctx k j (t + 1) x =
      P.codec.slice k (j + t) (ans f (P.chainInput ctx k (j + t) (P.chainValue f ctx k j t x))) := by
  intro t
  induction t with
  | zero => intro j x; rfl
  | succ t ih =>
    intro j x
    show P.chainValue f ctx k (j + 1) (t + 1) _ = _
    rw [ih, show j + 1 + t = j + (t + 1) by ring]
    rfl

theorem chainAnsF_spec (f : HashTable) (ctx : Fusion.Tops) (k : Fin numChains) :
    ∀ n j x t, t < n →
      chainAnsF P f ctx k j n x t = ans f (P.chainInput ctx k (j + t) (P.chainValue f ctx k j t x)) := by
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

/-- The three root states, extended periodically only to make the recursion total. -/
def rootState (f : HashTable) (P : Fusion.Params) (tp : Fusion.Tops) : ℕ → ℕ → BitVec 256 → BitVec 256
  | _,0,st => st
  | r,n+1,st => rootState f P tp (r+1) n (f ⟨896,P.rootInput tp ⟨r%3,Nat.mod_lt _ (by decide)⟩ st⟩)

/-- The answers of `n` root calls from call `r` and state `st`, in order. -/
def rootAnsQ (tp : Fusion.Tops) : ℕ → ℕ → BitVec 256 → OracleComp Spec (ℕ → BitVec 256)
  | _, 0, _ => pure (fun _ => 0)
  | r, n + 1, st => do
    let a ← hash896 (P.rootInput tp ⟨r%3,Nat.mod_lt _ (by decide)⟩ st)
    let A ← rootAnsQ tp (r + 1) n a
    pure (fun i => if i = 0 then a else A (i - 1))

/-- `rootAnsQ` under a fixed table. -/
def rootAnsF (f : HashTable) (tp : Fusion.Tops) : ℕ → ℕ → BitVec 256 → ℕ → BitVec 256
  | _, 0, _ => fun _ => 0
  | r, n + 1, st => fun i => if i = 0 then ans f (P.rootInput tp ⟨r%3,Nat.mod_lt _ (by decide)⟩ st) else
      rootAnsF f tp (r + 1) n (ans f (P.rootInput tp ⟨r%3,Nat.mod_lt _ (by decide)⟩ st)) (i - 1)

theorem fixed_rootAns (f : HashTable) (tp : Fusion.Tops) (r n : ℕ) (st : BitVec 256) :
    simulateQ (unifFwdAnswerImpl f) (rootAnsQ P tp r n st) = pure (rootAnsF P f tp r n st) := by
  induction n generalizing r st with
  | zero => rfl
  | succ n ih =>
    rw [rootAnsQ, simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind, ih, pure_bind,
      simulateQ_pure]
    rfl

theorem rootAnsF_spec (f : HashTable) (tp : Fusion.Tops) :
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
    Fusion.Tops := fun k => if k < 42 then topOf T bits y0 A k else 0

/-- The low cell of an answer. -/
def loC (a : BitVec 256) : E := cellOfBits (a.extractLsb' 0 128)

/-- The high cell of an answer. -/
def hiC (a : BitVec 256) : E := cellOfBits (a.extractLsb' 128 128)

/-- The honest landing product before group `u`. -/
def gpV (I : Word) (u : ℕ) : E :=
  ofK (LeanIsaFieldRescale.initialProduct 86 (hxs T I 0) *
    LeanIsaFieldRescale.costFactor (∑ w ∈ Finset.range u, cost T w (hxs T I (w + 1))))

def pairK (i : ℕ) : ℕ := [12, 13, 22, 23, 33, 37, 14, 15, 21, 24, 35, 36, 1, 2, 26, 0, 7, 0, 0, 3, 4, 5, 6, 8, 9, 10, 11, 16, 17, 18, 19, 20, 25, 27, 28, 29, 30, 31, 32, 34, 38, 39, 40, 41, 0].getD i 0

/-- The physical answer pair, placing the top at offset topOff k and the unused half beside it. -/
def topPair (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (k b : ℕ) : E :=
  if b = topOff k then cellOfBits (topOf T bits y0 A k) else hiOf T y0 A k

/-- The honest value of cell `c ≥ 47`, from the index answer `y0`, the chain answers `A` and the
root answers `RA`. -/
def hcell (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256) (RA : ℕ → BitVec 256)
    (c : ℕ) : E :=
  if c < 48 then 0
  else if c=48 then oneV
  else if c=49 then gV
  else if 51 ≤ c ∧ c < 73 then cV (c-50)
  else if c=80 then loC y0
  else if c=81 then hiC y0
  else if 100 ≤ c ∧ c < 113 then fpat (c-100) (hxs T (idxOf y0) (c-100+1))
  else if 120 ≤ c ∧ c < 132 then natV (ofDigitsW gb (fun w => hxs T (idxOf y0) (w+1)) (c-120+1))
  else if 160 ≤ c ∧ c < 174 then ofK (gpow (ent (c-160) (hxs T (idxOf y0) (c-160))))
  else if 180 ≤ c ∧ c < 194 then ofK (gpow (ent (c-180) (hxs T (idxOf y0) (c-180))+1))
  else if 200 ≤ c ∧ c < 214 then gpV T (idxOf y0) (c-200)
  else if c < 256 then 0
  else if c=286 then loC (RA 0)
  else if c=287 then hiC (RA 0)
  else if c=290 then loC (RA 1)
  else if c=291 then hiC (RA 1)
  else if c=344 then loC (RA 2)
  else if c=345 then hiC (RA 2)
  else if c < 346 then topPair T bits y0 A (pairK ((c-256)/2)) ((c-256)%2)
  else if c < 4096 then 0
  else if c < 5430 then
    (if (c-xcBase (bandIdx xcBase 42 c))%2=0
      then loC (A (bandIdx xcBase 42 c) ((c-xcBase (bandIdx xcBase 42 c))/2))
      else hiC (A (bandIdx xcBase 42 c) ((c-xcBase (bandIdx xcBase 42 c))/2)))
  else 0

/-- The honest image. -/
def imageOf (bits : List Bool) (y0 : BitVec 256) (A : ℕ → ℕ → BitVec 256)
    (RA : ℕ → BitVec 256) : MemImage 16 := fun c => hcell T bits y0 A RA c.val

/-- The chain answer table of an index. -/
def chainTab (CA : Fin numChains → ℕ → BitVec 256) : ℕ → ℕ → BitVec 256 :=
  fun k t => if h : k < 42 then CA ⟨k, h⟩ t else 0

/-- **The honest prover.** Query the index, the chains, the root; commit the image. -/
def prover (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec (MemImage 16) := do
  let y0 ← hash896 (P.codec.idxInput m (decodeNonce bits) pk)
  let ctx ← P.reconFrom (effective (idxOf y0)) bits Fusion.chainOrder (fun _ => 0)
  let CA ← tabulate (fun k : Fin numChains =>
    chainAnsQ P ctx k (LEN k.val - 1 - hd T y0 k.val) (hd T y0 k.val) (sigW bits k.val))
  let RA ← rootAnsQ P (topsOfV T bits y0 (chainTab CA)) 0 3 0
  pure (imageOf T bits y0 (chainTab CA) RA)

/-! ## The prover under a fixed table -/

section Fixed

variable (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

/-- The index answer. -/
def y0F : BitVec 256 := ans f (P.codec.idxInput m (decodeNonce bits) pk)

/-- The verifier reconstruction supplies all dependency tops for answer collection. -/
def ctxF : Fusion.Tops := topsOf f P (effective (idxOf (y0F P f pk m bits))) bits

/-- The chain answers. -/
def AF : ℕ → ℕ → BitVec 256 :=
  chainTab (fun k : Fin numChains => chainAnsF P f (ctxF P f pk m bits) k (LEN k.val - 1 - hd T (y0F P f pk m bits) k.val)
    (hd T (y0F P f pk m bits) k.val) (sigW bits k.val))

/-- The root answers. -/
def RAF : ℕ → BitVec 256 :=
  rootAnsF P f (topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits)) 0 3 0

/-- The honest image under the table. -/
def imageF : MemImage 16 :=
  imageOf T bits (y0F P f pk m bits) (AF P T f pk m bits) (RAF P T f pk m bits)

theorem fixed_prover :
    simulateQ (unifFwdAnswerImpl f) (prover P T pk m bits) = pure (imageF P T f pk m bits) := by
  unfold prover imageF RAF AF ctxF topsOf y0F
  rw [simulateQ_bind, fixed_hash896, pure_bind, simulateQ_bind, Fusion.Params.fixed_reconFrom, pure_bind, simulateQ_bind,
    fixed_tabulate f _ _ (fun k => fixed_chainAns P f _ k _ _ _), pure_bind, simulateQ_bind,
    fixed_rootAns, pure_bind, simulateQ_pure]

end Fixed

attribute [irreducible] hcell

end

end OptimalOTS.HLFusion
