import OptimalOTS.OracleAlgorithm
import OptimalOTS.LeanIsaMachine
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Layer schemes: the generic 42-chain one-time signature

A *layer scheme* has 42 hash chains, chain `k` with `len k` positions `0, …, len k - 1`
(so `len k - 1` steps), one 127-bit *index* per signature, and accepts an index `I` when the
remaining-step digits `digit I k < len k` sum to the layer `layer`. The accepted digit vectors
form an antichain, which replaces the Winternitz checksum.

Every oracle query is one leanISA `BLAKE2S`, i.e. one 896-bit `LeanIsa.hashInput cv block md`,
and the three query *shapes* are separated by the metadata cell:

* chain step of chain `k` at position `j`: `cv = P.cv`, block `m = [x, A, B, C]` with the three
  tag cells `P.tag k j`, `md = P.chainMd`; the next word is the answer slice `P.slice k j`: the
  high half for the step that produces the top of a `P.hiTop` chain, the low half otherwise;
* index: `cv = P.cv`, block `m = [msg.lo, msg.hi, η, pk]`, `md = P.idxMd`; the index is bits
  `1, …, 127` of the answer (`idxAns`);
* root call `r < 9` (tagged, "R9"): call 0 has `cv = (top 0, top 1)` and block
  `[top 2, …, top 5]`; call `r = 1, …, 7` has `cv = (top (5r+1), top (5r+2))` and block
  `[lo st, top (5r+3), top (5r+4), top (5r+5)]` with `st` the previous 256-bit answer; call 8
  has `cv = st` and block `[top 41, 0, 0, 0]`; `md = P.rootMd r`. `pk` is the low half of the
  last answer.

The signature is the 42 revealed words followed by the 128-bit nonce, `43 · 128 = 5504` bits.
The signer draws fresh uniform untried nonces, at most `trials = 2 ^ 19` of them; the secret key
stores the whole chain table and the public key, so signing only makes index queries.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

/-- A 128-bit chain word (one canonical cell). -/
abbrev Word := BitVec 128
/-- The signing nonce: one full signature cell. -/
abbrev Nonce := BitVec 128
/-- The index word: bits `1, …, 127` of the index answer (bit `0` is not read). -/
abbrev IdxWord := BitVec 127
/-- The index word of an index answer. -/
abbrev idxAns {n : ℕ} (y : BitVec n) : IdxWord := y.extractLsb' 1 127
/-- Number of chains. -/
abbrev numChains : ℕ := 42
/-- Signature length in bits: 42 words and the nonce. -/
def sigBits : ℕ := 5504
/-- Maximal number of signing trials: `signBudget / blockCost 896`. -/
def trials : ℕ := 2 ^ 19

/-- The parameters of a layer scheme. -/
structure Params where
  /-- Positions of chain `k`; its digit is `< len k`. -/
  len : Fin numChains → ℕ
  /-- The accepted layer: the digits sum to `layer`. -/
  layer : ℕ
  /-- Digit (remaining steps) of chain `k` read from the index. -/
  digit : IdxWord → Fin numChains → ℕ
  /-- The three tag cells `A, B, C` of the step of chain `k` at position `j`. -/
  tag : Fin numChains → ℕ → Fin 3 → Word
  /-- The constant chaining value of chain steps and the index query. -/
  cv : BitVec 256
  /-- Metadata of chain steps. -/
  chainMd : Word
  /-- Metadata of the index query. -/
  idxMd : Word
  /-- Metadata of root call `r`. -/
  rootMd : ℕ → Word
  /-- Chains whose top is the high half of the answer of their last step. -/
  hiTop : Fin numChains → Bool

namespace Params

variable (P : Params)

/-! ## Queries -/

/-- The chain step of chain `k` at position `j`: `m = [x, A, B, C]`. -/
def chainInput (k : Fin numChains) (j : ℕ) (x : Word) : BitVec 896 :=
  LeanIsa.hashInput P.cv (P.tag k j 2 ++ P.tag k j 1 ++ P.tag k j 0 ++ x) P.chainMd

/-- The index query: `m = [msg.lo, msg.hi, η, pk]`. -/
def idxInput (m : Message) (η : Nonce) (pk : PublicKey) : BitVec 896 :=
  LeanIsa.hashInput P.cv (pk ++ η ++ m) P.idxMd

/-- Bit offset of the answer slice that the step of chain `k` at position `j` keeps: `128` for
the step producing the top (`j + 2 = len k`) of a `hiTop` chain, `0` otherwise. -/
def stepOff (k : Fin numChains) (j : ℕ) : ℕ := if P.hiTop k ∧ j + 2 = P.len k then 128 else 0

/-- The next word of the step of chain `k` at position `j`: a 128-bit slice of the answer. -/
def slice (k : Fin numChains) (j : ℕ) (y : BitVec hashBits) : Word :=
  y.extractLsb' (P.stepOff k j) 128

/-- The tops, read by position (zero past the end). -/
def topAt (t : Fin numChains → Word) (i : ℕ) : Word :=
  if h : i < numChains then t ⟨i, h⟩ else 0

/-- The chaining value of root call `r` after state `st`: the state itself for calls `0` and
`8`, the pair `(top (5r+1), top (5r+2))` for calls `1, …, 7`. -/
def rootCv (t : Fin numChains → Word) (r : ℕ) (st : BitVec 256) : BitVec 256 :=
  if r = 0 ∨ 8 ≤ r then st else topAt t (5 * r + 2) ++ topAt t (5 * r + 1)

/-- The block of root call `r` after state `st`: `[top 2, …, top 5]` for call 0,
`[lo st, top (5r+3), top (5r+4), top (5r+5)]` for calls `1, …, 7`, `[top 41, 0, 0, 0]` for
call 8. -/
def rootBlock (t : Fin numChains → Word) (r : ℕ) (st : BitVec 256) : BitVec 512 :=
  if r = 0 then topAt t 5 ++ topAt t 4 ++ topAt t 3 ++ topAt t 2
  else if r < 8 then
    topAt t (5 * r + 5) ++ topAt t (5 * r + 4) ++ topAt t (5 * r + 3) ++ st.extractLsb' 0 128
  else (0 : Word) ++ (0 : Word) ++ (0 : Word) ++ topAt t 41

/-- Root call `r` under the state `st`. -/
def rootInput (t : Fin numChains → Word) (r : ℕ) (st : BitVec 256) : BitVec 896 :=
  LeanIsa.hashInput (rootCv t r st) (rootBlock t r st) (P.rootMd r)

/-- The initial root state: the cv pair `(top 0, top 1)`. -/
def rootInit (t : Fin numChains → Word) : BitVec 256 := topAt t 1 ++ topAt t 0

/-! ## Oracle programs -/

/-- One chain step: the answer slice `P.slice k j`. -/
def chainStep (k : Fin numChains) (j : ℕ) (x : Word) : OracleComp Spec Word :=
  P.slice k j <$> hash (P.chainInput k j x)

/-- `n` steps of chain `k` from position `j`. -/
def chain (k : Fin numChains) : ℕ → ℕ → Word → OracleComp Spec Word
  | _, 0, x => pure x
  | j, n + 1, x => do
    let y ← P.chainStep k j x
    chain k (j + 1) n y

/-- The chain values at positions `j, …, j + n` from `x` at position `j`. -/
def chainList (k : Fin numChains) : ℕ → ℕ → Word → OracleComp Spec (List Word)
  | _, 0, x => pure [x]
  | j, n + 1, x => do
    let y ← P.chainStep k j x
    let ys ← chainList k (j + 1) n y
    pure (x :: ys)

/-- The index of a message and nonce under a public key: bits `1, …, 127` of the answer. -/
def index (m : Message) (η : Nonce) (pk : PublicKey) : OracleComp Spec IdxWord :=
  idxAns <$> hash (P.idxInput m η pk)

/-- Root calls `r, …, r + n - 1` from state `st`. -/
def rootFrom (t : Fin numChains → Word) : ℕ → ℕ → BitVec 256 → OracleComp Spec (BitVec 256)
  | _, 0, st => pure st
  | r, n + 1, st => do
    let st' ← hash (P.rootInput t r st)
    rootFrom t (r + 1) n st'

/-- The tagged 9-call root; the public key is the low half of the last state. -/
def root (t : Fin numChains → Word) : OracleComp Spec PublicKey :=
  (fun y => y.extractLsb' 0 128) <$> P.rootFrom t 0 9 (rootInit t)

/-- Acceptance: the digits of the index sum to the layer. -/
def Accepted (I : IdxWord) : Prop := ∑ k : Fin numChains, P.digit I k = P.layer

instance (I : IdxWord) : Decidable (P.Accepted I) := by unfold Accepted; infer_instance

/-- The number of accepted indices. -/
def numValid : ℕ := (Finset.univ.filter fun I : IdxWord => P.Accepted I).card

end Params

/-- Run `f` on `0, …, n - 1` in order. -/
def tabulate {α : Type} : {n : ℕ} → (Fin n → OracleComp Spec α) → OracleComp Spec (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, f => do
    let x ← f 0
    let xs ← tabulate (fun i : Fin n => f i.succ)
    pure (Fin.cases x xs)

/-- The secret key: the chain table (chain `k`'s values at positions `0, …, len k - 1`) and the
public key. -/
structure SecretKey where
  table : Fin numChains → List Word
  pk : PublicKey

/-- Signature encoding: the 42 words, then the nonce, 128 bits each, least significant first. -/
def encode (xs : Fin numChains → Word) (η : Nonce) : List Bool :=
  (List.ofFn xs).flatMap toBits ++ toBits η

/-- The word of chain `k`: signature cell `k` (machine cell `4 + k`). -/
def decodeWord (bits : List Bool) (k : Fin numChains) : Word :=
  ofBits 128 ((bits.drop (128 * k.val)).take 128)

/-- The nonce: signature cell 42 (machine cell 46). -/
def decodeNonce (bits : List Bool) : Nonce := ofBits 128 ((bits.drop 5376).take 128)

namespace Params

variable (P : Params)

/-- The revealed word of chain `k` for index `I`: position `len k - 1 - digit I k`. -/
def revealed (sk : SecretKey) (I : IdxWord) (k : Fin numChains) : Word :=
  (sk.table k).getD (P.len k - 1 - P.digit I k) 0

/-- Key generation: 42 uniform seeds, the full chain tables, the root. -/
def keygen : OracleComp Spec (PublicKey × SecretKey) := do
  let seeds ← tabulate (fun _ : Fin numChains => sampleBits 128)
  let tables ← tabulate (fun k => P.chainList k 0 (P.len k - 1) (seeds k))
  let pk ← P.root (fun k => (tables k).getD (P.len k - 1) 0)
  pure (pk, ⟨tables, pk⟩)

/-- The signing loop: at most `k` fresh uniform nonces outside `tried`. -/
def signLoop (sk : SecretKey) (m : Message) :
    ℕ → Finset Nonce → OracleComp Spec (Option (List Bool))
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp Spec (Fin (fresh.card - 1 + 1)))
      let η : Nonce := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let I ← P.index m η sk.pk
      if P.Accepted I then
        return some (encode (P.revealed sk I) η)
      else
        signLoop sk m k (insert η tried)
    else
      pure none

/-- Signing: at most `trials` fresh nonces. Irreducible, so that elaboration never unfolds the
`2 ^ 19`-step loop; use `sign_eq`. -/
@[irreducible] def sign (sk : SecretKey) (m : Message) : OracleComp Spec (Option (List Bool)) :=
  P.signLoop sk m trials ∅

theorem sign_eq (sk : SecretKey) (m : Message) : P.sign sk m = P.signLoop sk m trials ∅ := by
  unfold sign; rfl

/-- Verification: length, index, layer, the chains from the revealed words, the root. -/
def verify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool := do
  if bits.length ≠ sigBits then return false
  let I ← P.index m (decodeNonce bits) pk
  if ¬ P.Accepted I then return false
  let tops ← tabulate (fun k => P.chain k (P.len k - 1 - P.digit I k) (P.digit I k)
    (decodeWord bits k))
  let r ← P.root tops
  pure (r == pk)

/-- The layer scheme in the contract's shape. -/
def scheme : OracleAlgorithm.Scheme where
  SecretKey := SecretKey
  keygen := P.keygen
  sign := P.sign
  verify := P.verify

end Params

end OptimalOTS.LeanIsaBaseline.Layer
