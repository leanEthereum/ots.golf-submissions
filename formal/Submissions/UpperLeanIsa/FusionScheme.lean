import Submissions.UpperLeanIsa.FusionOrder
import Submissions.UpperLeanIsa.Correctness

/-! Oracle algorithms for the dependency-aware construction. The signer reuses
only the certified codec; key generation and reconstruction follow the dependency order. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OptimalOTS OracleSpec OracleComp
open scoped Classical
noncomputable section

abbrev Tbl (P : Params) := Loc P → BitVec hashBits

def chainOrder : List (Fin 42) :=
  [0,12,13,17,18,22,23,27,28,32,33,37,38,29,30,31,34,35,36,39,40,41,14,15,16,19,20,21,24,25,26,1,2,7,3,4,5,6,8,9,10,11]

theorem chainOrder_values : chainOrder.map Fin.val = evaluationOrder := rfl

theorem chainOrder_permutation : chainOrder.Perm (List.finRange 42) := by decide

namespace Params
variable (P : Params)

def locationOrder : List (Loc P) :=
  chainOrder.flatMap (fun k => (List.finRange (P.codec.len k - 1)).map fun j => .inl ⟨k,j⟩) ++
    (List.finRange 3).map Sum.inr

/-- Query a location and place the answer in the immutable abstract record table. -/
def evalLocations (seeds : Fin 42 → Word) : List (Loc P) → Tbl P → OracleComp Spec (Tbl P)
  | [], y => pure y
  | a :: l, y => do
    let v ← hash (Record.input (seeds,y) a)
    evalLocations seeds l (Function.update y a v)

/-- Key generation queries all 625 chain locations and then the three roots. -/
def keygen : OracleComp Spec (PublicKey × SecretKey) := do
  let seeds ← tabulate (fun _ : Fin 42 => sampleBits 128)
  let y ← P.evalLocations seeds P.locationOrder (fun _ => 0)
  let ξ : Record P := (seeds,y)
  pure (ξ.pk,ξ.sk)

def chainStep (t : Tops) (k : Fin 42) (j : ℕ) (x : Word) : OracleComp Spec Word :=
  P.codec.slice k j <$> hash (P.chainInput t k j x)

def chain (t : Tops) (k : Fin 42) : ℕ → ℕ → Word → OracleComp Spec Word
  | _,0,x => pure x
  | j,n+1,x => do
    let y ← P.chainStep t k j x
    chain t k (j+1) n y

/-- Reconstruct the chains whose dependencies have already been reconstructed. -/
def reconFrom (I : Index) (bits : List Bool) : List (Fin 42) → Tops → OracleComp Spec Tops
  | [],t => pure t
  | k :: l,t => do
    let x ← P.chain t k (P.codec.len k - 1 - P.codec.digit I k) (P.codec.digit I k) (decodeWord bits k)
    reconFrom I bits l (Function.update t k.val x)

def rootFrom (t : Tops) : List (Fin 3) → BitVec 256 → OracleComp Spec (BitVec 256)
  | [],st => pure st
  | r :: l,st => do
    let v ← hash (P.rootInput t r st)
    rootFrom t l v

def root (t : Tops) : OracleComp Spec PublicKey :=
  (fun v => v.extractLsb' 0 128) <$> P.rootFrom t [0,1,2] 0

def verify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool := do
  if bits.length ≠ sigBits then return false
  let I ← P.codec.index m (decodeNonce bits) pk
  if ¬ P.codec.Accepted I then return false
  let tops ← P.reconFrom I bits chainOrder (fun _ => 0)
  let r ← P.root tops
  pure (r == pk)

def scheme : OracleAlgorithm.Scheme where
  SecretKey := SecretKey
  keygen := P.keygen
  sign := P.codec.sign
  verify := P.verify

/-- Deterministic DAG evaluation under a fixed table. -/
def evalLocationsValue (f : HashTable) (seeds : Fin 42 → Word) : List (Loc P) → Tbl P → Tbl P
  | [],y => y
  | a :: l,y => evalLocationsValue f seeds l (Function.update y a (f ⟨896,Record.input (seeds,y) a⟩))

theorem fixed_evalLocations (f : HashTable) (seeds : Fin 42 → Word) (l : List (Loc P)) (y : Tbl P) :
    simulateQ (unifFwdAnswerImpl f) (P.evalLocations seeds l y) = pure (P.evalLocationsValue f seeds l y) := by
  induction l generalizing y with
  | nil => rfl
  | cons a l ih =>
    simp only [evalLocations, simulateQ_bind, Layer.Params.fixed_hash, pure_bind, ih]
    rfl

end Params
end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
