import OptimalOTS.OracleAlgorithm
import OptimalOTS.LeanIsaMachine
import Submissions.UpperLeanIsa.Encoding

/-! Initial Winternitz algorithm specification. All queries have the exact 896-bit shape
available to leanISA. This file does not claim a security certificate or machine refinement. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp

abbrev Word := BitVec 128
abbrev Words := Fin 39 → Word

def tabulate {α : Type} : {n : ℕ} → (Fin n → OracleComp Spec α) →
    OracleComp Spec (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, f => do
    let x ← f 0
    let xs ← tabulate (fun i : Fin n => f i.succ)
    pure (Fin.cases x xs)

/-- Position-specific chain queries. The chain identifier and position are paid input bits. -/
def chainInput (i j : ℕ) (x : Word) : BitVec 896 :=
  LeanIsa.hashInput 0
    ((0 : BitVec 128) ++ BitVec.ofNat 128 j ++ BitVec.ofNat 128 i ++ x) 1

def chainStep (i j : ℕ) (x : Word) : OracleComp Spec Word :=
  (fun y => y.extractLsb' 0 128) <$> hash (chainInput i j x)

def chain (i j : ℕ) : ℕ → Word → OracleComp Spec Word
  | 0, x => pure x
  | n + 1, x => do
    let y ← chainStep i j x
    chain i (j + 1) n y

/-- Root absorption includes the number of remaining words in its metadata.
The 39 root positions use tags 40 down to 2; chain steps use tag 1. -/
def absorb (remaining : ℕ) (cv : BitVec 256) (x : Word) : OracleComp Spec (BitVec 256) :=
  hash (LeanIsa.hashInput cv (x.setWidth 512) (BitVec.ofNat 128 (2 + remaining)))

def rootFold : List Word → BitVec 256 → OracleComp Spec (BitVec 256)
  | [], cv => pure cv
  | x :: xs, cv => do
    let next ← absorb xs.length cv x
    rootFold xs next

def root (xs : Words) : OracleComp Spec PublicKey :=
  (fun y => y.extractLsb' 0 128) <$> rootFold (List.ofFn xs) 0

def encode (xs : Words) : List Bool := (List.ofFn xs).flatMap toBits

def decode (bits : List Bool) : Words :=
  fun i => ofBits 128 ((bits.drop (128 * i.val)).take 128)

def keygen : OracleComp Spec (PublicKey × Words) := do
  let sk ← tabulate (fun _ : Fin 39 => sampleBits 128)
  let endpoints ← tabulate (fun i : Fin 39 => chain i.val 0 127 (sk i))
  let pk ← root endpoints
  pure (pk, sk)

def sign (sk : Words) (m : Message) : OracleComp Spec (Option (List Bool)) := do
  let xs ← tabulate (fun i : Fin 39 => chain i.val 0 (digit m i) (sk i))
  pure (some (encode xs))

def verify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool := do
  if bits.length ≠ 4992 then return false
  let xs := decode bits
  let endpoints ← tabulate (fun i : Fin 39 =>
    chain i.val (digit m i) (127 - digit m i) (xs i))
  let reconstructed ← root endpoints
  pure (reconstructed == pk)

def scheme : OracleAlgorithm.Scheme where
  SecretKey := Words
  keygen := keygen
  sign := sign
  verify := verify

end OptimalOTS.LeanIsaBaseline
