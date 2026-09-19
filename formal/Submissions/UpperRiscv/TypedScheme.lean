import OptimalOTS.OracleAlgorithm

/-!
# Oracle algorithms with a typed signature and an injective encoding

An internal proof device of this root, not part of the contract. The contract's
`OracleAlgorithm.Scheme` transmits bit strings; here signatures have any type with an injective
bit encoding, as for DAG signatures (nonce, disclosed values). `WireAdapter` transfers every
requirement to the scheme on the encoded bit strings.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS

/-- Key generation, signing and verification with an injective signature encoding. -/
structure TypedScheme where
  SecretKey : Type
  Signature : Type
  encodeSignature : Signature → List Bool
  encodeSignature_injective : Function.Injective encodeSignature
  keygen : OracleComp Spec (PublicKey × SecretKey)
  sign : SecretKey → Message → OracleComp Spec (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp Spec Bool

namespace TypedScheme

/-- A one-signature attacker. -/
structure Adversary (S : TypedScheme) where
  State : Type
  choose : PublicKey → OracleComp Spec (Message × State)
  forge : State → Option S.Signature → OracleComp Spec (Message × S.Signature)

/-- The strong-forgery experiment. -/
def experiment (S : TypedScheme) (A : S.Adversary) : OracleComp Spec Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

def Secure (S : TypedScheme) : Prop :=
  ∀ (A : S.Adversary) (B : ℕ), CostAtMost (S.experiment A) B →
    probTrue (S.experiment A) < (B : ℝ≥0∞) / 2 ^ securityBits

def VerifyCostAtMost (S : TypedScheme) (c : ℕ) : Prop :=
  ∀ pk m σ, CostAtMost (S.verify pk m σ) c

def VerifyDeterministic (S : TypedScheme) : Prop :=
  ∀ pk m σ, Deterministic (S.verify pk m σ)

def KeygenCostAtMost (S : TypedScheme) (b : ℕ) : Prop := CostAtMost S.keygen b

def SignCostAtMost (S : TypedScheme) (b : ℕ) : Prop :=
  ∀ sk m, CostAtMost (S.sign sk m) b

def SignatureSizeAtMost (S : TypedScheme) (n : ℕ) : Prop :=
  ∀ sk m σ, some σ ∈ support (S.sign sk m) → (S.encodeSignature σ).length ≤ n

def RejectsOversized (S : TypedScheme) (n : ℕ) : Prop :=
  ∀ pk m σ, n < (S.encodeSignature σ).length → true ∉ support (S.verify pk m σ)

def Correct (S : TypedScheme) : Prop := ∀ message : PublicKey → Message,
  probTrue (do
    let (pk, sk) ← S.keygen
    let m := message pk
    let σ ← S.sign sk m
    match σ with
    | none => return false
    | some s => return !(← S.verify pk m s)) = 0

def SigningFailureAtMost (S : TypedScheme) (ε : ℝ≥0∞) : Prop :=
  ∀ message : PublicKey → Message,
  probTrue (do
    let (pk, sk) ← S.keygen
    return (← S.sign sk (message pk)).isNone) ≤ ε

/-- Every requirement except security, with signing failure at most `ε`. -/
structure Admissible (S : TypedScheme) (ε : ℝ≥0∞) : Prop where
  failure_lt_one : ε < 1
  correct : S.Correct
  verifyDeterministic : S.VerifyDeterministic
  signingFailure : S.SigningFailureAtMost ε
  signatureSize : S.SignatureSizeAtMost maxSignatureBits
  rejectsOversized : S.RejectsOversized maxSignatureBits
  keygenCost : S.KeygenCostAtMost keygenBudget
  signCost : S.SignCostAtMost signBudget

end TypedScheme

end OptimalOTS
