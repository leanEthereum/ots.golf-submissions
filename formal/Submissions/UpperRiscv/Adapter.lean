import Submissions.UpperRiscv.TypedScheme
import Submissions.UpperRiscv.GScheme
import Submissions.UpperRiscv.Payload

/-!
Every DAG scheme defines a generic oracle algorithm with the same wire data and oracle programs.
The embedding preserves and reflects strong security; it does not establish generic admissibility.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace AlgorithmAdapter

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- The DAG signature's actual wire contents: nonce bits followed by disclosed bits. -/
def encodeSignature (σ : Signature) : List Bool := toBits σ.1 ++ Payload.unpermute σ.2

theorem toBits_injective {n : ℕ} : Function.Injective (@toBits n) := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h' := congrArg (fun l : List Bool => l[i]?) h
  simpa [toBits, hi] using h'

theorem encodeSignature_injective : Function.Injective (@encodeSignature) := by
  intro a b h
  have hn : toBits a.1 = toBits b.1 := by
    have ht := congrArg (List.take nonceBits) h
    simpa [encodeSignature, toBits] using ht
  have hp := toBits_injective hn
  have ht : a.2 = b.2 := by
    exact Payload.unpermute_injective (List.append_cancel_left (by simpa only [encodeSignature, hn] using h))
  exact Prod.ext hp ht

@[simp] theorem length_encodeSignature (σ : Signature) :
    (encodeSignature σ).length = nonceBits + σ.2.length := by
  simp [encodeSignature, toBits]

end AlgorithmAdapter

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- Same key generation, signing, verification and wire data; only the interface changes. -/
def GScheme.toAlgorithm (S : GScheme) : TypedScheme where
  SecretKey := S.graph.Assignment
  Signature := Signature
  encodeSignature := AlgorithmAdapter.encodeSignature
  encodeSignature_injective := AlgorithmAdapter.encodeSignature_injective
  keygen := S.keygen
  sign := S.sign
  verify := S.verify

namespace AlgorithmAdapter

variable (S : GScheme)

def toDAGAdversary (A : S.toAlgorithm.Adversary) : Adversary where
  State := A.State
  choose := A.choose
  forge := A.forge

def fromDAGAdversary (A : Adversary) : S.toAlgorithm.Adversary where
  State := A.State
  choose := A.choose
  forge := A.forge

/-- The adapter preserves the entire forgery experiment, including every party's queries. -/
theorem experiment_eq (A : S.toAlgorithm.Adversary) :
    S.toAlgorithm.experiment A = GScheme.experiment S (toDAGAdversary S A) := by
  simp only [TypedScheme.experiment, experiment, GScheme.toAlgorithm, toDAGAdversary]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr
  intro ok
  congr 1
  by_cases h : signed.map (fun s => (chosen.1, s)) ≠ some (forged.1, forged.2) <;> simp [h]

theorem experiment_fromDAG_eq (A : Adversary) :
    S.toAlgorithm.experiment (fromDAGAdversary S A) = GScheme.experiment S A := by
  simp only [TypedScheme.experiment, experiment, GScheme.toAlgorithm, fromDAGAdversary]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr
  intro ok
  congr 1
  by_cases h : signed.map (fun s => (chosen.1, s)) ≠ some (forged.1, forged.2) <;> simp [h]

/-- The embedding preserves and reflects the exact security requirement. -/
theorem secure_iff : S.toAlgorithm.Secure ↔ S.Secure := by
  constructor
  · intro h A B hB
    have he := experiment_fromDAG_eq S A
    rw [← he] at hB ⊢
    exact h (fromDAGAdversary S A) B hB
  · intro h A B hB
    rw [experiment_eq] at hB ⊢
    exact h (toDAGAdversary S A) B hB

end AlgorithmAdapter
end OptimalOTS
