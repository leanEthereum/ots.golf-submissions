import Submissions.LowerGenerality1.PatternAttack
import Submissions.LowerGenerality1.PatternGoods
import Submissions.LowerGenerality1.PatternHelpers

/-! Assembly of the bare-oracle forgery attack from support and probability bounds. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.PatternAttack

open OptimalOTS.Dag


open BareLower

variable (S : Scheme)

attribute [local irreducible] signIdx signIdxLoop Scheme.sign Scheme.signLoop
  weakExperiment forge adversary Graph.encode Scheme.hashPattern Scheme.samePattern goodIndices

/-- The continuation after the signer has selected its nonce and disclosure index. -/
def afterSign (T : ℕ) (pk : PublicKey) (x : S.graph.Assignment)
    (m : Message) (r : Option (Nonce × Fin numCuts)) :
    OracleComp Spec Bool := do
  let σ := r.map fun p => (p.1, S.graph.encode (S.sets p.2) x)
  let out ← forge S T m σ
  let ok ← S.verify pk out.1 out.2
  return ok && (σ.isNone || decide (out.1 ≠ m))

theorem experiment_eq (T : ℕ) :
    weakExperiment S (adversary S T) = (do
      let (pk,x) ← S.keygen
      let m ← sampleBits msgBits
      let r ← signIdx m
      afterSign S T pk x m r) := by
  simp only [weakExperiment, adversary, sign_eq_map, afterSign,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

theorem afterSign_some (T : ℕ) (x : S.graph.Assignment) (m : Message)
    (η : Nonce) (i : Fin numCuts) :
    afterSign S T (S.publicKey x) x m (some (η,i)) =
      forge S T m (some (η,S.graph.encode (S.sets i) x)) >>= check S (S.publicKey x) m := by
  simp only [afterSign, Option.map_some, Option.isNone_some, Bool.false_or, check]
  rfl

end OptimalOTS.PatternAttack
