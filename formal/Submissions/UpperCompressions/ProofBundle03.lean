import Submissions.UpperCompressions.ProofBundle02
import OptimalOTS.Dag
import Submissions.UpperCompressions.ProofBundle00
import OptimalOTS.Model

section

/-! Verification never uses private randomness: every query of `Scheme.verify` is a hash query. -/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace Deterministic

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable {α β : Type}

theorem of_pure (x : α) : Deterministic (pure x : OracleComp Spec α) := trivial

theorem bind {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    (h₁ : Deterministic oa) (h₂ : ∀ x, Deterministic (ob x)) :
    Deterministic (oa >>= ob) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using h₂ x
  | query_bind t mx ih =>
    unfold Deterministic at h₁ ⊢
    rw [isQueryBound_query_bind_iff] at h₁
    rw [bind_assoc, isQueryBound_query_bind_iff]
    exact ⟨h₁.1, fun u => ih u (h₁.2 u)⟩

theorem map {oa : OracleComp Spec α} (h : Deterministic oa) (f : α → β) :
    Deterministic (f <$> oa) :=
  (isQueryBound_map_iff oa f _ _ _).2 h

theorem hash {k : ℕ} (u : BitVec k) : Deterministic (OptimalOTS.hash u) := by
  unfold Deterministic OptimalOTS.hash
  rw [isQueryBound_query_iff]
  rfl

theorem foldlM {γ δ : Type} (f : γ → δ → OracleComp Spec γ)
    (hf : ∀ x a, Deterministic (f x a)) :
    ∀ (l : List δ) (init : γ), Deterministic (l.foldlM f init)
  | [], _ => Deterministic.of_pure _
  | a :: l, init => by
      rw [List.foldlM_cons]
      exact Deterministic.bind (hf init a) fun y => Deterministic.foldlM f hf l y

end Deterministic

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

theorem deterministic_evalNode (x : G.Assignment) (v : Fin G.size)
    (s : OracleComp Spec (BitVec (G.len v))) (hs : Deterministic s) :
    Deterministic (G.evalNode x v s) := by
  unfold Graph.evalNode
  cases G.kind v with
  | source => exact hs
  | det => exact Deterministic.of_pure _
  | hash p _ h => exact Deterministic.map (Deterministic.hash _) _

theorem deterministic_reconstruct (A : Finset (Fin G.size)) (given : G.Assignment) :
    Deterministic (G.reconstruct A given) := by
  unfold Graph.reconstruct
  refine Deterministic.foldlM _ (fun x v => ?_) (List.finRange G.size) (fun _ => 0)
  split_ifs
  · exact Deterministic.of_pure _
  · exact Deterministic.map (G.deterministic_evalNode x v _ (Deterministic.of_pure _)) _
  · exact Deterministic.of_pure _

end Dag.Graph

end OptimalOTS
end
end

section

/-!
Perfect correctness of the DAG adapter. The shared cache preserves the key-generation equations
and the signing index. Reconstructing an honestly encoded cut therefore recovers the public key,
even when oracle inputs repeat. The message may be any function of the public key.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.GenericCorrectness

open OptimalOTS.Dag

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- A reconstruction satisfying the cached equations agrees with the original on visited nodes. -/
theorem reconstruct_eq (G : Graph) (A : Finset (Fin G.size)) (x y : G.Assignment)
    (c : Cache) (hc : G.CacheConsistent x c)
    (hsrc : ∀ v, G.Visited A v → v ∉ A → ¬ (G.kind v).IsSource)
    (hy : G.ReconEqs c A (G.decode A (G.encode A x)) y)
    (v : Fin G.size) (hv : G.Visited A v) : y v = x v := by
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    by_cases hA : v ∈ A
    · exact (hy v).1 hA |>.trans (G.decode_encode A x hA)
    · have hn := (hy v).2.2 hA hv
      have hx := hc v
      have hp : ∀ w ∈ (G.kind v).parents, y w = x w := fun w hw =>
        ih w ((G.kind v).lt_of_mem_parents hw) (Graph.Visited.parent hv hA hw)
      cases hk : G.kind v with
      | source => exact (hsrc v hv hA (by simp [hk, NodeKind.IsSource])).elim
      | det ps hps f hf =>
        have hx' : x v = f x := by simpa [Graph.CacheEqAt, hk] using hx
        exact (hn.2.1 ps hps f hf hk).trans ((hf y x (by simpa [hk, NodeKind.parents] using hp)).trans hx'.symm)
      | hash p hlt hl =>
        obtain ⟨w, hw, hyw⟩ := hn.1 p hlt hl hk
        have hpx : y p = x p := hp p (by simp [hk, NodeKind.parents])
        have hx' : c ⟨G.len p, x p⟩ = some ((x v).cast hl) := by
          simpa [Graph.CacheEqAt, hk] using hx
        rw [hpx, hx'] at hw
        have hw' := Option.some.inj hw
        rw [hyw, ← hw']
        simp

end OptimalOTS.GenericCorrectness
end
end

section

/-! Generic graph scheme with an86-bit nonce and weighted all-trial signer.
The decoder and tier function are explicit parameters. These resource and
correctness lemmas do not establish availability or strong security. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedScheme

open WeightedConstruction
abbrev Signature := NonceCodec.Signature86

structure Scheme (M : ℕ) where
  graph : Dag.Graph
  sets : Fin M → Finset (Fin graph.size)
  decode : BitVec hashBits → Option (Fin M)
  tier : Fin M → ℕ
  root_not_mem : ∀ i, graph.root ∉ sets i
  no_hidden_source :
    ∀ i v, graph.Visited (sets i) v → v ∉ sets i → ¬ (graph.kind v).IsSource
  reveal_le : ∀ i, graph.revealBits (sets i) + 86 ≤ maxSignatureBits
  keygen_le : graph.keygenCost ≤ keygenBudget

namespace Scheme
variable {M : ℕ} (S : Scheme M)

def publicKey (x : S.graph.Assignment) : PublicKey := (x S.graph.root).setWidth pkBits

def keygen : OracleComp Spec (PublicKey × S.graph.Assignment) :=
  GraphKeygenBridge.keygen S.graph S.publicKey

def sign (x : S.graph.Assignment) (m : Message) : OracleComp Spec (Option Signature) :=
  (Option.map fun r : WeightedSampling.Winner 86 M =>
    (r.1, S.graph.encode (S.sets r.2) x)) <$>
      WeightedSampling.loop 86 S.decode S.tier m signBudget

def verify (pk : PublicKey) (m : Message) (σ : Signature) : OracleComp Spec Bool := do
  let w ← hash (m ++ σ.1)
  match S.decode w with
  | none => return false
  | some i =>
      if σ.2.length = S.graph.revealBits (S.sets i) then
        let y ← S.graph.reconstruct (S.sets i) (S.graph.decode (S.sets i) σ.2)
        return decide (S.publicKey y = pk)
      else
        return false

def toAlgorithm : TypedScheme where
  SecretKey := S.graph.Assignment
  Signature := Signature
  encodeSignature := NonceCodec.encode
  encodeSignature_injective := NonceCodec.encode_injective
  keygen := S.keygen
  sign := S.sign
  verify := S.verify

open AlgorithmCosts

theorem costAtMost_keygen_exact : CostAtMost S.keygen S.graph.keygenCost :=
  CostAtMost.bind_le (AlgorithmCosts.Dag.Graph.costAtMost_keygen S.graph)
    (fun _ => costAtMost_pure _ 0) (by simp)

theorem keygenCost : S.toAlgorithm.KeygenCostAtMost keygenBudget :=
  CostAtMost.mono S.costAtMost_keygen_exact S.keygen_le

theorem signCost : S.toAlgorithm.SignCostAtMost signBudget := fun _x m =>
  CostAtMost.map (WeightedSampling.costAtMost_loop86 S.decode S.tier m) _

theorem verifyCost {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    S.toAlgorithm.VerifyCostAtMost (1+v) := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    CostAtMost (S.verify pk m σ) (1+v)
  intro pk m σ
  unfold verify
  refine CostAtMost.bind_le (costAtMost_hash _ WeightedSampling.index86_cost.le)
    (b₂ := v) (fun w => ?_) le_rfl
  cases S.decode w with
  | none => exact costAtMost_pure _ _
  | some i =>
    dsimp only
    split_ifs
    · exact CostAtMost.bind_le
        (CostAtMost.mono
          (AlgorithmCosts.Dag.Graph.costAtMost_reconstruct S.graph (S.sets i) _) (hv i))
        (fun _ => costAtMost_pure _ 0) (by simp)
    · exact costAtMost_pure _ _

theorem verifyDeterministic : S.toAlgorithm.VerifyDeterministic := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    Deterministic (S.verify pk m σ)
  intro pk m σ
  unfold verify
  refine Deterministic.bind (Deterministic.hash _) fun w => ?_
  cases S.decode w with
  | none => exact Deterministic.of_pure _
  | some i =>
    dsimp only
    split_ifs
    · exact Deterministic.bind (S.graph.deterministic_reconstruct _ _)
        fun _ => Deterministic.of_pure _
    · exact Deterministic.of_pure _

theorem signatureSize : S.toAlgorithm.SignatureSizeAtMost maxSignatureBits := by
  change ∀ (x : S.graph.Assignment) (m : Message) (σ : Signature),
    some σ ∈ support (S.sign x m) → (NonceCodec.encode σ).length ≤ maxSignatureBits
  intro x m σ h
  change some σ ∈ support (S.sign x m) at h
  rw [sign, support_map, Set.mem_image] at h
  obtain ⟨r, _, hr⟩ := h
  cases r with
  | none => simp at hr
  | some r =>
    simp only [Option.map_some, Option.some.injEq] at hr
    subst σ
    rw [NonceCodec.length_encode, S.graph.length_encode]
    have := S.reveal_le r.2
    omega

theorem rejectsOversized : S.toAlgorithm.RejectsOversized maxSignatureBits := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    maxSignatureBits < (NonceCodec.encode σ).length → true ∉ support (S.verify pk m σ)
  intro pk m σ hlen hmem
  change maxSignatureBits < (NonceCodec.encode σ).length at hlen
  rw [NonceCodec.length_encode] at hlen
  change true ∈ support (S.verify pk m σ) at hmem
  rw [verify, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨w, _, hmem⟩ := hmem
  cases hd : S.decode w with
  | none => simp [hd] at hmem
  | some i =>
    have hwrong : σ.2.length ≠ S.graph.revealBits (S.sets i) := by
      have := S.reveal_le i
      omega
    simp [hd, hwrong] at hmem

theorem keygen_cacheConsistent (c : Cache) :
    ∀ p ∈ support (run S.keygen c),
      p.1.1 = S.publicKey p.1.2 ∧ S.graph.CacheConsistent p.1.2 p.2 := by
  intro p hp
  simp only [keygen, GraphKeygenBridge.keygen, Dag.Graph.keygen,
    run_bind, support_bind, Set.mem_iUnion] at hp
  obtain ⟨⟨x,d⟩, ⟨⟨z,d'⟩, _, hx⟩, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  exact ⟨rfl, S.graph.evaluate_cacheConsistent z d' _ hx⟩

theorem sign_result (x : S.graph.Assignment) (m : Message) (σ : Signature) (c d : Cache)
    (h : (some σ,d) ∈ support (run (S.sign x m) c)) :
    ∃ i : Fin M, ∃ w : BitVec hashBits,
      σ.2 = S.graph.encode (S.sets i) x ∧
      d ⟨msgBits+86,m++σ.1⟩ = some w ∧ S.decode w = some i := by
  rw [sign, run_map, support_map, Set.mem_image] at h
  obtain ⟨⟨r,d'⟩, hr, he⟩ := h
  cases r with
  | none => simp at he
  | some r =>
    obtain ⟨η,i⟩ := r
    simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at he
    rcases he with ⟨he,rfl⟩
    obtain ⟨w,hw,hi⟩ :=
      (WeightedSampling.loop_support 86 S.decode S.tier m signBudget c _ hr).2 η i rfl
    cases he
    exact ⟨i,w,rfl,hw,hi⟩

theorem verify_accepts (x : S.graph.Assignment) (m : Message) (σ : Signature)
    (c : Cache) (hc : S.graph.CacheConsistent x c) (i : Fin M) (w : BitVec hashBits)
    (hσ : σ.2 = S.graph.encode (S.sets i) x)
    (hw : c ⟨msgBits+86,m++σ.1⟩ = some w) (hi : S.decode w = some i) :
    ∀ p ∈ support (run (S.verify (S.publicKey x) m σ) c), p.1 = true := by
  intro p hp
  unfold verify at hp
  rw [run_bind, WeightedSampling.run_hash_cached _ c w hw, pure_bind, hi] at hp
  dsimp only at hp
  have hlen : σ.2.length = S.graph.revealBits (S.sets i) := by
    rw [hσ,S.graph.length_encode]
  rw [if_pos hlen,run_bind,support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨y,e⟩,hy,hp⟩ := hp
  obtain ⟨hce,he⟩ := S.graph.reconstruct_support _ _ c (y,e) hy
  rw [hσ] at he
  have hec := Dag.Graph.CacheConsistent.mono S.graph hce hc
  have hr := GenericCorrectness.reconstruct_eq S.graph (S.sets i) x y e hec
    (S.no_hidden_source i) he S.graph.root Dag.Graph.Visited.root
  rw [run_pure,support_pure,Set.mem_singleton_iff] at hp
  subst p
  simp only [publicKey,hr,decide_true]

/-- Perfect correctness, including public-key-dependent message choices. -/
theorem correct : S.toAlgorithm.Correct := by
  intro message
  dsimp only [toAlgorithm]
  unfold probTrue
  rw [StateT.run'_eq,probOutput_eq_zero_iff,support_map]
  rintro ⟨⟨b,e⟩,h,hb⟩
  change (b,e) ∈ support (run _ ∅) at h
  rw [run_bind,support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨⟨pk,sk⟩,c⟩,hk,h⟩ := h
  rw [run_bind,support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨σ,d⟩,hs,h⟩ := h
  obtain ⟨hpk,hkc⟩ := S.keygen_cacheConsistent ∅ _ hk
  dsimp only at hpk hkc
  subst pk
  change b = true at hb
  cases σ with
  | none =>
    simp only [run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq] at h
    cases h.1.symm.trans hb
  | some σ =>
    obtain ⟨i,w,hσ,hw,hi⟩ := S.sign_result sk (message (S.publicKey sk)) σ c d hs
    have hcd := sub_of_mem_support_run (S.sign sk (message (S.publicKey sk))) c _ hs
    have hdc := Dag.Graph.CacheConsistent.mono S.graph hcd hkc
    rw [run_bind,support_bind] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨⟨ok,f⟩,hv,h⟩ := h
    have hok : ok = true := S.verify_accepts sk (message (S.publicKey sk)) σ d hdc
      i w hσ hw hi _ hv
    simp only [hok,Bool.not_true,run_pure,support_pure,Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    cases h.1.symm.trans hb

end Scheme
end OptimalOTS.WeightedScheme
end
end

section

/-!
# Names and graph for the wide weighted candidate

54 tagged hash chains of length 18 feed 18 ternary group hashes directly into
one root. Inputs have lengths 145, 403, and 2338 bits. The root costs five
compressions, so key generation costs 54 * 18 + 18 + 5 = 995.

This file defines the graph and certifies its topology and key-generation cost.
It does not establish a disclosure family, signing availability, or security.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace WeightedConstruction.WideForest

/-! ## Tweaks

The random oracle has no labels: a hash node queries it on its parent's value alone.  The scheme
keeps its hash nodes apart by starting every hash input with a 16-bit tweak naming the hash node.
Convention: the tweak occupies the HIGH bits, i.e. the input of the hash node `h` is
`tw h ++ payload` (`BitVec.append`, whose left argument is the most significant one).  The
payload is recovered by `setWidth`/`extractLsb' 0`, the tweak by `extractLsb' n 16` or
`tagNat`. -/

/-- The number written in the 16 high bits of a query. -/
def tagNat (q : Query) : ℕ := q.2.toNat / 2 ^ (q.1 - 16)

theorem tagNat_append {n : ℕ} (a : BitVec 16) (u : BitVec n) :
    tagNat ⟨16 + n, a ++ u⟩ = a.toNat := by
  unfold tagNat
  simp only [BitVec.toNat_append, Nat.add_sub_cancel_left]
  rw [← Nat.shiftLeft_add_eq_or_of_lt u.isLt, Nat.shiftLeft_eq, Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt u.isLt, Nat.zero_add]

/-- `tagNat` ignores casts. -/
theorem tagNat_cast {n m : ℕ} (e : n = m) (u : BitVec n) :
    tagNat ⟨m, u.cast e⟩ = tagNat ⟨n, u⟩ := by
  subst e; rfl

/-! ## The graph -/

/-- The 129-bit truncation. -/
def lowWord {w : ℕ} (x : BitVec w) : BitVec 129 := x.setWidth 129

end WeightedConstruction.WideForest

end OptimalOTS

end
end

section

/-! Exact fibers of low-bit truncation, generic in both widths. These finite
bijections support different internal and public-key binding widths. -/

namespace OptimalOTS.WeightedConstruction.TruncFiber

noncomputable section
open scoped Classical

/-- Join fixed low bits with free high bits. -/
def join {n w : ℕ} (hw : w ≤ n) (a : BitVec w) (b : BitVec (n - w)) : BitVec n :=
  (b ++ a).cast (Nat.sub_add_cancel hw)

@[simp] theorem low_join {n w : ℕ} (hw : w ≤ n) (a : BitVec w)
    (b : BitVec (n - w)) : (join hw a b).setWidth w = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [join, BitVec.getLsbD_append, hi]

@[simp] theorem high_join {n w : ℕ} (hw : w ≤ n) (a : BitVec w)
    (b : BitVec (n - w)) : ((join hw a b) >>> w).setWidth (n - w) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : ¬ w + i < w := by omega
  simp [join, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hi, hn]

theorem join_high {n w : ℕ} (hw : w ≤ n) {a : BitVec w} (x : BitVec n)
    (hx : x.setWidth w = a) : join hw a ((x >>> w).setWidth (n - w)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hl : i < w
  · have h := congrArg (fun t : BitVec w => t.getLsbD i) hx
    simpa [join, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hl] using h.symm
  · have hh : i - w < n - w := by omega
    have he : w + (i - w) = i := by omega
    simp [join, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, hl, hh, he]

/-- Truncation leaves exactly the high `n-w` bits free. -/
def fiberEquiv {n w : ℕ} (hw : w ≤ n) (a : BitVec w) :
    {x : BitVec n // x.setWidth w = a} ≃ BitVec (n - w) where
  toFun x := (x.val >>> w).setWidth (n - w)
  invFun b := ⟨join hw a b, low_join hw a b⟩
  left_inv x := Subtype.ext (join_high hw x.val x.property)
  right_inv b := high_join hw a b

theorem card_filter_setWidth {n w : ℕ} (hw : w ≤ n) (a : BitVec w) :
    (Finset.univ.filter fun x : BitVec n => x.setWidth w = a).card = 2 ^ (n - w) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberEquiv hw a), Fintype.card_bitVec]

theorem card_256_129 (a : BitVec 129) :
    (Finset.univ.filter fun x : BitVec 256 => x.setWidth 129 = a).card = 2 ^ 127 :=
  card_filter_setWidth (by omega) a

end
end OptimalOTS.WeightedConstruction.TruncFiber

end

section

/-! Transfer a typed-signature certificate to the contract's scheme on the encoded bit strings.
Signing outputs the encoding; verification parses a bit string with `decode`. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WireAdapter

variable (S : TypedScheme) (decode : List Bool → S.Signature)

/-- The scheme on bit strings. -/
abbrev scheme : OracleAlgorithm.Scheme where
  SecretKey := S.SecretKey
  keygen := S.keygen
  sign := fun sk m => Option.map S.encodeSignature <$> S.sign sk m
  verify := fun pk m bits => S.verify pk m (decode bits)

def adversary (A : OracleAlgorithm.Adversary) : S.Adversary where
  State := A.State
  choose := A.choose
  forge := fun state signed =>
    (fun pair => (pair.1, decode pair.2)) <$> A.forge state (signed.map S.encodeSignature)

variable (inverse : ∀ σ, decode (S.encodeSignature σ) = σ)
  (canonical : ∀ pk m bits, true ∈ support (S.verify pk m (decode bits)) →
    S.encodeSignature (decode bits) = bits)

include inverse canonical in
theorem experiment_eq (A : OracleAlgorithm.Adversary) :
    OracleAlgorithm.experiment (scheme S decode) A = S.experiment (adversary S decode A) := by
  simp only [OracleAlgorithm.experiment, TypedScheme.experiment, scheme, adversary,
    bind_map_left]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr_of_forall_mem_support
  intro ok hok
  cases ok with
  | false => rfl
  | true =>
    have hc := canonical keys.1 forged.1 forged.2 hok
    congr 1
    cases signed with
    | none => simp
    | some σ =>
      simp only [Option.map_some, Bool.true_and]
      have he : S.encodeSignature σ = forged.2 ↔ σ = decode forged.2 := by
        constructor
        · intro h
          have hd := congrArg decode h
          simpa only [inverse] using hd
        · intro h
          simpa only [h] using hc
      simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, he]

include inverse canonical in
theorem secure (h : S.Secure) : (scheme S decode).Secure := by
  intro A B hB
  rw [experiment_eq S decode inverse canonical A] at hB ⊢
  exact h (adversary S decode A) B hB

include inverse in
theorem correct (h : S.Correct) : (scheme S decode).Correct := by
  unfold TypedScheme.Correct at h
  unfold OracleAlgorithm.Scheme.Correct
  intro message
  rw [← h message]
  congr 1
  simp only [scheme, bind_map_left]
  apply bind_congr
  intro keys
  apply bind_congr
  intro signed
  cases signed <;> simp only [Option.map_none, Option.map_some, inverse]

theorem signingFailure (ε : ℝ≥0∞) (h : S.SigningFailureAtMost ε) :
    (scheme S decode).SigningFailureAtMost ε := by
  intro message
  have original := h message
  simpa only [OracleAlgorithm.Scheme.SigningFailureAtMost, scheme, bind_map_left,
    Option.isNone_map] using original

theorem signatureSize (n : ℕ) (h : S.SignatureSizeAtMost n) :
    (scheme S decode).SignatureSizeAtMost n := by
  intro sk m bits hb
  change some bits ∈ support (Option.map S.encodeSignature <$> S.sign sk m) at hb
  rw [support_map] at hb
  obtain ⟨signed, hs, he⟩ := hb
  cases signed with
  | none => cases he
  | some σ =>
    have equal : S.encodeSignature σ = bits := Option.some.inj he
    rw [← equal]
    exact h sk m σ hs

include canonical in
theorem rejectsOversized (n : ℕ) (h : S.RejectsOversized n) :
    (scheme S decode).RejectsOversized n := by
  intro pk m bits hsize accepted
  have hc := canonical pk m bits accepted
  exact h pk m (decode bits) (by simpa only [hc] using hsize) accepted

theorem verifyCost (c : ℕ) (h : S.VerifyCostAtMost c) : (scheme S decode).VerifyCostAtMost c :=
  fun pk m bits => h pk m (decode bits)

include inverse canonical in
theorem admissible (h : S.Admissible (1 / 2 ^ signingFailureBits)) {c : ℕ}
    (hcost : S.VerifyCostAtMost c) (hc : c ≤ verifyBudget) :
    (scheme S decode).Admissible where
  correct := correct S decode inverse h.correct
  verifyDeterministic := fun pk m bits => h.verifyDeterministic pk m (decode bits)
  signingFailure := signingFailure S decode _ h.signingFailure
  signatureSize := signatureSize S decode maxSignatureBits h.signatureSize
  rejectsOversized := rejectsOversized S decode canonical maxSignatureBits h.rejectsOversized
  keygenCost := h.keygenCost
  signCost := fun sk m => AlgorithmCosts.CostAtMost.map (h.signCost sk m) _
  verifyCost := OracleAlgorithm.Scheme.VerifyCostAtMost.mono _ (verifyCost S decode c hcost) hc

end OptimalOTS.WireAdapter
end
end

section

/-! Availability of the actual with-replacement loop, retaining shared-oracle
memoization. Cached nonce probability is paid inside the per-trial failure
factor; no additive nonce-collision error is used. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling.Availability

variable {M n : ℕ} {α : Type}

theorem nonce_suffix (m : Message) (η : Nonce n) : (m++η).setWidth n = η := by
  ext j hj
  simp [BitVec.getElem_setWidth,BitVec.getLsbD_append,hj]

theorem nonce_query_inj (m : Message) {η ζ : Nonce n}
    (h : (⟨msgBits+n,m++η⟩ : Query) = ⟨msgBits+n,m++ζ⟩) : η = ζ := by
  have hh := congrArg (fun q : Query => q.2.setWidth n) h
  simpa only [nonce_suffix] using hh

theorem fresh_insert (m : Message) (c : Cache) (tried : Finset (Nonce n))
    (hf : ∀ η ∉ tried, c ⟨msgBits+n,m++η⟩ = none) (η : Nonce n) (w : BitVec hashBits) :
    ∀ ζ ∉ insert η tried, (c.cacheQuery ⟨msgBits+n,m++η⟩ w) ⟨msgBits+n,m++ζ⟩ = none := by
  intro ζ hζ
  have hne : (⟨msgBits+n,m++ζ⟩ : Query) ≠ ⟨msgBits+n,m++η⟩ := by
    intro h
    have he := nonce_query_inj m h
    exact hζ (he ▸ Finset.mem_insert_self η tried)
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hf ζ (fun h => hζ (Finset.mem_insert_of_mem h))

theorem run_hash_fresh {b : ℕ} (u : BitVec b) (c : Cache)
    (h : c ⟨b,u⟩ = none) : run (hash u) c =
      ($ᵗ BitVec hashBits) >>= fun w => pure (w,c.cacheQuery ⟨b,u⟩ w) := by
  unfold hash run
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_none h

theorem uniform_tried (n : ℕ) (tried : Finset (Nonce n)) (a : ℝ≥0∞) :
    E ($ᵗ BitVec n) (fun η => if η ∈ tried then a else 0) =
      (tried.card : ℝ≥0∞) / 2^n * a := by
  rw [E_uniform]
  simp only [mul_ite,mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,
    nsmul_eq_mul,Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
  rw [div_eq_mul_inv,mul_assoc]

theorem uniform_miss_plus (n : ℕ) (tried : Finset (Nonce n)) (miss a : ℝ≥0∞) :
    E ($ᵗ BitVec n) (fun η => miss*a + (if η ∈ tried then a else 0)) =
      (miss + (tried.card : ℝ≥0∞)/2^n)*a := by
  rw [E_uniform]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [sum_inv_card_mul]
  have hh := uniform_tried n tried a
  rw [E_uniform] at hh
  rw [hh,add_mul]

theorem none_best (rank : α → ℕ) (a b : Option α) :
    (if (best rank a b).isNone then (1 : ℝ≥0∞) else 0) =
      if a.isNone then (if b.isNone then 1 else 0) else 0 := by
  cases a <;> cases b <;> simp [best]
  split_ifs <;> simp

theorem after_bound (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (k : ℕ) (c : Cache) (η : Nonce n)
    (w : BitVec hashBits) (a : ℝ≥0∞)
    (h : E (run (loop n decode tier m k) c) (fun p => if p.1.isNone then 1 else 0) ≤ a) :
    E (run (loop n decode tier m k) c)
      (fun p => if (best (fun s => tier s.2) (candidate decode η w) p.1).isNone
        then 1 else 0) ≤ if (decode w).isNone then a else 0 := by
  simp_rw [none_best]
  cases hd : decode w with
  | none => simpa [candidate,hd] using h
  | some i => simpa [candidate,hd] using E_const_le (run (loop n decode tier m k) c) 0

/-- A cache with at mosttried.card possibly occupied row slots. -/
theorem loop_failure (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (L : ℕ) (miss : ℝ≥0∞)
    (hmiss : ∀ a : ℝ≥0∞, E ($ᵗ BitVec hashBits)
      (fun w => if (decode w).isNone then a else 0) ≤ miss*a) :
    ∀ k (tried : Finset (Nonce n)) (c : Cache), tried.card+k ≤ L →
      (∀ η ∉ tried, c ⟨msgBits+n,m++η⟩ = none) →
      E (run (loop n decode tier m k) c) (fun p => if p.1.isNone then 1 else 0) ≤
        (miss + (L : ℝ≥0∞)/2^n)^k := by
  intro k
  induction k with
  | zero => intro tried c _ _; simp [loop,run_pure]
  | succ k ih =>
    intro tried c hL hf
    let a : ℝ≥0∞ := (miss+(L : ℝ≥0∞)/2^n)^k
    have hcard (η : Nonce n) : (insert η tried).card+k ≤ L := by
      have := Finset.card_insert_le η tried
      omega
    have hstep (η : Nonce n) :
        E (run (hash (m++η)) c) (fun q =>
          E (run (loop n decode tier m k) q.2) (fun p =>
            if (best (fun s => tier s.2) (candidate decode η q.1) p.1).isNone then 1 else 0)) ≤
          miss*a + (if η ∈ tried then a else 0) := by
      cases hc : c ⟨msgBits+n,m++η⟩ with
      | none =>
        rw [run_hash_fresh _ c hc,E_bind]
        simp only [E_pure]
        have hpt (w : BitVec hashBits) := after_bound n decode tier m k
          (c.cacheQuery ⟨msgBits+n,m++η⟩ w) η w a
          (ih (insert η tried) _ (hcard η) (fresh_insert m c tried hf η w))
        exact ((E_mono _ hpt).trans (hmiss a)).trans (le_add_right le_rfl)
      | some w =>
        rw [run_hash_cached _ c w hc,E_pure]
        have hη : η ∈ tried := by
          by_contra h
          rw [hf η h] at hc
          cases hc
        have hprev : E (run (loop n decode tier m k) c)
            (fun p => if p.1.isNone then 1 else 0) ≤ a :=
          ih (insert η tried) c (hcard η)
            (fun ζ hζ => hf ζ (fun h => hζ (Finset.mem_insert_of_mem h)))
        have ha := after_bound n decode tier m k c η w a hprev
        have ha' : (if (decode w).isNone then a else 0) ≤ a := by split_ifs <;> simp
        exact (ha.trans ha').trans (by rw [if_pos hη]; exact le_add_left le_rfl)
    rw [run_loop_succ,E_bind]
    simp only [E_bind,E_pure]
    calc
      _ ≤ E ($ᵗ BitVec n) (fun η => miss*a+(if η ∈ tried then a else 0)) := E_mono _ hstep
      _ = (miss+(tried.card : ℝ≥0∞)/2^n)*a := uniform_miss_plus n tried miss a
      _ ≤ (miss+(L : ℝ≥0∞)/2^n)*a := by
        apply mul_le_mul' _ le_rfl
        apply add_le_add le_rfl
        exact ENNReal.div_le_div_right (by exact_mod_cast (show tried.card ≤ L by omega)) _
      _ = _ := by dsimp [a]; rw [pow_succ,mul_comm]

end OptimalOTS.WeightedSampling.Availability
end
end
