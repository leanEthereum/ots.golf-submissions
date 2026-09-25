import Submissions.UpperLeanIsa.Resources

/-!
# The wire format and the admissibility of a layer scheme

* `encode_decode`: a 5503-bit string is the encoding of its decoded words and nonce, so two
  signatures of the right length with the same words and nonce are equal;
* signatures have exactly `sigBits = 5503` bits, verification is deterministic;
* `admissible`: all eight fields of `Admissible` under `Params.Hyp`.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

attribute [local irreducible] trials

/-! ## Decoding then encoding -/

theorem flatMap_chunks {w : ℕ} :
    ∀ (n : ℕ) (l : List Bool), l.length = w * n →
      (List.ofFn fun i : Fin n => ofBits w ((l.drop (w * i.val)).take w)).flatMap toBits = l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at hl
    simp [hl]
  | succ n ih =>
    intro l hl
    rw [List.ofFn_succ, List.flatMap_cons]
    have h0 : ofBits w ((l.drop (w * (0 : Fin (n + 1)).val)).take w) = ofBits w (l.take w) := by
      simp
    rw [h0, bits_ofBits _ (by rw [List.length_take]; rw [hl]; exact min_eq_left (by nlinarith))]
    have hrest : (List.ofFn fun i : Fin n =>
        ofBits w ((l.drop (w * (i.succ : Fin (n + 1)).val)).take w)) =
        List.ofFn fun i : Fin n => ofBits w (((l.drop w).drop (w * i.val)).take w) := by
      apply congrArg List.ofFn
      funext i
      rw [List.drop_drop, Fin.val_succ, Nat.mul_succ, Nat.add_comm (w * i.val) w]
    rw [hrest, ih (l.drop w) (by rw [List.length_drop, hl, Nat.mul_succ]; omega),
      List.take_append_drop]

/-- A 5503-bit string is the encoding of its decoded words and nonce. -/
theorem encode_decode (bits : List Bool) (h : bits.length = sigBits) :
    encode (decodeWord bits) (decodeNonce bits) = bits := by
  have hs : sigBits = 5503 := rfl
  rw [hs] at h
  unfold encode decodeWord decodeNonce
  have h1 := flatMap_chunks (w := 128) 42 (bits.take 5376) (by rw [List.length_take, h]; rfl)
  have h2 : (fun k : Fin numChains => ofBits 128 ((bits.drop (128 * k.val)).take 128)) =
      fun k : Fin 42 => ofBits 128 (((bits.take 5376).drop (128 * k.val)).take 128) := by
    funext k
    rw [List.drop_take, List.take_take]
    congr 2
    have hk : k.val < 42 := k.isLt
    omega
  rw [h2, h1, bits_ofBits _ (by rw [List.length_take, List.length_drop, h]; rfl),
    List.take_of_length_le (l := bits.drop 5376) (by rw [List.length_drop, h]),
    List.take_append_drop]

theorem eq_of_decode_eq {σ σ' : List Bool} (h : σ.length = sigBits) (h' : σ'.length = sigBits)
    (hw : decodeWord σ = decodeWord σ') (hn : decodeNonce σ = decodeNonce σ') : σ = σ' := by
  rw [← encode_decode σ h, ← encode_decode σ' h', hw, hn]

/-! ## Signature size and determinism -/

namespace Params

variable (P : Params)

theorem signLoop_support_length (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (s : List Bool),
      some s ∈ support (P.signLoop sk m k tried) → s.length = sigBits := by
  intro k
  induction k with
  | zero =>
    intro tried s hs
    simp only [signLoop, support_pure, Set.mem_singleton_iff] at hs
    cases hs
  | succ k ih =>
    intro tried s hs
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signLoop_succ sk m k tried hc, support_bind] at hs
      simp only [Set.mem_iUnion] at hs
      obtain ⟨j, -, hs⟩ := hs
      unfold loopBody at hs
      rw [support_bind] at hs
      simp only [Set.mem_iUnion] at hs
      obtain ⟨w, -, hs⟩ := hs
      unfold afterHash at hs
      split at hs
      · rw [support_pure, Set.mem_singleton_iff] at hs
        rw [Option.some.inj hs]
        exact encode_length _ _
      · exact ih _ s hs
    · rw [signLoop, dif_neg hc, support_pure, Set.mem_singleton_iff] at hs
      cases hs

theorem signatureSize : P.scheme.SignatureSizeAtMost maxSignatureBits := by
  intro (sk : SecretKey) m s hs
  have hs' : some s ∈ support (P.sign sk m) := hs
  rw [P.sign_eq sk m] at hs'
  rw [P.signLoop_support_length sk m trials ∅ s hs']
  norm_num [sigBits, maxSignatureBits]

theorem deterministic_pure {α : Type} (x : α) :
    Deterministic (pure x : OracleComp Spec α) := by trivial

theorem deterministic_bind {α β : Type} {oa : OracleComp Spec α}
    {ob : α → OracleComp Spec β} (ha : Deterministic oa)
    (hb : ∀ x, Deterministic (ob x)) : Deterministic (oa >>= ob) :=
  isQueryBound_bind (fun _ _ => ())
    (fun _ _ _ _ h => ⟨h, h⟩) (fun _ _ _ _ _ => ⟨rfl, rfl⟩) ha hb

theorem deterministic_map {α β : Type} {oa : OracleComp Spec α}
    (ha : Deterministic oa) (f : α → β) : Deterministic (f <$> oa) :=
  (isQueryBound_map_iff _ _ _ _ _).2 ha

theorem deterministic_hash {k : ℕ} (x : BitVec k) : Deterministic (hash x) := by
  unfold Deterministic hash
  rw [isQueryBound_query_iff]
  rfl

theorem deterministic_ite {α : Type} (p : Prop) [Decidable p] {a c : OracleComp Spec α}
    (ha : p → Deterministic a) (hc : ¬ p → Deterministic c) :
    Deterministic (if p then a else c) := by
  split
  · exact ha ‹_›
  · exact hc ‹_›

theorem deterministic_tabulate {α : Type} {n : ℕ} (f : Fin n → OracleComp Spec α)
    (h : ∀ i, Deterministic (f i)) : Deterministic (tabulate f) := by
  induction n with
  | zero => exact deterministic_pure _
  | succ n ih =>
    have ht := deterministic_bind (h 0) (fun x =>
      deterministic_map (ih _ (fun i => h i.succ))
        (fun (xs : Fin n → α) (i : Fin (n + 1)) =>
          Fin.cases (motive := fun _ => α) x xs i))
    simpa only [tabulate, map_eq_bind_pure_comp, Function.comp_def] using ht

attribute [local irreducible] Deterministic

theorem deterministic_chain (k : Fin numChains) : ∀ (j n : ℕ) (x : Word),
    Deterministic (P.chain k j n x) := by
  intro j n
  induction n generalizing j with
  | zero => intro x; exact deterministic_pure _
  | succ n ih =>
    intro x
    exact deterministic_bind (deterministic_map (deterministic_hash _) _) (fun y => ih (j + 1) y)

theorem deterministic_rootFrom (t : Fin numChains → Word) : ∀ (r n : ℕ) (st : BitVec 256),
    Deterministic (P.rootFrom t r n st) := by
  intro r n
  induction n generalizing r with
  | zero => intro st; exact deterministic_pure _
  | succ n ih =>
    intro st
    exact deterministic_bind (deterministic_hash _) (fun st' => ih (r + 1) st')

theorem verifyDeterministic : P.scheme.VerifyDeterministic := by
  intro pk m bits
  change Deterministic (P.verify pk m bits)
  unfold verify
  refine deterministic_ite _ (fun _ => deterministic_pure _) (fun _ => ?_)
  refine deterministic_bind (deterministic_map (deterministic_hash _) _) (fun I => ?_)
  refine deterministic_ite _ (fun _ => deterministic_pure _) (fun _ => ?_)
  exact deterministic_bind (deterministic_tabulate _ fun k => P.deterministic_chain k _ _ _)
    (fun tops => deterministic_bind (deterministic_map (P.deterministic_rootFrom _ _ _ _) _)
      (fun _ => deterministic_pure _))

/-- **Admissibility** of a layer scheme: every requirement except security. -/
theorem admissible (hP : P.Hyp) : P.scheme.Admissible where
  correct := P.correct hP
  verifyDeterministic := P.verifyDeterministic
  signingFailure := P.signingFailure hP.chain_idx hP.root_idx hP.numValid_ge
  signatureSize := P.signatureSize
  rejectsOversized := rejectsOversized P
  keygenCost := CostAtMost.mono P.cost_keygen (by unfold keygenBudget; exact hP.keygen_le)
  signCost := fun sk m => CostAtMost.mono (P.cost_sign sk m) (by unfold signBudget; exact le_rfl)
  verifyCost := fun pk m σ => CostAtMost.mono (P.cost_verify pk m σ)
    (by unfold verifyBudget; exact hP.verify_le)

end Params

end OptimalOTS.LeanIsaBaseline.Layer
