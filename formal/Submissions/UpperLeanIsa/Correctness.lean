import Submissions.UpperLeanIsa.Wire
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! Correctness for every fixed oracle table, transferred to the cached random oracle. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp

abbrev HashTable := QueryImpl hashSpec Id

def chainValue (f : HashTable) (i j : ℕ) : ℕ → Word → Word
  | 0, x => x
  | n + 1, x => chainValue f i (j + 1) n
      ((f ⟨896, chainInput i j x⟩).extractLsb' 0 128)

def rootValueFold (f : HashTable) : List Word → BitVec 256 → BitVec 256
  | [], cv => cv
  | x :: xs, cv => rootValueFold f xs
      (f ⟨896, LeanIsa.hashInput cv (x.setWidth 512) (BitVec.ofNat 128 (2 + xs.length))⟩)

def rootValue (f : HashTable) (xs : Words) : PublicKey :=
  (rootValueFold f (List.ofFn xs) 0).extractLsb' 0 128

theorem chainValue_add (f : HashTable) (i j a b : ℕ) (x : Word) :
    chainValue f i (j + a) b (chainValue f i j a x) = chainValue f i j (a + b) x := by
  induction a generalizing j x with
  | zero => simp only [chainValue, Nat.add_zero, Nat.zero_add]
  | succ a ih =>
    simp only [Nat.succ_add, chainValue]
    simpa only [Nat.add_assoc, Nat.add_comm 1 a] using
      ih (j + 1) ((f ⟨896, chainInput i j x⟩).extractLsb' 0 128)

theorem fixed_hash (f : HashTable) {n : ℕ} (x : BitVec n) :
    simulateQ (unifFwdAnswerImpl f) (hash x) = pure (f ⟨n, x⟩) := by
  rw [hash, simulateQ_spec_query]
  rfl

theorem fixed_chain (f : HashTable) (i j n : ℕ) (x : Word) :
    simulateQ (unifFwdAnswerImpl f) (chain i j n x) = pure (chainValue f i j n x) := by
  induction n generalizing j x with
  | zero => rfl
  | succ n ih => simp [chain, chainStep, fixed_hash, ih, chainValue]

theorem fixed_tabulate (f : HashTable) {α : Type} {n : ℕ}
    (oa : Fin n → OracleComp Spec α) (v : Fin n → α)
    (h : ∀ i, simulateQ (unifFwdAnswerImpl f) (oa i) = pure (v i)) :
    simulateQ (unifFwdAnswerImpl f) (tabulate oa) = pure v := by
  induction n with
  | zero =>
    simp only [tabulate, simulateQ_pure]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [tabulate, simulateQ_bind, simulateQ_pure, h, pure_bind]
    rw [ih (fun i => oa i.succ) (fun i => v i.succ) (fun i => h i.succ), pure_bind]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem fixed_rootFold (f : HashTable) (xs : List Word) (cv : BitVec 256) :
    simulateQ (unifFwdAnswerImpl f) (rootFold xs cv) = pure (rootValueFold f xs cv) := by
  induction xs generalizing cv with
  | nil => rfl
  | cons x xs ih =>
    rw [rootFold, simulateQ_bind]
    rw [show simulateQ (unifFwdAnswerImpl f) (absorb xs.length cv x) =
      (pure (f ⟨896, LeanIsa.hashInput cv (x.setWidth 512) (BitVec.ofNat 128 (2 + xs.length))⟩) :
        ProbComp (BitVec 256)) from
        fixed_hash f _]
    change (pure (f ⟨896, LeanIsa.hashInput cv (x.setWidth 512)
      (BitVec.ofNat 128 (2 + xs.length))⟩ : BitVec 256) >>= fun y =>
      simulateQ (unifFwdAnswerImpl f) (rootFold xs y)) = _
    rw [pure_bind]
    exact ih _

theorem fixed_root (f : HashTable) (xs : Words) :
    simulateQ (unifFwdAnswerImpl f) (root xs) = pure (rootValue f xs) := by
  change simulateQ (unifFwdAnswerImpl f)
    ((fun y : BitVec 256 => y.extractLsb' 0 128) <$> rootFold (List.ofFn xs) 0) =
      (pure (rootValue f xs) : ProbComp (BitVec 128))
  rw [simulateQ_map, fixed_rootFold, map_pure]
  rfl

def endpoints (f : HashTable) (sk : Words) : Words := fun i => chainValue f i.val 0 255 (sk i)

def signedWords (f : HashTable) (sk : Words) (m : Message) : Words :=
  fun i => chainValue f i.val 0 (digit m i) (sk i)

def reconstructedWords (f : HashTable) (m : Message) (bits : List Bool) : Words :=
  fun i => chainValue f i.val (digit m i) (255 - digit m i) (decode bits i)

/-- The exact fixed-table decision on arbitrary raw inputs, including malformed lengths. -/
theorem fixed_verify (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) :
    simulateQ (unifFwdAnswerImpl f) (verify pk m bits) =
      pure (if bits.length = 4352 then rootValue f (reconstructedWords f m bits) == pk
        else false) := by
  by_cases h : bits.length = 4352
  · simp only [verify, h, ne_eq, not_true_eq_false, ↓reduceIte, simulateQ_bind, simulateQ_pure]
    rw [fixed_tabulate f _ (reconstructedWords f m bits) (fun i => fixed_chain f _ _ _ _),
      pure_bind, fixed_root, pure_bind]
  · simp only [verify, h, ne_eq, not_false_eq_true, ↓reduceIte, simulateQ_pure]

theorem fixed_keygen (f : HashTable) :
    simulateQ (unifFwdAnswerImpl f) keygen =
      (simulateQ (unifFwdAnswerImpl f) (tabulate (fun _ : Fin 34 => sampleBits 128)) >>= fun sk =>
        pure (rootValue f (endpoints f sk), sk)) := by
  simp only [keygen, simulateQ_bind, simulateQ_pure]
  apply congrArg
  funext sk
  rw [fixed_tabulate f _ (endpoints f sk) (fun i => fixed_chain f _ _ _ _), pure_bind,
    fixed_root, pure_bind]

theorem fixed_sign (f : HashTable) (sk : Words) (m : Message) :
    simulateQ (unifFwdAnswerImpl f) (sign sk m) = pure (some (encode (signedWords f sk m))) := by
  simp only [sign, simulateQ_bind, simulateQ_pure]
  rw [fixed_tabulate f _ (signedWords f sk m) (fun i => fixed_chain f _ _ _ _), pure_bind]

theorem fixed_verify_honest (f : HashTable) (sk : Words) (m : Message) :
    simulateQ (unifFwdAnswerImpl f)
      (verify (rootValue f (endpoints f sk)) m (encode (signedWords f sk m))) = pure true := by
  have hc (i : Fin 34) :
      chainValue f i.val (digit m i) (255 - digit m i) (signedWords f sk m i) =
        endpoints f sk i := by
    unfold signedWords endpoints
    have h := chainValue_add f i.val 0 (digit m i) (255 - digit m i) (sk i)
    simpa only [Nat.zero_add, Nat.add_sub_of_le (digit_le m i)] using h
  simp only [verify, encode_length, ne_eq, not_true_eq_false, ↓reduceIte, decode_encode,
    simulateQ_bind, simulateQ_pure]
  rw [fixed_tabulate f _ (endpoints f sk) (fun i => (fixed_chain f _ _ _ _).trans
    (congrArg pure (hc i))), pure_bind, fixed_root, pure_bind]
  simp

/-- A zero-probability lemma that keeps all repeated hash answers consistent. -/
theorem probTrue_zero_of_fixed (oa : OracleComp Spec Bool)
    (h : ∀ f : HashTable, true ∉ support (simulateQ (unifFwdAnswerImpl f) oa)) :
    probTrue oa = 0 := by
  rw [probTrue, probOutput_eq_zero_iff]
  intro hs
  change true ∈ support (Prod.fst <$> (simulateQ oracleImpl oa).run ∅) at hs
  rw [support_map] at hs
  obtain ⟨⟨b, cache⟩, hs, hb⟩ := hs
  change b = true at hb
  subst b
  obtain ⟨f, _, hf⟩ :=
    (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff oa ∅ true).mpr ⟨cache, hs⟩
  exact h f hf

theorem correct : scheme.Correct := by
  intro message
  apply probTrue_zero_of_fixed
  intro f
  simp only [scheme, simulateQ_bind, fixed_keygen, bind_assoc, pure_bind, fixed_sign]
  simp only [simulateQ_pure, fixed_verify_honest, pure_bind,
    Bool.not_true, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
  simp

theorem admissible : scheme.Admissible where
  correct := correct
  verifyDeterministic := verify_deterministic
  signingFailure := signing_failure
  signatureSize := signature_size
  rejectsOversized := rejects_oversized
  keygenCost := keygen_cost
  signCost := sign_cost
  verifyCost := verification_budget

end OptimalOTS.LeanIsaBaseline
