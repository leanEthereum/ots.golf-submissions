import Submissions.UpperLeanIsa.Resources

namespace OptimalOTS.LeanIsaBaseline

open OracleComp

theorem encode_length (xs : Words) : (encode xs).length = 5504 := by
  have hw (y : Word) : (toBits y).length = 128 := by simp only [toBits, List.length_ofFn]
  have h (ys : List Word) : (ys.flatMap toBits).length = 128 * ys.length := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.flatMap_cons, List.length_append, hw, ih, List.length_cons]
      omega
  simpa only [encode, List.length_ofFn] using h (List.ofFn xs)

theorem signature_size : scheme.SignatureSizeAtMost maxSignatureBits := by
  intro sk m bits h
  change some bits ∈ support (sign sk m) at h
  simp only [sign, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
    Option.some.injEq] at h
  obtain ⟨xs, _, rfl⟩ := h
  rw [encode_length]
  norm_num [maxSignatureBits]

theorem rejects_oversized : scheme.RejectsOversized maxSignatureBits := by
  intro pk m bits h
  have hlen : bits.length ≠ 5504 := by unfold maxSignatureBits at h; omega
  change true ∉ support (verify pk m bits)
  simp [verify, hlen]

theorem signing_failure : scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) := by
  intro message
  have zero : probTrue (do
      let (pk, sk) ← scheme.keygen
      return (← scheme.sign sk (message pk)).isNone) = 0 := by
    rw [probTrue, probOutput_eq_zero_iff]
    intro h
    have raw := support_simulateQ_run'_subset oracleImpl _ ∅ h
    simp [scheme, sign] at raw
  rw [zero]
  exact zero_le

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

theorem deterministic_chain (i j n : ℕ) (x : Word) : Deterministic (chain i j n x) := by
  induction n generalizing j x with
  | zero => exact deterministic_pure _
  | succ n ih =>
    have h : Deterministic (chainStep i j x) :=
      deterministic_map (deterministic_hash _) _
    exact deterministic_bind h (fun y => ih (j + 1) y)

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

theorem deterministic_rootFold (xs : List Word) (cv : BitVec 256) :
    Deterministic (rootFold xs cv) := by
  induction xs generalizing cv with
  | nil => exact deterministic_pure _
  | cons x xs ih =>
    have h : Deterministic (absorb xs.length cv x) := deterministic_hash _
    exact deterministic_bind h ih

theorem verify_deterministic : scheme.VerifyDeterministic := by
  intro pk m bits
  change Deterministic (verify pk m bits)
  unfold verify
  split
  · exact deterministic_pure _
  · exact deterministic_bind
      (deterministic_tabulate _ (fun i => deterministic_chain _ _ _ _))
      (fun xs => deterministic_bind (deterministic_map (deterministic_rootFold _ _) _)
        (fun _ => deterministic_pure _))

end OptimalOTS.LeanIsaBaseline
