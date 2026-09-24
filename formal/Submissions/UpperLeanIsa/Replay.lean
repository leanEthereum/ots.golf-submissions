import Submissions.UpperLeanIsa.Coupling

/-! Honest chain computations replay the key-generation cache. In particular,
signing discloses the recorded cut and does not change the oracle cache. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleSpec
open scoped Classical
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem run_hash_hit {n : ℕ} (x : BitVec n) (c : Cache) (y : BitVec hashBits)
    (hc : c ⟨n, x⟩ = some y) : run (hash x) c = pure (y, c) := by
  change (simulateQ oracleImpl (liftM (Spec.query (.inr ⟨n, x⟩)))).run c = _
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_some hc

theorem Record.word_next (ξ : Record) (i : Fin 39) (j : Fin 127) :
    ξ.word i j.succ = (ξ.2 (.inl (i, j))).extractLsb' 0 128 := by
  simp only [Record.word, Fin.val_succ, dif_neg (Nat.succ_ne_zero j.val), Nat.add_sub_cancel]

theorem run_chain_record (ξ : Record) (c : Cache) (hc : Cache.Sub ξ.cache c)
    (i : Fin 39) (j n : ℕ) (hj : j + n ≤ 127) :
    run (chain i.val j n (ξ.word i ⟨j, by omega⟩)) c =
      pure (ξ.word i ⟨j + n, by omega⟩, c) := by
  induction n generalizing j with
  | zero => exact run_pure _ _
  | succ n ih =>
    let pos : Fin 127 := ⟨j, by omega⟩
    have hq : c ⟨896, chainInput i.val j (ξ.word i ⟨j, by omega⟩)⟩ =
        some (ξ.2 (.inl (i, pos))) := hc _ _ (ξ.cache_query (.inl (i, pos)))
    rw [chain, run_bind, chainStep, run_map, run_hash_hit _ c _ hq, map_pure, pure_bind]
    rw [← ξ.word_next i pos]
    have hn : j + 1 + n = j + (n + 1) := by omega
    simpa only [hn, pos, Fin.succ] using ih (j + 1) (by omega)

theorem run_tabulate_pure {α : Type} {n : ℕ} (f : Fin n → OracleComp Spec α)
    (v : Fin n → α) (c : Cache) (h : ∀ i, run (f i) c = pure (v i, c)) :
    run (tabulate f) c = pure (v, c) := by
  induction n with
  | zero =>
    rw [tabulate, run_pure]
    apply congrArg (fun x => pure (x, c))
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [tabulate, run_bind, h 0, pure_bind]
    rw [run_bind, ih (fun i => f i.succ) (fun i => v i.succ) (fun i => h i.succ),
      pure_bind, run_pure]
    apply congrArg (fun x => pure (x, c))
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

def Record.signature (ξ : Record) (m : Message) : List Bool :=
  encode (fun i => ξ.word i (afterSigning m i))

theorem signature_data_eq (m : Message) (ξ ζ : Record)
    (h : publicData (afterSigning m) ξ = publicData (afterSigning m) ζ) :
    ξ.signature m = ζ.signature m := by
  apply congrArg encode
  funext i
  exact data_word_eq (afterSigning m) ξ ζ h i (afterSigning m i) le_rfl

/-- This equality remains valid after any adversarial computation whose cache
extends the original honest cache. It does not assume an honest signing message. -/
theorem run_sign_record (ξ : Record) (c : Cache) (hc : Cache.Sub ξ.cache c) (m : Message) :
    run (sign ξ.1 m) c = pure (some (ξ.signature m), c) := by
  unfold sign
  rw [run_bind]
  have ht : run (tabulate (fun i : Fin 39 => chain i.val 0 (digit m i) (ξ.1 i))) c =
      pure ((fun i => ξ.word i (afterSigning m i)), c) := by
    apply run_tabulate_pure
    intro i
    simpa only [Nat.zero_add, afterSigning, Record.word, ↓reduceDIte] using
      run_chain_record ξ c hc i 0 (digit m i) (by simpa using digit_le m i)
  rw [ht, pure_bind, run_pure]
  rfl

end
end OptimalOTS.LeanIsaBaseline
