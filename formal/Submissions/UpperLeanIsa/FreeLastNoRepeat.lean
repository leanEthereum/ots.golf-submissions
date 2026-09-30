import Submissions.UpperLeanIsa.PackedSupport

/-! A fixed committed image has at most one successful successor at every
instruction, even under the uncached oracle semantics. Thus a completing run
cannot return to a register state. The free-last design needs this fact to
exclude stage and prologue re-entry without relying on hash binding. -/
namespace OptimalOTS.FreeLastNoRepeat
open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section DeterministicPath
variable {S : Type} (next : S → Option S) (stop : S → Prop)

inductive Run : Nat → S → Prop
  | done {r} : stop r → Run 0 r
  | step {n r s} : ¬stop r → next r = some s → Run n s → Run (n+1) r

inductive Prefix : Nat → S → S → Prop
  | refl (r) : Prefix 0 r r
  | step {n r s t} : ¬stop r → next r = some s → Prefix n s t → Prefix (n+1) r t

theorem length_unique {n m : Nat} {r : S}
    (h : Run next stop n r) (h' : Run next stop m r) : n = m := by
  induction h generalizing m with
  | done h =>
    cases h' with
    | done => rfl
    | step hn => exact (hn h).elim
  | step hn hs ht ih =>
    cases h' with
    | done hp => exact (hn hp).elim
    | step hn' hs' ht' =>
      have he := Option.some.inj (hs.symm.trans hs')
      subst he
      exact congrArg Nat.succ (ih ht')

theorem prefix_run {n m : Nat} {r s : S}
    (h : Prefix next stop n r s) (h' : Run next stop m s) :
    Run next stop (n+m) r := by
  induction h with
  | refl => simpa using h'
  | step hn hs ht ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using Run.step hn hs (ih h')

theorem no_return {n m : Nat} {r : S} (hn : 0 < n)
    (hp : Prefix next stop n r r) (hr : Run next stop m r) : False := by
  have he := length_unique next stop (prefix_run next stop hp hr) hr
  omega
end DeterministicPath

/-- Hash answers can reject a step; they cannot choose a successful successor. -/
def successor {κ : Nat} (M : MemImage κ) (r : Regs K) : Instr → Option (Regs K)
  | .blake2s .. => some r.next
  | i => LeanerVM.Semantics.execute M r i

theorem execute_successor {κ : Nat} (M : MemImage κ) (Sm : Sem)
    (r : Regs K) (i : Instr) {s : Regs K}
    (h : some s ∈ Sm.S (LeanIsa.execute M r i)) : successor M r i = some s := by
  cases i with
  | blake2s om cv out md =>
    simp only [LeanIsa.execute] at h
    split at h
    · rw [Sm.pure_iff] at h
      exact (Option.some_ne_none _ h).elim
    · rw [Sm.bind_iff] at h
      obtain ⟨ans, _, hh⟩ := h
      rw [Sm.pure_iff] at hh
      split_ifs at hh
      · exact hh.symm
  | _ => exact (Sm.pure_iff _ _).mp h |>.symm

def machineNext {κ : Nat} (P : Program) (M : MemImage κ) (r : Regs K) : Option (Regs K) :=
  (P.fetch r.pc).bind (successor M r)

def machineStop (P : Program) (r : Regs K) : Prop := r.pc = P.finalPc ∧ r.fp = 1

/-- Extract the deterministic path from any completing oracle execution. -/
theorem run_path {κ : Nat} (P : Program) (M : MemImage κ) (Sm : Sem)
    {n c : Nat} {r : Regs K}
    (h : some c ∈ Sm.S (LeanIsa.runCost P M n r)) :
    Run (machineNext P M) (machineStop P) n r := by
  induction n generalizing c r with
  | zero =>
    rw [LeanIsa.runCost.eq_1, Sm.pure_iff] at h
    split_ifs at h with hs
    · exact Run.done hs
  | succ n ih =>
    rw [LeanIsa.runCost.eq_2] at h
    split_ifs at h with hn
    · exact (Sm.some_not_pure_none h).elim
    · split at h
      · exact (Sm.some_not_pure_none h).elim
      · rename_i ins hf
        rw [Sm.bind_iff] at h
        obtain ⟨o, ho, hc⟩ := h
        cases o with
        | none => exact (Sm.some_not_pure_none hc).elim
        | some s =>
          obtain ⟨c', _, hc'⟩ := Sm.some_map_add hc
          exact Run.step (fun hs => hn hs.1)
            (by simp only [machineNext, hf, Option.bind_some]; exact execute_successor M Sm r ins ho)
            (ih hc')

theorem completing_length_unique {κ : Nat} (P : Program) (M : MemImage κ) (Sm Sm' : Sem)
    {n m c d : Nat} {r : Regs K}
    (h : some c ∈ Sm.S (LeanIsa.runCost P M n r))
    (h' : some d ∈ Sm'.S (LeanIsa.runCost P M m r)) : n = m :=
  length_unique _ _ (run_path P M Sm h) (run_path P M Sm' h')

/-- This applies in particular to `suppSem`, used for the universal cycle bound. -/
theorem completing_no_return {κ : Nat} (P : Program) (M : MemImage κ) (Sm : Sem)
    {n m c : Nat} {r : Regs K} (hn : 0 < n)
    (hp : Prefix (machineNext P M) (machineStop P) n r r)
    (hr : some c ∈ Sm.S (LeanIsa.runCost P M m r)) : False :=
  no_return _ _ hn hp (run_path P M Sm hr)

end
end OptimalOTS.FreeLastNoRepeat
