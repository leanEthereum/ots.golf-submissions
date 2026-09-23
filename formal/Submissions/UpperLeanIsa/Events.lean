import Submissions.UpperLeanIsa.Transcript
import Submissions.UpperLeanIsa.CutTargets

/-!
# The forgery events of the second stage

On the run of the second stage from a cache containing the points exposed by the signature of
`ζ` at `m₁` (but none of its hidden points), an accepted fresh pair yields either a query of a
hidden point of `ζ`, or a cut-target hit (`events_stB`). Only the exposed data of `ζ` are used:
a table that respects the exposed points (`RespectsExposed`) reproduces every chain value from
the cut on (`chainValue_exposed`) and the public key (`rootValue_exposed`).

* A root second preimage on the verifier's cached root fold is a hit of an exposed root target
  (`root_spi_targetHit`).
* A chain second preimage at or after the cut, on the verifier's cached chain path, is a hit of
  an exposed chain target (`chain_spi_targetHit`).
* For a different message, some chain moves backwards past the cut; reaching the honest word at
  the cut from below is a hidden hit or a hit of the boundary target (`boundary_hit`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

-- `hashBits` stays reducible here: root states are `BitVec 256`, cache answers `BitVec hashBits`.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Tables respecting the exposed points -/

/-- The table respects `ζ` at every location exposed at cut `d` (all roots, and the chain
locations `(i, j)` with `d i ≤ j`). -/
def RespectsExposed (f : HashTable) (d : Cut) (ζ : Record) : Prop :=
  ∀ a, ¬ Hidden d a → f (ζ.query a) = ζ.2 a

theorem respectsExposed_of_sub (d : Cut) (ζ : Record) {c : Cache}
    (h : Cache.Sub (exposedCache d ζ) c) : RespectsExposed (table c) d ζ := by
  intro a ha
  have h1 : exposedCache d ζ (ζ.query a) = some (ζ.2 a) :=
    (exposedCache_some_iff d ζ _ _).2 ⟨a, ha, rfl, rfl⟩
  exact table_eq_of_some (h _ _ h1)

theorem chainValue_exposed (f : HashTable) (d : Cut) (ζ : Record) (hf : RespectsExposed f d ζ)
    (i : Fin 34) (j n : ℕ) (hj : (d i).val ≤ j) (hjn : j + n ≤ 255) :
    chainValue f i.val j n (ζ.word i ⟨j, by omega⟩) = ζ.word i ⟨j + n, by omega⟩ := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [chainValue]
    have hq : f ⟨896, chainInput i.val j (ζ.word i ⟨j, by omega⟩)⟩ =
        ζ.2 (.inl (i, ⟨j, by omega⟩)) :=
      hf (.inl (i, ⟨j, by omega⟩)) (by show ¬ j < (d i).val; omega)
    rw [hq]
    have hw : ζ.word i ⟨j + 1, by omega⟩ =
        (ζ.2 (.inl (i, ⟨j, by omega⟩))).extractLsb' 0 128 := by
      simp only [Record.word, dif_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
    rw [← hw]
    have hn : j + 1 + n = j + (n + 1) := by omega
    simpa only [hn] using ih (j + 1) (by omega) (by omega)

/-- The public key is determined by the (always exposed) root answers. -/
theorem rootValue_exposed (f : HashTable) (d : Cut) (ζ : Record) (hf : RespectsExposed f d ζ) :
    rootValue f ζ.endpoint = ζ.publicKey :=
  rootValue_record_of_roots f ζ (fun i => hf (.inr i) (fun h => h))

/-- Reaching the honest endpoint from a word at an exposed position either starts at the honest
word, or exhibits a second preimage of an honest step at or after that position. -/
theorem endpoint_match_exposed (f : HashTable) (d : Cut) (ζ : Record)
    (hf : RespectsExposed f d ζ) (i : Fin 34) (j : ℕ) (hj : (d i).val ≤ j) (hj' : j ≤ 255)
    (x : Word) (h : chainValue f i.val j (255 - j) x = ζ.endpoint i) :
    x = ζ.word i ⟨j, by omega⟩ ∨ ∃ k, ∃ hk : k < 255, j ≤ k ∧
      chainValue f i.val j (k - j) x ≠ ζ.word i ⟨k, by omega⟩ ∧
      stepValue f i.val k (chainValue f i.val j (k - j) x) =
        stepValue f i.val k (ζ.word i ⟨k, by omega⟩) := by
  have hend : ζ.word i ⟨j + (255 - j), by omega⟩ = ζ.endpoint i :=
    congrArg (ζ.word i) (Fin.ext (by show j + (255 - j) = 255; omega))
  have hhon : chainValue f i.val j (255 - j) (ζ.word i ⟨j, by omega⟩) = ζ.endpoint i :=
    (chainValue_exposed f d ζ hf i j (255 - j) hj (by omega)).trans hend
  rcases chain_merge f i.val j (255 - j) x (ζ.word i ⟨j, by omega⟩) (h.trans hhon.symm) with
    heq | ⟨k, hk, hne, hstep⟩
  · exact Or.inl heq
  · right
    have hw := chainValue_exposed f d ζ hf i j k hj (by omega)
    refine ⟨j + k, by omega, by omega, ?_, ?_⟩
    · rw [Nat.add_sub_cancel_left]
      rw [hw] at hne
      exact hne
    · rw [Nat.add_sub_cancel_left]
      rw [hw] at hstep
      exact hstep

/-! ## Records realising a given query -/

/-- A word placed in the low half of an answer. -/
private def padWord (y : Word) : BitVec hashBits := (0 : BitVec 128) ++ y

private theorem padWord_low (y : Word) : (padWord y).extractLsb' 0 128 = y :=
  BitVec.extractLsb'_append_eq_right (a := (0 : BitVec 128)) (b := y)

private def chainRecord (y : Word) : Record := (fun _ => y, fun _ => padWord y)

private def rootRecord (cv : BitVec 256) (x : Word) : Record :=
  (fun _ => 0, Sum.elim (fun _ => padWord x) (fun _ => cv))

/-- Every tagged chain input is the input of some record at its location. -/
theorem exists_record_chainInput (i : Fin 34) (j : Fin 255) (y : Word) :
    ∃ ζ : Record, ζ.query (.inl (i, j)) = ⟨896, chainInput i.val j.val y⟩ := by
  refine ⟨chainRecord y, ?_⟩
  have hw : (chainRecord y).word i j.castSucc = y := by
    unfold Record.word
    split
    · rfl
    · exact padWord_low y
  exact congrArg (fun x : Word => (⟨896, chainInput i.val j.val x⟩ : Query)) hw

/-- Every tagged root input is the input of some record at its location; at the first root
position the chaining value of every record is `0`. -/
theorem exists_record_rootInput (k : Fin 34) (cv : BitVec 256) (x : Word)
    (h0 : k.val = 0 → cv = 0) :
    ∃ ζ : Record, ζ.query (.inr k) = ⟨896, rootInput (rootTag k) cv x⟩ := by
  refine ⟨rootRecord cv x, ?_⟩
  have he : (rootRecord cv x).endpoint k = x :=
    ((rootRecord cv x).word_next k ⟨254, by omega⟩).trans (padWord_low x)
  have hb : (rootRecord cv x).rootBefore k = cv := by
    unfold Record.rootBefore
    split
    · rename_i h
      exact (h0 h).symm
    · rfl
  exact congrArg₂ (fun (a : BitVec 256) (b : Word) => (⟨896, rootInput (rootTag k) a b⟩ : Query))
    hb he

private theorem queryLocation_chainInput (i : Fin 34) (j : Fin 255) (y : Word) :
    queryLocation ⟨896, chainInput i.val j.val y⟩ = some (.inl (i, j)) := by
  obtain ⟨ζ', hζ'⟩ := exists_record_chainInput i j y
  rw [← hζ']
  exact queryLocation_query ζ' _

private theorem queryLocation_rootInput (k : Fin 34) (cv : BitVec 256) (x : Word)
    (h0 : k.val = 0 → cv = 0) :
    queryLocation ⟨896, rootInput (rootTag k) cv x⟩ = some (.inr k) := by
  obtain ⟨ζ', hζ'⟩ := exists_record_rootInput k cv x h0
  rw [← hζ']
  exact queryLocation_query ζ' _

/-! ## Matching answers -/

private theorem low_eq_setWidth {n : ℕ} (x : BitVec n) : x.extractLsb' 0 128 = x.setWidth 128 := by
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.ushiftRight_zero]

private theorem mem_lowAnswers {u v : BitVec hashBits}
    (h : u.extractLsb' 0 128 = v.extractLsb' 0 128) : u ∈ lowAnswers v := by
  unfold lowAnswers
  rw [Finset.mem_filter, ← low_eq_setWidth, ← low_eq_setWidth]
  exact ⟨Finset.mem_univ _, h⟩

private theorem mem_matchingAnswers_chain (ζ : Record) (a : ChainLocation) {u : BitVec hashBits}
    (hu : u ∈ lowAnswers (ζ.2 (.inl a))) : u ∈ matchingAnswers ζ (.inl a) := hu

private theorem mem_matchingAnswers_root (ζ : Record) (k : Fin 34) (hk : k ≠ 33) :
    ζ.2 (.inr k) ∈ matchingAnswers ζ (.inr k) := by
  change ζ.2 (.inr k) ∈ (if k = 33 then lowAnswers (ζ.2 (.inr k)) else {ζ.2 (.inr k)})
  rw [if_neg hk]
  exact Finset.mem_singleton_self _

private theorem mem_matchingAnswers_last (ζ : Record) (k : Fin 34) (hk : k = 33)
    {u : BitVec hashBits} (hu : u ∈ lowAnswers (ζ.2 (.inr k))) :
    u ∈ matchingAnswers ζ (.inr k) := by
  change u ∈ (if k = 33 then lowAnswers (ζ.2 (.inr k)) else {ζ.2 (.inr k)})
  rw [if_pos hk]
  exact hu

/-! ## Chain events -/

/-- A chain second preimage at an exposed location, on a cached verifier step, is a cut-target
hit. -/
theorem chain_spi_targetHit (m : Message) (ζ : Record) (c : Cache)
    (hc : Cache.Sub (exposedCache (afterSigning m) ζ) c)
    (i : Fin 34) (k : ℕ) (hk : k < 255) (hexp : digit m i ≤ k) (y : Word)
    (hy : y ≠ ζ.word i ⟨k, by omega⟩)
    (hcached : (c ⟨896, chainInput i.val k y⟩).isSome)
    (hmatch : stepValue (table c) i.val k y =
      stepValue (table c) i.val k (ζ.word i ⟨k, by omega⟩)) :
    TargetHit (cutTargets (afterSigning m) ζ) c := by
  have hf := respectsExposed_of_sub (afterSigning m) ζ hc
  have hnh : ¬ Hidden (afterSigning m) (.inl (i, ⟨k, hk⟩)) := by
    show ¬ k < digit m i
    omega
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcached
  refine ⟨⟨896, chainInput i.val k y⟩, u, hu, ?_⟩
  have hloc : queryLocation ⟨896, chainInput i.val k y⟩ = some (.inl (i, ⟨k, hk⟩)) :=
    queryLocation_chainInput i ⟨k, hk⟩ y
  have hne : ζ.query (.inl (i, ⟨k, hk⟩)) ≠ ⟨896, chainInput i.val k y⟩ := by
    intro h
    have h' : (⟨896, chainInput i.val k (ζ.word i ⟨k, by omega⟩)⟩ : Query) =
        ⟨896, chainInput i.val k y⟩ := h
    have hx := eq_of_heq (Sigma.mk.inj_iff.mp h').2
    exact hy ((chainInput_eq_iff i i ⟨k, hk⟩ ⟨k, hk⟩ _ _).mp hx).2.2.symm
  have h1 : stepValue (table c) i.val k y = u.extractLsb' 0 128 :=
    congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_eq_of_some hu)
  have h2 : stepValue (table c) i.val k (ζ.word i ⟨k, by omega⟩) =
      (ζ.2 (.inl (i, ⟨k, hk⟩))).extractLsb' 0 128 :=
    congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (hf (.inl (i, ⟨k, hk⟩)) hnh)
  exact mem_cutTargets_exposed hloc hnh hne
    (mem_matchingAnswers_chain ζ (i, ⟨k, hk⟩) (mem_lowAnswers (h1.symm.trans (hmatch.trans h2))))

/-- A cached verifier step just below the cut whose output is the signed word: either the
honest hidden input was queried, or the boundary target was hit. -/
theorem boundary_hit (m : Message) (ζ : Record) (c : Cache)
    (hc : Cache.Sub (exposedCache (afterSigning m) ζ) c) (i : Fin 34) (hpos : 0 < digit m i)
    (y : Word) (hcached : (c ⟨896, chainInput i.val (digit m i - 1) y⟩).isSome)
    (hmatch : stepValue (table c) i.val (digit m i - 1) y =
      ζ.word i ⟨digit m i, by have := digit_le m i; omega⟩) :
    Cache.Hits c (hiddenCache (afterSigning m) ζ) ∨
      TargetHit (cutTargets (afterSigning m) ζ) c := by
  have hd := digit_le m i
  have he : digit m i - 1 < 255 := by omega
  have hhid : Hidden (afterSigning m) (.inl (i, ⟨digit m i - 1, he⟩)) := by
    show digit m i - 1 < digit m i
    omega
  by_cases hy : y = ζ.word i ⟨digit m i - 1, by omega⟩
  · left
    refine ⟨⟨896, chainInput i.val (digit m i - 1) y⟩, ?_, hcached⟩
    refine (hiddenCache_isSome_iff (afterSigning m) ζ _).2
      ⟨.inl (i, ⟨digit m i - 1, he⟩), hhid, ?_⟩
    exact (congrArg (fun x : Word => (⟨896, chainInput i.val (digit m i - 1) x⟩ : Query)) hy).symm
  · right
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcached
    refine ⟨⟨896, chainInput i.val (digit m i - 1) y⟩, u, hu, ?_⟩
    have hloc : queryLocation ⟨896, chainInput i.val (digit m i - 1) y⟩ =
        some (.inl (i, ⟨digit m i - 1, he⟩)) :=
      queryLocation_chainInput i ⟨digit m i - 1, he⟩ y
    have hbd : Boundary (afterSigning m) (.inl (i, ⟨digit m i - 1, he⟩)) := by
      show digit m i - 1 + 1 = digit m i
      omega
    have h1 : stepValue (table c) i.val (digit m i - 1) y = u.extractLsb' 0 128 :=
      congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_eq_of_some hu)
    have h2 : ζ.word i ⟨digit m i, by omega⟩ =
        (ζ.2 (.inl (i, ⟨digit m i - 1, he⟩))).extractLsb' 0 128 :=
      (congrArg (ζ.word i) (Fin.ext (by show digit m i = digit m i - 1 + 1; omega))).trans
        (ζ.word_next i ⟨digit m i - 1, he⟩)
    exact mem_cutTargets_boundary hloc hhid hbd
      (mem_matchingAnswers_chain ζ _ (mem_lowAnswers (h1.symm.trans (hmatch.trans h2))))

/-- Same message, different signature: the decoded word at the cut differs from the signed one
but reaches the honest endpoint, so an exposed chain target is hit. -/
private theorem same_message_chain (m : Message) (ζ : Record) (c : Cache)
    (hc : Cache.Sub (exposedCache (afterSigning m) ζ) c) (i : Fin 34) (y : Word)
    (hy : y ≠ ζ.word i (afterSigning m i))
    (hpath : ChainPath c i.val (digit m i) (255 - digit m i) y)
    (hend : chainValue (table c) i.val (digit m i) (255 - digit m i) y = ζ.endpoint i) :
    TargetHit (cutTargets (afterSigning m) ζ) c := by
  have hd := digit_le m i
  have hf := respectsExposed_of_sub (afterSigning m) ζ hc
  rcases endpoint_match_exposed (table c) (afterSigning m) ζ hf i (digit m i) (Nat.le_refl _) hd
      y hend with heq | ⟨k, hk, hjk, hne, hstep⟩
  · exact absurd heq hy
  · have hcached := hpath.cached (k := k) hjk (by omega)
    exact chain_spi_targetHit m ζ c hc i k hk hjk _ hne hcached hstep

/-- Different message: chain `i` starts strictly below the cut and reaches the honest endpoint.
Either it passes the honest word at the cut (boundary event) or it merges later (exposed chain
target). -/
private theorem diff_message_chain (m : Message) (ζ : Record) (c : Cache)
    (hc : Cache.Sub (exposedCache (afterSigning m) ζ) c) (i : Fin 34) (e : ℕ)
    (he : e < digit m i) (y : Word) (hpath : ChainPath c i.val e (255 - e) y)
    (hend : chainValue (table c) i.val e (255 - e) y = ζ.endpoint i) :
    Cache.Hits c (hiddenCache (afterSigning m) ζ) ∨
      TargetHit (cutTargets (afterSigning m) ζ) c := by
  have hd := digit_le m i
  have hf := respectsExposed_of_sub (afterSigning m) ζ hc
  have hmid : chainValue (table c) i.val (digit m i) (255 - digit m i)
      (chainValue (table c) i.val e (digit m i - e) y) = ζ.endpoint i := by
    have h := chainValue_add (table c) i.val e (digit m i - e) (255 - digit m i) y
    rw [show e + (digit m i - e) = digit m i by omega,
      show digit m i - e + (255 - digit m i) = 255 - e by omega] at h
    exact h.trans hend
  rcases endpoint_match_exposed (table c) (afterSigning m) ζ hf i (digit m i) (Nat.le_refl _) hd
      _ hmid with heq | ⟨k, hk, hjk, hne, hstep⟩
  · -- the path passes the honest word at the cut: its previous step is the boundary step
    have hpos : 0 < digit m i := by omega
    have hcached' : (c ⟨896, chainInput i.val (digit m i - 1)
        (chainValue (table c) i.val e (digit m i - 1 - e) y)⟩).isSome :=
      hpath.cached (by omega) (by omega)
    have hmatch' : stepValue (table c) i.val (digit m i - 1)
        (chainValue (table c) i.val e (digit m i - 1 - e) y) =
        ζ.word i ⟨digit m i, by omega⟩ := by
      have h := chainValue_snoc (table c) i.val e (digit m i - 1 - e) y
      rw [show digit m i - 1 - e + 1 = digit m i - e by omega,
        show e + (digit m i - 1 - e) = digit m i - 1 by omega] at h
      exact h.symm.trans heq
    exact boundary_hit m ζ c hc i hpos _ hcached' hmatch'
  · -- the path merges with the honest chain at or after the cut
    right
    have hY : chainValue (table c) i.val (digit m i) (k - digit m i)
        (chainValue (table c) i.val e (digit m i - e) y) =
        chainValue (table c) i.val e (k - e) y := by
      have h := chainValue_add (table c) i.val e (digit m i - e) (k - digit m i) y
      rw [show e + (digit m i - e) = digit m i by omega,
        show digit m i - e + (k - digit m i) = k - e by omega] at h
      exact h
    have hcached := hpath.cached (k := k) (by omega) (by omega)
    rw [← hY] at hcached
    exact chain_spi_targetHit m ζ c hc i k hk hjk _ hne hcached hstep

/-! ## Root events -/

private theorem rootState_succ (ζ : Record) (j : ℕ) (hj : j < 34) :
    ζ.rootState ⟨j + 1, by omega⟩ = ζ.2 (.inr ⟨j, hj⟩) :=
  ζ.rootState_after ⟨j, hj⟩

/-- The honest absorption at root position `j` (with `r = 33 - j` words remaining). -/
private theorem honest_absorb (ζ : Record) (f : HashTable)
    (hroot : ∀ k : Fin 34, f (ζ.query (.inr k)) = ζ.2 (.inr k))
    (j : ℕ) (hj : j < 34) (r : ℕ) (hr : r + j = 33) :
    absorbValue f r (ζ.rootState ⟨j, by omega⟩) (ζ.endpoint ⟨j, hj⟩) = ζ.2 (.inr ⟨j, hj⟩) := by
  have hr' : r = 33 - j := by omega
  subst hr'
  exact hroot ⟨j, hj⟩

private theorem rsp_single (f : HashTable) (x y : Word) (cv dv : BitVec 256) :
    RootSecondPreimage f [x] cv [y] dv ↔
      (cv ≠ dv ∨ x ≠ y) ∧
        (absorbValue f 0 cv x).extractLsb' 0 128 = (absorbValue f 0 dv y).extractLsb' 0 128 :=
  Iff.rfl

private theorem rsp_cons (f : HashTable) (x y : Word) (xs ys : List Word) (cv dv : BitVec 256)
    (hx : xs ≠ []) :
    RootSecondPreimage f (x :: xs) cv (y :: ys) dv ↔
      ((cv ≠ dv ∨ x ≠ y) ∧ absorbValue f xs.length cv x = absorbValue f ys.length dv y) ∨
        RootSecondPreimage f xs (absorbValue f xs.length cv x) ys
          (absorbValue f ys.length dv y) := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x' xs => exact Iff.rfl

private theorem ofFn_offset_succ (v : Fin 34 → Word) (n j : ℕ) (hj : j + (n + 1) = 34) :
    List.ofFn (fun t : Fin (n + 1) => v ⟨j + t.val, by have := t.isLt; omega⟩) =
      v ⟨j, by omega⟩ ::
        List.ofFn (fun t : Fin n => v ⟨j + 1 + t.val, by have := t.isLt; omega⟩) := by
  rw [List.ofFn_succ]
  refine congrArg₂ List.cons ?_ ?_
  · apply congrArg v
    apply Fin.ext
    simp
  · apply congrArg List.ofFn
    funext t
    apply congrArg v
    apply Fin.ext
    first
      | (show j + (t.val + 1) = j + 1 + t.val; omega)
      | (simp only [Fin.val_succ]; omega)
      | (dsimp; omega)

/-- A mismatching absorption at root position `k` with a matching (exposed) answer. -/
private theorem root_targetHit (d : Cut) (ζ : Record) (c : Cache) (k : Fin 34) (r : ℕ)
    (hr : r = 33 - k.val) (cv : BitVec 256) (x : Word) (h0 : k.val = 0 → cv = 0)
    (hne : cv ≠ ζ.rootBefore k ∨ x ≠ ζ.endpoint k)
    (hcached : (c ⟨896, LeanIsa.hashInput cv (x.setWidth 512)
      (BitVec.ofNat 128 (2 + r))⟩).isSome)
    (hmatch : absorbValue (table c) r cv x ∈ matchingAnswers ζ (.inr k)) :
    TargetHit (cutTargets d ζ) c := by
  subst hr
  have hcached' : (c ⟨896, rootInput (rootTag k) cv x⟩).isSome := hcached
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcached'
  refine ⟨⟨896, rootInput (rootTag k) cv x⟩, u, hu, ?_⟩
  have hnq : ζ.query (.inr k) ≠ ⟨896, rootInput (rootTag k) cv x⟩ := by
    intro h
    have h' : (⟨896, rootInput (rootTag k) (ζ.rootBefore k) (ζ.endpoint k)⟩ : Query) =
        ⟨896, rootInput (rootTag k) cv x⟩ := h
    obtain ⟨-, h1, h2⟩ :=
      (rootInput_eq_iff _ _ _ _ _ _).mp (eq_of_heq (Sigma.mk.inj_iff.mp h').2)
    rcases hne with hne | hne
    · exact hne h1.symm
    · exact hne h2.symm
  have hnh : ¬ Hidden d (.inr k) := fun h => h
  have hu' : absorbValue (table c) (33 - k.val) cv x = u := table_eq_of_some hu
  rw [hu'] at hmatch
  exact mem_cutTargets_exposed (queryLocation_rootInput k cv x h0) hnh hnq hmatch

/-- Root second preimages on suffixes of the fold: the forged suffix from position `j` (state
`cv`) against the honest suffix from position `j` (state `ζ.rootState j`). -/
private theorem root_spi_suffix (d : Cut) (ζ : Record) (c : Cache)
    (hroot : ∀ k : Fin 34, table c (ζ.query (.inr k)) = ζ.2 (.inr k)) (xs : Words) :
    ∀ (n j : ℕ) (hj : j + n = 34) (cv : BitVec 256), (j = 0 → cv = 0) →
      RootPath c (List.ofFn fun t : Fin n => xs ⟨j + t.val, by have := t.isLt; omega⟩) cv →
      RootSecondPreimage (table c)
        (List.ofFn fun t : Fin n => xs ⟨j + t.val, by have := t.isLt; omega⟩) cv
        (List.ofFn fun t : Fin n => ζ.endpoint ⟨j + t.val, by have := t.isLt; omega⟩)
        (ζ.rootState ⟨j, by omega⟩) →
      TargetHit (cutTargets d ζ) c := by
  intro n
  induction n with
  | zero =>
    intro j hj cv _ _ hspi
    simp only [List.ofFn_zero] at hspi
    exact False.elim hspi
  | succ n ih =>
    intro j hj cv h0 hpath hspi
    have hjlt : j < 34 := by omega
    rw [ofFn_offset_succ xs n j hj] at hpath hspi
    rw [ofFn_offset_succ ζ.endpoint n j hj] at hspi
    obtain ⟨hcached, hpath'⟩ := hpath
    cases n with
    | zero =>
      -- the last absorption (`j = 33`): only the low 128 output bits are compared
      have hspi' : RootSecondPreimage (table c) [xs ⟨j, hjlt⟩] cv [ζ.endpoint ⟨j, hjlt⟩]
          (ζ.rootState ⟨j, by omega⟩) := by
        simpa only [List.ofFn_zero] using hspi
      obtain ⟨hne, heq⟩ := (rsp_single (table c) _ _ _ _).1 hspi'
      have hk : (⟨j, hjlt⟩ : Fin 34) = 33 :=
        Fin.ext (by first | (show j = 33; omega) | (simp; omega) | simp)
      have honest : absorbValue (table c) 0 (ζ.rootState ⟨j, by omega⟩) (ζ.endpoint ⟨j, hjlt⟩) =
          ζ.2 (.inr ⟨j, hjlt⟩) :=
        honest_absorb ζ (table c) hroot j hjlt 0 (by omega)
      have hlow : (absorbValue (table c) 0 cv (xs ⟨j, hjlt⟩)).extractLsb' 0 128 =
          (ζ.2 (.inr ⟨j, hjlt⟩)).extractLsb' 0 128 :=
        heq.trans (congrArg (fun z : BitVec 256 => z.extractLsb' 0 128) honest)
      rw [List.length_ofFn] at hcached
      exact root_targetHit d ζ c ⟨j, hjlt⟩ 0 (by show 0 = 33 - j; omega) cv (xs ⟨j, hjlt⟩) h0
        hne hcached (mem_matchingAnswers_last ζ ⟨j, hjlt⟩ hk (mem_lowAnswers hlow))
    | succ n =>
      have hLne : (List.ofFn fun t : Fin (n + 1) =>
          xs ⟨j + 1 + t.val, by have := t.isLt; omega⟩) ≠ [] :=
        List.ne_nil_of_length_pos (by rw [List.length_ofFn]; omega)
      have hk : (⟨j, hjlt⟩ : Fin 34) ≠ 33 :=
        fun h => absurd (congrArg Fin.val h)
          (by first | (show j ≠ 33; omega) | (simp; omega) | simp)
      have hH : absorbValue (table c) (List.ofFn fun t : Fin (n + 1) =>
          ζ.endpoint ⟨j + 1 + t.val, by have := t.isLt; omega⟩).length
          (ζ.rootState ⟨j, by omega⟩) (ζ.endpoint ⟨j, hjlt⟩) = ζ.2 (.inr ⟨j, hjlt⟩) := by
        rw [List.length_ofFn]
        exact honest_absorb ζ (table c) hroot j hjlt (n + 1) (by omega)
      rcases (rsp_cons (table c) _ _ _ _ _ _ hLne).1 hspi with ⟨hne, heq⟩ | hrec
      · -- first mismatch at position `j`, full 256-bit match
        refine root_targetHit d ζ c ⟨j, hjlt⟩ _ ?_ cv (xs ⟨j, hjlt⟩) h0 hne hcached ?_
        · rw [List.length_ofFn]
          show n + 1 = 33 - j
          omega
        · rw [heq, hH]
          exact mem_matchingAnswers_root ζ ⟨j, hjlt⟩ hk
      · -- the honest states agree so far: continue at position `j + 1`
        rw [hH, ← rootState_succ ζ j hjlt] at hrec
        exact ih (j + 1) (by omega) _ (fun h => absurd h (Nat.succ_ne_zero j)) hpath' hrec

/-- A root second preimage on the verifier's cached root fold is a cut-target hit. -/
theorem root_spi_targetHit (m : Message) (ζ : Record) (c : Cache)
    (hc : Cache.Sub (exposedCache (afterSigning m) ζ) c)
    (xs : Words) (hpath : RootPath c (List.ofFn xs) 0)
    (hspi : RootSecondPreimage (table c) (List.ofFn xs) 0 (List.ofFn ζ.endpoint) 0) :
    TargetHit (cutTargets (afterSigning m) ζ) c := by
  have hf := respectsExposed_of_sub (afterSigning m) ζ hc
  have hroot : ∀ k : Fin 34, table c (ζ.query (.inr k)) = ζ.2 (.inr k) :=
    fun k => hf (.inr k) (fun h => h)
  have hx : (fun t : Fin 34 => xs ⟨0 + t.val, by have := t.isLt; omega⟩) = xs := by
    funext t
    simp only [Nat.zero_add]
  have he : (fun t : Fin 34 => ζ.endpoint ⟨0 + t.val, by have := t.isLt; omega⟩) =
      ζ.endpoint := by
    funext t
    simp only [Nat.zero_add]
  have h0 : ζ.rootState ⟨0, by omega⟩ = 0 := by
    first | rfl | simp [Record.rootState]
  refine root_spi_suffix (afterSigning m) ζ c hroot xs 34 0 rfl 0 (fun _ => rfl) ?_ ?_
  · rw [hx]
    exact hpath
  · rw [hx, he, h0]
    exact hspi

/-! ## The events lemma -/

section StageB

variable (A : OracleAlgorithm.Adversary)

/-- On the exposed stage-B run, an accepted fresh pair yields a hidden hit or a cut-target
hit. -/
theorem events_stB (pk : PublicKey) (m₁ : Message) (st : A.State) (ζ : Record) (c : Cache)
    (hc : Cache.Sub (exposedCache (afterSigning m₁) ζ) c) (hpk : ζ.publicKey = pk)
    (p : Bool × Cache) (hp : p ∈ support (run (stB A pk m₁ st (some (ζ.signature m₁))) c))
    (hok : p.1 = true) :
    Cache.Hits p.2 (hiddenCache (afterSigning m₁) ζ) ∨
      TargetHit (cutTargets (afterSigning m₁) ζ) p.2 := by
  obtain ⟨hcp, h⟩ := stB_support A pk m₁ st (some (ζ.signature m₁)) c p hp
  obtain ⟨m₂, σ₂, hne, hlen, hroot, hchains, hrpath⟩ := h hok
  have hsub : Cache.Sub (exposedCache (afterSigning m₁) ζ) p.2 := hc.trans hcp
  have hf := respectsExposed_of_sub (afterSigning m₁) ζ hsub
  have hroot' : rootValue (table p.2) (reconstructedWords (table p.2) m₂ σ₂) =
      rootValue (table p.2) ζ.endpoint :=
    hroot.trans ((rootValue_exposed (table p.2) (afterSigning m₁) ζ hf).trans hpk).symm
  rcases root_value_match (table p.2) _ _ hroot' with hrec | hspi
  · by_cases hm : m₂ = m₁
    · -- same message, different signature
      right
      have hσ : σ₂ ≠ ζ.signature m₁ := by
        intro h
        apply hne
        show some (m₁, ζ.signature m₁) = some (m₂, σ₂)
        rw [hm, h]
      have hd : decode σ₂ ≠ fun i => ζ.word i (afterSigning m₁ i) := by
        intro h
        apply hσ
        show σ₂ = encode (fun i => ζ.word i (afterSigning m₁ i))
        rw [← encode_decode σ₂ hlen, h]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
      have hpath : ChainPath p.2 i.val (digit m₁ i) (255 - digit m₁ i) (decode σ₂ i) := by
        rw [← hm]
        exact hchains i
      have hend : chainValue (table p.2) i.val (digit m₁ i) (255 - digit m₁ i) (decode σ₂ i) =
          ζ.endpoint i := by
        rw [← hm]
        exact congrFun hrec i
      exact same_message_chain m₁ ζ p.2 hsub i (decode σ₂ i) hi hpath hend
    · -- different message: some chain moves backwards past the cut
      obtain ⟨i, hi⟩ := exists_lower_digit (Ne.symm hm)
      exact diff_message_chain m₁ ζ p.2 hsub i (digit m₂ i) hi (decode σ₂ i) (hchains i)
        (congrFun hrec i)
  · right
    exact root_spi_targetHit m₁ ζ p.2 hsub _ hrpath hspi

end StageB

end OptimalOTS.LeanIsaBaseline

end
