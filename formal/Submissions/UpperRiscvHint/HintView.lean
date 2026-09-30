import Submissions.UpperRiscvHint.MixedVerifier
import Submissions.UpperRiscvHint.HintTrap
import Submissions.UpperRiscvHint.ViewCompletion

/-! Views for the free-chain signature scheme. The capped view length L determines
the count 31 - (L % 128)/4. Counts below 19 use the fixed payload layout. Larger
counts select a raw encoding: the signature, one true marker, then zero padding
to a multiple of 128 bits. The marker makes this encoding injective for arbitrary
signature lengths. Both ordinary and oversized raw encodings have count 31 and
halt rejecting before a potentially faulting hash. Honest accepted signatures use
their index's free count in the view length. -/

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open OptimalOTS.RiscvHint RiscvZkvm.Rv64

-- Path equalities otherwise evaluate the checksum through the decision instance.
set_option allowUnsafeReducibility true in
attribute [local irreducible] stagedBlocks stagedRun freeBlocks freeRun instDecidablePredNatStagedRank

/-- Remove raw-form zero padding and its final true marker. -/
def rawDecode (view : List Bool) : List Bool :=
  ((view.reverse.dropWhile (! ·)).drop 1).reverse

def viewCompress (view : List Bool) : List Bool :=
  if 19 ≤ viewDigit view then rawDecode view
  else Completion.project (viewNonce view ++ viewPayload view)

/-- Raw signatures are marked then padded to at least 8192 bits and a multiple of 128 bits. The length count is 31,
including when the loader caps an oversized view. -/
def rawView (σ : List Bool) : List Bool :=
  (σ ++ [true]) ++ List.replicate ((127 - σ.length % 128) + (8192 - 128*(σ.length/128+1))) false

/-- The index query of a signature. -/
def indexQuery (pk : PublicKey) (m : Message) (σ : List Bool) :=
  swapHalves (emsg m pk ++ ofBits nonceBits (σ.take 128))

/-- The honest layout of a signature: its values in place, with its index's free count. -/
def layoutFull (pk : PublicKey) (m : Message) (σ : List Bool) : OracleComp Spec (List Bool) := do
  let answer ← hash (indexQuery pk m σ)
  pure (honestView (padFull σ) (freeDigit (pack answer) % 19))

def layoutView (pk : PublicKey) (m : Message) (σ : List Bool) : OracleComp Spec (List Bool) := do
  let full ← Completion.recover pk m σ
  match full with
  | none => pure (rawView σ)
  | some full => layoutFull pk m full

theorem getLsbD_flipHi (pk : PublicKey) (i : ℕ) :
    (flipHi pk).getLsbD i = (pk.getLsbD i ^^ decide (i = 64)) := by
  simp only [flipHi, BitVec.getLsbD_xor, BitVec.getLsbD_twoPow]
  by_cases h : i = 64
  · subst h; simp [pkBits]
  · simp [h, Ne.symm h]

theorem eq_flipHi_iff (r pk : PublicKey) :
    r = flipHi pk ↔ r.extractLsb' 0 64 = pk.extractLsb' 0 64 ∧
      r.extractLsb' 64 64 ^^^ pk.extractLsb' 64 64 = 1 := by
  have hpk : pkBits = 128 := rfl
  constructor
  · rintro rfl
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, getLsbD_flipHi, hi,
        decide_true, Bool.true_and, BitVec.getLsbD_one] <;>
      cases pk.getLsbD (0 + i) <;> cases pk.getLsbD (64 + i) <;> simp <;> omega
  · rintro ⟨hlo, hhi⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [hpk] at hi
    rw [getLsbD_flipHi]
    by_cases h : i < 64
    · have := congrArg (fun x => x.getLsbD i) hlo
      simp only [BitVec.getLsbD_extractLsb', h, decide_true, Bool.true_and, Nat.zero_add] at this
      rw [this]
      simp [show i ≠ 64 by omega]
    · have := congrArg (fun x => x.getLsbD (i - 64)) hhi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_one,
        show i - 64 < 64 by omega, decide_true, Bool.true_and,
        show 64 + (i - 64) = i by omega] at this
      by_cases h64 : i = 64
      · subst h64
        cases hr : r.getLsbD 64 <;> cases hp : pk.getLsbD 64 <;> simp_all
      · have h0 : i - 64 ≠ 0 := by omega
        cases hr : r.getLsbD i <;> cases hp : pk.getLsbD i <;> simp_all

theorem decisionOutcome_eq_true_iff (r pk : PublicKey) :
    decisionOutcome r pk = some true ↔ r = flipHi pk := by
  rw [eq_flipHi_iff]
  unfold decisionOutcome
  split_ifs with lo one zero
  · exact ⟨fun _ => ⟨lo, one⟩, fun _ => rfl⟩
  · exact ⟨(fun h => nomatch h), fun h => absurd h.2 one⟩
  · exact ⟨(fun h => nomatch h), fun h => absurd h.2 one⟩
  · exact ⟨(fun h => nomatch h), fun h => absurd h.1 lo⟩

/-- The decision accepts exactly the root whose flipped form is the public key. -/
theorem decisionOutcome_eq_true (r pk : PublicKey) :
    decisionOutcome r pk = some true ↔ flipHi r = pk := by
  rw [decisionOutcome_eq_true_iff]
  exact ⟨fun h => h ▸ flipHi_flipHi pk, fun h => h ▸ (flipHi_flipHi r).symm⟩

/-! ## The free count of a view -/

theorem viewDigit_honestView (σ : List Bool) (c : ℕ) (hc : c < 32) :
    viewDigit (honestView σ c) = c := by
  simp only [viewDigit, viewLength, honestView, List.length_ofFn, RiscvHint.maxViewBits]
  rw [Nat.min_eq_left (by omega)]
  omega

theorem viewBank_honestView (σ : List Bool) (c : ℕ) (hc : c < 32) :
    viewBank (honestView σ c) = 3 := by
  simp only [viewBank, viewLength, honestView, List.length_ofFn, RiscvHint.maxViewBits]
  omega

theorem viewBank_rawView (σ : List Bool) : 4 ≤ viewBank (rawView σ) := by
  simp only [viewBank, viewLength, rawView, List.length_append, List.length_cons,
    List.length_nil, List.length_replicate, RiscvHint.maxViewBits]
  omega

theorem viewDigit_rawView (σ : List Bool) : viewDigit (rawView σ) = 31 := by
  simp only [viewDigit, viewLength, rawView, List.length_append, List.length_cons,
    List.length_nil, List.length_replicate, RiscvHint.maxViewBits]
  have h := Nat.mod_lt σ.length (show 0 < 128 by omega)
  omega

theorem viewCompress_layout (σ : List Bool) (c : ℕ) (hc : c < 19) :
    viewCompress (honestView σ c) = Completion.project (viewNonce (honestView σ c) ++ viewPayload (honestView σ c)) :=
  if_neg (by rw [viewDigit_honestView σ c (by omega)]; omega)

theorem layout_compress (σ : List Bool) (len : σ.length = 5495 ∨ σ.length = 5498)
    (c : ℕ) (hc : c < 19) : viewCompress (honestView (padFull σ) c) = Completion.project σ := by
  rw [viewCompress_layout (padFull σ) c hc, viewNonce_honestView c (padFull_length len),
    viewPayload_honestView c (padFull_length len), List.take_append_drop, padFull_project len]

theorem raw_compress (σ : List Bool) : viewCompress (rawView σ) = σ := by
  unfold viewCompress
  rw [if_pos (by rw [viewDigit_rawView]; omega)]
  simp [rawDecode, rawView, List.reverse_append]

set_option allowUnsafeReducibility true in
attribute [local irreducible] honestView viewDigit viewLength

theorem layoutView_compress (pk : PublicKey) (m : Message) (σ : List Bool)
    (_h : true ∈ support (Completion.scheme.verify pk m σ)) :
    ∀ view ∈ support (layoutView pk m σ), viewCompress view = σ := by
  intro view hv
  unfold layoutView at hv
  rw [mem_support_bind_iff] at hv
  obtain ⟨full, hf, hv⟩ := hv
  cases full with
  | none =>
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv, raw_compress]
  | some full =>
    have member := Completion.findValid_mem pk m (Completion.candidates σ) full hf
    have hp := Completion.candidate_project member
    unfold layoutFull at hv
    rw [mem_support_bind_iff] at hv
    obtain ⟨answer, _, hv⟩ := hv
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv, layout_compress full (candidate_length member) _ (Nat.mod_lt _ (by omega)), hp]

theorem trap_raw (pk : PublicKey) (m : Message) (σ : List Bool) :
    ∀ o ∈ support (trapVerify pk m (rawView σ)), o = some false := by
  intro o ho
  unfold trapVerify at ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨answer, -, ho⟩ := ho
  have bank := viewBank_rawView σ
  rw [if_neg (by omega), if_pos (by omega), support_pure, Set.mem_singleton_iff] at ho
  exact ho

/-- The verdict on a staged run accepts exactly when the verifier's decision does. -/
theorem freeDecision_path (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (c₀ c₁ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (freeDecision index payload pk) (some true) c₀ c₁) :
    Riscv.cachedPaths.Path (freeBlocks index payload pk (fun _ => 0)) true c₀ c₁ := by
  unfold freeDecision at h
  rw [Riscv.cachedPaths.path_map] at h
  obtain ⟨o, ho, he⟩ := h
  obtain ⟨r, rfl⟩ : ∃ r, o = some r := by
    cases o with
    | none => simp at he
    | some r => exact ⟨r, rfl⟩
  have hflip : flipHi r = pk := (decisionOutcome_eq_true r pk).1 he
  rw [freeBlocks_eq_freeRun, Riscv.cachedPaths.path_map]
  exact ⟨some r, ho, by simp [hflip]⟩


/-- An accepting machine view contains a full signature accepted under the same cache. -/
theorem trap_full (pk : PublicKey) (m : Message) (view : List Bool)
    (c₀ c₁ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (trapVerify pk m view) (some true) c₀ c₁) :
    ∃ full : List Bool, (full.length = 5495 ∨ full.length = 5498) ∧
      Completion.project full = viewCompress view ∧
      Riscv.cachedPaths.Path (RiscvUpperForest.Wire.scheme.verify pk m full) true c₀ c₁ := by
  unfold trapVerify at h
  rw [Riscv.cachedPaths.path_bind] at h
  obtain ⟨answer, ca, ha, h⟩ := h
  dsimp only at h
  by_cases low : viewBank view < 3
  · rw [if_pos low, Riscv.cachedPaths.path_pure] at h
    exact absurd h.1 (by simp)
  rw [if_neg low] at h
  by_cases high : 3 < viewBank view
  · rw [if_pos high, Riscv.cachedPaths.path_pure] at h
    exact absurd h.1 (by simp)
  rw [if_neg high] at h
  by_cases big : 19 ≤ viewDigit view
  · rw [if_pos big, Riscv.cachedPaths.path_pure] at h
    exact absurd h.1 (by simp)
  rw [if_neg big] at h
  by_cases rank : freeDigit (executionIndex answer view).val = viewDigit view
  swap
  · rw [decide_eq_false rank] at h
    exact False.elim (checkedFreeDecision_false _ _ _
      (mem_support_of_mem_support_run _ _ ca c₁ h))
  have rank' : freeDigit (pack answer) = viewDigit view := by
    simpa only [executionIndex_val] using rank
  rw [decide_eq_true rank, checkedFreeDecision_true,
    executionIndex_canonical answer view rank'] at h
  have hr : stagedRank (pack answer) := by unfold stagedRank; omega
  have hi : pack answer ∈ validSet := mem_validSet.mpr ⟨pack_lt answer,
    (stagedRank_and_caps_iff _).mp ⟨hr, fun q => pairAllowed_all _ q⟩⟩
  let full := viewFull (rawIdx answer) view
  have hlen : full.length = fullSignatureBits (rawIdx answer) := viewFull_length _ _
  refine ⟨full, ?_, ?_, ?_⟩
  · rw [hlen]
    exact fullSignatureBits_cases _
  · rw [viewFull_project]
    exact (if_neg big).symm
  · rw [← stagedVerify_eq_wire]
    unfold stagedVerify
    rw [viewFull_nonce, ofBits_viewNonce, Riscv.cachedPaths.path_bind]
    refine ⟨answer, ca, ha, ?_⟩
    dsimp only
    rw [if_pos ⟨hr, hlen⟩, viewFull_payload]
    have takeEq := freeBlocks_take (⟨pack answer, hi⟩ : Idx) (viewPayload view) pk
    dsimp +instances only [Idx.toRaw] at takeEq
    change freeBlocks (rawIdx answer) ((viewPayload view).take (fullSignatureBits (rawIdx answer) - 128)) pk
      (fun _ => 0) = freeBlocks (rawIdx answer) (viewPayload view) pk (fun _ => 0) at takeEq
    change Riscv.cachedPaths.Path (freeBlocks (rawIdx answer)
      ((viewPayload view).take (fullSignatureBits (rawIdx answer) - 128)) pk (fun _ => 0)) true ca c₁
    rw [takeEq]
    exact freeDecision_path _ _ pk ca c₁ h

theorem trap_sound (pk : PublicKey) (m : Message) (view : List Bool)
    (c₀ c₁ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (trapVerify pk m view) (some true) c₀ c₁) :
    ∀ c₂, Subcache c₁ c₂ → ∀ b c₃,
      Riscv.cachedPaths.Path (Completion.scheme.verify pk m (viewCompress view)) b c₂ c₃ → b = true := by
  obtain ⟨full, hlen, hp, hf⟩ := trap_full pk m view c₀ c₁ h
  intro c₂ hsub b c₃ hb
  rw [← hp] at hb
  exact Completion.verify_from_accepted pk m full hlen c₀ c₁ hf c₂
    (fun _ _ hq => hsub hq) (b, c₃) hb

/-- Replaying a successful block computation forces the machine's root decision to accept. -/
theorem freeDecision_accepts (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (c₀ c₁ c₂ c₃ : hashSpec.QueryCache)
    (hv : Riscv.cachedPaths.Path (freeBlocks index payload pk (fun _ => 0)) true c₀ c₁)
    (hsub : Subcache c₁ c₂) (o : Option Bool)
    (h : Riscv.cachedPaths.Path (freeDecision index payload pk) o c₂ c₃) : o = some true := by
  unfold freeDecision at h
  rw [Riscv.cachedPaths.path_map] at h
  obtain ⟨result, hrun, rfl⟩ := h
  have hb : Riscv.cachedPaths.Path (freeBlocks index payload pk (fun _ => 0))
      (result.elim false fun r => decide (flipHi r = pk)) c₂ c₃ := by
    rw [freeBlocks_eq_freeRun, Riscv.cachedPaths.path_map]
    exact ⟨result, hrun, rfl⟩
  have replay := replay_deterministic _ (freeBlocks_deterministic index payload pk (fun _ => 0))
    c₀ c₁ c₂ true hv hsub
  change (_, c₃) ∈ support ((simulateQ oracleImpl _).run c₂) at hb
  rw [replay, support_pure, Set.mem_singleton_iff] at hb
  have accepted := congrArg Prod.fst hb
  cases result with
  | none => cases accepted
  | some r =>
    have hr : flipHi r = pk := of_decide_eq_true accepted
    exact (decisionOutcome_eq_true r pk).2 hr

theorem trap_accepts_full (pk : PublicKey) (m : Message) (σ : List Bool)
    (c₀ c₁ : hashSpec.QueryCache)
    (hv : Riscv.cachedPaths.Path (RiscvUpperForest.Wire.scheme.verify pk m σ) true c₀ c₁)
    (view : List Bool) (c₂ : hashSpec.QueryCache)
    (hl : Riscv.cachedPaths.Path (layoutFull pk m σ) view c₁ c₂)
    (o : Option Bool) (c₃ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (trapVerify pk m view) o c₂ c₃) : o = some true := by
  rw [← stagedVerify_eq_wire] at hv
  unfold stagedVerify at hv
  rw [Riscv.cachedPaths.path_bind] at hv
  obtain ⟨answer, ca, ha, hv⟩ := hv
  dsimp only at hv
  change Riscv.cachedPaths.Path
    (if stagedRank (pack answer) ∧ σ.length = fullSignatureBits (rawIdx answer) then
      freeBlocks (rawIdx answer) (σ.drop 128) pk (fun _ => 0) else pure false) true ca c₁ at hv
  by_cases guard : stagedRank (pack answer) ∧ σ.length = fullSignatureBits (rawIdx answer)
  swap
  · rw [if_neg guard, Riscv.cachedPaths.path_pure] at hv
    exact absurd hv.1 (by simp)
  rw [if_pos guard] at hv
  have hi : pack answer ∈ validSet := mem_validSet.mpr ⟨pack_lt answer,
    (stagedRank_and_caps_iff _).mp ⟨guard.1, fun q => pairAllowed_all _ q⟩⟩
  have hlen : σ.length = 5495 ∨ σ.length = 5498 := by
    rw [guard.2]
    exact fullSignatureBits_cases _
  have padded := padded_blocks (⟨pack answer, hi⟩ : Idx) σ guard.2 pk
  dsimp +instances only [Idx.toRaw] at padded
  change freeBlocks (rawIdx answer) ((padFull σ).drop 128) pk (fun _ => 0) =
    freeBlocks (rawIdx answer) (σ.drop 128) pk (fun _ => 0) at padded
  rw [← padded] at hv
  have hpad := padFull_length hlen
  have hnonce : 128 ≤ σ.length := by rcases hlen with hlen | hlen <;> omega
  have hgrow := subcache_run_grow _ ca _ c₁ hv
  unfold layoutFull indexQuery at hl
  rw [Riscv.cachedPaths.path_bind] at hl
  obtain ⟨a₁, cl, ha₁, hl⟩ := hl
  have hreplay := replay_deterministic _ (Deterministic.hash _) c₀ ca c₁ answer ha hgrow
  change (a₁, cl) ∈ support ((simulateQ oracleImpl _).run c₁) at ha₁
  rw [hreplay] at ha₁
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at ha₁
  obtain ⟨rfl, rfl⟩ := ha₁
  rw [Riscv.cachedPaths.path_pure] at hl
  obtain ⟨rfl, hc12⟩ := hl
  rw [hc12] at h
  have hc : freeDigit (pack a₁) % 19 = freeDigit (pack a₁) := by
    unfold stagedRank at guard
    exact Nat.mod_eq_of_lt guard.1
  generalize hcd : freeDigit (pack a₁) % 19 = c at h
  have hd := viewDigit_honestView (padFull σ) c (by omega)
  unfold trapVerify at h
  rw [← ofBits_viewNonce (honestView (padFull σ) c), viewNonce_honestView c hpad,
    padFull_nonce hnonce, Riscv.cachedPaths.path_bind] at h
  obtain ⟨a', cb, ha', h⟩ := h
  change (a', cb) ∈ support ((simulateQ oracleImpl _).run cl) at ha'
  rw [hreplay] at ha'
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at ha'
  obtain ⟨rfl, hcb⟩ := ha'
  rw [hcb] at h
  have rank' : freeDigit (pack a') = viewDigit (honestView (padFull σ) c) := by rw [hd]; omega
  have rankI : freeDigit (executionIndex a' (honestView (padFull σ) c)).val =
      viewDigit (honestView (padFull σ) c) := by rw [executionIndex_val]; exact rank'
  dsimp only at h
  rw [decide_eq_true rankI, checkedFreeDecision_true,
    executionIndex_canonical a' (honestView (padFull σ) c) rank',
    viewBank_honestView (padFull σ) c (by omega), if_neg (by omega), if_neg (by omega),
    hd, if_neg (by omega), viewPayload_honestView c hpad] at h
  exact freeDecision_accepts (rawIdx a') ((padFull σ).drop 128) pk ca cl cl c₃ hv
    (Subcache.refl cl) o h

theorem trap_accepts (pk : PublicKey) (m : Message) (σ : List Bool)
    (c₀ c₁ : hashSpec.QueryCache)
    (hv : Riscv.cachedPaths.Path (Completion.scheme.verify pk m σ) true c₀ c₁)
    (view : List Bool) (c₂ : hashSpec.QueryCache)
    (hl : Riscv.cachedPaths.Path (layoutView pk m σ) view c₁ c₂)
    (o : Option Bool) (c₃ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (trapVerify pk m view) o c₂ c₃) : o = some true := by
  obtain ⟨full, middle, recoverPath, fullPath, _⟩ := Completion.verify_path pk m σ c₀ c₁ hv
  unfold layoutView at hl
  rw [Riscv.cachedPaths.path_bind] at hl
  obtain ⟨result, cl, hr, hl⟩ := hl
  have hgrow := subcache_run_grow _ middle true c₁ fullPath
  have replay := replay_deterministic _
    (Completion.findValid_deterministic pk m (Completion.candidates σ))
    c₀ middle c₁ (some full) recoverPath hgrow
  change (simulateQ oracleImpl (Completion.recover pk m σ)).run c₁ = pure (some full, c₁) at replay
  change (result, cl) ∈ support ((simulateQ oracleImpl _).run c₁) at hr
  rw [replay, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact trap_accepts_full pk m full middle cl fullPath view c₂ hl o c₃ h

end OptimalOTS.RiscvMixedProgram
