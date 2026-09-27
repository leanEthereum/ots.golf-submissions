import Submissions.UpperRiscvHint.MixedVerifier
import Submissions.UpperRiscvHint.HintTrap

/-! In-place views of the free-chain scheme's signatures. A view whose free count (bits `2 … 7` of
view byte 64) is below 16 holds the nonce and every chain value at fixed positions, and `compress`
extracts them in signature order. A view with a larger count carries a raw signature after view
byte 64; the image rejects it at the free dispatch, before its first possible trap. The honest
prover lays out accepted signatures with the free count of their index, and hands every other
signature over in the raw form (`HintTrap`). -/

noncomputable section

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open OptimalOTS.RiscvHint RiscvZkvm.Rv64

-- Path equalities otherwise evaluate the checksum through the decision instance.
set_option allowUnsafeReducibility true in
attribute [local irreducible] stagedBlocks stagedRun freeBlocks freeRun instDecidablePredNatStagedRank

/-- A raw view carries its signature after these bits: view byte 64 is the free count. -/
def rawFlagBits : ℕ := 520

def viewCompress (view : List Bool) : List Bool :=
  if 16 ≤ viewDigit view then view.drop rawFlagBits
  else viewNonce view ++ viewPayload view

/-- The raw form: free count 63, then the signature. -/
def rawView (σ : List Bool) : List Bool :=
  List.replicate 512 false ++ List.replicate 8 true ++ σ

/-- The index query of a signature. -/
def indexQuery (pk : PublicKey) (m : Message) (σ : List Bool) :=
  swapHalves (emsg m pk ++ ofBits nonceBits (σ.take 128))

/-- The honest layout of a signature: its values in place, with its index's free count. -/
def layoutView (pk : PublicKey) (m : Message) (σ : List Bool) : OracleComp Spec (List Bool) := do
  let answer ← hash (indexQuery pk m σ)
  pure (honestView σ (freeDigit (pack answer) % 16))

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

theorem honestView_free (σ : List Bool) (c b : ℕ) (hb : freeBit ≤ b ∧ b < freeBit + 8) :
    (honestView σ c).getD b false = (4 * c).testBit (b - freeBit) := by
  have hl : b < honestViewBits := by unfold freeBit honestViewBits at *; omega
  unfold honestView
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hl, Option.getD_some]
  exact if_pos hb

theorem viewDigit_honestView (σ : List Bool) (c : ℕ) (hc : c < 64) :
    viewDigit (honestView σ c) = c := by
  have e : ofBits 8 ((honestView σ c).drop 512) = BitVec.ofNat 8 (4 * c) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
      testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [← List.getD_eq_getElem?_getD, honestView_free σ c (512 + i) (by unfold freeBit; omega)]
    unfold freeBit
    rw [show 512 + i - 512 = i by omega]
  unfold viewDigit
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem viewDigit_rawView (σ : List Bool) : viewDigit (rawView σ) = 63 := by
  have e : ofBits 8 ((rawView σ).drop 512) = BitVec.ofNat 8 255 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
      testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_drop]
    have hbit : (rawView σ)[512 + i]? = some true := by
      unfold rawView
      rw [List.getElem?_append_left (by simp only [List.length_append, List.length_replicate]; omega),
        List.getElem?_append_right (by simp only [List.length_replicate]; omega),
        List.getElem?_replicate]
      simp only [List.length_replicate, show 512 + i - 512 < 8 by omega, if_true]
    rw [hbit, Option.getD_some]
    interval_cases i <;> decide
  unfold viewDigit
  rw [e]
  decide

theorem viewCompress_layout (σ : List Bool) (c : ℕ) (hc : c < 16) :
    viewCompress (honestView σ c) = viewNonce (honestView σ c) ++ viewPayload (honestView σ c) :=
  if_neg (by rw [viewDigit_honestView σ c (by omega)]; omega)

theorem layout_compress (σ : List Bool) (len : σ.length = 5504) (c : ℕ) (hc : c < 16) :
    viewCompress (honestView σ c) = σ := by
  rw [viewCompress_layout σ c hc, viewNonce_honestView c len, viewPayload_honestView c len,
    List.take_append_drop]

theorem raw_compress (σ : List Bool) : viewCompress (rawView σ) = σ := by
  unfold viewCompress
  rw [if_pos (by rw [viewDigit_rawView]; omega), rawView]
  exact List.drop_left' (by simp only [List.length_append, List.length_replicate, rawFlagBits])

/-! ## The staged verifier on views -/

/-- The staged verifier with its nonce and chain values given separately. -/
def viewCore (pk : PublicKey) (m : Message) (nonce payload : List Bool) :
    OracleComp Spec Bool := do
  let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits nonce))
  if stagedRank (pack answer) then
    freeBlocks ⟨pack answer, pack_lt answer⟩ payload pk (fun _ => 0)
  else pure false

theorem stagedVerify_eq_viewCore (pk : PublicKey) (m : Message) (σ : List Bool)
    (len : σ.length = 5504) :
    stagedVerify pk m σ = viewCore pk m (σ.take 128) (σ.drop 128) := by
  unfold stagedVerify viewCore
  simp only [len, and_true]

theorem stagedVerify_short (pk : PublicKey) (m : Message) (σ : List Bool)
    (len : σ.length ≠ 5504) : ∀ b ∈ support (stagedVerify pk m σ), b = false := by
  intro b hb
  unfold stagedVerify at hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨answer, -, hb⟩ := hb
  rw [if_neg (fun h => len h.2), support_pure, Set.mem_singleton_iff] at hb
  exact hb

theorem stagedVerify_length (pk : PublicKey) (m : Message) (σ : List Bool)
    (h : true ∈ support (stagedVerify pk m σ)) : σ.length = 5504 := by
  by_contra hl
  exact absurd (stagedVerify_short pk m σ hl true h) (by simp)

theorem stagedVerify_view (pk : PublicKey) (m : Message) (view : List Bool)
    (short : viewDigit view < 16) :
    stagedVerify pk m (viewCompress view) = viewCore pk m (viewNonce view) (viewPayload view) := by
  have hn := viewNonce_length view
  have hc : viewCompress view = viewNonce view ++ viewPayload view := if_neg (by omega)
  rw [stagedVerify_eq_viewCore, hc, List.take_left' hn, List.drop_left' hn]
  rw [hc, List.length_append, hn, viewPayload_length]

theorem layoutView_compress (pk : PublicKey) (m : Message) (σ : List Bool)
    (h : true ∈ support (stagedVerify pk m σ)) :
    ∀ view ∈ support (layoutView pk m σ), viewCompress view = σ := by
  intro view hv
  unfold layoutView at hv
  rw [mem_support_bind_iff] at hv
  obtain ⟨answer, -, hv⟩ := hv
  rw [support_pure, Set.mem_singleton_iff] at hv
  rw [hv]
  exact layout_compress σ (stagedVerify_length pk m σ h) _ (Nat.mod_lt _ (by omega))

theorem trap_raw (pk : PublicKey) (m : Message) (σ : List Bool) :
    ∀ o ∈ support (trapVerify pk m (rawView σ)), o = some false := by
  intro o ho
  unfold trapVerify at ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨answer, -, ho⟩ := ho
  rw [if_pos (by rw [viewDigit_rawView]; omega), support_pure, Set.mem_singleton_iff] at ho
  exact ho

/-- The verdict on a staged run accepts exactly when the verifier's decision does. -/
theorem freeDecision_path (index : RawIdx) (payload : List Bool) (pk : PublicKey)
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

theorem trap_sound (pk : PublicKey) (m : Message) (view : List Bool)
    (c₀ c₁ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (trapVerify pk m view) (some true) c₀ c₁) :
    Riscv.cachedPaths.Path (stagedVerify pk m (viewCompress view)) true c₀ c₁ := by
  unfold trapVerify at h
  rw [Riscv.cachedPaths.path_bind] at h
  obtain ⟨answer, ca, ha, h⟩ := h
  dsimp only [rawIdx] at h
  by_cases big : 16 ≤ viewDigit view
  · rw [if_pos big, Riscv.cachedPaths.path_pure] at h
    exact absurd h.1 (by simp)
  rw [if_neg big] at h
  by_cases rank : freeDigit (pack answer) = viewDigit view
  swap
  · rw [if_neg rank] at h
    split_ifs at h <;> rw [Riscv.cachedPaths.path_pure] at h <;> exact absurd h.1 (by simp)
  rw [if_pos rank] at h
  rw [stagedVerify_view pk m view (by omega)]
  unfold viewCore
  rw [ofBits_viewNonce, Riscv.cachedPaths.path_bind]
  refine ⟨answer, ca, ha, ?_⟩
  have hr : stagedRank (pack answer) := by unfold stagedRank; omega
  rw [if_pos hr]
  exact freeDecision_path _ _ pk ca c₁ h

set_option maxRecDepth 100000 in
theorem trap_accepts (pk : PublicKey) (m : Message) (σ : List Bool)
    (c₀ c₁ : hashSpec.QueryCache)
    (hv : Riscv.cachedPaths.Path (stagedVerify pk m σ) true c₀ c₁)
    (view : List Bool) (c₂ : hashSpec.QueryCache)
    (hl : Riscv.cachedPaths.Path (layoutView pk m σ) view c₁ c₂)
    (o : Option Bool) (c₃ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (trapVerify pk m view) o c₂ c₃) : o = some true := by
  have len : σ.length = 5504 :=
    stagedVerify_length pk m σ (mem_support_of_mem_support_run _ _ c₀ c₁ hv)
  rw [stagedVerify_eq_viewCore pk m σ len] at hv
  unfold viewCore at hv
  rw [Riscv.cachedPaths.path_bind] at hv
  obtain ⟨answer, ca, ha, hv⟩ := hv
  by_cases hr : stagedRank (pack answer)
  swap
  · rw [if_neg hr, Riscv.cachedPaths.path_pure] at hv
    exact absurd hv.1 (by simp)
  rw [if_pos hr, freeBlocks_eq_freeRun, Riscv.cachedPaths.path_map] at hv
  obtain ⟨o', ho', he'⟩ := hv
  obtain ⟨r, rfl⟩ : ∃ r, o' = some r := by
    cases o' with
    | none => simp at he'
    | some r => exact ⟨r, rfl⟩
  have hflip : flipHi r = pk := by simpa using he'
  have hgrow := subcache_run_grow _ ca _ c₁ ho'
  -- the layout's index query replays the verifier's
  unfold layoutView indexQuery at hl
  rw [Riscv.cachedPaths.path_bind] at hl
  obtain ⟨a₁, cl, ha₁, hl⟩ := hl
  have hreplay₁ := replay_deterministic _ (Deterministic.hash _) c₀ ca c₁ answer ha hgrow
  change (a₁, cl) ∈ support ((simulateQ oracleImpl _).run c₁) at ha₁
  rw [hreplay₁] at ha₁
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at ha₁
  obtain ⟨rfl, rfl⟩ := ha₁
  rw [Riscv.cachedPaths.path_pure] at hl
  obtain ⟨rfl, hc12⟩ := hl
  rw [hc12] at h
  have hc : freeDigit (pack a₁) % 16 = freeDigit (pack a₁) := by
    unfold stagedRank at hr; exact Nat.mod_eq_of_lt hr
  generalize hcd : freeDigit (pack a₁) % 16 = c at h
  have hd := viewDigit_honestView σ c (by omega)
  -- the machine's index query replays it too
  unfold trapVerify at h
  rw [← ofBits_viewNonce (honestView σ c), viewNonce_honestView c len,
    Riscv.cachedPaths.path_bind] at h
  obtain ⟨a', cb, ha', h⟩ := h
  change (a', cb) ∈ support ((simulateQ oracleImpl _).run cl) at ha'
  rw [hreplay₁] at ha'
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at ha'
  obtain ⟨rfl, hcb⟩ := ha'
  rw [hcb] at h
  dsimp only [rawIdx] at h
  rw [hd, if_neg (by omega), if_pos (by omega), viewPayload_honestView c len] at h
  unfold freeDecision at h
  rw [Riscv.cachedPaths.path_map] at h
  obtain ⟨o'', ho'', rfl⟩ := h
  have hrun := replay_deterministic _ (freeRun_deterministic _ _ _) ca cl cl (some r) ho'
    (Subcache.refl cl)
  change (o'', c₃) ∈ support ((simulateQ oracleImpl _).run cl) at ho''
  rw [hrun] at ho''
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at ho''
  obtain ⟨rfl, -⟩ := ho''
  exact (decisionOutcome_eq_true r pk).2 hflip

end OptimalOTS.RiscvMixedProgram
