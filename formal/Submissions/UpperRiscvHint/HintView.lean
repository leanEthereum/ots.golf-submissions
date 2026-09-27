import Submissions.UpperRiscvHint.MixedVerifier
import Submissions.UpperRiscvHint.HintTrap

/-! In-place views of the cap-chain scheme's signatures. A view shorter than `rawViewBits` bits
holds the nonce and every chain value at fixed positions, and `compress` extracts them in
signature order. A longer view carries a raw signature after `rawViewBits` padding bits; the image
rejects it at pair 0's length test, before its first possible trap. The honest prover lays out accepted signatures and
hands every other signature over in the raw form (`HintTrap`). -/

noncomputable section

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open OptimalOTS.RiscvHint RiscvZkvm.Rv64

-- Path equalities otherwise evaluate the checksum through the decision instance.
set_option allowUnsafeReducibility true in
attribute [local irreducible] stagedBlocks stagedRun instDecidablePredNatStagedRank

/-- Views at least this long carry a raw signature. -/
def rawViewBits : ℕ := 65536

def viewCompress (view : List Bool) : List Bool :=
  if rawViewBits ≤ view.length then view.drop rawViewBits
  else viewNonce view ++ viewPayload view

def rawView (σ : List Bool) : List Bool := List.replicate rawViewBits false ++ σ

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

/-- The staged verifier with its nonce and chain values given separately. -/
def viewCore (pk : PublicKey) (m : Message) (nonce payload : List Bool) :
    OracleComp Spec Bool := do
  let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits nonce))
  if stagedRank (pack answer) then
    stagedBlocks ⟨pack answer, pack_lt answer⟩ payload pk 16 0 (fun _ => 0) 0
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

theorem viewCompress_short (view : List Bool) (short : view.length < rawViewBits) :
    viewCompress view = viewNonce view ++ viewPayload view :=
  if_neg (by omega)

theorem stagedVerify_view (pk : PublicKey) (m : Message) (view : List Bool)
    (short : view.length < rawViewBits) :
    stagedVerify pk m (viewCompress view) = viewCore pk m (viewNonce view) (viewPayload view) := by
  have hn := viewNonce_length view
  rw [stagedVerify_eq_viewCore, viewCompress_short view short, List.take_left' hn,
    List.drop_left' hn]
  rw [viewCompress_short view short, List.length_append, hn, viewPayload_length]

theorem layout_compress (σ : List Bool) (len : σ.length = 5504) :
    viewCompress (honestView σ) = σ := by
  rw [viewCompress_short _ (by rw [honestView_length]; decide), viewNonce_honestView len,
    viewPayload_honestView len, List.take_append_drop]

theorem raw_compress (σ : List Bool) : viewCompress (rawView σ) = σ := by
  unfold viewCompress rawView
  rw [if_pos (by simp), List.drop_left' (List.length_replicate ..)]

theorem trap_raw (pk : PublicKey) (m : Message) (σ : List Bool) :
    ∀ o ∈ support (trapVerify pk m (rawView σ)), o = some false := by
  intro o ho
  unfold trapVerify at ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨answer, -, ho⟩ := ho
  have hlen : (rawView σ).length ≠ honestViewBits := by
    simp only [rawView, List.length_append, List.length_replicate, rawViewBits, honestViewBits]
    omega
  rw [if_pos hlen, support_pure, Set.mem_singleton_iff] at ho
  exact ho

theorem trap_sound (pk : PublicKey) (m : Message) (view : List Bool)
    (c₀ c₁ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (trapVerify pk m view) (some true) c₀ c₁) :
    Riscv.cachedPaths.Path (stagedVerify pk m (viewCompress view)) true c₀ c₁ := by
  unfold trapVerify at h
  rw [Riscv.cachedPaths.path_bind] at h
  obtain ⟨answer, ca, ha, h⟩ := h
  dsimp only [rawIdx] at h
  by_cases hlen : view.length ≠ honestViewBits
  · rw [if_pos hlen, Riscv.cachedPaths.path_pure] at h
    exact absurd h.1 (by simp)
  have short : view.length < rawViewBits := by
    unfold rawViewBits
    unfold honestViewBits at hlen
    omega
  rw [if_neg hlen] at h
  by_cases hr : stagedRank (pack answer)
  swap
  · rw [if_neg hr] at h
    split_ifs at h <;> rw [Riscv.cachedPaths.path_pure] at h <;> exact absurd h.1 (by simp)
  rw [if_pos hr, Riscv.cachedPaths.path_map] at h
  obtain ⟨o, ho, he⟩ := h
  obtain ⟨r, rfl⟩ : ∃ r, o = some r := by
    cases o with
    | none => simp at he
    | some r => exact ⟨r, rfl⟩
  have hflip : flipHi r = pk := (decisionOutcome_eq_true r pk).1 he
  rw [stagedVerify_view pk m view short]
  unfold viewCore
  rw [ofBits_viewNonce, Riscv.cachedPaths.path_bind]
  refine ⟨answer, ca, ha, ?_⟩
  rw [if_pos hr, stagedBlocks_eq_stagedRun, Riscv.cachedPaths.path_map]
  exact ⟨some r, ho, by simp [hflip]⟩

theorem trap_accepts (pk : PublicKey) (m : Message) (σ : List Bool)
    (c₀ c₁ : hashSpec.QueryCache)
    (hv : Riscv.cachedPaths.Path (stagedVerify pk m σ) true c₀ c₁)
    (o : Option Bool) (c₂ : hashSpec.QueryCache)
    (h : Riscv.cachedPaths.Path (trapVerify pk m (honestView σ)) o c₁ c₂) : o = some true := by
  have len : σ.length = 5504 := by
    by_contra hl
    exact absurd (stagedVerify_short pk m σ hl true (mem_support_of_mem_support_run _ _ c₀ c₁ hv))
      (by simp)
  rw [stagedVerify_eq_viewCore pk m σ len] at hv
  unfold viewCore at hv
  rw [Riscv.cachedPaths.path_bind] at hv
  obtain ⟨answer, ca, ha, hv⟩ := hv
  by_cases hr : stagedRank (pack answer)
  swap
  · rw [if_neg hr, Riscv.cachedPaths.path_pure] at hv
    exact absurd hv.1 (by simp)
  rw [if_pos hr, stagedBlocks_eq_stagedRun, Riscv.cachedPaths.path_map] at hv
  obtain ⟨o', ho', he'⟩ := hv
  obtain ⟨r, rfl⟩ : ∃ r, o' = some r := by
    cases o' with
    | none => simp at he'
    | some r => exact ⟨r, rfl⟩
  have hflip : flipHi r = pk := by simpa using he'
  have hgrow := subcache_run_grow _ ca _ c₁ ho'
  unfold trapVerify at h
  rw [← ofBits_viewNonce (honestView σ), viewNonce_honestView len,
    Riscv.cachedPaths.path_bind] at h
  obtain ⟨a', cb, ha', h⟩ := h
  have hreplay := replay_deterministic _ (Deterministic.hash _) c₀ ca c₁ answer ha hgrow
  change (a', cb) ∈ support ((simulateQ oracleImpl _).run c₁) at ha'
  rw [hreplay] at ha'
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at ha'
  obtain ⟨rfl, hcb⟩ := ha'
  rw [hcb] at h
  dsimp only [rawIdx] at h
  have hlen : ¬ (honestView σ).length ≠ honestViewBits := by
    rw [honestView_length]; exact not_not.mpr rfl
  rw [if_neg hlen, if_pos hr, Riscv.cachedPaths.path_map, viewPayload_honestView len] at h
  obtain ⟨o'', ho'', rfl⟩ := h
  have hrun := replay_deterministic _ (stagedRun_deterministic _ _ _ _ _ _) ca c₁ c₁ (some r) ho'
    (Subcache.refl c₁)
  change (o'', c₂) ∈ support ((simulateQ oracleImpl _).run c₁) at ho''
  rw [hrun] at ho''
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at ho''
  obtain ⟨rfl, -⟩ := ho''
  exact (decisionOutcome_eq_true r pk).2 hflip

end OptimalOTS.RiscvMixedProgram
