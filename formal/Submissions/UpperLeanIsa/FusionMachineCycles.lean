import Submissions.UpperLeanIsa.FusionMachinePath
import OptimalOTS.LeanIsa

/-!
# The universal 1149-cycle bound

A completing walk exits on the sentinel, so the last landing product is g^sentinel
(`exit_forced`, via the hash-free exit table). The free seed and all group products
therefore imply C_(s+sum costs)=C_87. Raising to the sixteenth power proves equality of the
small integer totals, so every completing path has exactly 86 chain hashes.

There are 104 non-hash block instructions and 25 non-hash prologue instructions, one index
hash, and three root hashes. Every completing run has 219 instructions and costs 1029 before
the 120-cycle boundary charge. The bound covers every admitted memory size and step count.
-/

namespace OptimalOTS.HLFusion

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

variable {T : Tab}

/-! ## The exponent identity -/

/-- The group cost of an index vector: `Σ_u cost (u, xs (u + 1))`. -/
def gsum (T : Tab) (xs : ℕ → ℕ) : ℕ := ∑ u ∈ Finset.range 13, cost T u (xs (u + 1))

section Layer

variable {B : BlakeRel} {v : ℕ → E}

/-- **Exponent identity.** The hash-free relations on any path force the layer. -/
theorem layer_of_facts (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs) (hP : PathFacts T B v xs)
    (hL : Landing v xs) : xs 0 + gsum T xs = 86 := by
  have h13 := prod_eq hT hV hP.pro hP.blk 13 le_rfl
  rw [hP.gp13] at h13
  have hbound : ∑ w ∈ Finset.range 13, cost T w (xs (w + 1)) ≤ ∑ _w ∈ Finset.range 13, 16 :=
    Finset.sum_le_sum fun w hw => by
      have hw' := Finset.mem_range.mp hw
      have := hV (w + 1) (by omega); rw [Wf_succ hw'] at this
      exact cost_le hT hw' this
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hbound
  have hx0 : xs 0 < 64 := by have := hV 0 (by omega); rwa [Wf_zero] at this
  have heq := (ofK_injective h13).symm
  exact (LeanIsaFieldRescale.checksum_exact (by omega : 86 ≤ 300)
    (by omega : xs 0 + ∑ w ∈ Finset.range 13, cost T w (xs (w + 1)) ≤ 300)).mp heq

end Layer

/-! ## The cost -/

theorem gcuF_sum : ∑ f ∈ Finset.range 14, gcuF f = 104 := by decide

theorem gcuF_frU (s : ℕ) {f : ℕ} (_hf : f < 14) : gcuF (frU s f) = gcuF f := rfl

theorem hmF_frU (s : ℕ) {f : ℕ} (_hf : f < 14) : hmF (frU s f) = hmF f := rfl

theorem cF_frU (T : Tab) (s : ℕ) {f : ℕ} (_hf : f < 14) (x : ℕ) : cF T (frU s f) x = cF T f x := rfl

theorem hmF_sum : ∑ f ∈ Finset.range 14, hmF f = 3 := by decide

theorem gcuF_ge (f : ℕ) : 2 ≤ gcuF f := by
  unfold gcuF gcu; split_ifs <;> omega

theorem cF_sum (T : Tab) (xs : ℕ → ℕ) :
    ∑ f ∈ Finset.range 14, cF T f (xs f) = xs 0 + gsum T xs := by
  rw [Finset.sum_range_succ', cF_zero, Nat.add_comm]
  unfold gsum
  congr 1

/-- On the layer, every path costs `1029` cycles. -/
theorem totalCost_eq (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs) (h : xs 0 + gsum T xs = 86) :
    totalCost T xs = 1029 := by
  unfold totalCost
  have : ∀ f ∈ Finset.range 14, 2 + lcost (bodyF T (frU (xs 0) f) (xs f)) =
      gcuF f + 10 * cF T f (xs f) + 10 * hmF f := fun f hf => by
    have hf' := Finset.mem_range.mp hf
    rw [bodyF_lcost hT (frU_lt _ hf') (by rw [Wf_frU _ hf']; exact hV f hf'), gcuF_frU _ hf',
      cF_frU T _ hf', hmF_frU _ hf']
    have := gcuF_ge f
    omega
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, gcuF_sum, hmF_sum, cF_sum, h]
  norm_num

/-- On the layer, every path executes `219` instructions. -/
theorem totalSteps_eq (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs) (h : xs 0 + gsum T xs = 86) :
    totalSteps T xs = 219 := by
  unfold totalSteps
  have : ∀ f ∈ Finset.range 14, 2 + (bodyF T (frU (xs 0) f) (xs f)).length =
      gcuF f + cF T f (xs f) + hmF f := fun f hf => by
    have hf' := Finset.mem_range.mp hf
    rw [bodyF_len hT (frU_lt _ hf') (by rw [Wf_frU _ hf']; exact hV f hf'), gcuF_frU _ hf',
      cF_frU T _ hf', hmF_frU _ hf']
    have := gcuF_ge f
    omega
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib, gcuF_sum,
    hmF_sum, cF_sum, h]
  norm_num

/-- The claim: `boundaryCycles + 1029`. -/
def claim : ℕ := 1149

theorem boundary_eq : LeanIsa.boundaryCycles = 120 := by decide

/-! ## The certificate clauses -/

/-- **Cycles.** Every completing execution of the bytecode, under every admissible memory size,
every committed image and every step count, costs exactly `1029` plus the boundary. -/
theorem cycles (hT : T.Hyp) (S : LeanIsa.Submission) (hS : S.program = program T) :
    S.CyclesAtMost claim := by
  intro pk m σ κ h16 hκ L n cost h
  unfold LeanIsa.Submission.exec at h
  rw [hS, initial_eq] at h
  have hpin := pinned_of_sem suppSem trueRel (supp_straight hT h16 hκ (lengthDomain_load h16 pk m σ L)) h
  obtain ⟨hV, hP, hL, -, hc⟩ := walk_full hT (walk_of_supp hT h16 hκ (lengthDomain_load h16 pk m σ L) hpin (by norm_num) h)
  have h1 := totalCost_eq hT hV (layer_of_facts hT hV hP hL)
  rw [boundary_eq]
  unfold claim; omega

/-- The seeded rows of a submission running this bytecode at memory size `2 ^ 16`. -/
theorem seededRows_lt (S : LeanIsa.Submission) (hS : S.program = program T) (hm : S.memLog = 16) :
    S.seededRows < LeanIsa.maxSeededRows := by
  unfold LeanIsa.Submission.seededRows
  rw [hS, hm, program_logSize]
  decide

end

end OptimalOTS.HLFusion
