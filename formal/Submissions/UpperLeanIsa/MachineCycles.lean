import Submissions.UpperLeanIsa.MachinePath
import OptimalOTS.LeanIsa

/-!
# The cycle bound

`CyclesAtMost 1598` for the HL-FLAT-A bytecode, over every admissible memory size, every
committed image and every step count, in the cache-free `support` semantics.

* `layer_of_facts`: the hash-free relations along the path force the exponent identity
  `∑_k (BASE k + 21 · s k) = rootSlot`: the landing hints `H_k = g ^ (entryOf k (s k))` multiply
  into `K0 = g ^ rootSlot`, and `gpow` is injective below the group order; with
  `∑_k BASE k = 259906` this is `∑_k s k = 106`.
* `totalCost_eq`: every path of a layer vector costs exactly `1478`: each chain segment's non-hash
  cost is independent of its digit, and the hashes number `1 + 106 + 10`.
* `cycles`: a completing run is a walk (`walk_of_supp`), the walk is a path (`walk_full`), and
  the two facts give its cost. No hash binding is used.
-/

namespace OptimalOTS.HLFlat

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

/-! ## The exponent identity -/

theorem base_sum : ∑ k ∈ Finset.range 42, BASE k = 259906 := by decide

theorem prodPrev_succ {k : ℕ} (h1 : 1 ≤ k) (h : k < 41) : prodPrev (k + 1) = prodOut k := by
  unfold prodPrev prodOut; rw [if_neg (by omega), if_neg (by omega)]; congr 1

theorem blockOp_three {k s : ℕ} (hk : k ≠ 0) :
    blockOp k s 3 = .mul (prodPrev k) (hCell k) (prodOut k) := by
  unfold blockOp; rw [if_neg hk, if_neg (by omega), if_neg (by omega), if_pos rfl]

section Layer

variable {v : ℕ → E} {R : ℕ → Prop} (hR : ∀ t, R t → (cinstrAt t).RelNH v)
include hR

/-- The landing product after chain `k ≥ 1`. -/
theorem prod_eq {s : ℕ → ℕ} (hV : Valid s) (hP : PathFacts R s) (hL : Landing v s) :
    ∀ k, 1 ≤ k → k < 42 →
      v (prodOut k) = ofK (gpow (∑ j ∈ Finset.range (k + 1), entryOf j (s j))) := by
  have hmul : ∀ k, 1 ≤ k → k < 42 → v (prodOut k) = v (prodPrev k) * v (hCell k) := by
    intro k h1 hk
    have := hR _ (hP.blk k hk 3 (by omega) (by rw [pre_pos (by omega)]; omega))
    rwa [cinstrAt_blk hk (hV k hk) (by omega) (by rw [pre_pos (by omega)]; omega),
      blockOp_three (by omega)] at this
  intro k h1
  induction k with
  | zero => omega
  | succ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hmul 1 le_rfl (by omega), show prodPrev 1 = hCell 0 from rfl, hL 0 (by omega),
        hL 1 (by omega), ← ofK_mul, gpow_mul_gpow, Finset.sum_range_succ, Finset.sum_range_one]
    · rw [hmul (k + 1) (by omega) hk, prodPrev_succ hk0 (by omega), ih hk0 (by omega),
        hL (k + 1) hk, ← ofK_mul, gpow_mul_gpow, Finset.sum_range_succ _ (k + 1)]

/-- **Exponent identity.** The hash-free relations on any path force the layer. -/
theorem layer_of_facts {s : ℕ → ℕ} (hV : Valid s) (hP : PathFacts R s) (hL : Landing v s) :
    ∑ k ∈ Finset.range 42, s k = 106 := by
  have h41 := prod_eq hR hV hP hL 41 (by omega) (by omega)
  have hk0 : v k0Cell = k0V := by
    have := hR 5 (hP.pro 5 (by omega)); rwa [cinstrAt_set5] at this
  rw [show prodOut 41 = k0Cell from rfl, hk0, k0V] at h41
  have hbound : ∑ j ∈ Finset.range 42, entryOf j (s j) ≤ ∑ _j ∈ Finset.range 42, 10142 :=
    Finset.sum_le_sum fun j hj => by
      have := entryOf_lt (Finset.mem_range.mp hj) (hV j (Finset.mem_range.mp hj)); omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hbound
  have heq := gpow_inj (show rootSlot < 2 ^ 64 - 1 by unfold rootSlot; omega)
    (show ∑ j ∈ Finset.range 42, entryOf j (s j) < 2 ^ 64 - 1 by omega) (ofK_injective h41)
  have hsplit : ∑ j ∈ Finset.range 42, entryOf j (s j) =
      ∑ j ∈ Finset.range 42, BASE j + 21 * ∑ j ∈ Finset.range 42, s j := by
    unfold entryOf; rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, base_sum] at heq
  unfold rootSlot at heq
  omega

end Layer

/-! ## The cost -/

theorem segBase_sum : ∑ k ∈ Finset.range 42, (if k = 0 then 5 else 6) = 251 := by decide

/-- On the layer, every path costs `1478` cycles. -/
theorem totalCost_eq {s : ℕ → ℕ} (h : ∑ k ∈ Finset.range 42, s k = 106) : totalCost s = 1478 := by
  unfold totalCost segCost
  rw [Finset.sum_add_distrib, segBase_sum, ← Finset.mul_sum, h]; norm_num

/-- On the layer, every path executes `425` instructions. -/
theorem totalSteps_eq {s : ℕ → ℕ} (h : ∑ k ∈ Finset.range 42, s k = 106) : totalSteps s = 425 := by
  unfold totalSteps segSteps
  rw [Finset.sum_add_distrib, segBase_sum, h]; norm_num

/-- The claim: `boundaryCycles + 1478`. -/
def claim : ℕ := 1598

theorem boundary_eq : LeanIsa.boundaryCycles = 120 := by decide

/-! ## The certificate clauses -/

/-- **Cycles.** Every completing execution of the bytecode, under every admissible memory size,
every committed image and every step count, costs exactly `1478` plus the boundary. -/
theorem cycles (S : LeanIsa.Submission) (hS : S.program = program) : S.CyclesAtMost claim := by
  intro pk m σ κ h16 hκ L n cost h
  unfold LeanIsa.Submission.exec at h
  rw [hS, initial_eq] at h
  have hpin := pinned_of_sem suppSem trueRel (supp_straight h16 hκ) h
  obtain ⟨hV, hP, hL, -, rfl⟩ :=
    walk_full (fun _ h => h) (walk_of_supp h16 hκ hpin (by norm_num) h)
  rw [totalCost_eq (layer_of_facts (fun _ h => h) hV hP hL), boundary_eq]
  unfold claim; omega

/-- The seeded rows of a submission running this bytecode at memory size `2 ^ 16`. -/
theorem seededRows_lt (S : LeanIsa.Submission) (hS : S.program = program) (hm : S.memLog = 16) :
    S.seededRows < LeanIsa.maxSeededRows := by
  unfold LeanIsa.Submission.seededRows
  rw [hS, hm, program_logSize]
  decide

end

end OptimalOTS.HLFlat
