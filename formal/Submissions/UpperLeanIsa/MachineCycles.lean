import Submissions.UpperLeanIsa.MachinePath

/-!
# The cycle bound

`CyclesAtMost claim` for the RT-MX bytecode (design `NOTES.md` §5 and §8), over every
admissible memory size, every committed image and every step count, in the cache-free `support`
semantics.

* `checksum_of_facts`: the non-hash relations of the constants and the leaves force the checksum
  identity `∑_{k<41} E k + 64 · (E 41 - 64) + E 42 = 5271` on the leaf vector `E` of any walk.
  The landing constants `tgtV` multiply in the exponent, and `gpow` is injective below the group
  order, so the product `k0Cell = G_41 · T_42 = tgtV K0` pins the exponent sum.
* `totalCost_le`: under that identity the closed-form cost is at most `33723`, by the affine
  per-chain bounds `chainCost_bound`, `hiCost_bound` of `MachineProgram`.
* `cycles`: a completing run is a `Walk (HoldsNH L)` (`walk_of_supp`), its shape is a leaf
  vector (`walk_full`), and the two facts above bound its cost. No hash binding is used: the
  walk's step count and cost are functions of `E`, and `E` is pinned by `SET`, `MUL` and `XOR`
  relations only.
* `seededRows_lt`: the seeded rows at `memLog = 16`.
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters LeanerVM.Semantics OracleComp

noncomputable section

/-! ## Landing constants in the exponent -/

theorem tgtV_mul (a b : ℕ) : tgtV a * tgtV b = tgtV (a + b) := by
  unfold tgtV
  rw [← ofK_mul]
  exact congrArg ofK (pow_add g a b).symm

theorem tgtV_zero : tgtV 0 = oneV := by
  rw [oneV_eq_ofK]; unfold tgtV; rw [gpow_zero]

/-- `tgtV` is injective below the group order. -/
theorem tgtV_inj {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) (h : tgtV a = tgtV b) :
    a = b :=
  gpow_injOn (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr hb) (ofK_injective h)

/-! ## The checksum identity -/

section Checksum

variable {κ : ℕ} {R : ℕ → Prop} {L : MemImage κ}

/-- Slot 127 pins `k0Cell := tgtV K0`. -/
theorem k0_of_facts (hR : ∀ s, R s → HoldsNH L s) (h : R 127) : Lx L k0Cell = tgtV K0 :=
  (setc_of_holdsNH cinstrAt_k0 (hR _ h)).2

/-- The leaf of chain digit `e` of Rice chain `k` multiplies the running product by
`tgtV (s0 k + e + 1)`, for `e < 127` through `tCell k` as the jump cell and for `e = 127` through
the uniform `SET`. -/
theorem leaf_product (hR : ∀ s, R s → HoldsNH L s) {k e : ℕ} (hk : k < 41 ∨ k = 42)
    (he1 : off k ≤ e) (he2 : e < off k + nLeaves k) (h : ∀ i < leafLen k e, R (leafSlot k e + i)) :
    Lx L (gOut k) = Lx L (gPrev k) * tgtV (s0 k + e + 1) := by
  have hlen : leafLen k e = tieLen k + if e < 127 then 4 else 5 := rfl
  have htl := tieLen_le k
  have he' := off_add_nLeaves k
  have h1 := hR _ (h (tieLen k + 1) (by rw [hlen]; split_ifs <;> omega))
  have h2 := hR _ (h (tieLen k + 2) (by rw [hlen]; split_ifs <;> omega))
  have hs1 : cinstrAt (leafSlot k e + (tieLen k + 1)) = coreOp k e 1 :=
    (cinstrAt_leaf hk he1 he2 (by omega)).trans (leafOp_core k e 1)
  have hs2 : cinstrAt (leafSlot k e + (tieLen k + 2)) = coreOp k e 2 :=
    (cinstrAt_leaf hk he1 he2 (by omega)).trans (leafOp_core k e 2)
  rcases Nat.lt_or_ge e 127 with h127 | h127
  · rw [coreOp_mul h127] at hs1
    rw [coreOp_set h127] at hs2
    rw [(mul_of_holdsNH hs1 h1).2.2.2, (setc_of_holdsNH hs2 h2).2]
  · obtain rfl : e = 127 := by omega
    rw [coreOp127_setT h127] at hs1
    rw [coreOp127_mul h127] at hs2
    rw [(mul_of_holdsNH hs2 h2).2.2.2, (setc_of_holdsNH hs1 h1).2, Nat.add_assoc]

/-- The leaf `dh` of chain 41 multiplies the running product by `tgtV (64 · dh)`. -/
theorem leafHi_product (hR : ∀ s, R s → HoldsNH L s) {dh : ℕ} (hdh : dh ≤ 50)
    (h : ∀ i < 5, R (leafSlotHi dh + i)) :
    Lx L (gCell 41) = Lx L (gCell 40) * tgtV (64 * dh) := by
  have h1 := hR _ (h 1 (by omega))
  have h2 := hR _ (h 2 (by omega))
  rw [(mul_of_holdsNH ((cinstrAt_hileaf hdh (by omega)).trans (hiLeafOp_mul dh)) h2).2.2.2,
    (setc_of_holdsNH ((cinstrAt_hileaf hdh (by omega)).trans (hiLeafOp_setU dh)) h1).2]

/-- The running product after message chain `k < 41`. -/
theorem gCell_eq (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {E : ℕ → ℕ}
    (hE : Valid E) (hP : PathFacts R E) :
    ∀ k, k < 41 → Lx L (gCell k) = tgtV (∑ i ∈ Finset.range (k + 1), (s0 i + E i + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h := leaf_product hR (Or.inl hk) (hE.1 0 (Or.inl hk)).1 (hE.1 0 (Or.inl hk)).2
      (hP.leaf 0 (Or.inl hk))
    rw [gOut_of (by omega), gPrev_zero, hone, ← tgtV_zero, tgtV_mul, Nat.zero_add] at h
    rw [h, Finset.sum_range_one]
  | succ k ih =>
    intro hk
    have h := leaf_product hR (Or.inl hk) (hE.1 (k + 1) (Or.inl hk)).1
      (hE.1 (k + 1) (Or.inl hk)).2 (hP.leaf (k + 1) (Or.inl hk))
    rw [gOut_of (by omega), gPrev_of (by omega), Nat.add_sub_cancel, ih (by omega),
      tgtV_mul] at h
    rw [h]
    exact congrArg tgtV (Finset.sum_range_succ _ (k + 1)).symm

theorem sum_le_of_lt {E : ℕ → ℕ} (hE : ∀ k, k < 41 → E k < 128) :
    ∀ j, j ≤ 41 → ∑ k ∈ Finset.range j, E k ≤ 127 * j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [Finset.sum_range_succ]
    have := hE j (by omega)
    have := ih (by omega)
    omega

/-- Every Rice chain digit of a valid leaf vector is below 128. -/
theorem Valid.lt_128 {E : ℕ → ℕ} (hE : Valid E) {k : ℕ} (hk : k < 41 ∨ k = 42) : E k < 128 := by
  have := (hE.1 k hk).2
  rw [off_add_nLeaves] at this
  exact this

/-- **Checksum identity.** The non-hash relations on the constants and the leaves of any walk with
leaf vector `E` force `∑_{k<41} E k + 64 · (E 41 - 64) + E 42 = 5271`. -/
theorem checksum_of_facts (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV)
    {E : ℕ → ℕ} (hP : PathFacts R E) (hE : Valid E) :
    (∑ k ∈ Finset.range 41, E k) + 64 * (E 41 - 64) + E 42 = 5271 := by
  have h40 := gCell_eq hR hone hE hP 40 (by omega)
  have hHi := leafHi_product hR (dh := E 41 - 64) (by have := hE.2.2; omega) hP.leafHi
  have h42 := leaf_product hR (Or.inr rfl) (hE.1 42 (Or.inr rfl)).1 (hE.1 42 (Or.inr rfl)).2
    (hP.leaf 42 (Or.inr rfl))
  rw [gOut_42, gPrev_42, hHi, h40, tgtV_mul, tgtV_mul, k0_of_facts hR (hP.const 127 (by omega))]
    at h42
  have hsplit : ∑ i ∈ Finset.range 41, (s0 i + E i + 1) =
      (∑ i ∈ Finset.range 41, (s0 i + 1)) + ∑ i ∈ Finset.range 41, E i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  have hEle := sum_le_of_lt (fun k hk => hE.lt_128 (Or.inl hk)) 41 le_rfl
  have hK0 : K0 = (∑ k ∈ Finset.range 41, (s0 k + 1)) + (s0 42 + 1) + 5271 := rfl
  have hK0' := K0_eq
  have h42' := s0_42
  have hE41 := hE.2.2
  have hE42 := hE.lt_128 (Or.inr rfl)
  rw [hsplit] at h42
  have hbig : (4000000 : ℕ) < 2 ^ 64 - 1 := by norm_num
  have hA := tgtV_inj (lt_trans (by omega) hbig) (lt_trans (by omega) hbig) h42
  omega

end Checksum

/-! ## The cost bound -/

/-- **Cost bound.** Under the checksum identity, the closed-form cost of a valid leaf vector is at
most `33723`: `totalCost E ≤ 5523 + 564 · (E 41 - 64) ≤ 33723`. -/
theorem totalCost_le {E : ℕ → ℕ} (hE : Valid E)
    (hsum : (∑ k ∈ Finset.range 41, E k) + 64 * (E 41 - 64) + E 42 = 5271) :
    totalCost E ≤ 33723 := by
  have hchains : ∑ k ∈ Finset.range 41, (chainCost k (E k) + 9 * E k) ≤
      ∑ k ∈ Finset.range 41, (1277 - off k + tieLen k) :=
    Finset.sum_le_sum fun k hk =>
      chainCost_bound k (hE.1 k (Or.inl (Finset.mem_range.mp hk))).1
        (hE.1 k (Or.inl (Finset.mem_range.mp hk))).2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, chainBound_sum] at hchains
  have h42 := chainCost_bound 42 (hE.1 42 (Or.inr rfl)).1 (hE.1 42 (Or.inr rfl)).2
  rw [tieLen_of_ge (by norm_num), off_42] at h42
  have hHi := hiCost_bound (dh := E 41 - 64) (by have := hE.2.2; omega)
  have hE41 := hE.2.2
  unfold totalCost
  omega

/-! ## The certificate clauses -/

/-- **Cycles.** Every completing execution of the bytecode, under every admissible memory size,
every committed image and every step count, costs at most `claim = boundaryCycles + 33723`. -/
theorem cycles (S : LeanIsa.Submission) (hS : S.program = program) : S.CyclesAtMost claim := by
  intro pk m σ κ _ hκ L n cost h
  unfold LeanIsa.Submission.exec at h
  rw [hS, initial_eq] at h
  have hone := one_of_supp hκ h
  obtain ⟨E, hE, -, rfl, hP⟩ :=
    walk_full (fun _ h => h) hone (walk_of_supp hκ hone (by norm_num) h)
  exact Nat.add_le_add_left (totalCost_le hE (checksum_of_facts (fun _ h => h) hone hP hE)) _

/-- The seeded rows of a submission running this bytecode at memory size `2 ^ 16`. -/
theorem seededRows_lt (S : LeanIsa.Submission) (hS : S.program = program) (hm : S.memLog = 16) :
    S.seededRows < LeanIsa.maxSeededRows := by
  unfold LeanIsa.Submission.seededRows
  rw [hS, hm, program_logSize]
  exact seeded

end

end OptimalOTS.LeanIsaBaseline.Machine
