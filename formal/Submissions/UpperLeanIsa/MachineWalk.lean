import Submissions.UpperLeanIsa.MachineRun

/-!
# Pure path lemmas for `Walk`

Monad-free reasoning about a `Walk R L n s c` (design `NOTES.md` §9.2), for any slot
predicate `R` implying the hash-free relation (`hR : ∀ s, R s → HoldsNH L s`) on an image with
`Lx L oneCell = oneV` (`hone`). Destructors are named `walk_*`, constructors `walk_*_mk`:

* `Walk.inv`, `Walk.at_sentinel`: the two shapes of a walk;
* `walk_seg`: a run of non-jump slots, with its cost as a sum over the decoded slots;
* `walk_node`: a `SET tc := tgtV t` followed by `JUMP zc tc oneCell`, landing on `s + 2` or `t`;
* `walk_unary`: a generic unary chain of nodes (instantiated for the Rice chains and `c_hi`);
* `walk_group`: the two-level subtree of a Rice group;
* `walk_leaf`, `walk_leaf32`: a leaf's straight ops, then its unconditional `JUMP`;
* `walk_body`: the body steps up to the next segment.
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters LeanerVM.Semantics

noncomputable section

section Generic

variable {κ : ℕ} {R : ℕ → Prop} {L : MemImage κ}

/-- Transport a walk along equalities of its indices. -/
theorem Walk.cast {n s c n' s' c' : ℕ} (h : Walk R L n s c) (hn : n = n') (hs : s = s')
    (hc : c = c') : Walk R L n' s' c' := by
  subst hn hs hc; exact h

theorem rcast {a b : ℕ} (h : R a) (e : a = b) : R b := e ▸ h

/-- A walk away from the sentinel takes a step. -/
theorem Walk.inv {n s c : ℕ} (h : Walk R L n s c) (hs : s ≠ sentinel) :
    ∃ n' c', n = n' + 1 ∧ c = (cinstrAt s).cost + c' ∧ s < sentinel ∧ R s ∧
      Walk R L n' (nextSlot L s) c' := by
  cases h with
  | done => exact absurd rfl hs
  | step hlt hr hw => exact ⟨_, _, rfl, rfl, hlt, hr, hw⟩

/-- A walk at the sentinel is the empty walk. -/
theorem Walk.at_sentinel {n c : ℕ} (h : Walk R L n sentinel c) : n = 0 ∧ c = 0 := by
  cases h with
  | done => exact ⟨rfl, rfl⟩
  | step hlt _ _ => exact absurd hlt (lt_irrefl _)

theorem oneCell_ne_zero (hone : Lx L oneCell = oneV) : Lx L oneCell ≠ 0 := by
  rw [hone]; exact oneV_ne_zero

/-! ### Straight segments -/

/-- A walk over `a` non-jump slots from `s`: `R` on each, and the rest of the walk at `s + a`. -/
theorem walk_seg {a s n c : ℕ} (hj : ∀ i < a, (cinstrAt (s + i)).isJump = false)
    (hle : s + a ≤ sentinel) (h : Walk R L n s c) :
    (∀ i < a, R (s + i)) ∧ ∃ n' c', n = a + n' ∧
      c = (∑ i ∈ Finset.range a, (cinstrAt (s + i)).cost) + c' ∧ Walk R L n' (s + a) c' := by
  induction a generalizing s n c with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), n, c, by omega, by simp, ?_⟩
    exact h.cast rfl (by omega) rfl
  | succ a ih =>
    obtain ⟨n1, c1, rfl, rfl, hlt, hr, hw⟩ := h.inv (by omega)
    have hj0 := hj 0 (by omega)
    rw [Nat.add_zero] at hj0
    rw [nextSlot_of_not_jump L hj0] at hw
    have hj' : ∀ i < a, (cinstrAt (s + 1 + i)).isJump = false := fun i hi => by
      rw [show s + 1 + i = s + (i + 1) by omega]; exact hj (i + 1) (by omega)
    obtain ⟨hR', n', c', rfl, rfl, hw'⟩ := ih hj' (by omega) hw
    have hsum : ∑ i ∈ Finset.range a, (cinstrAt (s + 1 + i)).cost =
        ∑ i ∈ Finset.range a, (cinstrAt (s + (i + 1))).cost :=
      Finset.sum_congr rfl fun i _ => by rw [show s + 1 + i = s + (i + 1) by omega]
    refine ⟨fun i hi => ?_, n', c', by omega, ?_, hw'.cast rfl (by omega) rfl⟩
    · rcases i with _ | i
      · exact rcast hr (by omega)
      · exact rcast (hR' i (by omega)) (by omega)
    · rw [Finset.sum_range_succ', ← hsum]
      simp only [Nat.add_zero]
      omega

theorem walk_seg_mk {a s n c : ℕ} (hj : ∀ i < a, (cinstrAt (s + i)).isJump = false)
    (hle : s + a ≤ sentinel) (hr : ∀ i < a, R (s + i)) (h : Walk R L n (s + a) c) :
    Walk R L (a + n) s ((∑ i ∈ Finset.range a, (cinstrAt (s + i)).cost) + c) := by
  induction a generalizing s with
  | zero => exact h.cast (by omega) (by omega) (by simp)
  | succ a ih =>
    have hj0 := hj 0 (by omega)
    rw [Nat.add_zero] at hj0
    have hj' : ∀ i < a, (cinstrAt (s + 1 + i)).isJump = false := fun i hi => by
      rw [show s + 1 + i = s + (i + 1) by omega]; exact hj (i + 1) (by omega)
    have hr' : ∀ i < a, R (s + 1 + i) := fun i hi => rcast (hr (i + 1) (by omega)) (by omega)
    have hw := ih hj' (by omega) hr' (h.cast rfl (by omega) rfl)
    have hw0 := Walk.step (by omega) (rcast (hr 0 (by omega)) (by omega))
      (hw.cast rfl (nextSlot_of_not_jump L hj0).symm rfl)
    have hsum : ∑ i ∈ Finset.range a, (cinstrAt (s + 1 + i)).cost =
        ∑ i ∈ Finset.range a, (cinstrAt (s + (i + 1))).cost :=
      Finset.sum_congr rfl fun i _ => by rw [show s + 1 + i = s + (i + 1) by omega]
    refine hw0.cast (by omega) rfl ?_
    rw [Finset.sum_range_succ', hsum]
    simp only [Nat.add_zero]
    omega

/-- A segment of `a` slots of cost `w` each. -/
theorem seg_cost {s a w : ℕ} (hc : ∀ i < a, (cinstrAt (s + i)).cost = w) :
    ∑ i ∈ Finset.range a, (cinstrAt (s + i)).cost = w * a := by
  rw [Finset.sum_congr rfl fun i hi => hc i (Finset.mem_range.mp hi), Finset.sum_const,
    Finset.card_range, smul_eq_mul, Nat.mul_comm]

/-! ### Nodes -/

/-- A node: `SET tc := tgtV t` at `s`, then `JUMP zc tc oneCell`; it lands on `s + 2` when the
condition cell is zero and on `t` otherwise, after two steps and two cycles. -/
theorem walk_node (hR : ∀ s, R s → HoldsNH L s) {s tc zc t n c : ℕ}
    (hset : cinstrAt s = .setc tc (tgtV t)) (hjmp : cinstrAt (s + 1) = .jump zc tc oneCell)
    (ht : t < 2 ^ 17) (hs : s + 1 < sentinel) (h : Walk R L n s c) :
    R s ∧ R (s + 1) ∧ ∃ n' c', n = n' + 2 ∧ c = c' + 2 ∧
      Walk R L n' (if Lx L zc = 0 then s + 2 else t) c' := by
  obtain ⟨n1, c1, rfl, rfl, -, hr0, hw⟩ := h.inv (by omega)
  have hj0 : (cinstrAt s).isJump = false := by rw [hset]; rfl
  rw [nextSlot_of_not_jump L hj0] at hw
  obtain ⟨n2, c2, rfl, rfl, -, hr1, hw2⟩ := hw.inv (by omega)
  have htc := (setc_of_holdsNH hset (hR s hr0)).2
  rw [nextSlot_of_jump L hjmp, htc, limb_tgtV, slotOf_gpow ht,
    show s + 1 + 1 = s + 2 by omega] at hw2
  refine ⟨hr0, hr1, n2, c2, rfl, ?_, hw2⟩
  rw [hset, hjmp]
  simp only [CInstr.cost]
  omega

theorem walk_node_mk (hR : ∀ s, R s → HoldsNH L s) {s tc zc t n c : ℕ}
    (hset : cinstrAt s = .setc tc (tgtV t)) (hjmp : cinstrAt (s + 1) = .jump zc tc oneCell)
    (ht : t < 2 ^ 17) (hs : s + 1 < sentinel) (hr0 : R s) (hr1 : R (s + 1))
    (h : Walk R L n (if Lx L zc = 0 then s + 2 else t) c) : Walk R L (n + 2) s (c + 2) := by
  have htc := (setc_of_holdsNH hset (hR s hr0)).2
  have hn : nextSlot L (s + 1) = if Lx L zc = 0 then s + 2 else t := by
    rw [nextSlot_of_jump L hjmp, htc, limb_tgtV, slotOf_gpow ht, show s + 1 + 1 = s + 2 by omega]
  have hw1 := Walk.step (by omega) hr1 (h.cast rfl hn.symm rfl)
  have hj0 : (cinstrAt s).isJump = false := by rw [hset]; rfl
  have hw0 := Walk.step (by omega) hr0 (hw1.cast rfl (nextSlot_of_not_jump L hj0).symm rfl)
  refine hw0.cast rfl rfl ?_
  rw [hset, hjmp]
  simp only [CInstr.cost]
  omega

/-! ### Unary chains -/

/-- The layout of a unary chain of `L0` nodes of width `w` from `base`: node `i` sets its target
cell to the next node (or, for the last, the exit `base + w · L0`) and jumps on `zc i`. -/
structure UnaryShape (base w L0 : ℕ) (zc tc : ℕ → ℕ) : Prop where
  two_le : 2 ≤ w
  lt : base + w * L0 < sentinel
  set : ∀ i < L0, cinstrAt (base + w * i) = .setc (tc i) (tgtV (base + w * (i + 1)))
  jmp : ∀ i < L0, cinstrAt (base + w * i + 1) = .jump (zc i) (tc i) oneCell

/-- Exit slot of a unary chain left at node `x` (`x = L0`: every node taken). -/
def unaryExit (base w L0 x : ℕ) : ℕ := if x < L0 then base + w * x + 2 else base + w * L0

/-- The node facts of a unary chain left at node `x`: nodes `0..x` were visited, and node `i`'s
condition is zero exactly at the exit node. -/
def UnaryFacts (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (base w L0 : ℕ) (zc : ℕ → ℕ)
    (x : ℕ) : Prop :=
  ∀ i < L0, i ≤ x → R (base + w * i) ∧ R (base + w * i + 1) ∧ (Lx L (zc i) = 0 ↔ i = x)

theorem UnaryShape.node_lt {base w L0 : ℕ} {zc tc : ℕ → ℕ} (hU : UnaryShape base w L0 zc tc)
    {i : ℕ} (hi : i < L0) :
    base + w * i + 1 < base + w * (i + 1) ∧ base + w * (i + 1) ≤ base + w * L0 := by
  have h1 : w * (i + 1) = w * i + w := Nat.mul_succ w i
  have h2 : w * (i + 1) ≤ w * L0 := Nat.mul_le_mul_left w hi
  have := hU.two_le
  omega

theorem walk_unary_from (hR : ∀ s, R s → HoldsNH L s) {base w L0 : ℕ} {zc tc : ℕ → ℕ}
    (hU : UnaryShape base w L0 zc tc) :
    ∀ m j n c, j + m = L0 → Walk R L n (base + w * j) c →
      ∃ x, j ≤ x ∧ x ≤ L0 ∧
        (∀ i < L0, j ≤ i → i ≤ x →
          R (base + w * i) ∧ R (base + w * i + 1) ∧ (Lx L (zc i) = 0 ↔ i = x)) ∧
        ∃ n' c', n = 2 * (min (x + 1) L0 - j) + n' ∧ c = 2 * (min (x + 1) L0 - j) + c' ∧
          Walk R L n' (unaryExit base w L0 x) c' := by
  have hlt := hU.lt
  intro m
  induction m with
  | zero =>
    intro j n c hj h
    refine ⟨L0, by omega, le_refl _, fun i hi hji _ => absurd hi (by omega), n, c, by omega,
      by omega, h.cast rfl ?_ rfl⟩
    rw [unaryExit, if_neg (lt_irrefl _), show j = L0 by omega]
  | succ m ih =>
    intro j n c hj h
    have hjL : j < L0 := by omega
    obtain ⟨h1, h2⟩ := hU.node_lt hjL
    obtain ⟨hr0, hr1, n1, c1, rfl, rfl, hw⟩ :=
      walk_node hR (hU.set j hjL) (hU.jmp j hjL) (by rw [sentinel] at hlt; omega) (by omega) h
    by_cases hz : Lx L (zc j) = 0
    · rw [if_pos hz] at hw
      refine ⟨j, le_refl _, by omega, fun i hi hji hix => ?_, n1, c1, by omega, by omega,
        hw.cast rfl (by rw [unaryExit, if_pos hjL]) rfl⟩
      obtain rfl : i = j := by omega
      exact ⟨hr0, hr1, iff_of_true hz rfl⟩
    · rw [if_neg hz] at hw
      obtain ⟨x, hjx, hxL, hF, n', c', rfl, rfl, hw'⟩ := ih (j + 1) n1 c1 (by omega) hw
      refine ⟨x, by omega, hxL, fun i hi hji hix => ?_, n', c', by omega, by omega, hw'⟩
      rcases (show i = j ∨ j + 1 ≤ i by omega) with rfl | hi'
      · exact ⟨hr0, hr1, iff_of_false hz (by omega)⟩
      · exact hF i hi hi' hix

/-- **Unary chain.** A walk from the head of a unary chain leaves it at some node `x ≤ L0`,
after `2 · min (x + 1) L0` steps and cycles, at `unaryExit`. -/
theorem walk_unary (hR : ∀ s, R s → HoldsNH L s) {base w L0 : ℕ} {zc tc : ℕ → ℕ}
    (hU : UnaryShape base w L0 zc tc) {n c : ℕ} (h : Walk R L n base c) :
    ∃ x, x ≤ L0 ∧ UnaryFacts R L base w L0 zc x ∧
      ∃ n' c', n = 2 * min (x + 1) L0 + n' ∧ c = 2 * min (x + 1) L0 + c' ∧
        Walk R L n' (unaryExit base w L0 x) c' := by
  obtain ⟨x, -, hxL, hF, n', c', rfl, rfl, hw⟩ :=
    walk_unary_from hR hU L0 0 n c (by omega) (h.cast rfl (by omega) rfl)
  exact ⟨x, hxL, fun i hi hix => hF i hi (Nat.zero_le _) hix, n', c', by omega, by omega, hw⟩

theorem walk_unary_mk_from (hR : ∀ s, R s → HoldsNH L s) {base w L0 : ℕ} {zc tc : ℕ → ℕ}
    (hU : UnaryShape base w L0 zc tc) {x n c : ℕ} (hxL : x ≤ L0) (hF : UnaryFacts R L base w L0 zc x)
    (h : Walk R L n (unaryExit base w L0 x) c) :
    ∀ m j, j + m = L0 → j ≤ x →
      Walk R L (2 * (min (x + 1) L0 - j) + n) (base + w * j) (2 * (min (x + 1) L0 - j) + c) := by
  have hlt := hU.lt
  intro m
  induction m with
  | zero =>
    intro j hj hjx
    refine h.cast (by omega) ?_ (by omega)
    rw [unaryExit, if_neg (by omega), show j = L0 by omega]
  | succ m ih =>
    intro j hj hjx
    have hjL : j < L0 := by omega
    obtain ⟨h1, h2⟩ := hU.node_lt hjL
    obtain ⟨hr0, hr1, hz⟩ := hF j hjL hjx
    by_cases hjx' : j = x
    · subst hjx'
      have hw := walk_node_mk hR (hU.set j hjL) (hU.jmp j hjL) (by rw [sentinel] at hlt; omega)
        (by omega) hr0 hr1 (n := n) (c := c)
        (by rw [if_pos (hz.mpr rfl)]; exact h.cast rfl (by rw [unaryExit, if_pos hjL]) rfl)
      exact hw.cast (by omega) rfl (by omega)
    · have hw' := ih (j + 1) (by omega) (by omega)
      have hw := walk_node_mk hR (hU.set j hjL) (hU.jmp j hjL) (by rw [sentinel] at hlt; omega)
        (by omega) hr0 hr1 (by rw [if_neg (fun e => hjx' (hz.mp e))]; exact hw')
      exact hw.cast (by omega) rfl (by omega)

theorem walk_unary_mk (hR : ∀ s, R s → HoldsNH L s) {base w L0 : ℕ} {zc tc : ℕ → ℕ}
    (hU : UnaryShape base w L0 zc tc) {x n c : ℕ} (hxL : x ≤ L0) (hF : UnaryFacts R L base w L0 zc x)
    (h : Walk R L n (unaryExit base w L0 x) c) :
    Walk R L (2 * min (x + 1) L0 + n) base (2 * min (x + 1) L0 + c) :=
  (walk_unary_mk_from hR hU hxL hF h L0 0 (by omega) (Nat.zero_le _)).cast (by omega) (by omega)
    (by omega)

end Generic

/-! ## Layout bounds -/

theorem rBase_add_le {k : ℕ} (hk : k < 32 ∨ k = 33) : rBase k + 2942 ≤ 105947 := by
  rcases hk with hk | rfl
  · rw [rBase_of_le (by omega)]; omega
  · rw [rBase_33]

theorem gBase_add_le (k : ℕ) {q : ℕ} (hq : q < 64) : gBase k q + 44 ≤ rBase k + 2942 := by
  unfold gBase; split_ifs <;> omega

theorem leafSlot_add_le (k : ℕ) {e : ℕ} (he : e < 256) : leafSlot k e + 7 ≤ rBase k + 2942 := by
  have := gBase_add_le k (q := e / 4) (by omega)
  unfold leafSlot; omega

theorem leafSlot32_add_le {c : ℕ} : leafSlot32 c + 5 ≤ rBase 32 + 222 := by
  unfold leafSlot32; split_ifs <;> omega

theorem s0_le {k : ℕ} (hk : k < 34) : s0 k + 255 ≤ rootBase := by
  rcases Nat.lt_or_ge k 32 with h | h
  · rw [s0_of_lt h, show rootBase = 131036 from rfl]; omega
  · rcases (show k = 32 ∨ k = 33 by omega) with rfl | rfl <;> decide

/-! ## Instances of the unary chain -/

theorem riceShape {k : ℕ} (hk : k < 32 ∨ k = 33) :
    UnaryShape (rBase k) 46 63 (zuCell k) (tuCell k) where
  two_le := by omega
  lt := by have := rBase_add_le hk; rw [sentinel]; omega
  set := fun _ hi => cinstrAt_uset hk hi
  jmp := fun _ hi => cinstrAt_ujmp hk hi

theorem c32Shape : UnaryShape (rBase 32) 7 31 (zuCell 32) (tuCell 32) where
  two_le := by omega
  lt := by rw [rBase_32, sentinel]; norm_num
  set := fun _ hi => cinstrAt_u32set hi
  jmp := fun _ hi => cinstrAt_u32jmp hi

theorem unaryExit_rice (k : ℕ) {x : ℕ} (hx : x ≤ 63) : unaryExit (rBase k) 46 63 x = gBase k x := by
  unfold unaryExit
  split_ifs with h
  · rw [gBase_of_lt h]
  · rw [show x = 63 by omega, gBase_63]

theorem unaryExit_c32 {c : ℕ} (hc : c < 32) : unaryExit (rBase 32) 7 31 (31 - c) = leafSlot32 c := by
  unfold unaryExit
  split_ifs with h
  · rw [leafSlot32_of_pos (by omega)]
  · rw [show c = 0 by omega, leafSlot32_zero]

section Tree

variable {κ : ℕ} {R : ℕ → Prop} {L : MemImage κ}

/-! ### Groups -/

/-- The node facts of the group subtree taken to leaf `4q + b`: node `(0,0)`, then node
`(1, 2 ⌊b/2⌋)`, with condition cells encoding the two bits of `b`. -/
def GroupFacts (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (k q b : ℕ) : Prop :=
  R (gBase k q) ∧ R (gBase k q + 1) ∧ (Lx L (zbCell k 0) = 0 ↔ b < 2) ∧
    R (gBase k q + 11 * (2 * (b / 2)) + 2) ∧ R (gBase k q + 11 * (2 * (b / 2)) + 3) ∧
    (Lx L (zbCell k 1) = 0 ↔ b % 2 = 0)

theorem walk_g1 (hR : ∀ s, R s → HoldsNH L s) {k q b' n c : ℕ} (hk : k < 32 ∨ k = 33)
    (hq : q < 64) (hb' : b' = 0 ∨ b' = 2) (h : Walk R L n (gBase k q + 11 * b' + 2) c) :
    R (gBase k q + 11 * b' + 2) ∧ R (gBase k q + 11 * b' + 3) ∧ ∃ n' c', n = n' + 2 ∧
      c = c' + 2 ∧ Walk R L n' (if Lx L (zbCell k 1) = 0 then gBase k q + 11 * b' + 4
        else gBase k q + 11 * (b' + 1) + 4) c' := by
  have hb := gBase_add_le k hq
  have hr := rBase_add_le hk
  have hjmp : cinstrAt (gBase k q + 11 * b' + 2 + 1) = .jump (zbCell k 1) (tbCell k 1) oneCell := by
    rw [show gBase k q + 11 * b' + 2 + 1 = gBase k q + 11 * b' + 3 by omega]
    exact cinstrAt_g1jmp hk hq hb'
  obtain ⟨hr0, hr1, n', c', rfl, rfl, hw⟩ := walk_node hR (cinstrAt_g1set hk hq hb') hjmp
    (by omega) (by rw [sentinel]; omega) h
  refine ⟨hr0, rcast hr1 (by omega), n', c', rfl, rfl, hw.cast rfl ?_ rfl⟩
  split_ifs <;> omega

theorem walk_g1_mk (hR : ∀ s, R s → HoldsNH L s) {k q b' n c : ℕ} (hk : k < 32 ∨ k = 33)
    (hq : q < 64) (hb' : b' = 0 ∨ b' = 2) (hr0 : R (gBase k q + 11 * b' + 2))
    (hr1 : R (gBase k q + 11 * b' + 3))
    (h : Walk R L n (if Lx L (zbCell k 1) = 0 then gBase k q + 11 * b' + 4
        else gBase k q + 11 * (b' + 1) + 4) c) :
    Walk R L (n + 2) (gBase k q + 11 * b' + 2) (c + 2) := by
  have hb := gBase_add_le k hq
  have hr := rBase_add_le hk
  have hjmp : cinstrAt (gBase k q + 11 * b' + 2 + 1) = .jump (zbCell k 1) (tbCell k 1) oneCell := by
    rw [show gBase k q + 11 * b' + 2 + 1 = gBase k q + 11 * b' + 3 by omega]
    exact cinstrAt_g1jmp hk hq hb'
  refine walk_node_mk hR (cinstrAt_g1set hk hq hb') hjmp (by omega) (by rw [sentinel]; omega) hr0
    (rcast hr1 (by omega)) (h.cast rfl ?_ rfl)
  split_ifs <;> omega

/-- **Group.** A walk from group `q`'s entry reaches leaf `4q + b` after four steps and cycles. -/
theorem walk_group (hR : ∀ s, R s → HoldsNH L s) {k q n c : ℕ} (hk : k < 32 ∨ k = 33)
    (hq : q < 64) (h : Walk R L n (gBase k q) c) :
    ∃ b, b < 4 ∧ GroupFacts R L k q b ∧ ∃ n' c', n = 4 + n' ∧ c = 4 + c' ∧
      Walk R L n' (leafSlot k (4 * q + b)) c' := by
  have hb := gBase_add_le k hq
  have hr := rBase_add_le hk
  obtain ⟨hr0, hr1, n1, c1, rfl, rfl, hw⟩ := walk_node hR (cinstrAt_g0set hk hq)
    (cinstrAt_g0jmp hk hq) (by omega) (by rw [sentinel]; omega) h
  by_cases h0 : Lx L (zbCell k 0) = 0
  · rw [if_pos h0] at hw
    obtain ⟨hr2, hr3, n2, c2, rfl, rfl, hw2⟩ :=
      walk_g1 hR hk hq (b' := 0) (Or.inl rfl) (hw.cast rfl (by omega) rfl)
    by_cases h1 : Lx L (zbCell k 1) = 0
    · rw [if_pos h1] at hw2
      exact ⟨0, by omega, ⟨hr0, hr1, iff_of_true h0 (by omega), hr2, hr3, iff_of_true h1 rfl⟩,
        n2, c2, by omega, by omega, hw2.cast rfl (by rw [leafSlot_eq (by omega)]) rfl⟩
    · rw [if_neg h1] at hw2
      exact ⟨1, by omega, ⟨hr0, hr1, iff_of_true h0 (by omega), hr2, hr3,
        iff_of_false h1 (by omega)⟩, n2, c2, by omega, by omega,
        hw2.cast rfl (by rw [leafSlot_eq (by omega)]) rfl⟩
  · rw [if_neg h0] at hw
    obtain ⟨hr2, hr3, n2, c2, rfl, rfl, hw2⟩ :=
      walk_g1 hR hk hq (b' := 2) (Or.inr rfl) (hw.cast rfl (by omega) rfl)
    by_cases h1 : Lx L (zbCell k 1) = 0
    · rw [if_pos h1] at hw2
      exact ⟨2, by omega, ⟨hr0, hr1, iff_of_false h0 (by omega), rcast hr2 (by omega),
        rcast hr3 (by omega), iff_of_true h1 rfl⟩, n2, c2, by omega, by omega,
        hw2.cast rfl (by rw [leafSlot_eq (by omega)]) rfl⟩
    · rw [if_neg h1] at hw2
      exact ⟨3, by omega, ⟨hr0, hr1, iff_of_false h0 (by omega), rcast hr2 (by omega),
        rcast hr3 (by omega), iff_of_false h1 (by omega)⟩, n2, c2, by omega, by omega,
        hw2.cast rfl (by rw [leafSlot_eq (by omega)]) rfl⟩

theorem walk_group_mk (hR : ∀ s, R s → HoldsNH L s) {k q b n c : ℕ} (hk : k < 32 ∨ k = 33)
    (hq : q < 64) (hb4 : b < 4) (hF : GroupFacts R L k q b)
    (h : Walk R L n (leafSlot k (4 * q + b)) c) : Walk R L (4 + n) (gBase k q) (4 + c) := by
  have hb := gBase_add_le k hq
  have hr := rBase_add_le hk
  obtain ⟨hr0, hr1, h0, hr2, hr3, h1⟩ := hF
  rw [leafSlot_eq hb4] at h
  have hb' : 2 * (b / 2) = 0 ∨ 2 * (b / 2) = 2 := by omega
  have e1 : gBase k q + 11 * b + 4 = if Lx L (zbCell k 1) = 0 then
      gBase k q + 11 * (2 * (b / 2)) + 4 else gBase k q + 11 * (2 * (b / 2) + 1) + 4 := by
    by_cases h1' : Lx L (zbCell k 1) = 0
    · rw [if_pos h1']; have := h1.mp h1'; omega
    · rw [if_neg h1']; have : b % 2 ≠ 0 := fun e => h1' (h1.mpr e); omega
  have e0 : gBase k q + 11 * (2 * (b / 2)) + 2 =
      if Lx L (zbCell k 0) = 0 then gBase k q + 2 else gBase k q + 24 := by
    by_cases h0' : Lx L (zbCell k 0) = 0
    · rw [if_pos h0']; have := h0.mp h0'; omega
    · rw [if_neg h0']; have : ¬ b < 2 := fun e => h0' (h0.mpr e); omega
  have hw2 := walk_g1_mk hR hk hq hb' hr2 hr3 (n := n) (c := c) (h.cast rfl e1 rfl)
  have hw := walk_node_mk hR (cinstrAt_g0set hk hq) (cinstrAt_g0jmp hk hq) (by omega)
    (by rw [sentinel]; omega) hr0 hr1 (hw2.cast rfl e0 rfl)
  exact hw.cast (by omega) rfl (by omega)

/-! ### Leaves -/

/-- The last two ops of leaf `e`, indexed from `a = leafLen k e - 2`. -/
theorem leaf_split (k e : ℕ) :
    ∃ a, leafLen k e = a + 2 ∧
      leafOp k e a = .setc (leafJC k e) (tgtV (s0 k + min e 254 + 1)) ∧
      leafOp k e (a + 1) = .jump oneCell (leafJC k e) oneCell ∧
      (∑ i ∈ Finset.range a, (leafOp k e i).cost) + 2 = leafCost k e := by
  have h4 := leafLen_ge k e
  refine ⟨leafLen k e - 2, by omega, leafOp_setJ k e, ?_, ?_⟩
  · rw [show leafLen k e - 2 + 1 = leafLen k e - 1 by omega]; exact leafOp_last k e
  · rw [← leafOp_cost_sum k e, show leafLen k e = leafLen k e - 2 + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, show leafLen k e - 2 + 1 + 1 - 2 = leafLen k e - 2
        by omega, leafOp_setJ, show leafLen k e - 2 + 1 = leafLen k e - 1 by omega, leafOp_last]
    simp only [CInstr.cost]

/-- **Leaf.** A walk from leaf `e`'s first op runs its `leafLen` ops and lands on body step
`min e 254 + 1`, i.e. `s0 k + e + 1`, or the next segment `s0 k + 255` when `e = 255`. -/
theorem walk_leaf (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {k e n c : ℕ}
    (hk : k < 32 ∨ k = 33) (he : e < 256) (h : Walk R L n (leafSlot k e) c) :
    (∀ i < leafLen k e, R (leafSlot k e + i)) ∧ ∃ n' c', n = leafLen k e + n' ∧
      c = leafCost k e + c' ∧ Walk R L n' (s0 k + min e 254 + 1) c' := by
  obtain ⟨a, ha, hsetJ, hlast, hsum⟩ := leaf_split k e
  have h7 := leafLen_le k e
  have hb := leafSlot_add_le k he
  have hr := rBase_add_le hk
  have hs0 := s0_le (k := k) (by omega)
  have hjs : ∀ i < a, (cinstrAt (leafSlot k e + i)).isJump = false := fun i hi => by
    rw [cinstrAt_leaf hk he (by omega)]; exact leafOp_isJump (by omega)
  obtain ⟨hr1, n1, c1, rfl, rfl, hw1⟩ := walk_seg hjs (by rw [sentinel]; omega) h
  have hs1 : cinstrAt (leafSlot k e + a) = .setc (leafJC k e) (tgtV (s0 k + min e 254 + 1)) := by
    rw [cinstrAt_leaf hk he (by omega), hsetJ]
  have hs2 : cinstrAt (leafSlot k e + a + 1) = .jump oneCell (leafJC k e) oneCell := by
    rw [Nat.add_assoc, cinstrAt_leaf hk he (by omega), hlast]
  obtain ⟨hr2, hr3, n2, c2, rfl, rfl, hw2⟩ := walk_node hR hs1 hs2
    (by rw [show rootBase = 131036 from rfl] at hs0; omega) (by rw [sentinel]; omega) hw1
  rw [if_neg (oneCell_ne_zero hone)] at hw2
  have hsum' : ∑ i ∈ Finset.range a, (cinstrAt (leafSlot k e + i)).cost =
      ∑ i ∈ Finset.range a, (leafOp k e i).cost :=
    Finset.sum_congr rfl fun i hi => by
      rw [cinstrAt_leaf hk he (by have := Finset.mem_range.mp hi; omega)]
  refine ⟨fun i hi => ?_, n2, c2, by omega, by omega, hw2⟩
  rcases (show i < a ∨ i = a ∨ i = a + 1 by omega) with hi | rfl | rfl
  · exact hr1 i hi
  · exact hr2
  · exact rcast hr3 (by omega)

theorem walk_leaf_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {k e n c : ℕ}
    (hk : k < 32 ∨ k = 33) (he : e < 256) (hr : ∀ i < leafLen k e, R (leafSlot k e + i))
    (h : Walk R L n (s0 k + min e 254 + 1) c) :
    Walk R L (leafLen k e + n) (leafSlot k e) (leafCost k e + c) := by
  obtain ⟨a, ha, hsetJ, hlast, hsum⟩ := leaf_split k e
  have h7 := leafLen_le k e
  have hb := leafSlot_add_le k he
  have hrb := rBase_add_le hk
  have hs0 := s0_le (k := k) (by omega)
  have hjs : ∀ i < a, (cinstrAt (leafSlot k e + i)).isJump = false := fun i hi => by
    rw [cinstrAt_leaf hk he (by omega)]; exact leafOp_isJump (by omega)
  have hs1 : cinstrAt (leafSlot k e + a) = .setc (leafJC k e) (tgtV (s0 k + min e 254 + 1)) := by
    rw [cinstrAt_leaf hk he (by omega), hsetJ]
  have hs2 : cinstrAt (leafSlot k e + a + 1) = .jump oneCell (leafJC k e) oneCell := by
    rw [Nat.add_assoc, cinstrAt_leaf hk he (by omega), hlast]
  have hw2 := walk_node_mk hR hs1 hs2 (by rw [show rootBase = 131036 from rfl] at hs0; omega)
    (by rw [sentinel]; omega) (hr a (by omega)) (rcast (hr (a + 1) (by omega)) (by omega))
    (by rw [if_neg (oneCell_ne_zero hone)]; exact h)
  have hw1 := walk_seg_mk hjs (by rw [sentinel]; omega) (fun i hi => hr i (by omega)) hw2
  have hsum' : ∑ i ∈ Finset.range a, (cinstrAt (leafSlot k e + i)).cost =
      ∑ i ∈ Finset.range a, (leafOp k e i).cost :=
    Finset.sum_congr rfl fun i hi => by
      rw [cinstrAt_leaf hk he (by have := Finset.mem_range.mp hi; omega)]
  exact hw1.cast (by omega) rfl (by omega)

/-- The five ops of leaf `c` of chain 32: the first three are straight, then a node. -/
theorem leaf32_facts {c : ℕ} (hc : c < 32) :
    (∀ i < 3, (cinstrAt (leafSlot32 c + i)).isJump = false) ∧
    ∑ i ∈ Finset.range 3, (cinstrAt (leafSlot32 c + i)).cost = 12 ∧
    cinstrAt (leafSlot32 c + 3) = .setc (tCell 32) (tgtV (s0 32 + c + 1)) ∧
    cinstrAt (leafSlot32 c + 3 + 1) = .jump oneCell (tCell 32) oneCell := by
  refine ⟨fun i hi => ?_, ?_, by rw [cinstrAt_leaf32 hc (by omega), leaf32Op_setT],
    by rw [Nat.add_assoc, cinstrAt_leaf32 hc (by omega), leaf32Op_jmp]⟩
  · rw [cinstrAt_leaf32 hc (by omega)]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · rw [leaf32Op_blake]; rfl
    · rw [leaf32Op_setU]; rfl
    · rw [leaf32Op_mul]; rfl
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      cinstrAt_leaf32 hc (show 0 < 5 by omega), cinstrAt_leaf32 hc (show 1 < 5 by omega),
      cinstrAt_leaf32 hc (show 2 < 5 by omega), leaf32Op_blake, leaf32Op_setU, leaf32Op_mul]
    rfl

/-- **Leaf of chain 32.** Five ops, fourteen cycles, landing on body step `c + 1`. -/
theorem walk_leaf32 (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {c n cost : ℕ}
    (hc : c < 32) (h : Walk R L n (leafSlot32 c) cost) :
    (∀ i < 5, R (leafSlot32 c + i)) ∧ ∃ n' c', n = 5 + n' ∧ cost = 14 + c' ∧
      Walk R L n' (s0 32 + c + 1) c' := by
  obtain ⟨hj, hsum, hs1, hs2⟩ := leaf32_facts hc
  have hb : leafSlot32 c + 5 ≤ rBase 32 + 222 := leafSlot32_add_le
  rw [rBase_32] at hb
  obtain ⟨hr1, n1, c1, rfl, rfl, hw1⟩ := walk_seg hj (by rw [sentinel]; omega) h
  obtain ⟨hr2, hr3, n2, c2, rfl, rfl, hw2⟩ := walk_node hR hs1 hs2
    (by rw [s0_32]; omega) (by rw [sentinel]; omega) hw1
  rw [if_neg (oneCell_ne_zero hone)] at hw2
  refine ⟨fun i hi => ?_, n2, c2, by omega, by omega, hw2⟩
  rcases (show i < 3 ∨ i = 3 ∨ i = 4 by omega) with hi | rfl | rfl
  · exact hr1 i hi
  · exact hr2
  · exact rcast hr3 (by omega)

theorem walk_leaf32_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV)
    {c n cost : ℕ} (hc : c < 32) (hr : ∀ i < 5, R (leafSlot32 c + i))
    (h : Walk R L n (s0 32 + c + 1) cost) : Walk R L (5 + n) (leafSlot32 c) (14 + cost) := by
  obtain ⟨hj, hsum, hs1, hs2⟩ := leaf32_facts hc
  have hb : leafSlot32 c + 5 ≤ rBase 32 + 222 := leafSlot32_add_le
  rw [rBase_32] at hb
  have hw2 := walk_node_mk hR hs1 hs2 (by rw [s0_32]; omega) (by rw [sentinel]; omega)
    (hr 3 (by omega)) (rcast (hr 4 (by omega)) (by omega))
    (by rw [if_neg (oneCell_ne_zero hone)]; exact h)
  have hw1 := walk_seg_mk hj (by rw [sentinel]; omega) (fun i hi => hr i (by omega)) hw2
  exact hw1.cast (by omega) rfl (by omega)

/-! ### Bodies -/

/-- **Body.** From body step `j0 ≥ 1` the walk runs steps `j0..254`, ten cycles each, and lands
on `s0 k + 255`. -/
theorem walk_body {k j0 n c : ℕ} (hk : k < 34) (hj1 : 1 ≤ j0) (hj2 : j0 ≤ 255)
    (h : Walk R L n (s0 k + j0) c) :
    (∀ j, j0 ≤ j → j ≤ 254 → R (s0 k + j)) ∧ ∃ n' c', n = (255 - j0) + n' ∧
      c = 10 * (255 - j0) + c' ∧ Walk R L n' (s0 k + 255) c' := by
  have hs0 := s0_le hk
  have hbody : ∀ i < 255 - j0, cinstrAt (s0 k + j0 + i) = bodyInstr k (j0 + i) := fun i hi => by
    rw [Nat.add_assoc, cinstrAt_body hk (by omega) (by omega)]
  obtain ⟨hr, n', c', rfl, rfl, hw⟩ := walk_seg (a := 255 - j0)
    (fun i hi => by rw [hbody i hi]; rfl) (by rw [sentinel, show rootBase = 131036 from rfl] at *; omega) h
  refine ⟨fun j hj hj' => rcast (hr (j - j0) (by omega)) (by omega), n', c', rfl, ?_,
    hw.cast rfl (by omega) rfl⟩
  rw [seg_cost (w := 10) fun i hi => by rw [hbody i hi]; rfl]

theorem walk_body_mk {k j0 n c : ℕ} (hk : k < 34) (hj1 : 1 ≤ j0) (hj2 : j0 ≤ 255)
    (hr : ∀ j, j0 ≤ j → j ≤ 254 → R (s0 k + j)) (h : Walk R L n (s0 k + 255) c) :
    Walk R L ((255 - j0) + n) (s0 k + j0) (10 * (255 - j0) + c) := by
  have hs0 := s0_le hk
  have hbody : ∀ i < 255 - j0, cinstrAt (s0 k + j0 + i) = bodyInstr k (j0 + i) := fun i hi => by
    rw [Nat.add_assoc, cinstrAt_body hk (by omega) (by omega)]
  have hw := walk_seg_mk (a := 255 - j0) (fun i hi => by rw [hbody i hi]; rfl)
    (by rw [sentinel, show rootBase = 131036 from rfl] at *; omega)
    (fun i hi => rcast (hr (j0 + i) (by omega) (by omega)) (by omega)) (h.cast rfl (by omega) rfl)
  rw [seg_cost (w := 10) fun i hi => by rw [hbody i hi]; rfl] at hw
  exact hw

end Tree

end

end OptimalOTS.LeanIsaBaseline.Machine
