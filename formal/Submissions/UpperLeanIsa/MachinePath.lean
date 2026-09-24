import Submissions.UpperLeanIsa.MachineRun

/-!
# The forced path of the HL-FLAT-A bytecode

Every walk from slot `0` is the forced walk of one digit vector `s = digitOf v` (read off the
landing hints): the prologue `0 … 56`, then for each chain `k` the dispatch at its control slot,
the landing at `entryOf k (s k) = BASE k + 21 · s k`, the block's straight-line ops (`pre k`
non-hash ops, the `s k` chain steps, `post k` non-hash ops), and finally the exit into the root
segment `rootSlot … rootSlot + 10`, which falls through to the sentinel.

* `walk_full`: a walk of any relation `R` implying the hash-free one yields the digit vector,
  the relation at every slot of its path (`PathFacts`), the landings (`Landing`), and the exact
  step count and cost `totalSteps s`, `totalCost s`.
* `walk_full_mk`: conversely, those facts assemble the walk (the honest direction).
-/

namespace OptimalOTS.HLFlat

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

noncomputable section

/-! ## Block shape -/

/-- The entry slot of digit `s` of chain `k`. -/
def entryOf (k s : ℕ) : ℕ := BASE k + 21 * s

/-- Straight-line ops before the chain steps. -/
def pre (k : ℕ) : ℕ := if k = 0 then 1 else 3

/-- Straight-line ops after the chain steps. -/
def post (k : ℕ) : ℕ := if k = 0 then 2 else if k < 41 then 1 else 0

/-- The control slot after the block of digit `s` of chain `k`: the next dispatch, or the exit. -/
def ctlAfter (k s : ℕ) : ℕ := entryOf k s + 1 + pre k + s + post k

/-- Walk steps of chain `k`'s segment (dispatch, block, and for chain 41 the exit). -/
def segSteps (k s : ℕ) : ℕ := (if k = 0 then 5 else 6) + s

/-- Cycles of chain `k`'s segment. -/
def segCost (k s : ℕ) : ℕ := (if k = 0 then 5 else 6) + 10 * s

theorem pre_add_post (k : ℕ) (hk : k < 42) : 2 + pre k + post k + (if k = 41 then 1 else 0) =
    (if k = 0 then 5 else 6) := by
  unfold pre post; split_ifs <;> omega

theorem pre_zero : pre 0 = 1 := rfl
theorem post_zero : post 0 = 2 := rfl
theorem pre_pos {k : ℕ} (h : k ≠ 0) : pre k = 3 := if_neg h
theorem post_mid {k : ℕ} (h : k ≠ 0) (h41 : k < 41) : post k = 1 := by
  unfold post; rw [if_neg h, if_pos h41]
theorem post_41 : post 41 = 0 := rfl

theorem blockOp_pre {k s i : ℕ} (hi : i < pre k) :
    (blockOp k s (1 + i)).straight = true ∧ (blockOp k s (1 + i)).cost = 1 := by
  unfold blockOp
  by_cases h0 : k = 0
  · subst h0
    rw [pre_zero] at hi
    obtain rfl : i = 0 := by omega
    rw [if_pos rfl, if_pos rfl]; exact ⟨rfl, rfl⟩
  · rw [pre_pos h0] at hi
    rw [if_neg h0]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · rw [if_pos rfl]; split_ifs <;> exact ⟨rfl, rfl⟩
    · rw [if_neg (by omega), if_pos rfl]; exact ⟨rfl, rfl⟩
    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl]; exact ⟨rfl, rfl⟩

theorem blockOp_chain {k s t : ℕ} (ht : t < s) : blockOp k s (1 + pre k + t) = chainOp k s t := by
  unfold blockOp
  by_cases h0 : k = 0
  · subst h0
    rw [pre_zero, if_pos rfl, if_neg (by omega), if_pos (by omega),
      show 1 + 1 + t - 2 = t by omega]
  · rw [pre_pos h0, if_neg h0, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega), show 1 + 3 + t - 4 = t by omega]

theorem chainOp_straight (k s t : ℕ) :
    (chainOp k s t).straight = true ∧ (chainOp k s t).cost = 10 := by
  unfold chainOp; exact ⟨rfl, rfl⟩

theorem blockOp_post {k s i : ℕ} (hi : i < post k) :
    (blockOp k s (1 + pre k + s + i)).straight = true ∧
      (blockOp k s (1 + pre k + s + i)).cost = 1 := by
  unfold blockOp
  by_cases h0 : k = 0
  · subst h0
    rw [post_zero] at hi
    rw [pre_zero, if_pos rfl]
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; exact ⟨rfl, rfl⟩
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      exact ⟨rfl, rfl⟩
  · have h41 : k < 41 := by
      by_contra h
      obtain rfl : k = 41 := by unfold post at hi; rw [if_neg h0, if_neg h] at hi; omega
      rw [post_41] at hi; omega
    rw [post_mid h0 h41] at hi
    obtain rfl : i = 0 := by omega
    rw [pre_pos h0, if_neg h0, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega), if_pos h41]
    exact ⟨rfl, rfl⟩

/-- The last post op of chain `k < 41` is the next chain's `MUL(H_{k+1}, g, H'_{k+1})`. -/
theorem blockOp_nextMul {k s : ℕ} (hk : k < 41) :
    blockOp k s (1 + pre k + s + post k - 1) = .mul (hCell (k + 1)) gCell (h1Cell (k + 1)) := by
  unfold blockOp
  by_cases h0 : k = 0
  · subst h0
    rw [pre_zero, post_zero, if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
  · rw [pre_pos h0, post_mid h0 hk, if_neg h0, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos hk]

/-- The control op after the block of chain `k < 41`: the next dispatch. -/
theorem blockOp_ctl_disp {k s : ℕ} (hk : k < 41) :
    blockOp k s (1 + pre k + s + post k) = .dispatch (k + 1) := by
  unfold blockOp
  by_cases h0 : k = 0
  · subst h0
    rw [pre_zero, post_zero, if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega)]
  · rw [pre_pos h0, post_mid h0 hk, if_neg h0, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, hk⟩]

/-- The control op after the block of chain 41: the exit. -/
theorem blockOp_ctl_exit {s : ℕ} : blockOp 41 s (1 + pre 41 + s + post 41) = .exit := by
  unfold blockOp
  rw [pre_pos (by omega), post_41, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]

theorem blockOp_ctl {k s : ℕ} (hk : k < 42) :
    blockOp k s (1 + pre k + s + post k) = if k < 41 then .dispatch (k + 1) else .exit := by
  by_cases h41 : k < 41
  · rw [if_pos h41]; exact blockOp_ctl_disp h41
  · obtain rfl : k = 41 := by omega
    rw [if_neg h41]; exact blockOp_ctl_exit

theorem blk_lt {k s : ℕ} (hk : k < 42) (hs : s < W k) : 1 + pre k + s + post k < 21 := by
  unfold pre post W at *; split_ifs at * <;> omega

theorem cinstrAt_blk {k s i : ℕ} (hk : k < 42) (hs : s < W k) (hi0 : 0 < i)
    (hi : i ≤ 1 + pre k + s + post k) : cinstrAt (entryOf k s + i) = blockOp k s i :=
  cinstrAt_block hk hs hi0 (lt_of_le_of_lt hi (blk_lt hk hs))

/-! ## Prologue shape -/

/-- Cycles of prologue op `t`. -/
def proW (t : ℕ) : ℕ := if t = 55 then 10 else 1

/-- Cycles of root op `t`. -/
def rootW (t : ℕ) : ℕ := if t < 10 then 10 else 1

theorem prologue_straight {t : ℕ} (ht : t < 57) :
    (cinstrAt t).straight = true ∧ (cinstrAt t).cost = proW t := by
  rw [cinstrAt_pro (by omega)]
  unfold prologue proW
  split_ifs <;> first | exact ⟨rfl, rfl⟩ | omega

theorem cinstrAt_57 : cinstrAt 57 = .dispatch 0 := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_56 : cinstrAt 56 = .mul (hCell 0) gCell (h1Cell 0) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_55 : cinstrAt 55 = .blake msgLo msgHi nonceCell pkCell zCell idxCell tidxCell := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set0 : cinstrAt 0 = .setc zCell 0 := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set1 : cinstrAt 1 = .setc oneCell oneV := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set2 : cinstrAt 2 = .setc lenCell (natV 5504) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set3 : cinstrAt 3 = .setc tidxCell (natV 10) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set4 : cinstrAt 4 = .setc gCell gV := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_set5 : cinstrAt 5 = .setc k0Cell k0V := by
  rw [cinstrAt_pro (by omega)]; unfold prologue; simp

theorem cinstrAt_sym {v : ℕ} (hv : v < 7) : cinstrAt (6 + v) = .setc (symCell v) (natV (v + 3)) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 6 + v - 6 = v by omega, show 6 + v - 3 = v + 3 by omega]

theorem cinstrAt_frame {k : ℕ} (hk : k < 42) : cinstrAt (13 + k) = .setc (fCell k) (frameV k) := by
  rw [cinstrAt_pro (by omega)]; unfold prologue
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 13 + k - 13 = k by omega]

/-- The root segment is straight: ten `BLAKE2S` and the pk `XOR`. -/
theorem root_straight {t : ℕ} (ht : t < 11) :
    (cinstrAt (rootSlot + t)).straight = true ∧
      (cinstrAt (rootSlot + t)).cost = rootW t := by
  rw [cinstrAt_root ht]; unfold rootOp rootW; split_ifs <;> exact ⟨rfl, rfl⟩

/-! ## Walk lemmas -/

section Walks

variable {R : ℕ → Prop} {v : ℕ → E}

theorem Walk.inv {n t c : ℕ} (h : Walk R v n t c) (ht : t ≠ sentinel) :
    t < sentinel ∧ R t ∧ ∃ n' c', n = n' + (cinstrAt t).steps ∧ c = (cinstrAt t).cost + c' ∧
      Walk R v n' (nextSlot v t) c' := by
  cases h with
  | done => exact absurd rfl ht
  | step hs hR hw => exact ⟨hs, hR, _, _, rfl, rfl, hw⟩

theorem Walk.at_sentinel {n c : ℕ} (h : Walk R v n sentinel c) : n = 0 ∧ c = 0 := by
  cases h with
  | done => exact ⟨rfl, rfl⟩
  | step hs _ _ => exact absurd hs (lt_irrefl _)

/-- A straight segment of `a` ops of cost `w` each. -/
theorem walk_seg {a t w : ℕ} (hst : ∀ i < a, (cinstrAt (t + i)).straight = true ∧
    (cinstrAt (t + i)).cost = w) (hta : t + a ≤ sentinel) :
    ∀ {n c : ℕ}, Walk R v n t c → (∀ i < a, R (t + i)) ∧
      ∃ n' c', n = n' + a ∧ c = a * w + c' ∧ Walk R v n' (t + a) c' := by
  induction a generalizing t with
  | zero => intro n c h; exact ⟨fun i hi => absurd hi (by omega), n, c, rfl, by simp, h⟩
  | succ a ih =>
    intro n c h
    obtain ⟨hs1, hc1⟩ := hst 0 (by omega)
    rw [Nat.add_zero] at hs1 hc1
    obtain ⟨-, hR, n1, c1, rfl, rfl, hw⟩ := h.inv (by omega)
    rw [nextSlot_straight v hs1] at hw
    have hst' : ∀ i < a, (cinstrAt (t + 1 + i)).straight = true ∧
        (cinstrAt (t + 1 + i)).cost = w := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact hst (i + 1) (by omega)
    obtain ⟨hRs, n2, c2, rfl, rfl, hw2⟩ := ih hst' (by omega) hw
    refine ⟨fun i hi => ?_, n2, c2, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rwa [Nat.add_zero]
      · have := hRs (i - 1) (by omega)
        rwa [show t + 1 + (i - 1) = t + i by omega] at this
    · rw [straight_steps hs1]; ring
    · rw [hc1]; ring
    · rwa [show t + 1 + a = t + (a + 1) by omega] at hw2

theorem walk_seg_mk {a t w : ℕ} (hst : ∀ i < a, (cinstrAt (t + i)).straight = true ∧
    (cinstrAt (t + i)).cost = w) (hta : t + a ≤ sentinel) (hR : ∀ i < a, R (t + i))
    {n c : ℕ} (h : Walk R v n (t + a) c) : Walk R v (n + a) t (a * w + c) := by
  induction a generalizing t n c with
  | zero => simpa using h
  | succ a ih =>
    obtain ⟨hs1, hc1⟩ := hst 0 (by omega)
    rw [Nat.add_zero] at hs1 hc1
    have hst' : ∀ i < a, (cinstrAt (t + 1 + i)).straight = true ∧
        (cinstrAt (t + 1 + i)).cost = w := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact hst (i + 1) (by omega)
    have hR' : ∀ i < a, R (t + 1 + i) := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact hR (i + 1) (by omega)
    have hw := ih hst' (by omega) hR' (by rwa [show t + 1 + a = t + (a + 1) by omega])
    rw [← nextSlot_straight v hs1] at hw
    have := Walk.step (by omega) (by simpa using hR 0 (by omega)) hw
    rw [straight_steps hs1, hc1] at this
    convert this using 1 <;> ring

end Walks

/-! ## The digit vector of an image -/

/-- The digit of chain `k` read off its landing hint. -/
def digitOf (v : ℕ → E) (k : ℕ) : ℕ := (slotOf ((v (hCell k)).limb 0) - BASE k) / 21

/-- The landing hints of the digit vector `s`. -/
def Landing (v : ℕ → E) (s : ℕ → ℕ) : Prop := ∀ k < 42, v (hCell k) = ofK (gpow (entryOf k (s k)))

/-- The digit vector is in range. -/
def Valid (s : ℕ → ℕ) : Prop := ∀ k < 42, s k < W k

/-- The relation holds at every slot of the path of `s`. -/
structure PathFacts (R : ℕ → Prop) (s : ℕ → ℕ) : Prop where
  pro : ∀ t < 58, R t
  blk : ∀ k < 42, ∀ i, 0 < i → i ≤ 1 + pre k + s k + post k → R (entryOf k (s k) + i)
  root : ∀ t < 11, R (rootSlot + t)

/-- The dispatch slot of chain `j` on the path of `s`. -/
def ctl (s : ℕ → ℕ) (j : ℕ) : ℕ := if j = 0 then 57 else ctlAfter (j - 1) (s (j - 1))

theorem ctl_succ (s : ℕ → ℕ) (j : ℕ) : ctl s (j + 1) = ctlAfter j (s j) := by
  unfold ctl; rw [if_neg (by omega), Nat.add_sub_cancel]

theorem cinstrAt_ctl {s : ℕ → ℕ} {j : ℕ} (hj : j < 42) (hs : ∀ k < j, s k < W k) :
    cinstrAt (ctl s j) = .dispatch j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact cinstrAt_57
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [ctl_succ, ctlAfter,
      show entryOf k (s k) + 1 + pre k + s k + post k = entryOf k (s k) + (1 + pre k + s k + post k)
        by ring, cinstrAt_blk (by omega) (hs k (by omega)) (by omega) le_rfl, blockOp_ctl (by omega),
      if_pos (by omega)]

theorem entryOf_lt {k s : ℕ} (hk : k < 42) (hs : s < W k) : entryOf k s + 21 ≤ 10142 := by
  unfold entryOf BASE; unfold W at hs; split_ifs at * <;> omega

theorem entryOf_ge (k s : ℕ) : 2740 ≤ entryOf k s := by
  unfold entryOf; have := base_ge k; omega

/-- A landing at an entry of chain `k` determines its digit. -/
theorem digitOf_eq {v : ℕ → E} {k e : ℕ} (he : IsEntry k e) (hx : (v (hCell k)).limb 0 = gpow e) :
    e = entryOf k (digitOf v k) ∧ digitOf v k < W k := by
  have hlt := isEntry_lt he
  unfold digitOf
  rw [hx, slotOf_gpow (by omega)]
  exact isEntry_eq he

section Chains

variable {R : ℕ → Prop} {v : ℕ → E} (hR : ∀ t, R t → (cinstrAt t).RelNH v)
include hR

/-- The dispatch step: a landing on an entry of chain `k`, and the walk resumes after it. -/
theorem walk_disp {d k n c : ℕ} (hci : cinstrAt d = .dispatch k) (hg : v gCell = gV)
    (hmul : v (h1Cell k) = v (hCell k) * v gCell) (h : Walk R v n d c) :
    R d ∧ digitOf v k < W k ∧ v (hCell k) = ofK (gpow (entryOf k (digitOf v k))) ∧
      ∃ n' c', n = n' + 2 ∧ c = 2 + c' ∧ Walk R v n' (entryOf k (digitOf v k) + 1) c' := by
  have hdne : d ≠ sentinel := fun e => by rw [e, cinstrAt_sentinel] at hci; cases hci
  obtain ⟨-, hRd, n', c', rfl, rfl, hw⟩ := h.inv hdne
  have hrel := hR d hRd
  rw [hci] at hrel
  obtain ⟨hH, -, e, he, hx⟩ := hrel
  obtain ⟨he', hdig⟩ := digitOf_eq he hx
  have hHv : v (hCell k) = ofK (gpow (entryOf k (digitOf v k))) := by
    rw [ofK_limb hH, hx, ← he']
  have hlt := entryOf_lt he.1 hdig
  have hnext : nextSlot v d = entryOf k (digitOf v k) + 1 := by
    unfold nextSlot; rw [hci]
    show slotOf _ = _
    rw [hmul, hHv, hg, gV, ← ofK_mul, limb_ofK_zero, mul_comm, g_mul_gpow, slotOf_gpow (by omega)]
  rw [hnext] at hw
  exact ⟨hRd, hdig, hHv, n', c', by rw [hci]; rfl, by rw [hci]; rfl, hw⟩

/-- One chain segment, from its dispatch to the next control slot (or the root). -/
theorem walk_chain {j n c : ℕ} (hj : j < 42) {d : ℕ} (hci : cinstrAt d = .dispatch j)
    (hg : v gCell = gV) (hk0 : v k0Cell = k0V) (hmul : v (h1Cell j) = v (hCell j) * v gCell)
    (h : Walk R v n d c) :
    R d ∧ digitOf v j < W j ∧ v (hCell j) = ofK (gpow (entryOf j (digitOf v j))) ∧
      (∀ i, 0 < i → i ≤ 1 + pre j + digitOf v j + post j → R (entryOf j (digitOf v j) + i)) ∧
      ∃ n' c', n = n' + segSteps j (digitOf v j) ∧ c = segCost j (digitOf v j) + c' ∧
        Walk R v n' (if j < 41 then ctlAfter j (digitOf v j) else rootSlot) c' := by
  obtain ⟨hRd, hdig, hHv, n1, c1, rfl, rfl, hw1⟩ := walk_disp hR hci hg hmul h
  set s := digitOf v j with hs
  set e := entryOf j s with he
  have hlt := entryOf_lt hj hdig
  have hpre : ∀ i < pre j, (cinstrAt (e + 1 + i)).straight = true ∧ (cinstrAt (e + 1 + i)).cost = 1 :=
    fun i hi => by
      rw [Nat.add_assoc, cinstrAt_blk hj hdig (by omega) (by have := blk_lt hj hdig; omega)]
      exact blockOp_pre hi
  have hch : ∀ t < s, (cinstrAt (e + 1 + pre j + t)).straight = true ∧
      (cinstrAt (e + 1 + pre j + t)).cost = 10 := fun t ht => by
    rw [show e + 1 + pre j + t = e + (1 + pre j + t) by ring,
      cinstrAt_blk hj hdig (by omega) (by omega), blockOp_chain ht]
    exact chainOp_straight _ _ _
  have hpo : ∀ i < post j, (cinstrAt (e + 1 + pre j + s + i)).straight = true ∧
      (cinstrAt (e + 1 + pre j + s + i)).cost = 1 := fun i hi => by
    rw [show e + 1 + pre j + s + i = e + (1 + pre j + s + i) by ring,
      cinstrAt_blk hj hdig (by omega) (by omega)]
    exact blockOp_post hi
  have hb := blk_lt hj hdig
  obtain ⟨hR1, n2, c2, rfl, rfl, hw2⟩ := walk_seg hpre (by unfold sentinel; omega) hw1
  obtain ⟨hR2, n3, c3, rfl, rfl, hw3⟩ := walk_seg hch (by unfold sentinel; omega) hw2
  obtain ⟨hR3, n4, c4, rfl, rfl, hw4⟩ := walk_seg hpo (by unfold sentinel; omega) hw3
  have hctl : cinstrAt (e + 1 + pre j + s + post j) = if j < 41 then .dispatch (j + 1) else .exit := by
    rw [show e + 1 + pre j + s + post j = e + (1 + pre j + s + post j) by ring,
      cinstrAt_blk hj hdig (by omega) le_rfl, blockOp_ctl hj]
  have hfacts : ∀ i, 0 < i → i ≤ 1 + pre j + s + post j → i < 1 + pre j + s + post j →
      R (e + i) := fun i hi0 hi1 hi2 => by
    by_cases a : i < 1 + pre j
    · have := hR1 (i - 1) (by omega); rwa [show e + 1 + (i - 1) = e + i by omega] at this
    by_cases b : i < 1 + pre j + s
    · have := hR2 (i - 1 - pre j) (by omega)
      rwa [show e + 1 + pre j + (i - 1 - pre j) = e + i by omega] at this
    · have := hR3 (i - 1 - pre j - s) (by omega)
      rwa [show e + 1 + pre j + s + (i - 1 - pre j - s) = e + i by omega] at this
  by_cases h41 : j < 41
  · rw [if_pos h41] at hctl ⊢
    refine ⟨hRd, hdig, hHv, fun i hi0 hi1 => ?_, n4, c4, ?_, ?_, ?_⟩
    · by_cases hi : i < 1 + pre j + s + post j
      · exact hfacts i hi0 hi1 hi
      · obtain rfl : i = 1 + pre j + s + post j := by omega
        have hw4' := hw4
        rw [show e + 1 + pre j + s + post j = e + (1 + pre j + s + post j) by ring] at hw4'
        exact (hw4'.inv (by unfold sentinel; omega)).2.1
    · unfold segSteps pre post; split_ifs <;> omega
    · unfold segCost pre post; split_ifs <;> omega
    · unfold ctlAfter; exact hw4
  · obtain rfl : j = 41 := by omega
    rw [if_neg h41] at hctl ⊢
    have hne : e + 1 + pre 41 + s + post 41 ≠ sentinel := by unfold sentinel; omega
    obtain ⟨-, hRx, n5, c5, rfl, rfl, hw5⟩ := hw4.inv hne
    have hnext : nextSlot v (e + 1 + pre 41 + s + post 41) = rootSlot := by
      unfold nextSlot; rw [hctl]
      show slotOf _ = _
      rw [hk0, k0V, limb_ofK_zero, slotOf_gpow (by unfold rootSlot; omega)]
    rw [hnext] at hw5
    refine ⟨hRd, hdig, hHv, fun i hi0 hi1 => ?_, n5, c5, ?_, ?_, hw5⟩
    · by_cases hi : i < 1 + pre 41 + s + post 41
      · exact hfacts i hi0 hi1 hi
      · obtain rfl : i = 1 + pre 41 + s + post 41 := by omega
        rwa [show e + (1 + pre 41 + s + post 41) = e + 1 + pre 41 + s + post 41 by ring]
    · rw [hctl]; unfold segSteps pre post; simp [CInstr.steps]; omega
    · rw [hctl]; unfold segCost pre post; simp [CInstr.cost]; omega

end Chains

/-! ## The full path -/

/-- Steps of the whole path. -/
def totalSteps (s : ℕ → ℕ) : ℕ := 57 + ∑ k ∈ Finset.range 42, segSteps k (s k) + 11

/-- Cycles of the whole path. -/
def totalCost (s : ℕ → ℕ) : ℕ := 66 + ∑ k ∈ Finset.range 42, segCost k (s k) + 101

theorem prologue_cost : ∑ i ∈ Finset.range 57, proW i = 66 := by decide

theorem root_cost : ∑ i ∈ Finset.range 11, rootW i = 101 := by decide

section Full0

variable {R : ℕ → Prop} {v : ℕ → E}

/-- A straight segment of non-uniform costs. -/
theorem walk_seg' {a t : ℕ} (w : ℕ → ℕ) (hst : ∀ i < a, (cinstrAt (t + i)).straight = true ∧
    (cinstrAt (t + i)).cost = w i) (hta : t + a ≤ sentinel) :
    ∀ {n c : ℕ}, Walk R v n t c → (∀ i < a, R (t + i)) ∧
      ∃ n' c', n = n' + a ∧ c = (∑ i ∈ Finset.range a, w i) + c' ∧ Walk R v n' (t + a) c' := by
  induction a generalizing t w with
  | zero => intro n c h; exact ⟨fun i hi => absurd hi (by omega), n, c, rfl, by simp, h⟩
  | succ a ih =>
    intro n c h
    obtain ⟨hs1, hc1⟩ := hst 0 (by omega)
    rw [Nat.add_zero] at hs1 hc1
    obtain ⟨-, hR0, n1, c1, rfl, rfl, hw⟩ := h.inv (by omega)
    rw [nextSlot_straight v hs1] at hw
    have hst' : ∀ i < a, (cinstrAt (t + 1 + i)).straight = true ∧
        (cinstrAt (t + 1 + i)).cost = w (i + 1) := fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact hst (i + 1) (by omega)
    obtain ⟨hRs, n2, c2, rfl, rfl, hw2⟩ := ih (fun i => w (i + 1)) hst' (by omega) hw
    refine ⟨fun i hi => ?_, n2, c2, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rwa [Nat.add_zero]
      · have := hRs (i - 1) (by omega)
        rwa [show t + 1 + (i - 1) = t + i by omega] at this
    · rw [straight_steps hs1]; ring
    · rw [hc1, Finset.sum_range_succ']; ring
    · rwa [show t + 1 + a = t + (a + 1) by omega] at hw2

end Full0

section Full

variable {R : ℕ → Prop} {v : ℕ → E} (hR : ∀ t, R t → (cinstrAt t).RelNH v)
include hR

/-- **The forced path.** Every walk from slot `0` is the path of the digit vector `digitOf v`,
with its exact step count and cost. -/
theorem walk_full {n c : ℕ} (h : Walk R v n 0 c) :
    Valid (digitOf v) ∧ PathFacts R (digitOf v) ∧ Landing v (digitOf v) ∧
      n = totalSteps (digitOf v) ∧ c = totalCost (digitOf v) := by
  -- the prologue
  obtain ⟨hRp, n0, c0, rfl, rfl, hw0⟩ := walk_seg' proW
    (fun i hi => by simpa using prologue_straight (t := i) hi) (by unfold sentinel; omega) h
  rw [Nat.zero_add] at hw0
  simp only [Nat.zero_add] at hRp
  have hg : v gCell = gV := by have := hR 4 (hRp 4 (by omega)); rwa [cinstrAt_set4] at this
  have hk0 : v k0Cell = k0V := by have := hR 5 (hRp 5 (by omega)); rwa [cinstrAt_set5] at this
  have hmul0 : v (h1Cell 0) = v (hCell 0) * v gCell := by
    have := hR 56 (hRp 56 (by omega)); rwa [cinstrAt_56] at this
  -- the chains, by induction
  have key : ∀ j ≤ 42, (∀ k < j, digitOf v k < W k ∧ v (hCell k) = ofK (gpow (entryOf k (digitOf v k))) ∧
      R (ctl (digitOf v) k) ∧ ∀ i, 0 < i → i ≤ 1 + pre k + digitOf v k + post k → R (entryOf k (digitOf v k) + i)) ∧
      ∃ n' c', n0 = n' + ∑ k ∈ Finset.range j, segSteps k (digitOf v k) ∧
        c0 = (∑ k ∈ Finset.range j, segCost k (digitOf v k)) + c' ∧
        Walk R v n' (if j < 42 then ctl (digitOf v) j else rootSlot) c' ∧
        (j < 42 → v (h1Cell j) = v (hCell j) * v gCell) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun k hk => absurd hk (by omega), n0, c0, by simp, by simp, ?_, fun _ => hmul0⟩
      rw [if_pos (by omega)]; unfold ctl; rwa [if_pos rfl]
    | succ j ih =>
      intro hj
      obtain ⟨hprev, n', c', hn, hc, hw, hm⟩ := ih (by omega)
      rw [if_pos (by omega)] at hw
      have hci := cinstrAt_ctl (s := digitOf v) (j := j) (by omega) (fun k hk => (hprev k hk).1)
      obtain ⟨hRd, hdig, hHv, hblk, n'', c'', rfl, rfl, hw'⟩ :=
        walk_chain hR (by omega) hci hg hk0 (hm (by omega)) hw
      refine ⟨fun k hk => ?_, n'', c'', ?_, ?_, ?_, fun hj' => ?_⟩
      · by_cases hkj : k < j
        · exact hprev k hkj
        · obtain rfl : k = j := by omega
          exact ⟨hdig, hHv, hRd, hblk⟩
      · rw [hn, Finset.sum_range_succ]; ring
      · rw [hc, Finset.sum_range_succ]; ring
      · by_cases h41 : j < 41
        · rw [if_pos h41] at hw'; rw [if_pos (by omega), ctl_succ]; exact hw'
        · rw [if_neg h41] at hw'; rw [if_neg (by omega)]; exact hw'
      · have hlast := hblk (1 + pre j + digitOf v j + post j - 1)
          (by unfold pre post; split_ifs <;> omega) (by omega)
        have := hR _ hlast
        rw [show entryOf j (digitOf v j) + (1 + pre j + digitOf v j + post j - 1) =
            entryOf j (digitOf v j) + (1 + pre j + digitOf v j + post j - 1) from rfl,
          cinstrAt_blk (by omega) hdig (by unfold pre post; split_ifs <;> omega) (by omega),
          blockOp_nextMul (by omega)] at this
        exact this
  have hk42 := key 42 (le_refl 42)
  obtain ⟨hall, n1, c1, hn1, hc1, hw1, -⟩ := hk42
  rw [if_neg (by omega)] at hw1
  -- the root
  obtain ⟨hRr, n2, c2, hn2, hc2, hw2⟩ := walk_seg' rootW
    (fun i hi => root_straight hi) (by unfold rootSlot sentinel; omega) hw1
  rw [show rootSlot + 11 = sentinel from rfl] at hw2
  obtain ⟨h0n, h0c⟩ := hw2.at_sentinel
  refine ⟨fun k hk => (hall k hk).1, ⟨fun t ht => ?_, fun k hk => (hall k hk).2.2.2, hRr⟩,
    fun k hk => (hall k hk).2.1, ?_, ?_⟩
  · by_cases h57 : t < 57
    · exact hRp t h57
    · obtain rfl : t = 57 := by omega
      have := (hall 0 (by omega)).2.2.1
      unfold ctl at this; rwa [if_pos rfl] at this
  · unfold totalSteps; omega
  · rw [root_cost] at hc2; rw [prologue_cost]; unfold totalCost; omega

end Full

/-! ## Assembling a walk (the honest direction) -/

section Mk

variable {R : ℕ → Prop} {v : ℕ → E}

/-- A straight segment whose relations hold extends a walk backwards. -/
theorem walk_seg_ex {a t : ℕ} (hst : ∀ i < a, (cinstrAt (t + i)).straight = true)
    (hR : ∀ i < a, R (t + i)) (hta : t + a ≤ sentinel)
    (h : ∃ n c, Walk R v n (t + a) c) : ∃ n c, Walk R v n t c := by
  induction a generalizing t with
  | zero => simpa using h
  | succ a ih =>
    have h1 := ih (t := t + 1) (fun i hi => by
        rw [show t + 1 + i = t + (i + 1) by omega]; exact hst (i + 1) (by omega))
      (fun i hi => by rw [show t + 1 + i = t + (i + 1) by omega]; exact hR (i + 1) (by omega))
      (by omega) (by rwa [show t + 1 + a = t + (a + 1) by omega])
    obtain ⟨n, c, hw⟩ := h1
    have hs0 : (cinstrAt t).straight = true := by simpa using hst 0 (by omega)
    rw [← nextSlot_straight v hs0] at hw
    exact ⟨_, _, Walk.step (by omega) (by simpa using hR 0 (by omega)) hw⟩

/-- One chain segment, assembled backwards from its successor. -/
theorem chain_mk {s : ℕ → ℕ} {k : ℕ} (hk : k < 42) (hs : ∀ j ≤ k, s j < W j)
    (hblk : ∀ i, 0 < i → i ≤ 1 + pre k + s k + post k → R (entryOf k (s k) + i))
    (hRd : R (ctl s k)) (hH1 : v (h1Cell k) = ofK (gpow (entryOf k (s k) + 1)))
    (hk0 : v k0Cell = k0V)
    (h : ∃ n c, Walk R v n (if k < 41 then ctlAfter k (s k) else rootSlot) c) :
    ∃ n c, Walk R v n (ctl s k) c := by
  have hsk := hs k le_rfl
  set e := entryOf k (s k) with he
  have hlt := entryOf_lt hk hsk
  have hb := blk_lt hk hsk
  -- the control slot after the block
  have hctl : ∃ n c, Walk R v n (e + 1 + pre k + s k + post k) c := by
    by_cases h41 : k < 41
    · rw [if_pos h41] at h; exact h
    · obtain rfl : k = 41 := by omega
      rw [if_neg h41] at h
      obtain ⟨n, c, hw⟩ := h
      have hci : cinstrAt (e + 1 + pre 41 + s 41 + post 41) = .exit := by
        rw [show e + 1 + pre 41 + s 41 + post 41 = e + (1 + pre 41 + s 41 + post 41) by ring,
          cinstrAt_blk hk hsk (by omega) le_rfl, blockOp_ctl_exit]
      have hnext : nextSlot v (e + 1 + pre 41 + s 41 + post 41) = rootSlot := by
        unfold nextSlot; rw [hci]
        show slotOf _ = _
        rw [hk0, k0V, limb_ofK_zero, slotOf_gpow (by unfold rootSlot; omega)]
      rw [← hnext] at hw
      have hR' := hblk (1 + pre 41 + s 41 + post 41) (by omega) le_rfl
      rw [show e + (1 + pre 41 + s 41 + post 41) = e + 1 + pre 41 + s 41 + post 41 by ring] at hR'
      exact ⟨_, _, Walk.step (by unfold sentinel; omega) hR' hw⟩
  -- the post, chain and pre segments
  have h3 := walk_seg_ex (t := e + 1 + pre k + s k) (a := post k)
    (fun i hi => by
      rw [show e + 1 + pre k + s k + i = e + (1 + pre k + s k + i) by ring,
        cinstrAt_blk hk hsk (by omega) (by omega)]
      exact (blockOp_post hi).1)
    (fun i hi => by
      have := hblk (1 + pre k + s k + i) (by omega) (by omega)
      rwa [show e + (1 + pre k + s k + i) = e + 1 + pre k + s k + i by ring] at this)
    (by unfold sentinel; omega) hctl
  have h2 := walk_seg_ex (t := e + 1 + pre k) (a := s k)
    (fun i hi => by
      rw [show e + 1 + pre k + i = e + (1 + pre k + i) by ring,
        cinstrAt_blk hk hsk (by omega) (by omega), blockOp_chain hi]
      exact (chainOp_straight _ _ _).1)
    (fun i hi => by
      have := hblk (1 + pre k + i) (by omega) (by omega)
      rwa [show e + (1 + pre k + i) = e + 1 + pre k + i by ring] at this)
    (by unfold sentinel; omega) h3
  have h1 := walk_seg_ex (t := e + 1) (a := pre k)
    (fun i hi => by
      rw [Nat.add_assoc, cinstrAt_blk hk hsk (by omega) (by omega)]
      exact (blockOp_pre hi).1)
    (fun i hi => by
      have := hblk (1 + i) (by omega) (by omega)
      rwa [← Nat.add_assoc] at this)
    (by unfold sentinel; omega) h2
  -- the dispatch
  obtain ⟨n, c, hw⟩ := h1
  have hci := cinstrAt_ctl (s := s) (j := k) hk (fun j hj => hs j (by omega))
  have hnext : nextSlot v (ctl s k) = e + 1 := by
    unfold nextSlot; rw [hci]
    show slotOf _ = _
    rw [hH1, limb_ofK_zero, slotOf_gpow (by omega)]
  have hctlk : ctl s k < sentinel := by
    unfold ctl ctlAfter
    split_ifs
    · unfold sentinel; omega
    · have := entryOf_lt (k := k - 1) (s := s (k - 1)) (by omega) (hs (k - 1) (by omega))
      have := blk_lt (k := k - 1) (s := s (k - 1)) (by omega) (hs (k - 1) (by omega))
      unfold sentinel; omega
  rw [← hnext] at hw
  exact ⟨_, _, Walk.step hctlk hRd hw⟩

/-- **Assembling the forced path.** The relations along the path of `s`, with its return
hints and `K0`, give a walk from slot `0`. -/
theorem walk_mk {s : ℕ → ℕ} (hV : Valid s) (hP : PathFacts R s)
    (hH1 : ∀ k < 42, v (h1Cell k) = ofK (gpow (entryOf k (s k) + 1)))
    (hk0 : v k0Cell = k0V) : ∃ n c, Walk R v n 0 c := by
  -- the root
  have hroot : ∃ n c, Walk R v n rootSlot c :=
    walk_seg_ex (a := 11) (fun i hi => (root_straight hi).1) hP.root
      (by unfold rootSlot sentinel; omega) ⟨0, 0, Walk.done⟩
  -- the chains, backwards
  have key : ∀ d ≤ 42, ∃ n c, Walk R v n (if 42 - d < 42 then ctl s (42 - d) else rootSlot) c := by
    intro d
    induction d with
    | zero => intro _; simpa using hroot
    | succ d ih =>
      intro hd
      obtain ⟨n, c, hw⟩ := ih (by omega)
      rw [if_pos (by omega)]
      have hk : 42 - (d + 1) < 42 := by omega
      refine chain_mk hk (fun j _ => hV j (by omega)) (hP.blk _ hk) ?_ (hH1 _ hk) hk0 ?_
      · rcases Nat.eq_zero_or_pos (42 - (d + 1)) with h0 | h0
        · rw [h0]; unfold ctl; rw [if_pos rfl]; exact hP.pro 57 (by omega)
        · obtain ⟨j, hj⟩ : ∃ j, 42 - (d + 1) = j + 1 := ⟨42 - (d + 1) - 1, by omega⟩
          rw [hj, ctl_succ]
          have := hP.blk j (by omega) (1 + pre j + s j + post j) (by omega) le_rfl
          rwa [show entryOf j (s j) + (1 + pre j + s j + post j) = ctlAfter j (s j) by
            unfold ctlAfter; ring] at this
      · by_cases h41 : 42 - (d + 1) < 41
        · rw [if_pos h41]
          have hd' : 42 - d = 42 - (d + 1) + 1 := by omega
          rw [hd', if_pos (by omega), ctl_succ] at hw
          exact ⟨n, c, hw⟩
        · rw [if_neg h41]
          rw [show 42 - d = 42 by omega, if_neg (by omega)] at hw
          exact ⟨n, c, hw⟩
  obtain ⟨n, c, hw⟩ := key 42 le_rfl
  rw [if_pos (by omega), show 42 - 42 = 0 from rfl] at hw
  unfold ctl at hw
  rw [if_pos rfl] at hw
  -- the prologue
  have := walk_seg_ex (t := 0) (a := 57) (fun i hi => (prologue_straight (t := 0 + i) (by omega)).1)
    (fun i hi => hP.pro _ (by omega)) (by unfold sentinel; omega) ⟨n, c, hw⟩
  exact this

end Mk

/-! ## The pinned constants of a completing run -/

section Prefix

variable {κ : ℕ} {L : MemImage κ}

/-- The relations of a straight prefix of a completing run. -/
theorem rel_prefix (Sm : Sem) (B : BlakeRel)
    (hst : ∀ s pc x, (cinstrAt s).straight = true →
      x ∈ Sm.S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt s).toInstr) →
        x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt s).RelB B (Lx L))) :
    ∀ a t n c, (∀ i < a, (cinstrAt (t + i)).straight = true) → t + a < sentinel →
      some c ∈ Sm.S (LeanIsa.runCost program L n ⟨gpow t, 1⟩) →
        ∀ i < a, (cinstrAt (t + i)).RelB B (Lx L) := by
  intro a
  induction a with
  | zero => intro t n c _ _ _ i hi; omega
  | succ a ih =>
    intro t n c hstr hta h i hi
    cases n with
    | zero => rw [runCost_zero_slot L (by omega)] at h; exact absurd h Sm.some_not_pure_none
    | succ m =>
      have hs0 : (cinstrAt t).straight = true := by simpa using hstr 0 (by omega)
      rw [runCost_slot L m (by omega), Sm.bind_iff] at h
      obtain ⟨x, hx, hc⟩ := h
      rcases hst t _ x hs0 hx with rfl | ⟨rfl, hrel⟩
      · exact absurd hc Sm.some_not_pure_none
      · rw [Option.elim_some, g_mul_gpow] at hc
        obtain ⟨c', -, hc'⟩ := Sm.some_map_add hc
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · simpa using hrel
        · have := ih (t + 1) m c' (fun j hj => by
            rw [show t + 1 + j = t + (j + 1) by omega]; exact hstr (j + 1) (by omega))
            (by omega) hc' (i - 1) (by omega)
          rwa [show t + 1 + (i - 1) = t + i by omega] at this

/-- A completing run from slot `0` has the constants `ONE` and `F_k` pinned. -/
theorem pinned_of_sem (Sm : Sem) (B : BlakeRel)
    (hst : ∀ s pc x, (cinstrAt s).straight = true →
      x ∈ Sm.S (LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt s).toInstr) →
        x = none ∨ (x = some ⟨g * pc, 1⟩ ∧ (cinstrAt s).RelB B (Lx L)))
    {n c : ℕ} (h : some c ∈ Sm.S (LeanIsa.runCost program L n ⟨gpow 0, 1⟩)) : Pinned (Lx L) := by
  have hp := rel_prefix Sm B hst 57 0 n c
    (fun i hi => (prologue_straight (t := 0 + i) (by omega)).1) (by unfold sentinel; omega) h
  refine ⟨?_, fun k hk => ?_⟩
  · have := hp 1 (by omega); rwa [Nat.zero_add, cinstrAt_set1] at this
  · have := hp (13 + k) (by omega); rwa [Nat.zero_add, cinstrAt_frame hk] at this

end Prefix

end

end OptimalOTS.HLFlat
