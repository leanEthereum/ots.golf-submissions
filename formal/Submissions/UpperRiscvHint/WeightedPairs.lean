import Mathlib

/-! A finite pair encoding with the executed decoder overhead included in its rank.

Pairs 0–5 (both chains caps) use a second alphabet: when the right chain hashes zero times its
pointer pair is skipped. Their rank is shifted by one so that it stays a natural number:
`pairWeight true x 0 = x + [16 ≤ x]` and `pairWeight true x y = φ x + φ y + 1` for `y ≠ 0`.
These are construction lemmas; they are not a complete OTS certificate. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace WeightedPairs

abbrev Pair := Fin 16 × Fin 16

/-- The recoding of the normal pairs 6–15 (unchanged from the 312). -/
def swaps : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  [((9,15),(0,16)), ((10,14),(0,17)), ((10,15),(0,18)),
   ((11,13),(0,19)), ((11,14),(0,20)), ((11,15),(1,16)),
   ((12,12),(1,17)), ((12,13),(1,18)), ((12,14),(1,19)), ((12,15),(2,16)),
   ((13,11),(2,17)), ((13,12),(2,18)), ((13,13),(3,16)),
   ((13,14),(3,17)), ((13,15),(4,16)),
   ((14,9),(16,0)), ((14,10),(16,1)), ((14,11),(16,2)),
   ((14,12),(16,3)), ((14,13),(16,4)), ((14,14),(17,0)), ((14,15),(17,1)),
   ((15,8),(17,2)), ((15,9),(17,3)), ((15,10),(18,0)), ((15,11),(18,1)),
   ((15,12),(18,2)), ((15,13),(19,0)), ((15,14),(19,1)), ((15,15),(20,0))]

/-- The recoding of the cap pairs 0–5: the 256 cheapest points under the skip-aware weight. -/
def capSwaps : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  [((9,15),(0,16)), ((10,14),(0,17)), ((10,15),(0,18)), ((11,13),(0,19)), ((11,14),(0,20)),
   ((11,15),(1,16)), ((12,11),(1,17)), ((12,12),(1,18)), ((12,13),(1,19)), ((12,14),(2,16)),
   ((12,15),(2,17)), ((13,10),(2,18)), ((13,11),(3,16)), ((13,12),(3,17)), ((13,13),(4,16)),
   ((13,14),(16,0)), ((13,15),(16,1)), ((14,9),(16,2)), ((14,10),(16,3)), ((14,11),(16,4)),
   ((14,12),(17,0)), ((14,13),(17,1)), ((14,14),(17,2)), ((14,15),(17,3)), ((15,8),(18,0)),
   ((15,9),(18,1)), ((15,10),(18,2)), ((15,11),(19,0)), ((15,12),(19,1)), ((15,13),(20,0)),
   ((15,14),(21,0)), ((15,15),(22,0))]

/-- The recoding table of a cap pair (`true`) or a normal pair (`false`). -/
def swapsOf (c : Bool) : List ((ℕ × ℕ) × (ℕ × ℕ)) := if c then capSwaps else swaps

def raw (p : Pair) : ℕ × ℕ := (p.1.val, p.2.val)

def recode (c : Bool) (p : Pair) : ℕ × ℕ :=
  (((swapsOf c).find? fun e => e.1 == raw p).map Prod.snd).getD (raw p)

def unrecode (c : Bool) (p : ℕ × ℕ) : ℕ × ℕ :=
  (((swapsOf c).find? fun e => e.2 == p).map Prod.fst).getD p

theorem unrecode_recode : ∀ c : Bool, ∀ p : Pair, unrecode c (recode c p) = raw p := by
  decide +kernel

theorem recode_injective (c : Bool) : Function.Injective (recode c) := by
  intro p q h
  have e := congrArg (unrecode c) h
  rw [unrecode_recode, unrecode_recode] at e
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst e)
  · exact Fin.ext (congrArg Prod.snd e)

def digitWeight (d : ℕ) : ℕ := d + if 16 ≤ d then 2 else 0

/-- The shifted rank of a recoded pair: cycles of the pair, less a per-kind constant. A cap
pair whose right digit is 0 skips its pointer pair. -/
def pairWeight (c : Bool) (x y : ℕ) : ℕ :=
  if c then (if y = 0 then x + (if 16 ≤ x then 1 else 0) else digitWeight x + digitWeight y + 1)
  else digitWeight x + digitWeight y

def weight (c : Bool) (p : Pair) : ℕ := pairWeight c (recode c p).1 (recode c p).2

def helper (c : Bool) (p : Pair) : ℕ := if recode c p = raw p then 0 else 1

/-- The right chain of a cap pair hashes zero times: its pointer pair is skipped. -/
def skip (c : Bool) (p : Pair) : ℕ := if c = true ∧ (recode c p).2 = 0 then 1 else 0

/-- Instructions the skip removes: the pointer pair, less the checksum `ADDI` that a
non-redirected skip row adds (a redirect already carries one). -/
def skipSave (c : Bool) (p : Pair) : ℕ := skip c p * (1 + helper c p)

theorem recode_bounds : ∀ c : Bool, ∀ p : Pair, (recode c p).1 ≤ 22 ∧ (recode c p).2 ≤ 20 := by
  decide +kernel

theorem weight_le : ∀ c : Bool, ∀ p : Pair, weight c p ≤ 24 := by decide +kernel

theorem weight_le_normal : ∀ p : Pair, weight false p ≤ 23 := by decide +kernel

/-- The checksum sees the raw pair; every correction `raw + [cap] - weight` is nonnegative. -/
theorem weight_le_raw : ∀ c : Bool, ∀ p : Pair,
    weight c p ≤ p.1.val + p.2.val + (if c then 1 else 0) := by decide +kernel

/-- An unredirected, unskipped pair needs no correction. -/
theorem weight_plain : ∀ c : Bool, ∀ p : Pair, helper c p = 0 → skip c p = 0 →
    weight c p = p.1.val + p.2.val + (if c then 1 else 0) := by decide +kernel

/-- The rank is the executed cost: hashes, the redirect fee, and the skip saving. -/
theorem decoder_cost_exact : ∀ c : Bool, ∀ p : Pair,
    weight c p + skipSave c p =
      (recode c p).1 + (recode c p).2 + 2 * helper c p + (if c then 1 else 0) := by
  decide +kernel

/-- A skip saves at most the cap offset plus the redirect fee it replaces. -/
theorem skipSave_le : ∀ c : Bool, ∀ p : Pair,
    skipSave c p ≤ (if c then 1 else 0) + helper c p := by decide +kernel

theorem skip_le : ∀ c : Bool, ∀ p : Pair, skip c p ≤ 1 := by decide +kernel

theorem skip_false : ∀ p : Pair, skip false p = 0 := by decide +kernel

theorem digitWeight_strictMono : StrictMono digitWeight := by
  intro a b hab
  unfold digitWeight
  split_ifs <;> omega

/-- Each pair weight is strictly increasing in the product order. -/
theorem pairWeight_lt (c : Bool) {x y x' y' : ℕ} (hx : x ≤ x') (hy : y ≤ y')
    (hne : x < x' ∨ y < y') : pairWeight c x y < pairWeight c x' y' := by
  unfold pairWeight digitWeight
  cases c <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split_ifs <;> omega

theorem pairWeight_le (c : Bool) {x y x' y' : ℕ} (hx : x ≤ x') (hy : y ≤ y') :
    pairWeight c x y ≤ pairWeight c x' y' := by
  rcases Nat.eq_or_lt_of_le hx with rfl | h
  · rcases Nat.eq_or_lt_of_le hy with rfl | h'
    · exact le_rfl
    · exact (pairWeight_lt c hx hy (Or.inr h')).le
  · exact (pairWeight_lt c hx hy (Or.inl h)).le

/-- Pairs 0–5 are cap pairs. -/
def capPos (q : ℕ) : Bool := decide (q < 6)

/-- The rank of 33 chain digits: the free digit, plus the weight of each of the sixteen pairs
of chains `2q+1, 2q+2`. -/
def rank (d : Fin 33 → ℕ) : ℕ :=
  d 0 + ∑ q : Fin 16, pairWeight (capPos q.val) (d ⟨2*q.val+1, by omega⟩) (d ⟨2*q.val+2, by omega⟩)

theorem rank_lt {a b : Fin 33 → ℕ} (hle : ∀ k, a k ≤ b k) (hne : a ≠ b) : rank a < rank b := by
  have hex : ∃ k, a k < b k := by
    by_contra h
    push Not at h
    exact hne (funext fun k => Nat.le_antisymm (hle k) (h k))
  obtain ⟨k, hk⟩ := hex
  unfold rank
  by_cases h0 : k.val = 0
  · have hk0 : k = 0 := Fin.ext h0
    subst hk0
    have hs := Finset.sum_le_sum fun (q : Fin 16) (_ : q ∈ Finset.univ) =>
      pairWeight_le (capPos q.val) (hle ⟨2*q.val+1, by omega⟩) (hle ⟨2*q.val+2, by omega⟩)
    omega
  · have hq : (k.val-1)/2 < 16 := by omega
    let q : Fin 16 := ⟨(k.val-1)/2, hq⟩
    have hs : ∑ q : Fin 16, pairWeight (capPos q.val) (a ⟨2*q.val+1, by omega⟩)
          (a ⟨2*q.val+2, by omega⟩) <
        ∑ q : Fin 16, pairWeight (capPos q.val) (b ⟨2*q.val+1, by omega⟩)
          (b ⟨2*q.val+2, by omega⟩) := by
      apply Finset.sum_lt_sum
        (fun j _ => pairWeight_le (capPos j.val) (hle ⟨2*j.val+1, by omega⟩) (hle ⟨2*j.val+2, by omega⟩))
      refine ⟨q, Finset.mem_univ _, pairWeight_lt _ (hle _) (hle _) ?_⟩
      by_cases hodd : (k.val-1) % 2 = 0
      · left
        have e : (⟨2*q.val+1, by omega⟩ : Fin 33) = k := Fin.ext (by simp only [q]; omega)
        rw [e]; exact hk
      · right
        have e : (⟨2*q.val+2, by omega⟩ : Fin 33) = k := Fin.ext (by simp only [q]; omega)
        rw [e]; exact hk
    have h0' := hle 0
    omega

/-- Equal rank rules out componentwise movement in either direction. -/
theorem equal_rank_crossing {a b : Fin 33 → ℕ}
    (hr : rank a = rank b) (hne : a ≠ b) : ∃ k, a k < b k := by
  by_contra h
  push Not at h
  have := rank_lt h (Ne.symm hne)
  omega

/-- Cap alphabet weight histogram, weights 0 through 24. -/
def capMultiplicity (s : ℕ) : ℕ :=
  [1,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,15,16,15,15,16,17,18,19,4].getD s 0

/-- Normal alphabet weight histogram, weights 0 through 23. -/
def normalMultiplicity (s : ℕ) : ℕ :=
  [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,15,14,15,16,17,18,19,6].getD s 0

def multiplicity (c : Bool) (s : ℕ) : ℕ := if c then capMultiplicity s else normalMultiplicity s

theorem multiplicity_eq : ∀ c : Bool, ∀ s : Fin 25,
    ((Finset.univ : Finset Pair).filter (fun p => weight c p = s.val)).card =
      multiplicity c s.val := by
  decide +kernel

theorem sum_weight (c : Bool) (f : ℕ → ℕ) :
    (∑ p : Pair, f (weight c p)) = ∑ s ∈ Finset.range 25, multiplicity c s * f s := by
  have regroup := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset Pair)) (t := Finset.range 25)
    (g := weight c) (f := fun p => f (weight c p))
    (fun p _ => Finset.mem_range.mpr (by have := weight_le c p; omega))
  rw [← regroup]
  refine Finset.sum_congr rfl fun s hs => ?_
  have eqf : ∀ p ∈ Finset.univ.filter (fun p : Pair => weight c p = s),
      f (weight c p) = f s := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl eqf, Finset.sum_const, nsmul_eq_mul,
    multiplicity_eq c ⟨s, Finset.mem_range.mp hs⟩]
  rfl

/-- Tuples of `n` pairs, pair `q` of kind `capPos q`, of total weight `s`. -/
def tuples (n s : ℕ) : Finset (Fin n → Pair) :=
  Finset.univ.filter fun c => ∑ q, weight (capPos q.val) (c q) = s

def count : ℕ → ℕ → ℕ
  | 0, s => if s = 0 then 1 else 0
  | n+1, s => ∑ v ∈ Finset.range 25,
      multiplicity (capPos n) v * if v ≤ s then count n (s-v) else 0

theorem tuples_card (n s : ℕ) : (tuples n s).card = count n s := by
  induction n generalizing s with
  | zero =>
    by_cases hs : s = 0
    · subst s; simp [tuples, count]
    · simp [tuples, count, hs, Ne.symm hs]
  | succ n ih =>
    rw [count, ← sum_weight]
    simp only [tuples, Finset.card_filter] at ih ⊢
    rw [← (Fin.snocEquiv fun _ : Fin (n+1) => Pair).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.snocEquiv_apply, Fin.sum_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
    split_ifs with hp
    · rw [← ih]
      refine Finset.sum_congr rfl fun c _ => ?_
      apply if_congr _ rfl rfl
      omega
    · refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      omega

theorem sum_map_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ v ∈ Finset.range m, f v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

def table (S : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate S 0
  | n+1 =>
    let previous := table S n
    (List.range (S+1)).map fun s =>
      ((List.range 25).map fun v => multiplicity (capPos n) v *
        if v ≤ s then previous.getD (s-v) 0 else 0).sum

theorem table_getD (S n s : ℕ) (hs : s ≤ S) : (table S n).getD s 0 = count n s := by
  induction n generalizing s with
  | zero =>
    rw [table, count]
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_replicate, Nat.succ_ne_zero, if_false]
      split_ifs <;> rfl
  | succ n ih =>
    rw [table, count, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some,
      sum_map_range]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with hv
    · rw [ih (s-v) (by omega)]
    · rfl

theorem window_count :
    ∑ s ∈ Finset.range 19, count 16 (129+s) = 29392495299674139897463880312407816 := by
  rw [Finset.sum_congr rfl fun s hs =>
    (table_getD 147 16 (129+s) (by rw [Finset.mem_range] at hs; omega)).symm,
    ← sum_map_range]
  decide +kernel

def accepted : Finset (Fin 16 → Pair) :=
  Finset.univ.filter fun p =>
    129 ≤ ∑ q, weight (capPos q.val) (p q) ∧ ∑ q, weight (capPos q.val) (p q) ≤ 147

attribute [local irreducible] accepted tuples

theorem card_accepted : accepted.card = 29392495299674139897463880312407816 := by
  rw [← window_count]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p => (∑ q, weight (capPos q.val) (p q))-129) (t := Finset.range 19)]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [← tuples_card]
    apply congrArg Finset.card
    ext p
    simp only [accepted, tuples, Finset.mem_filter, Finset.mem_univ, true_and]
    have h := Finset.mem_range.mp hs
    omega
  · intro p hp
    simp only [accepted, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    apply Finset.mem_range.mpr
    change (∑ q, weight (capPos q.val) (p q)) - 129 < 19
    omega

theorem availability_count : 89*2^108 ≤ accepted.card := by
  rw [card_accepted]
  norm_num

/-- Maximum rank `6 · 24 + 10 · 23 = 374`, so a free count of at most 18 never reaches the
next residue `147 + 257`. -/
theorem modulus_alias_excluded {s c : ℕ} (hs : s ≤ 374) (hc : c ≤ 18) :
    (s+c)%257 = 147 ↔ s+c = 147 := by omega

end WeightedPairs
