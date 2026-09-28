import Submissions.UpperLeanIsa.SplitProfile

/-! Packed sparse certificates for the multiplicative convolution `compM`.

A cost row `s ↦ F s w` (costs `s < K`) is packed into the single natural number
`∑ s < K, F s w * B ^ s`. Scaling, shifting and adding rows is then one big-number
operation, and a sparse table is an association list `(weight, packed row)`.
Tables are combined by sorted merges of scattered copies, so the kernel never searches
a key list. The semantics `evalA` sums every entry with a matching key; it is additive
for every merge result, sorted or not, so no sortedness invariant is needed.
Digits stay below `B` by an a-priori bound, which makes truncation modulo `B ^ K` exact. -/

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitPack

open Finset

/-- Packing base. Every tuple count is below `2 ^ 127`, and window sums below `2 ^ 133`. -/
def B : ℕ := 2 ^ 134

theorem B_pos : 0 < B := Nat.two_pow_pos 134

theorem two_le_B : 2 ≤ B := by
  unfold B
  exact Nat.le_self_pow (by decide) 2

attribute [irreducible] B

/-- The first `K` costs of a row, packed in base `B`. -/
def pkK (K : ℕ) (e : ℕ → ℕ) : ℕ := ∑ s ∈ range K, e s * B ^ s

/-! ### Sparse association lists -/

/-- Sum of the values of all entries with key `w`. -/
def evalA (L : List (ℕ × ℕ)) (w : ℕ) : ℕ :=
  (L.map fun e => if e.1 = w then e.2 else 0).sum

theorem evalA_nil (w : ℕ) : evalA [] w = 0 := rfl

theorem evalA_cons (e : ℕ × ℕ) (L : List (ℕ × ℕ)) (w : ℕ) :
    evalA (e :: L) w = (if e.1 = w then e.2 else 0) + evalA L w := by
  simp [evalA]

theorem evalA_append (A C : List (ℕ × ℕ)) (w : ℕ) :
    evalA (A ++ C) w = evalA A w + evalA C w := by
  simp [evalA]

/-- Sorted merge with key-wise addition. The fuel only bounds the recursion;
when it runs out the lists are appended, which has the same semantics. -/
def mergeF : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, A, C => A ++ C
  | _ + 1, [], C => C
  | _ + 1, a :: A, [] => a :: A
  | n + 1, a :: A, c :: C =>
      if a.1 < c.1 then a :: mergeF n A (c :: C)
      else if c.1 < a.1 then c :: mergeF n (a :: A) C
      else (a.1, a.2 + c.2) :: mergeF n A C

theorem evalA_mergeF : ∀ (n : ℕ) (A C : List (ℕ × ℕ)) (w : ℕ),
    evalA (mergeF n A C) w = evalA A w + evalA C w
  | 0, A, C, w => by rw [mergeF, evalA_append]
  | _ + 1, [], C, w => by rw [mergeF, evalA_nil, Nat.zero_add]
  | _ + 1, a :: A, [], w => by rw [mergeF, evalA_nil, Nat.add_zero]
  | n + 1, a :: A, c :: C, w => by
    rw [mergeF]
    split_ifs with h1 h2
    · simp only [evalA_cons, evalA_mergeF n]
      omega
    · simp only [evalA_cons, evalA_mergeF n]
      omega
    · have he : a.1 = c.1 := by omega
      simp only [evalA_cons, evalA_mergeF n, he]
      split_ifs <;> omega

/-- Scatter a table to weights `k * m`, scaling every packed row by `q`. -/
def scat (m q : ℕ) (T : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  T.map fun e => (e.1 * m, q * e.2)

theorem evalA_scat {m : ℕ} (hm : 0 < m) (q : ℕ) (T : List (ℕ × ℕ)) (w : ℕ) :
    evalA (scat m q T) w = if m ∣ w then q * evalA T (w / m) else 0 := by
  induction T with
  | nil => split_ifs <;> rfl
  | cons e T ih =>
    rw [scat, List.map_cons, ← scat, evalA_cons, ih, evalA_cons]
    dsimp only
    by_cases hd : m ∣ w
    · have hiff : e.1 * m = w ↔ e.1 = w / m := by
        constructor
        · intro h
          rw [← h, Nat.mul_div_cancel _ hm]
        · intro h
          rw [h, Nat.div_mul_cancel hd]
      simp only [hd, if_true, hiff]
      split_ifs <;> ring
    · have hne : e.1 * m ≠ w := fun h => hd (h ▸ Dvd.intro_left _ rfl)
      simp [hd, hne]

/-- One grouped sparse step: scatter a copy of the table for every multiplicity group
`(m, q)` and merge the copies. -/
def stepG (gp : List (ℕ × ℕ)) (T : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  gp.foldr (fun y acc => mergeF 2048 (scat y.1 y.2 T) acc) []

/-- Semantic counterpart of `stepG`. -/
def applyG (gp : List (ℕ × ℕ)) (F : ℕ → ℕ) (w : ℕ) : ℕ :=
  (gp.map fun y => if y.1 ∣ w then y.2 * F (w / y.1) else 0).sum

theorem evalA_stepG (gp : List (ℕ × ℕ)) (hpos : ∀ y ∈ gp, 0 < y.1)
    (T : List (ℕ × ℕ)) (w : ℕ) : evalA (stepG gp T) w = applyG gp (evalA T) w := by
  induction gp with
  | nil => rfl
  | cons y gp ih =>
    rw [stepG, List.foldr_cons, ← stepG, evalA_mergeF,
      evalA_scat (hpos y List.mem_cons_self), ih (fun z hz => hpos z (List.mem_cons_of_mem _ hz))]
    simp [applyG]

/-- Reduce every packed row modulo `M`. -/
def modA (M : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) := L.map fun e => (e.1, e.2 % M)

theorem evalA_modA (M : ℕ) (L : List (ℕ × ℕ)) (w : ℕ) :
    evalA (modA M L) w % M = evalA L w % M := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [modA, List.map_cons, ← modA, evalA_cons, evalA_cons, Nat.add_mod, ih,
      ← Nat.add_mod]
    dsimp only
    split_ifs
    · rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    · rfl

/-- Applying a zero-preserving map to the values of a table with distinct keys. -/
theorem evalA_map_nodup (f : ℕ → ℕ) (hf : f 0 = 0) :
    ∀ (L : List (ℕ × ℕ)), (L.map Prod.fst).Nodup → ∀ w,
      evalA (L.map fun e => (e.1, f e.2)) w = f (evalA L w)
  | [], _, w => by simp [evalA, hf]
  | e :: L, hn, w => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.map_cons, evalA_cons, evalA_map_nodup f hf L hn.2, evalA_cons]
    dsimp only
    by_cases he : e.1 = w
    · have h0 : evalA L w = 0 := by
        unfold evalA
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        have hzk : z.1 ≠ w := fun h => hn.1 (he ▸ h ▸ List.mem_map_of_mem hz)
        simp [hzk]
      simp [he, h0, hf]
    · simp [he]

/-- Lookup form of `evalA` for a zipped table with distinct keys. -/
theorem evalA_zip : ∀ (K V : List ℕ), K.Nodup → V.length = K.length → ∀ w,
    evalA (K.zip V) w = V.getD (K.idxOf w) 0
  | [], [], _, _, w => rfl
  | [], _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, h, _ => absurd h (by simp)
  | k :: K, v :: V, hn, hl, w => by
    rw [List.nodup_cons] at hn
    rw [List.zip_cons_cons, evalA_cons, evalA_zip K V hn.2 (by simpa using hl), List.idxOf_cons]
    dsimp only
    by_cases hk : k = w
    · subst hk
      have hnot : k ∉ K := hn.1
      rw [List.getD_eq_default V 0 (by rw [List.idxOf_of_notMem hnot]; simp at hl; omega)]
      simp
    · have hb : (k == w) = false := by simpa using hk
      simp [hk, hb]

/-! ### Kernel-checkable strict sortedness -/

/-- Adjacent strict-order check. -/
def ltChain : List ℕ → Bool
  | a :: b :: l => Nat.blt a b && ltChain (b :: l)
  | _ => true

theorem pairwise_of_ltChain : ∀ (l : List ℕ), ltChain l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [ltChain, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := pairwise_of_ltChain (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem nodup_of_ltChain (l : List ℕ) (h : ltChain l = true) : l.Nodup :=
  (pairwise_of_ltChain l h).nodup

/-! ### Grouping a profile by multiplicity -/

/-- Packed coefficient of one profile entry: its raw count shifted by its cost. -/
def coefP (x : MProfile) : ℕ := x.2.2 * x.2.1 * B ^ x.1

/-- Semantic step of a profile on packed rows. -/
def applyP (p : List MProfile) (F : ℕ → ℕ) (w : ℕ) : ℕ :=
  (p.map fun x => if x.2.1 ∣ w then coefP x * F (w / x.2.1) else 0).sum

/-- The profile grouped by the multiplicities `ms`. -/
def groupP (p : List MProfile) (ms : List ℕ) : List (ℕ × ℕ) :=
  ms.map fun m => (m, (p.map fun x => if x.2.1 = m then coefP x else 0).sum)

theorem list_sum_comm {α β : Type} (A : List α) (C : List β) (g : α → β → ℕ) :
    (A.map fun a => (C.map (g a)).sum).sum = (C.map fun c => (A.map fun a => g a c).sum).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp [ih, List.sum_map_add]

theorem sum_ite_mem (ms : List ℕ) (hn : ms.Nodup) (k a : ℕ) :
    (ms.map fun m => if k = m then a else 0).sum = if k ∈ ms then a else 0 := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.sum_cons, ih hn.2]
    by_cases hk : k = m
    · subst hk
      simp [hn.1]
    · simp [hk]

theorem applyP_groupP (p : List MProfile) (ms : List ℕ) (hn : ms.Nodup)
    (hmem : ∀ x ∈ p, x.2.1 ∈ ms) (F : ℕ → ℕ) (w : ℕ) :
    applyP p F w = applyG (groupP p ms) F w := by
  unfold applyG groupP
  simp only [List.map_map, Function.comp_def]
  have h1 : ∀ m ∈ ms, (if m ∣ w then
      (p.map fun x => if x.2.1 = m then coefP x else 0).sum * F (w / m) else 0) =
      (p.map fun x => if x.2.1 = m then
        (if x.2.1 ∣ w then coefP x * F (w / x.2.1) else 0) else 0).sum := by
    intro m _
    split_ifs with hd
    · rw [← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro x _
      split_ifs with he <;> simp_all
    · symm
      apply List.sum_eq_zero
      intro y hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      split_ifs with he he2 <;> simp_all
  rw [List.map_congr_left h1, list_sum_comm]
  unfold applyP
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [sum_ite_mem ms hn, if_pos (hmem x hx)]

/-! ### Packed arithmetic -/

theorem pkK_lt (K : ℕ) (e : ℕ → ℕ) (h : ∀ t < K, e t < B) : pkK K e < B ^ K := by
  induction K with
  | zero => simp [pkK]
  | succ K ih =>
    rw [pkK, Finset.sum_range_succ, ← pkK, pow_succ]
    have h1 := ih (fun t ht => h t (by omega))
    have h2 : e K + 1 ≤ B := h K (by omega)
    have h3 : (e K + 1) * B ^ K ≤ B * B ^ K := Nat.mul_le_mul_right _ h2
    rw [Nat.mul_comm (B ^ K) B]
    nlinarith

/-- Multiplying a packed row by `B ^ c` shifts it by `c` costs, modulo `B ^ K`. -/
theorem shift_mod (K c : ℕ) (a : ℕ → ℕ) :
    (B ^ c * pkK K a) % B ^ K =
      pkK K (fun t => if c ≤ t then a (t - c) else 0) % B ^ K := by
  by_cases hc : c ≤ K
  · obtain ⟨d, rfl⟩ : ∃ d, K = c + d := ⟨K - c, by omega⟩
    have hr : pkK (c + d) (fun t => if c ≤ t then a (t - c) else 0) =
        ∑ j ∈ range d, a j * B ^ (c + j) := by
      rw [pkK, Finset.sum_range_add]
      have h0 : ∑ t ∈ range c, (if c ≤ t then a (t - c) else 0) * B ^ t = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        rw [if_neg (by simp at ht; omega), Nat.zero_mul]
      rw [h0, Nat.zero_add]
      apply Finset.sum_congr rfl
      intro j _
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
    have hl : B ^ c * pkK (c + d) a =
        ∑ j ∈ range d, a j * B ^ (c + j) +
          B ^ (c + d) * ∑ i ∈ range c, a (d + i) * B ^ i := by
      rw [pkK, Nat.add_comm c d, Finset.sum_range_add, Nat.mul_add, Finset.mul_sum,
        Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        rw [pow_add]
        ring
      · apply Finset.sum_congr rfl
        intro i _
        simp only [pow_add]
        ring
    rw [hl, hr, Nat.add_mul_mod_self_left]
  · have h0 : pkK K (fun t => if c ≤ t then a (t - c) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hn : ¬ c ≤ t := by simp at ht; omega
      simp [hn]
    obtain ⟨d, rfl⟩ : ∃ d, c = K + d := ⟨c - K, by omega⟩
    rw [h0, pow_add, Nat.mul_assoc, Nat.mul_mod_right, Nat.zero_mod]

theorem modEq_list_sum {α : Type} (M : ℕ) (L : List α) (f g : α → ℕ)
    (h : ∀ x ∈ L, f x % M = g x % M) : (L.map f).sum % M = (L.map g).sum % M := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, Nat.add_mod,
      h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy)), ← Nat.add_mod]

theorem sum_list_finset {α : Type} (p : List α) (I : Finset ℕ) (F : ℕ → α → ℕ) :
    ∑ s ∈ I, (p.map (F s)).sum = (p.map fun x => ∑ s ∈ I, F s x).sum := by
  induction p with
  | nil => simp
  | cons x xs ih => simp [Finset.sum_add_distrib, ih]

/-- The packed form of one convolution step, modulo `B ^ K`. -/
theorem applyP_mod (K : ℕ) (p : List MProfile) (F G : ℕ → ℕ → ℕ)
    (hG : ∀ s w, G s w = (p.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * F (s - x.1) (w / x.2.1) else 0).sum) (w : ℕ) :
    applyP p (fun v => pkK K (F · v)) w % B ^ K = pkK K (G · w) % B ^ K := by
  have hR : pkK K (G · w) = (p.map fun x => if x.2.1 ∣ w then x.2.2 * x.2.1 *
      pkK K (fun t => if x.1 ≤ t then F (t - x.1) (w / x.2.1) else 0) else 0).sum := by
    unfold pkK
    simp only [hG, ← List.sum_map_mul_right]
    rw [sum_list_finset]
    congr 1
    apply List.map_congr_left
    intro x _
    by_cases hd : x.2.1 ∣ w
    · simp only [hd, and_true, if_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> ring
    · simp [hd]
  rw [hR, applyP]
  apply modEq_list_sum
  intro x _
  by_cases hd : x.2.1 ∣ w
  · simp only [hd, if_true, coefP]
    rw [Nat.mul_assoc, Nat.mul_mod, shift_mod, ← Nat.mul_mod]
  · simp [hd]

/-! ### The stage invariant -/

/-- `T` represents the packed rows of `F` modulo `B ^ K`, including zero rows. -/
def Inv (K : ℕ) (F : ℕ → ℕ → ℕ) (T : List (ℕ × ℕ)) : Prop :=
  ∀ w, evalA T w % B ^ K = pkK K (F · w)

theorem inv_step (K : ℕ) (p : List MProfile) (ms : List ℕ) (hn : ms.Nodup)
    (hmem : ∀ x ∈ p, x.2.1 ∈ ms) (hpos : ∀ m ∈ ms, 0 < m) (F G : ℕ → ℕ → ℕ)
    (hG : ∀ s w, G s w = (p.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * F (s - x.1) (w / x.2.1) else 0).sum)
    (hB : ∀ s w, G s w < B) (T : List (ℕ × ℕ)) (hT : Inv K F T) (w : ℕ) :
    evalA (stepG (groupP p ms) T) w % B ^ K = pkK K (G · w) := by
  have hgpos : ∀ y ∈ groupP p ms, 0 < y.1 := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hy
    exact hpos m hm
  rw [evalA_stepG _ hgpos, ← applyP_groupP p ms hn hmem]
  have hc : applyP p (evalA T) w % B ^ K = applyP p (fun v => pkK K (F · v)) w % B ^ K := by
    unfold applyP
    apply modEq_list_sum
    intro x _
    split_ifs
    · dsimp only
      rw [← hT, Nat.mul_mod_mod]
    · rfl
  rw [hc, applyP_mod K p F G hG w, Nat.mod_eq_of_lt (pkK_lt K _ fun t _ => hB t w)]

/-! ### Digit bounds and window extraction -/

/-- Total raw count of a profile. -/
def tot (p : List MProfile) : ℕ := (p.map fun x => x.2.2 * x.2.1).sum

theorem bound_step (p : List MProfile) (F G : ℕ → ℕ → ℕ)
    (hG : ∀ s w, G s w = (p.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * F (s - x.1) (w / x.2.1) else 0).sum)
    (M : ℕ) (hF : ∀ s v, F s v ≤ M) (s w : ℕ) : G s w ≤ tot p * M := by
  rw [hG, tot, ← List.sum_map_mul_right]
  apply List.sum_le_sum
  intro x _
  split_ifs
  · exact Nat.mul_le_mul_left _ (hF _ _)
  · exact Nat.zero_le _

theorem inv_zero (K : ℕ) (hK : 0 < K) (F : ℕ → ℕ → ℕ)
    (hF : ∀ s w, F s w = if s = 0 ∧ w = 1 then 1 else 0) : Inv K F [(1, 1)] := by
  intro w
  rw [evalA_cons, evalA_nil, Nat.add_zero, pkK, Finset.sum_eq_single 0]
  · have h1 : 1 < B ^ K := Nat.one_lt_pow hK.ne' two_le_B
    by_cases hw : w = 1
    · subst hw
      simp [hF, Nat.mod_eq_of_lt h1]
    · simp [hF, hw, Ne.symm hw]
  · intro t _ ht
    simp [hF, ht]
  · intro h
    simp at h
    omega

theorem window_extract (d : ℕ → ℕ) (hd : ∀ t < 86, d t < B)
    (hs : ∑ s ∈ Ico 22 86, d s < B - 1) :
    pkK 86 d / B ^ 22 % (B - 1) = ∑ s ∈ Ico 22 86, d s := by
  have hsplit : pkK 86 d = pkK 22 d + B ^ 22 * ∑ j ∈ range 64, d (22 + j) * B ^ j := by
    unfold pkK
    rw [show (86 : ℕ) = 22 + 64 from rfl, Finset.sum_range_add, Finset.mul_sum]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun j _ => ?_)
    rw [pow_add]
    ring
  rw [hsplit, Nat.add_mul_div_left _ _ (Nat.pow_pos (n := 22) B_pos),
    Nat.div_eq_of_lt (pkK_lt 22 d fun t ht => hd t (by omega)), Nat.zero_add]
  have h1 : B ≡ 1 [MOD B - 1] := Nat.modEq_sub (by have := two_le_B; omega)
  have hmod : (∑ j ∈ range 64, d (22 + j) * B ^ j) ≡ (∑ j ∈ range 64, d (22 + j)) [MOD B - 1] := by
    apply Nat.ModEq.sum
    intro j _
    simpa using (h1.pow j).mul_left (d (22 + j))
  rw [Finset.sum_Ico_eq_sum_range] at hs ⊢
  rw [hmod, Nat.mod_eq_of_lt hs]

end OptimalOTS.LeanIsaBaseline.Layer.SplitPack
