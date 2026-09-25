import Submissions.UpperLeanIsa.LayerAvailability
import Submissions.UpperLeanIsa.LayerDigits
import Submissions.UpperLeanIsa.LayerProfile
import Submissions.UpperLeanIsa.TierCodec

/-! Layer-86 codec for the fixed-tag fusion candidate. Each unit has its own table.
The six binding units omit the zero tuple. Their live bands start at field zero;
unused field values occur only after the live bands. The base `params` stores the
index and signing codec; the fusion construction supplies different chain/root queries. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace FusionCodec

open LeanerVM.Parameters

/-! ## Table shapes

Shape `s` is the (3,9) table of the first group, (4,11), (3,10), or the plain (3,9) table of the
exporters, for `s = 0 … 3`. Its table has `nT s c` tuples of cost `c < nb s`, each at `muT s c`
adjacent field values (its *aliases*); the band of cost `c` is `[AS s c, AS s (c + 1))`, and the
values from `cutS s` on are *dummies*. The tuples of cost `c` are the first `nT s c` tuples of
digit sum `c` in lex order whose digits are all below `gB s`. -/

/-- Digits per tuple of shape `s`: 4 for shape 1, else 3. -/
def shK (s : ℕ) : ℕ := if s = 5 ∨ s = 6 then 4 else 3

/-- Field width of shape `s`. -/
def shB (s : ℕ) : ℕ := if s = 5 ∨ s = 6 then 11 else if 7 ≤ s then 10 else 9

/-- The digit bound of the tuple enumeration of shape `s`. -/
def gB (s : ℕ) : ℕ := if 7 ≤ s then 17 else 13

/-- Digit bound of coordinate `i` of shape `s`: one more than its maximum over the table. -/
def shLen (s i : ℕ) : ℕ := if 7 ≤ s then 17 else if (s = 5 ∨ s = 6) ∧ i = 0 then 12 else 13

/-- Tuples of each cost. -/
def shN (s : ℕ) : List ℕ :=
  ([[0, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 51, 0, 0, 0],
    [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 57, 0, 0, 0],
    [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 54, 0, 0, 0],
    [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 47, 0, 0, 0],
    [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 57, 0, 0, 0],
    [0, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 454, 229, 0, 0, 0],
    [0, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 454, 229, 0, 0, 0],
    [0, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 118],
    [0, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 153],
    [0, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 153],
    [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 153],
    [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 83, 0, 0],
    [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 153]]).getD s []

/-- Field values per tuple of each cost (`1` for an empty band). -/
def shMu (s : ℕ) : List ℕ :=
  ([[1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 128, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]).getD s []

/-- Cumulative band sizes: entry `c` counts the live values of cost `< c`. -/
def shCum (s : ℕ) : List ℕ :=
  ([[0, 0, 3, 15, 25, 40, 61, 89, 125, 170, 225, 291, 369, 460, 511, 511, 511, 511],
    [0, 1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 455, 512, 512, 512, 512],
    [0, 1, 7, 13, 23, 38, 59, 87, 123, 168, 223, 289, 367, 458, 512, 512, 512, 512],
    [0, 1, 4, 10, 30, 45, 66, 94, 130, 175, 230, 296, 374, 465, 512, 512, 512, 512],
    [0, 1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 455, 512, 512, 512, 512],
    [0, 0, 4, 14, 34, 69, 125, 209, 329, 494, 714, 1000, 1364, 1818, 2047, 2047, 2047, 2047],
    [0, 0, 4, 14, 34, 69, 125, 209, 329, 494, 714, 1000, 1364, 1818, 2047, 2047, 2047, 2047],
    [0, 0, 3, 99, 109, 124, 145, 173, 209, 254, 309, 375, 453, 544, 649, 769, 905, 1023],
    [0, 0, 12, 36, 46, 61, 82, 110, 146, 191, 246, 312, 390, 481, 586, 706, 842, 995],
    [0, 0, 3, 15, 25, 40, 61, 89, 125, 170, 225, 291, 369, 460, 565, 685, 821, 974],
    [0, 1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 455, 560, 680, 816, 969],
    [0, 1, 385, 391, 401, 416, 437, 465, 501, 546, 601, 667, 745, 836, 941, 1024, 1024, 1024],
    [0, 1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 455, 560, 680, 816, 969]]).getD s []

/-- Number of cost bands of shape `s`. -/
def nb (s : ℕ) : ℕ := (shN s).length

/-- Tuples of cost `c`. -/
def nT (s c : ℕ) : ℕ := (shN s).getD c 0

/-- Aliases per tuple of cost `c`. -/
def muT (s c : ℕ) : ℕ := (shMu s).getD c 1

/-- `AS s c`: the number of live values of cost `< c` (the live size from `nb s` on). -/
def AS (s c : ℕ) : ℕ := (shCum s).getD (min c (nb s)) 0

/-- The live values of shape `s`: the others are dummies. -/
def cutS (s : ℕ) : ℕ := AS s (nb s)

/-- Scan for the cost band of `v`. -/
def bandAux (s v : ℕ) : ℕ → ℕ → ℕ
  | 0, c => c
  | fuel + 1, c => if v < AS s (c + 1) then c else bandAux s v fuel (c + 1)

/-- The band of a live value `v`: the `c` with `AS s c ≤ v < AS s (c + 1)`. -/
def band (s v : ℕ) : ℕ := bandAux s v (nb s) 0

/-- The rank of the tuple of a live value inside its band. -/
def rank (s v : ℕ) : ℕ := (v - AS s (band s v)) / muT s (band s v)

/-- The `m`-tuples with sum `c` and digits `< B`, in lex order. -/
def tuplesB (B : ℕ) : ℕ → ℕ → List (List ℕ)
  | 0, c => if c = 0 then [[]] else []
  | m + 1, c => (List.range (min c (B - 1) + 1)).flatMap fun x => (tuplesB B m (c - x)).map (x :: ·)

/-- The tuples of cost `c` of shape `s`. -/
def tabR (s c : ℕ) : List (List ℕ) := (tuplesB (gB s) (shK s) c).take (nT s c)

/-- Tuple `r` of cost `c` of shape `s`. -/
def tupR (s c r : ℕ) : List ℕ := (tabR s c).getD r []

/-- Entry `v` of the table of shape `s`: its tuple, or all zeros for a dummy. -/
def tupS (s v : ℕ) : List ℕ :=
  if v < cutS s then tupR s (band s v) (rank s v) else List.replicate (shK s) 0

/-- The cost of entry `v`: its band, `0` for a dummy (the digit sum of `tupS s v`). -/
def costS (s v : ℕ) : ℕ := if v < cutS s then band s v else 0

/-- The (cost, lex) key; the tuples of a band have strictly increasing keys. -/
def key (t : List ℕ) : ℕ := t.foldl (fun a x => a * 32 + x) t.sum

/-- Strictly increasing keys along a list of tuples. -/
def keysUp : List (List ℕ) → Bool
  | a :: b :: l => decide (key a < key b) && keysUp (b :: l)
  | _ => true

/-- The kernel-checked facts about the tuples of cost `c`. -/
def bandOK (s c : ℕ) : Bool :=
  (tabR s c).length == nT s c && keysUp (tabR s c) &&
    (tabR s c).all (fun t => t.length == shK s && t.sum == c &&
      (List.range (shK s)).all (fun i => decide (t.getD i 0 < shLen s i)))

/-- The kernel-checked facts of shape `s`: tuples, band sizes, positive multiplicities. -/
def shapeOK (s : ℕ) : Bool :=
  (List.range (nb s)).all (fun c => bandOK s c && AS s (c + 1) == AS s c + nT s c * muT s c &&
    decide (1 ≤ muT s c)) && AS s 0 == 0 && decide (cutS s ≤ 2 ^ shB s) && decide (nb s ≤ 17) &&
    decide (1 ≤ nb s)

theorem shape0_ok : shapeOK 0 = true := by decide +kernel
theorem shape1_ok : shapeOK 1 = true := by decide +kernel
theorem shape2_ok : shapeOK 2 = true := by decide +kernel
theorem shape3_ok : shapeOK 3 = true := by decide +kernel
theorem shape4_ok : shapeOK 4 = true := by decide +kernel
theorem shape5_ok : shapeOK 5 = true := by decide +kernel
theorem shape6_ok : shapeOK 6 = true := by decide +kernel
theorem shape7_ok : shapeOK 7 = true := by decide +kernel
theorem shape8_ok : shapeOK 8 = true := by decide +kernel
theorem shape9_ok : shapeOK 9 = true := by decide +kernel
theorem shape10_ok : shapeOK 10 = true := by decide +kernel
theorem shape11_ok : shapeOK 11 = true := by decide +kernel
theorem shape12_ok : shapeOK 12 = true := by decide +kernel

theorem shape_ok {s : ℕ} (hs : s < 13) : shapeOK s = true := by
  interval_cases s
  · exact shape0_ok
  · exact shape1_ok
  · exact shape2_ok
  · exact shape3_ok
  · exact shape4_ok
  · exact shape5_ok
  · exact shape6_ok
  · exact shape7_ok
  · exact shape8_ok
  · exact shape9_ok
  · exact shape10_ok
  · exact shape11_ok
  · exact shape12_ok

theorem shapeOK_iff (s : ℕ) : shapeOK s = true ↔
    (∀ c < nb s, bandOK s c = true ∧ AS s (c + 1) = AS s c + nT s c * muT s c ∧ 1 ≤ muT s c) ∧
      AS s 0 = 0 ∧ cutS s ≤ 2 ^ shB s ∧ nb s ≤ 17 ∧ 1 ≤ nb s := by
  simp only [shapeOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc]

theorem bandOK_iff (s c : ℕ) : bandOK s c = true ↔
    (tabR s c).length = nT s c ∧ keysUp (tabR s c) = true ∧ ∀ t ∈ tabR s c,
      t.length = shK s ∧ t.sum = c ∧ ∀ i < shK s, t.getD i 0 < shLen s i := by
  simp only [bandOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc]

theorem keysUp_lt : ∀ (l : List (List ℕ)), keysUp l = true → ∀ i j, i < j → j < l.length →
    key (l.getD i []) < key (l.getD j [])
  | [], _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | [_], _, i, j, hij, hj => by simp at hj; omega
  | a :: b :: l, h, i, j, hij, hj => by
    simp only [keysUp, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := keysUp_lt (b :: l) h.2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : j < (b :: l).length := by simp only [List.length_cons] at hj ⊢; omega
    rw [List.getD_cons_succ]
    rcases i with _ | i
    · rw [List.getD_cons_zero]
      rcases j with _ | j
      · simpa using h.1
      · have := ih 0 (j + 1) (Nat.succ_pos j) hj'
        rw [List.getD_cons_zero] at this
        exact h.1.trans this
    · rw [List.getD_cons_succ]
      exact ih i j (by omega) hj'

theorem AS_zero {s : ℕ} (hs : s < 13) : AS s 0 = 0 := ((shapeOK_iff s).mp (shape_ok hs)).2.1

theorem AS_ge {s c : ℕ} (hc : nb s ≤ c) : AS s c = cutS s := by
  simp only [AS, cutS, min_eq_right hc, min_self]

theorem AS_succ {s c : ℕ} (hs : s < 13) (hc : c < nb s) :
    AS s (c + 1) = AS s c + nT s c * muT s c := (((shapeOK_iff s).mp (shape_ok hs)).1 c hc).2.1

theorem muT_pos {s c : ℕ} (hs : s < 13) (hc : c < nb s) : 1 ≤ muT s c :=
  (((shapeOK_iff s).mp (shape_ok hs)).1 c hc).2.2

theorem cutS_le {s : ℕ} (hs : s < 13) : cutS s ≤ 2 ^ shB s :=
  ((shapeOK_iff s).mp (shape_ok hs)).2.2.1

theorem nb_le {s : ℕ} (hs : s < 13) : nb s ≤ 17 := ((shapeOK_iff s).mp (shape_ok hs)).2.2.2.1

theorem nb_pos {s : ℕ} (hs : s < 13) : 1 ≤ nb s := ((shapeOK_iff s).mp (shape_ok hs)).2.2.2.2

theorem AS_mono {s : ℕ} (hs : s < 13) : Monotone (AS s) := by
  refine monotone_nat_of_le_succ fun c => ?_
  rcases Nat.lt_or_ge c (nb s) with h | h
  · rw [AS_succ hs h]; omega
  · rw [AS_ge h, AS_ge (by omega)]

theorem AS_le_cut {s : ℕ} (hs : s < 13) (c : ℕ) : AS s c ≤ cutS s := by
  rcases Nat.lt_or_ge c (nb s) with h | h
  · rw [← AS_ge (le_refl (nb s))]; exact AS_mono hs h.le
  · rw [AS_ge h]

theorem bandAux_spec {s v : ℕ} (hs : s < 13) : ∀ fuel c, AS s c ≤ v → v < AS s (c + fuel) →
    AS s (bandAux s v fuel c) ≤ v ∧ v < AS s (bandAux s v fuel c + 1) ∧
      bandAux s v fuel c < c + fuel
  | 0, c, h1, h2 => by simp at h2; omega
  | fuel + 1, c, h1, h2 => by
    unfold bandAux
    split_ifs with h
    · exact ⟨h1, h, by omega⟩
    · have := bandAux_spec hs fuel (c + 1) (Nat.le_of_not_lt h)
        (by rw [show c + 1 + fuel = c + (fuel + 1) by omega]; exact h2)
      omega

/-- A live value lies in its band. -/
theorem band_spec {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    AS s (band s v) ≤ v ∧ v < AS s (band s v + 1) ∧ band s v < nb s := by
  have := bandAux_spec hs (v := v) (nb s) 0 (by rw [AS_zero hs]; omega)
    (by rw [Nat.zero_add]; exact hv)
  unfold band
  omega

/-- The band of a value is determined by the band's bounds. -/
theorem band_unique {s v c : ℕ} (hs : s < 13) (hv : v < cutS s) (h1 : AS s c ≤ v)
    (h2 : v < AS s (c + 1)) : band s v = c := by
  obtain ⟨b1, b2, -⟩ := band_spec hs hv
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := AS_mono hs (show band s v + 1 ≤ c by omega); omega
  · have := AS_mono hs (show c + 1 ≤ band s v by omega); omega

theorem rank_lt {s v : ℕ} (hs : s < 13) (hv : v < cutS s) : rank s v < nT s (band s v) := by
  obtain ⟨h1, h2, h3⟩ := band_spec hs hv
  rw [AS_succ hs h3] at h2
  have hm := muT_pos hs h3
  unfold rank
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  omega

theorem tabR_facts {s c : ℕ} (hs : s < 13) (hc : c < nb s) :
    (tabR s c).length = nT s c ∧ keysUp (tabR s c) = true ∧ ∀ t ∈ tabR s c,
      t.length = shK s ∧ t.sum = c ∧ ∀ i < shK s, t.getD i 0 < shLen s i :=
  (bandOK_iff s c).mp (((shapeOK_iff s).mp (shape_ok hs)).1 c hc).1

theorem tupR_facts {s c r : ℕ} (hs : s < 13) (hc : c < nb s) (hr : r < nT s c) :
    (tupR s c r).length = shK s ∧ (tupR s c r).sum = c ∧
      ∀ i < shK s, (tupR s c r).getD i 0 < shLen s i := by
  obtain ⟨hl, -, ht⟩ := tabR_facts hs hc
  apply ht
  unfold tupR
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- The tuples of a band are distinct. -/
theorem tupR_inj {s c : ℕ} (hs : s < 13) (hc : c < nb s) {a b : ℕ} (ha : a < nT s c)
    (hb : b < nT s c) (h : tupR s c a = tupR s c b) : a = b := by
  obtain ⟨hl, hk, -⟩ := tabR_facts hs hc
  unfold tupR at h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (h ▸ keysUp_lt _ hk _ _ hlt (by omega)) (lt_irrefl _)
  · exact absurd (h ▸ keysUp_lt _ hk _ _ hlt (by omega)) (lt_irrefl _)

theorem tupS_length {s v : ℕ} (hs : s < 13) (hv : v < 2 ^ shB s) : (tupS s v).length = shK s := by
  unfold tupS
  split_ifs with h
  · exact (tupR_facts hs (band_spec hs h).2.2 (rank_lt hs h)).1
  · exact List.length_replicate

theorem tupS_sum {s v : ℕ} (hs : s < 13) (hv : v < 2 ^ shB s) : (tupS s v).sum = costS s v := by
  unfold tupS costS
  split_ifs with h
  · exact (tupR_facts hs (band_spec hs h).2.2 (rank_lt hs h)).2.1
  · simp

theorem tupS_lt {s v : ℕ} (hs : s < 13) (hv : v < 2 ^ shB s) {i : ℕ} (hi : i < shK s) :
    (tupS s v).getD i 0 < shLen s i := by
  unfold tupS
  split_ifs with h
  · exact (tupR_facts hs (band_spec hs h).2.2 (rank_lt hs h)).2.2 i hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    unfold shLen
    split_ifs <;> simp

/-- The first alias of the tuple of a live value. -/
def lead (s v : ℕ) : ℕ := AS s (band s v) + rank s v * muT s (band s v)

/-- Two live values have the same tuple exactly when they are aliases: the second lies in the
`muT` values from the first's `lead`. -/
theorem tupS_eq_iff {s v w : ℕ} (hs : s < 13) (hv : v < cutS s) (hw : w < cutS s) :
    tupS s w = tupS s v ↔ lead s v ≤ w ∧ w < lead s v + muT s (band s v) := by
  obtain ⟨v1, v2, v3⟩ := band_spec hs hv
  obtain ⟨w1, w2, w3⟩ := band_spec hs hw
  have hmv := muT_pos hs v3
  have hrv := rank_lt hs hv
  have hrw := rank_lt hs hw
  have hleadv : lead s v + muT s (band s v) ≤ AS s (band s v + 1) := by
    rw [AS_succ hs v3]; unfold lead
    have := Nat.mul_le_mul_right (muT s (band s v)) (show rank s v + 1 ≤ nT s (band s v) by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hrank : ∀ x, x < cutS s → rank s x * muT s (band s x) ≤ x - AS s (band s x) ∧
      x - AS s (band s x) < (rank s x + 1) * muT s (band s x) := by
    intro x hx
    have := muT_pos hs (band_spec hs hx).2.2
    refine ⟨Nat.div_mul_le_self _ _, ?_⟩
    have h := Nat.lt_div_mul_add (a := x - AS s (band s x)) (b := muT s (band s x)) (by omega)
    unfold rank
    rw [Nat.add_mul, Nat.one_mul]
    exact h
  unfold tupS
  rw [if_pos hv, if_pos hw]
  constructor
  · intro h
    have hc : band s w = band s v := by
      have := congrArg List.sum h
      rwa [(tupR_facts hs w3 hrw).2.1, (tupR_facts hs v3 hrv).2.1] at this
    rw [hc] at h hrw
    have hr := tupR_inj hs v3 hrw hrv h
    obtain ⟨r1, r2⟩ := hrank w hw
    rw [hc, hr] at r1 r2
    rw [hc] at w1
    unfold lead
    rw [Nat.add_mul, Nat.one_mul] at r2
    omega
  · rintro ⟨h1, h2⟩
    have hc : band s w = band s v := band_unique hs hw (by unfold lead at h1; omega) (by omega)
    have hr : rank s w = rank s v := by
      show (w - AS s (band s w)) / muT s (band s w) = rank s v
      rw [hc]
      unfold lead at h1 h2
      refine (Nat.div_eq_of_lt_le ?_ ?_)
      · omega
      · rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hc, hr]

/-- The aliases of a live value are live. -/
theorem lead_add_le {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    lead s v + muT s (band s v) ≤ cutS s := by
  obtain ⟨-, -, v3⟩ := band_spec hs hv
  have hrv := rank_lt hs hv
  have := AS_le_cut hs (band s v + 1)
  rw [AS_succ hs v3] at this
  unfold lead
  have := Nat.mul_le_mul_right (muT s (band s v)) (show rank s v + 1 ≤ nT s (band s v) by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-! ## Units, chains and positions -/

/-- The table shape of unit `u`. -/
def ushape (u : ℕ) : ℕ := u % 13

/-- Width of group field `u` (zero past the 13 units). -/
def ubits (u : ℕ) : ℕ := if u < 13 then shB (ushape u) else 0

/-- The chains of unit `u`, by coordinate: the home of call 1, four exporters, the homes of calls
0 and 7, the homes of calls 2 … 6, and the fifth exporter. -/
def unitChains (u : ℕ) : List ℕ :=
  [[1, 2, 7], [12, 13, 17], [18, 22, 23], [27, 28, 32], [33, 37, 38], [3, 4, 5, 6], [8, 9, 10, 11], [14, 15, 16], [19, 20, 21], [24, 25, 26], [29, 30, 31], [34, 35, 36], [39, 40, 41]].getD u []

/-- Chain `i` of unit `u`. -/
def chainAt (u i : ℕ) : ℕ := (unitChains u).getD i 0

/-- The unit of group chain `k ≥ 1`. -/
def unitOf (k : ℕ) : ℕ :=
  [0, 0, 0, 5, 5, 5, 5, 0, 6, 6, 6, 6, 1, 1, 7, 7, 7, 1, 2, 8, 8, 8, 2, 2, 9, 9, 9, 3, 3, 10, 10, 10, 3, 4, 11, 11, 11, 4, 4, 12, 12, 12].getD k 0

/-- The coordinate of group chain `k ≥ 1` in its unit. -/
def coordOf (k : ℕ) : ℕ :=
  [0, 0, 1, 0, 1, 2, 3, 2, 0, 1, 2, 3, 0, 1, 0, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2].getD k 0

/-- Positions of chain `k`: 64 for the free chain, else its coordinate's digit bound. -/
def lenN (k : ℕ) : ℕ := if k = 0 then 64 else shLen (ushape (unitOf k)) (coordOf k)

/-- First step position of chain `k` (`off (k + 1) = off k + len k - 1`; 625 steps). -/
def off (k : ℕ) : ℕ :=
  [0, 63, 75, 87, 98, 110, 122, 134, 146, 157, 169, 181, 193, 205, 217, 233, 249, 265, 277, 289, 305, 321, 337, 349, 361, 377, 393, 409, 421, 433, 449, 465, 481, 493, 505, 521, 537, 553, 565, 577, 593, 609].getD k 625

/-- The chain and step of position `p`. -/
def locAux (p : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, k => (k, p - off k)
  | fuel + 1, k => if p < off (k + 1) then (k, p - off k) else locAux p fuel (k + 1)

/-- The chain and step of position `p < 625`. -/
def locate (p : ℕ) : ℕ × ℕ := locAux p 42 0

theorem ushape_lt (u : ℕ) : ushape u < 13 := Nat.mod_lt _ (by decide)

theorem ubits_eq {u : ℕ} (hu : u < 13) : ubits u = shB (ushape u) := if_pos hu

/-- The chain maps are mutually inverse. -/
theorem chain_facts : ∀ k < 41, unitOf (k + 1) < 13 ∧ coordOf (k + 1) < shK (ushape (unitOf (k + 1)))
    ∧ chainAt (unitOf (k + 1)) (coordOf (k + 1)) = k + 1 := by decide

theorem unit_facts : ∀ u < 13, ∀ i < shK (ushape u), 1 ≤ chainAt u i ∧ chainAt u i < 42 ∧
    unitOf (chainAt u i) = u ∧ coordOf (chainAt u i) = i := by decide

/-- Step positions are below `9 ^ 3` and determine the chain and step. -/
theorem pos_facts : ∀ k < 42, ∀ j < lenN k - 1, off k + j < 729 ∧ locate (off k + j) = (k, j) := by
  decide +kernel

theorem posW_13 : posW ubits 13 = 127 := by decide

theorem steps_eq : ∑ k : Fin 42, (lenN k - 1) = 625 := by decide +kernel

/-! ## Digits -/

/-- Entry `v` of unit `u`. -/
def tup (u v : ℕ) : List ℕ := tupS (ushape u) v

/-- The cost of entry `v` of unit `u`: its digit sum (`tup_sum`). -/
def cost (u v : ℕ) : ℕ := costS (ushape u) v

/-- Group field `u` of the index. -/
def field (u : ℕ) (I : Index) : ℕ := digitW ubits I.toNat u

/-- The total cost of the 13 group fields. -/
def gsum (I : Index) : ℕ := ∑ u ∈ Finset.range 13, cost u (field u I)

/-- The free chain's digit: the layer minus the total cost, when that is in `[0, 63]`. -/
def freeDigit (c : ℕ) : ℕ := if 23 ≤ c ∧ c ≤ 86 then 86 - c else 0

/-- The live entries of unit `u`. -/
def cut (u : ℕ) : ℕ := cutS (ushape u)

/-- An index is a *dummy* when some field is a dummy entry. The machine has no blocks for these
entries, and the free digit keeps dummy indices off the layer. -/
def dummy (I : Index) : Prop := ∃ u < 13, cut u ≤ field u I

/-- The free digit of an index: `[gsum = 86]` for a dummy (so its digit sum is never `86`),
else `freeDigit (gsum I)`. -/
def freeD (I : Index) : ℕ :=
  if dummy I then (if gsum I = 86 then 1 else 0) else freeDigit (gsum I)

/-- Digit of chain `k` (on naturals). -/
def digitN (I : Index) (k : ℕ) : ℕ :=
  if k = 0 then freeD I else (tup (unitOf k) (field (unitOf k) I)).getD (coordOf k) 0

theorem field_lt (u : ℕ) (I : Index) : field u I < 2 ^ ubits u := digitW_lt ubits _ _

theorem field_lt' {u : ℕ} (hu : u < 13) (I : Index) : field u I < 2 ^ shB (ushape u) := by
  rw [← ubits_eq hu]; exact field_lt u I

theorem tup_length {u v : ℕ} (hv : v < 2 ^ shB (ushape u)) : (tup u v).length = shK (ushape u) :=
  tupS_length (ushape_lt u) hv

theorem tup_sum {u v : ℕ} (hv : v < 2 ^ shB (ushape u)) : (tup u v).sum = cost u v :=
  tupS_sum (ushape_lt u) hv

theorem sum_range_getD (l : List ℕ) :
    ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

/-- The digits of the 41 group chains sum to the total cost. -/
theorem sum_group_digits (I : Index) :
    ∑ k ∈ Finset.range 41, digitN I (k + 1) = gsum I := by
  have hu : ∀ u ∈ Finset.range 13, cost u (field u I) =
      ∑ i ∈ Finset.range (shK (ushape u)), (tup u (field u I)).getD i 0 := by
    intro u hu
    have hv := field_lt' (Finset.mem_range.mp hu) I
    rw [← tup_sum hv, ← sum_range_getD, tup_length hv]
  rw [gsum, Finset.sum_congr rfl hu, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun k => ⟨unitOf (k + 1), coordOf (k + 1)⟩)
    (fun x => chainAt x.1 x.2 - 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have := chain_facts k (Finset.mem_range.mp hk)
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨this.1, this.2.1⟩
  · rintro ⟨u, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have := unit_facts u hx.1 i hx.2
    simp only [Finset.mem_range]
    omega
  · intro k hk
    have := chain_facts k (Finset.mem_range.mp hk)
    simp only [this.2.2, Nat.add_sub_cancel]
  · rintro ⟨u, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have := unit_facts u hx.1 i hx.2
    simp only [Nat.sub_add_cancel this.1, this.2.2.1, this.2.2.2]
  · intro k _
    simp only [digitN, Nat.add_one_ne_zero, if_false]

/-! ## The parameters -/

/-- The 128-bit word of the field constant `g ^ e`: the cell `ofK (gpow e)` as `BLAKE2S` reads
it. -/
def gword (e : ℕ) : Word := LeanIsa.cellBits (ofK (gpow e))

/-- Tag symbol `d < 9`: the cost constant `C_d = g ^ (67 d)`. -/
def sym (d : ℕ) : Word := gword (1152921504606846976 * d)

/-- The frame exponent of root call `r` (the machine's frame constant `F_r`). -/
def rootExp (r : ℕ) : ℕ := (r + 1) * 1152921504606846976

/-- Positions of chain `k`. -/
def len (k : Fin numChains) : ℕ := lenN k

/-- The accepted layer. -/
def layer : ℕ := 86

/-- Digit of chain `k`. -/
def digit (I : Index) (k : Fin numChains) : ℕ := digitN I k

/-- Tag cells `A, B, C` of the step of chain `k` at position `j`: the base-9 digits of
`off k + j`. -/
def tag (k : Fin numChains) (j : ℕ) : Fin 3 → Word :=
  ![sym ((off k + j) % 9), sym ((off k + j) / 9 % 9), sym ((off k + j) / 81)]

/-- The constant cv pair `(cv₀, cv₁) = (1, g)` (the machine's adjacent `ONE, G` cells). -/
def cv : BitVec 256 := gword 1 ++ gword 0

/-- Metadata of chain steps: `ONE`. -/
def chainMd : Word := gword 0

/-- Metadata of the index query: `G`. -/
def idxMd : Word := gword 1

/-- Metadata of root call `r`: the frame constant `F_r`. -/
def rootMd (r : ℕ) : Word := gword (rootExp r)

/-- The GROUP-3 parameters. -/
def params : Params where
  len := len
  layer := layer
  digit := digit
  tag := tag
  cv := cv
  chainMd := chainMd
  idxMd := idxMd
  rootMd := rootMd
  hiTop := fun k => decide (k.val ∈ [1, 7, 12, 14, 21, 22, 26, 33, 35])

/-- The HL-GROUP-3 scheme. -/
def scheme : OracleAlgorithm.Scheme := params.scheme


/-! ## Field-constant words -/

theorem gword_eq (e : ℕ) : gword e = (0 : BitVec 64) ++ (gpow e : K) := by
  unfold gword LeanIsa.cellBits
  rw [limb_ofK, limb_ofK]
  simp

/-- Words of distinct `g`-powers below the group order are distinct. -/
theorem gword_inj {a b : ℕ} (ha : a < 18446744073709551615) (hb : b < 18446744073709551615)
    (h : gword a = gword b) : a = b := by
  rw [gword_eq, gword_eq] at h
  have h' : (gpow a : K) = gpow b := by
    simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (64 + 64) => z.extractLsb' 0 64) h
  exact gpow_injOn (Set.mem_Iio.mpr (by norm_num; omega)) (Set.mem_Iio.mpr (by norm_num; omega)) h'

theorem sym_inj {a b : ℕ} (ha : a < 9) (hb : b < 9) (h : sym a = sym b) : a = b := by
  have := gword_inj (by omega) (by omega) h
  omega

theorem chainMd_ne : params.chainMd ≠ params.idxMd := by
  intro h
  have := gword_inj (a := 0) (b := 1) (by norm_num) (by norm_num) h
  omega

theorem rootMd_ne : ∀ r < 9, params.rootMd r ≠ params.idxMd := by
  intro r hr h
  have := gword_inj (a := rootExp r) (b := 1) (by unfold rootExp; omega) (by norm_num) h
  unfold rootExp at this
  omega

theorem chainMd_ne_root : ∀ r < 9, params.chainMd ≠ params.rootMd r := by
  intro r hr h
  have := gword_inj (a := 0) (b := rootExp r) (by norm_num) (by unfold rootExp; omega) h
  unfold rootExp at this
  omega

theorem rootMd_inj : ∀ r s, r < 9 → s < 9 → params.rootMd r = params.rootMd s → r = s := by
  intro r s hr hs h
  have := gword_inj (a := rootExp r) (b := rootExp s) (by unfold rootExp; omega)
    (by unfold rootExp; omega) h
  unfold rootExp at this
  omega

/-! ## Digits: bounds, injectivity, acceptance -/

theorem digit_lt (I : Index) (k : Fin numChains) : digit I k < len k := by
  unfold digit len digitN lenN
  by_cases hk : k.val = 0
  · rw [if_pos hk, if_pos hk]
    unfold freeD freeDigit
    split_ifs <;> omega
  · rw [if_neg hk, if_neg hk]
    have hf := chain_facts (k.val - 1) (by have : k.val < 42 := k.isLt; omega)
    rw [Nat.sub_add_cancel (by omega)] at hf
    exact tupS_lt (ushape_lt _) (field_lt' hf.1 I) hf.2.1

theorem tup_eq_of_getD {u : ℕ} {a b : ℕ} (ha : a < 2 ^ shB (ushape u))
    (hb : b < 2 ^ shB (ushape u))
    (h : ∀ i < shK (ushape u), (tup u a).getD i 0 = (tup u b).getD i 0) : tup u a = tup u b := by
  have la := tupS_length (ushape_lt u) ha
  have lb := tupS_length (ushape_lt u) hb
  apply List.ext_getElem (by unfold tup; rw [la, lb])
  intro i hi hi'
  have := h i (by unfold tup at hi; rwa [la] at hi)
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi', Option.getD_some, Option.getD_some] at this

/-- Equal digits give equal tuples in every unit. -/
theorem tup_eq_of_digit {I I' : Index} (h : digit I' = digit I) {u : ℕ} (hu : u < 13) :
    tup u (field u I') = tup u (field u I) := by
  refine tup_eq_of_getD (field_lt' hu I') (field_lt' hu I) fun i hi => ?_
  obtain ⟨h1, h2, h3, h4⟩ := unit_facts u hu i hi
  have := congrFun h ⟨chainAt u i, h2⟩
  simp only [digit, digitN, if_neg (show chainAt u i ≠ 0 by omega), h3, h4] at this
  exact this

theorem sum_digits (I : Index) :
    ∑ k : Fin numChains, digit I k = freeD I + gsum I := by
  change ∑ k : Fin 42, digitN I k.val = _
  rw [Fin.sum_univ_eq_sum_range (fun k => digitN I k) 42, Finset.sum_range_succ',
    sum_group_digits]
  simp only [digitN, ↓reduceIte]
  omega

/-- **Acceptance** is a window on the total cost. -/
theorem accepted_iff (I : Index) :
    params.Accepted I ↔ ¬ dummy I ∧ 23 ≤ gsum I ∧ gsum I < 87 := by
  change ∑ k : Fin numChains, digit I k = 86 ↔ _
  rw [sum_digits]
  unfold freeD freeDigit
  by_cases hd : dummy I
  · rw [if_pos hd]
    simp only [hd, not_true_eq_false, false_and, iff_false]
    split_ifs <;> omega
  · rw [if_neg hd]
    simp only [hd, not_false_eq_true, true_and]
    split_ifs <;> omega

/-! ## Field tuples -/

/-- The digit function of a field tuple, extended by zero. -/
def digitFun (c : (u : Fin 13) → Fin (2 ^ ubits u)) (u : ℕ) : ℕ :=
  if h : u < 13 then (c ⟨u, h⟩).val else 0

theorem digitFun_lt (c : (u : Fin 13) → Fin (2 ^ ubits u)) (u : ℕ) :
    digitFun c u < 2 ^ ubits u := by
  unfold digitFun
  split_ifs with h
  · exact (c ⟨u, h⟩).isLt
  · positivity

/-- The index with the given group fields. -/
def indexOf (c : (u : Fin 13) → Fin (2 ^ ubits u)) : Index :=
  BitVec.ofNat 127 (ofDigitsW ubits (digitFun c) 13)

theorem indexOf_toNat (c : (u : Fin 13) → Fin (2 ^ ubits u)) :
    (indexOf c).toNat = ofDigitsW ubits (digitFun c) 13 := by
  have h := ofDigitsW_lt ubits (digitFun c) (digitFun_lt c) 13
  rw [posW_13] at h
  rw [indexOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem field_indexOf (c : (u : Fin 13) → Fin (2 ^ ubits u)) (u : Fin 13) :
    field u (indexOf c) = (c u).val := by
  rw [field, indexOf_toNat, digitW_ofDigitsW ubits _ (digitFun_lt c) 13 u u.isLt, digitFun,
    dif_pos u.isLt]

/-- An index is the index of its fields. -/
theorem indexOf_fields (I : Index) : indexOf (fun u => ⟨field u I, field_lt u I⟩) = I := by
  apply BitVec.eq_of_toNat_eq
  rw [indexOf_toNat]
  have hI : I.toNat < 2 ^ posW ubits 13 := by rw [posW_13]; exact I.isLt
  conv_rhs => rw [← ofDigitsW_digitW ubits I.toNat 13 hI]
  unfold ofDigitsW
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [digitFun, dif_pos (Finset.mem_range.mp hu)]
  rfl

theorem gsum_eq (I : Index) : gsum I = ∑ u : Fin 13, cost u (field u I) :=
  (Fin.sum_univ_eq_sum_range (fun u => cost u (field u I)) 13).symm

theorem cut_le : ∀ u < 13, cut u ≤ 2 ^ ubits u := by decide

theorem cut_le' {u : ℕ} (hu : u < 13) : cut u ≤ 2 ^ shB (ushape u) := by
  rw [← ubits_eq hu]; exact cut_le u hu

theorem not_dummy_iff (I : Index) : ¬ dummy I ↔ ∀ u < 13, field u I < cut u := by
  simp only [dummy, not_exists, not_and, not_le]

/-! ## Classes and their weights

A class is the digit vector of an accepted index. Two accepted indices have the same digits
exactly when their fields are aliases, so the accepted indices of a class number the product of
the field multiplicities (`weight_eq`). -/

/-- The multiplicity of entry `v` of unit `u`: the number of its aliases. -/
def mult (u v : ℕ) : ℕ := muT (ushape u) (cost u v)

/-- The product of the multiplicities of the fields of `I`. -/
def wprod (I : Index) : ℕ := ∏ u : Fin 13, mult u (field u I)

/-- The aliases of field `u` of `I`. -/
def aliases (I : Index) (u : Fin 13) : Finset (Fin (2 ^ ubits u)) :=
  Finset.univ.filter fun x => lead (ushape u) (field u I) ≤ x.val ∧
    x.val < lead (ushape u) (field u I) + mult u (field u I)

theorem cost_live {u v : ℕ} (hv : v < cut u) : cost u v = band (ushape u) v := by
  simp only [cost, costS, if_pos (show v < cutS (ushape u) from hv)]

theorem card_aliases {I : Index} {u : Fin 13} (hl : field u I < cut u) :
    (aliases I u).card = mult u (field u I) := by
  have hs := ushape_lt u
  have hle := lead_add_le hs hl
  have hcut := cut_le u u.isLt
  unfold mult at hle ⊢
  rw [cost_live hl]
  unfold cut at hl hcut
  have hI : (Finset.Ico (lead (ushape u) (field u I)) (lead (ushape u) (field u I) +
      muT (ushape u) (band (ushape u) (field u I)))).card =
      muT (ushape u) (band (ushape u) (field u I)) := by simp
  rw [← hI]
  refine Finset.card_bij' (fun x _ => x.val) (fun y hy => ⟨y, by
      rw [Finset.mem_Ico] at hy; omega⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [aliases, mult, cost_live hl, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Finset.mem_Ico.mpr hx
  · intro y hy
    simp only [aliases, mult, cost_live hl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_Ico.mp hy
  · intro x _; rfl
  · intro y _; rfl

/-- Accepted indices with the same digits as an accepted `I` are exactly the indices whose fields
are aliases of `I`'s. -/
theorem same_digits_iff {I : Index} (hI : params.Accepted I) (I' : Index) :
    (params.Accepted I' ∧ params.digit I' = params.digit I) ↔ ∀ u : Fin 13,
      lead (ushape u) (field u I) ≤ field u I' ∧
        field u I' < lead (ushape u) (field u I) + mult u (field u I) := by
  have hlI := (not_dummy_iff I).mp ((accepted_iff I).mp hI).1
  constructor
  · rintro ⟨hI', hd⟩ u
    have hl' := (not_dummy_iff I').mp ((accepted_iff I').mp hI').1
    have ht := tup_eq_of_digit hd u.isLt
    have := (tupS_eq_iff (ushape_lt u) (hlI u u.isLt) (hl' u u.isLt)).mp ht
    unfold mult; rw [cost_live (hlI u u.isLt)]; exact this
  · intro h
    have hl' : ∀ u < 13, field u I' < cut u := by
      intro u hu
      have hh := h ⟨u, hu⟩
      simp only at hh
      have := lead_add_le (ushape_lt u) (hlI u hu)
      unfold mult at hh; rw [cost_live (hlI u hu)] at hh
      unfold cut; omega
    have ht : ∀ u < 13, tup u (field u I') = tup u (field u I) := by
      intro u hu
      have hh := h ⟨u, hu⟩
      simp only at hh
      unfold mult at hh; rw [cost_live (hlI u hu)] at hh
      exact (tupS_eq_iff (ushape_lt u) (hlI u hu) (hl' u hu)).mpr hh
    have hc : ∀ u < 13, cost u (field u I') = cost u (field u I) := by
      intro u hu
      rw [← tup_sum (field_lt' hu I'), ← tup_sum (field_lt' hu I), ht u hu]
    have hg : gsum I' = gsum I := by
      rw [gsum_eq, gsum_eq]
      exact Finset.sum_congr rfl fun u _ => hc u u.isLt
    have hacc := (accepted_iff I).mp hI
    have hnd' := (not_dummy_iff I').mpr hl'
    refine ⟨(accepted_iff I').mpr ⟨hnd', hg ▸ hacc.2⟩, ?_⟩
    funext k
    change digitN I' k = digitN I k
    unfold digitN
    split_ifs with hk
    · unfold freeD; rw [if_neg hnd', if_neg hacc.1, hg]
    · have hf := chain_facts (k.val - 1) (by have : k.val < 42 := k.isLt; omega)
      rw [Nat.sub_add_cancel (by omega)] at hf
      rw [ht _ hf.1]

/-- **The weight of an accepted index** is the product of its field multiplicities. -/
theorem weight_eq {I : Index} (hI : params.Accepted I) : params.weight I = wprod I := by
  have hlI := (not_dummy_iff I).mp ((accepted_iff I).mp hI).1
  unfold Params.weight wprod
  rw [← Finset.prod_congr rfl fun (u : Fin 13) _ => card_aliases (hlI u.val u.isLt),
    ← Fintype.card_piFinset]
  refine Finset.card_bij' (fun I' _ => fun u => ⟨field u I', field_lt u I'⟩)
    (fun c _ => indexOf c) ?_ ?_ ?_ ?_
  · intro I' hI'
    rw [Finset.mem_filter] at hI'
    have := (same_digits_iff hI I').mp hI'.2
    simp only [Fintype.mem_piFinset, aliases, Finset.mem_filter, Finset.mem_univ, true_and]
    exact this
  · intro c hc
    simp only [Fintype.mem_piFinset, aliases, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (same_digits_iff hI (indexOf c)).mpr fun u => ?_⟩
    rw [field_indexOf]; exact hc u
  · intro I' _; exact indexOf_fields I'
  · intro c _
    funext u
    exact Fin.ext (field_indexOf c u)

/-! ## Interface for the machine -/

/-- The bit positions of the group fields (`POS`), and `128` past the last one. -/
theorem posW_eq : ∀ u < 14, posW ubits u =
    [0, 9, 18, 27, 36, 45, 56, 67, 77, 87, 97, 107, 117, 127].getD u 0 := by decide

theorem digit_free (I : Index) : digit I 0 = freeD I := by
  simp only [digit, digitN]; rfl

/-- The free digit of an index without dummy fields. -/
theorem digit_free_live {I : Index} (h : ∀ u < 13, field u I < cut u) :
    digit I 0 = freeDigit (gsum I) := by
  rw [digit_free, freeD, if_neg ((not_dummy_iff I).mpr h)]

theorem digit_group (I : Index) (k : Fin numChains) (hk : k.val ≠ 0) :
    digit I k = (tup (unitOf k) (field (unitOf k) I)).getD (coordOf k) 0 := by
  simp only [digit, digitN, if_neg hk]

/-- A live entry lies in the band of its cost. -/
theorem cost_spec {u v : ℕ} (hv : v < cut u) :
    AS (ushape u) (cost u v) ≤ v ∧ v < AS (ushape u) (cost u v + 1) := by
  rw [cost_live hv]
  exact ⟨(band_spec (ushape_lt u) hv).1, (band_spec (ushape_lt u) hv).2.1⟩

theorem cost_lt {u v : ℕ} (hv : v < cut u) : cost u v < 17 := by
  rw [cost_live hv]
  have := (band_spec (ushape_lt u) hv).2.2
  have := nb_le (ushape_lt u)
  omega

theorem gword_zero : gword 0 = LeanIsa.cellBits (ofK 1) := by
  show LeanIsa.cellBits (ofK (g ^ 0)) = _; rw [pow_zero]

theorem gword_one : gword 1 = LeanIsa.cellBits (ofK g) := by
  show LeanIsa.cellBits (ofK (g ^ 1)) = _; rw [pow_one]

end FusionCodec


end OptimalOTS.LeanIsaBaseline.Layer
