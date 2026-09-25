import Submissions.UpperLeanIsa.LayerAvailability
import Submissions.UpperLeanIsa.LayerDigits
import Submissions.UpperLeanIsa.LayerProfile

/-!
# The concrete field-rescaled Group3 scheme

The 127-bit effective index has field widths [9,9,9,9,9,11,11,10,10,10,10,10,10].
The first group homes root call 1; four exporter groups precede the homes of calls 0 and 7
(the two quads), the homes of calls 2..6, and a fifth exporter (the last group).
Tuple shapes enumerate the cheapest (cost, lex) tuples: (3,9) excluding the origin (shape 0,
no longer used), (3,9), (4,11), and (3,10). The shape proofs cover all base entries with kernel
evaluation.

The cost-17 entries of the six (3,10) tables (fields `969 … 1023`) are *dummies*: an index with a
dummy field gets free digit `[gsum = 96]`, so its digit sum is never 96. Otherwise chain 0
supplies the free digit 96-gsum when it lies in [0,63]. Acceptance is exactly: no dummy field
and 33 ≤ gsum ≤ 96. There are 30698186487542081244787668213344876 accepted effective indices,
at least 188*2^107. The concrete chains have 655 steps in total.

With Q=2^60, tags are the three base-9 digits of each step position encoded as g^(Q*d).
Chain/index metadata are ONE/g; root metadata of calls r < 7 are g^((r+1)*Q). The high-top set
is [1,7,12,17,22,27,32,37,38,39].
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Group3

open LeanerVM.Parameters

/-! ## Table shapes -/

/-- Digits per tuple of shape `s`: 4 for shape 2, else 3. -/
def shK (s : ℕ) : ℕ := if s = 2 then 4 else 3

/-- Field width of shape `s`. -/
def shB (s : ℕ) : ℕ := if s = 0 then 9 else if s = 1 then 9 else if s = 2 then 11 else 10

/-- Cumulative layer sizes of shape `s`: entry `c` counts the table's tuples of cost `< c`. -/
def shCum (s : ℕ) : List ℕ :=
  if s = 0 then
    [0, 0, 3, 9, 19, 34, 55, 83, 119, 164, 219, 285, 363, 454, 512, 512, 512, 512, 512]
  else if s = 1 then
    [0, 1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 455, 512, 512, 512, 512, 512]
  else if s = 2 then
    [0, 1, 5, 15, 35, 70, 126, 210, 330, 495, 715, 1001, 1365, 1820, 2048, 2048, 2048, 2048,
      2048]
  else
    [0, 1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 455, 560, 680, 816, 969, 1024]

/-- `AS s c`: the number of table entries of cost `< c` (the table size from `c = 18` on). -/
def AS (s c : ℕ) : ℕ := (shCum s).getD c (2 ^ shB s)

/-- Scan for the cost band of `v`. -/
def bandAux (s v : ℕ) : ℕ → ℕ → ℕ
  | 0, c => c
  | fuel + 1, c => if v < AS s (c + 1) then c else bandAux s v fuel (c + 1)

/-- The cost of entry `v` of shape `s`: the `c` with `AS s c ≤ v < AS s (c + 1)`. -/
def band (s v : ℕ) : ℕ := bandAux s v 18 0

/-- Number of `m`-tuples of naturals with sum `s`, for `m ≤ 3`. -/
def ncomp (m s : ℕ) : ℕ :=
  if m = 1 then 1 else if m = 2 then s + 1 else if m = 3 then (s + 1) * (s + 2) / 2 else 0

/-- The first digit of the `r`-th lex tuple of sum `s` with `m` further digits, and the rank
left for those. -/
def firstAux (m s : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, x, r => (x, r)
  | fuel + 1, x, r =>
    if r < ncomp m (s - x) then (x, r) else firstAux m s fuel (x + 1) (r - ncomp m (s - x))

/-- The `r`-th `m`-tuple of sum `s` in lex order (`m ≤ 4`). -/
def lexU : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | 1, s, _ => [s]
  | m + 2, s, r =>
    let p := firstAux (m + 1) s (s + 1) 0 r
    p.1 :: lexU (m + 1) (s - p.1) p.2

/-- Entry `v` of the table of shape `s`. -/
def tupS (s v : ℕ) : List ℕ := lexU (shK s) (band s v) (v - AS s (band s v))

/-- Digit bound of coordinate `i` of shape `s`: one more than its maximum over the table. -/
def shLen (s i : ℕ) : ℕ :=
  if s = 3 then (if i = 0 then 17 else 18)
  else if i = 0 then 13 else 14

/-- The (cost, lex) key; entries of a table have strictly increasing keys. -/
def key (t : List ℕ) : ℕ := t.foldl (fun a x => a * 32 + x) t.sum

/-- The kernel-checked facts about entry `v` of shape `s`. -/
def shapeOK (s v : ℕ) : Bool :=
  (tupS s v).length == shK s && (tupS s v).sum == band s v &&
    decide (AS s (band s v) ≤ v) && decide (v < AS s (band s v + 1)) &&
    (List.range (shK s)).all (fun i => decide ((tupS s v).getD i 0 < shLen s i)) &&
    (decide (2 ^ shB s ≤ v + 1) || decide (key (tupS s v) < key (tupS s (v + 1))))

/-- `p 0 ∧ ⋯ ∧ p (n - 1)`, by structural recursion. -/
def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

theorem allBelow_spec {p : ℕ → Bool} : ∀ {n : ℕ}, allBelow p n = true → ∀ v < n, p v = true
  | 0, _, v, hv => absurd hv (Nat.not_lt_zero v)
  | n + 1, h, v, hv => by
    rw [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · exact allBelow_spec h.2 v hv
    · exact h.1

theorem shape0_ok : allBelow (shapeOK 0) 512 = true := by decide +kernel
theorem shape1_ok : allBelow (shapeOK 1) 512 = true := by decide +kernel
theorem shape2_ok : allBelow (shapeOK 2) 2048 = true := by decide +kernel
theorem shape3_ok : allBelow (shapeOK 3) 1024 = true := by decide +kernel

theorem shape_ok {s : ℕ} (hs : s < 4) {v : ℕ} (hv : v < 2 ^ shB s) : shapeOK s v = true := by
  interval_cases s
  · exact allBelow_spec shape0_ok v hv
  · exact allBelow_spec shape1_ok v hv
  · exact allBelow_spec shape2_ok v hv
  · exact allBelow_spec shape3_ok v hv


/-! ### Shape facts -/

theorem shapeOK_iff (s v : ℕ) : shapeOK s v = true ↔
    ((tupS s v).length = shK s ∧ (tupS s v).sum = band s v ∧ AS s (band s v) ≤ v ∧
      v < AS s (band s v + 1) ∧ (∀ i < shK s, (tupS s v).getD i 0 < shLen s i)) ∧
      (2 ^ shB s ≤ v + 1 ∨ key (tupS s v) < key (tupS s (v + 1))) := by
  simp only [shapeOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, and_assoc]

theorem tupS_length {s v : ℕ} (hs : s < 4) (hv : v < 2 ^ shB s) : (tupS s v).length = shK s :=
  ((shapeOK_iff s v).mp (shape_ok hs hv)).1.1

theorem tupS_sum {s v : ℕ} (hs : s < 4) (hv : v < 2 ^ shB s) : (tupS s v).sum = band s v :=
  ((shapeOK_iff s v).mp (shape_ok hs hv)).1.2.1

/-- Entry `v` lies in the cost band `band s v`. -/
theorem band_spec {s v : ℕ} (hs : s < 4) (hv : v < 2 ^ shB s) :
    AS s (band s v) ≤ v ∧ v < AS s (band s v + 1) :=
  ⟨((shapeOK_iff s v).mp (shape_ok hs hv)).1.2.2.1,
    ((shapeOK_iff s v).mp (shape_ok hs hv)).1.2.2.2.1⟩

theorem tupS_lt {s v : ℕ} (hs : s < 4) (hv : v < 2 ^ shB s) {i : ℕ} (hi : i < shK s) :
    (tupS s v).getD i 0 < shLen s i :=
  ((shapeOK_iff s v).mp (shape_ok hs hv)).1.2.2.2.2 i hi

theorem key_lt_of_lt {s : ℕ} (hs : s < 4) {a b : ℕ} (hab : a < b) (hb : b < 2 ^ shB s) :
    key (tupS s a) < key (tupS s b) := by
  induction b with
  | zero => omega
  | succ b ih =>
    have hstep : key (tupS s b) < key (tupS s (b + 1)) := by
      rcases ((shapeOK_iff s b).mp (shape_ok hs (by omega))).2 with h | h
      · omega
      · exact h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | rfl
    · exact (ih h (by omega)).trans hstep
    · exact hstep

/-- Each table is injective. -/
theorem tupS_inj {s : ℕ} (hs : s < 4) {a b : ℕ} (ha : a < 2 ^ shB s) (hb : b < 2 ^ shB s)
    (h : tupS s a = tupS s b) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (h ▸ key_lt_of_lt hs hlt hb) (lt_irrefl _)
  · exact absurd (h ▸ key_lt_of_lt hs hlt ha) (lt_irrefl _)

theorem AS_zero {s : ℕ} (hs : s < 4) : AS s 0 = 0 := by interval_cases s <;> decide

theorem AS_top {s : ℕ} (hs : s < 4) : AS s 18 = 2 ^ shB s := by interval_cases s <;> decide

theorem AS_ge {s c : ℕ} (hs : s < 4) (hc : 18 ≤ c) : AS s c = 2 ^ shB s := by
  rcases Nat.lt_or_ge c 19 with h | h
  · rw [show c = 18 by omega]; exact AS_top hs
  · unfold AS
    rw [List.getD_eq_default]
    interval_cases s <;> simp [shCum] <;> omega

theorem AS_mono {s : ℕ} (hs : s < 4) : Monotone (AS s) := by
  refine monotone_nat_of_le_succ fun c => ?_
  rcases Nat.lt_or_ge c 18 with h | h
  · have key : ∀ c < 18, AS s c ≤ AS s (c + 1) := by interval_cases s <;> decide
    exact key c h
  · rw [AS_ge hs h, AS_ge hs (by omega)]

/-! ## Units, chains and positions -/

/-- The table shape of unit `u`. -/
def ushape (u : ℕ) : ℕ := [1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3, 3].getD u 3

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

/-- First step position of chain `k` (`off (k + 1) = off k + len k - 1`; 655 steps). -/
def off (k : ℕ) : ℕ :=
  [0, 63, 75, 88, 100, 113, 126, 139, 152, 164, 177, 190, 203, 215, 228, 244, 261, 278, 291, 303, 319, 336, 353, 366, 379, 395, 412, 429, 441, 454, 470, 487, 504, 517, 529, 545, 562, 579, 592, 605, 621, 638].getD k 655

/-- The chain and step of position `p`. -/
def locAux (p : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, k => (k, p - off k)
  | fuel + 1, k => if p < off (k + 1) then (k, p - off k) else locAux p fuel (k + 1)

/-- The chain and step of position `p < 655`. -/
def locate (p : ℕ) : ℕ × ℕ := locAux p 42 0

theorem ushape_lt (u : ℕ) : ushape u < 4 := by
  unfold ushape
  rcases Nat.lt_or_ge u 13 with h | h
  · interval_cases u <;> decide
  · rw [List.getD_eq_default _ _ (by simpa using h)]; decide

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

theorem steps_eq : ∑ k : Fin 42, (lenN k - 1) = 655 := by decide +kernel

/-! ## Digits -/

/-- Entry `v` of unit `u`. -/
def tup (u v : ℕ) : List ℕ := tupS (ushape u) v

/-- The cost of entry `v` of unit `u`: its digit sum (`tup_sum`). -/
def cost (u v : ℕ) : ℕ := band (ushape u) v

/-- Group field `u` of the index. -/
def field (u : ℕ) (I : Index) : ℕ := digitW ubits I.toNat u

/-- The total cost of the 13 group fields. -/
def gsum (I : Index) : ℕ := ∑ u ∈ Finset.range 13, cost u (field u I)

/-- The free chain's digit: the layer minus the total cost, when that is in `[0, 63]`. -/
def freeDigit (c : ℕ) : ℕ := if 33 ≤ c ∧ c ≤ 96 then 96 - c else 0

/-- The table entries of unit `u` of cost at most 16 (`969` for the (3,10) tables, the whole
table otherwise). -/
def cut (u : ℕ) : ℕ := AS (ushape u) 17

/-- An index is a *dummy* when some field is a cost-17 entry of a (3,10) table. The machine has
no blocks for these entries, and the free digit keeps dummy indices off the layer. -/
def dummy (I : Index) : Prop := ∃ u < 13, cut u ≤ field u I

/-- The free digit of an index: `[gsum = 96]` for a dummy (so its digit sum is never `96`),
else `freeDigit (gsum I)`. -/
def freeD (I : Index) : ℕ :=
  if dummy I then (if gsum I = 96 then 1 else 0) else freeDigit (gsum I)

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
def layer : ℕ := 96

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
  hiTop := fun k => decide (k.val ∈ [1, 7, 12, 17, 22, 27, 32, 37, 38, 39])

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

theorem rootMd_ne : ∀ r < 7, params.rootMd r ≠ params.idxMd := by
  intro r hr h
  have := gword_inj (a := rootExp r) (b := 1) (by unfold rootExp; omega) (by norm_num) h
  unfold rootExp at this
  omega

theorem chainMd_ne_root : ∀ r < 7, params.chainMd ≠ params.rootMd r := by
  intro r hr h
  have := gword_inj (a := 0) (b := rootExp r) (by norm_num) (by unfold rootExp; omega) h
  unfold rootExp at this
  omega

theorem rootMd_inj : ∀ r s, r < 7 → s < 7 → params.rootMd r = params.rootMd s → r = s := by
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

theorem tup_ext {u : ℕ} {a b : ℕ} (ha : a < 2 ^ shB (ushape u)) (hb : b < 2 ^ shB (ushape u))
    (h : ∀ i < shK (ushape u), (tup u a).getD i 0 = (tup u b).getD i 0) : a = b := by
  apply tupS_inj (ushape_lt u) ha hb
  have la := tupS_length (ushape_lt u) ha
  have lb := tupS_length (ushape_lt u) hb
  apply List.ext_getElem (by rw [la, lb])
  intro i hi hi'
  have := h i (by rwa [la] at hi)
  unfold tup at this
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi', Option.getD_some, Option.getD_some] at this

/-- The group digits determine the index. -/
theorem digit_inj (I I' : Index) (h : ∀ k, digit I k = digit I' k) : I = I' := by
  apply BitVec.eq_of_toNat_eq
  have hI : I.toNat < 2 ^ posW ubits 13 := by rw [posW_13]; exact I.isLt
  have hI' : I'.toNat < 2 ^ posW ubits 13 := by rw [posW_13]; exact I'.isLt
  rw [← ofDigitsW_digitW ubits I.toNat 13 hI, ← ofDigitsW_digitW ubits I'.toNat 13 hI']
  unfold ofDigitsW
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  have hf : field u I = field u I' := by
    refine tup_ext (field_lt' hu' I) (field_lt' hu' I') fun i hi => ?_
    obtain ⟨h1, h2, h3, h4⟩ := unit_facts u hu' i hi
    have := h ⟨chainAt u i, h2⟩
    simp only [digit, digitN, if_neg (show chainAt u i ≠ 0 by omega), h3, h4] at this
    exact this
  unfold field at hf
  rw [hf]

theorem sum_digits (I : Index) :
    ∑ k : Fin numChains, digit I k = freeD I + gsum I := by
  change ∑ k : Fin 42, digitN I k.val = _
  rw [Fin.sum_univ_eq_sum_range (fun k => digitN I k) 42, Finset.sum_range_succ',
    sum_group_digits]
  simp only [digitN, ↓reduceIte]
  omega

/-- **Acceptance** is a window on the total cost. -/
theorem accepted_iff (I : Index) :
    params.Accepted I ↔ ¬ dummy I ∧ 33 ≤ gsum I ∧ gsum I < 97 := by
  change ∑ k : Fin numChains, digit I k = 96 ↔ _
  rw [sum_digits]
  unfold freeD freeDigit
  by_cases hd : dummy I
  · rw [if_pos hd]
    simp only [hd, not_true_eq_false, false_and, iff_false]
    split_ifs <;> omega
  · rw [if_neg hd]
    simp only [hd, not_false_eq_true, true_and]
    split_ifs <;> omega

/-! ## Counting the accepted indices -/

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

theorem gsum_eq (I : Index) : gsum I = ∑ u : Fin 13, cost u (field u I) :=
  (Fin.sum_univ_eq_sum_range (fun u => cost u (field u I)) 13).symm

attribute [local irreducible] gsum

theorem cut_le : ∀ u < 13, cut u ≤ 2 ^ ubits u := by decide

theorem cut_le' {u : ℕ} (hu : u < 13) : cut u ≤ 2 ^ shB (ushape u) := by
  rw [← ubits_eq hu]; exact cut_le u hu

theorem not_dummy_iff (I : Index) : ¬ dummy I ↔ ∀ u < 13, field u I < cut u := by
  simp only [dummy, not_exists, not_and, not_le]

theorem card_accepted :
    params.numValid = ∑ s ∈ Finset.Ico 33 97, compP cut cost 13 s := by
  rw [← card_window, Params.numValid]
  refine Finset.card_bij' (fun I hI => fun u => ⟨field u I, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepted_iff] at hI
      exact (not_dummy_iff I).mp hI.1 u u.isLt⟩)
    (fun c _ => indexOf (fun u => Fin.castLE (cut_le u u.isLt) (c u))) ?_ ?_ ?_ ?_
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepted_iff, gsum_eq] at hI ⊢
    exact hI.2
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepted_iff, gsum_eq] at hc ⊢
    simp only [field_indexOf, Fin.val_castLE]
    refine ⟨(not_dummy_iff _).mpr fun u hu => ?_, hc⟩
    have := field_indexOf (fun u => Fin.castLE (cut_le u u.isLt) (c u)) ⟨u, hu⟩
    simp only [Fin.val_castLE] at this
    rw [this]
    exact (c ⟨u, hu⟩).isLt
  · intro I _
    apply BitVec.eq_of_toNat_eq
    rw [indexOf_toNat]
    have hI : I.toNat < 2 ^ posW ubits 13 := by rw [posW_13]; exact I.isLt
    conv_rhs => rw [← ofDigitsW_digitW ubits I.toNat 13 hI]
    unfold ofDigitsW
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [digitFun, dif_pos (Finset.mem_range.mp hu)]
    rfl
  · intro c _
    funext u
    exact Fin.ext ((field_indexOf _ u).trans (Fin.val_castLE _ _))

/-- The profile of unit `u`: its entries of cost `c`. -/
def uprof (u c : ℕ) : ℕ := AS (ushape u) (c + 1) - AS (ushape u) c

theorem compP_rec : ∀ n < 13, ∀ s, compP cut cost (n + 1) s =
    ∑ c ∈ Finset.range 17, if c ≤ s then uprof n c * compP cut cost n (s - c) else 0 := by
  intro n hn s
  have hs := ushape_lt n
  exact compP_succ_band _ _ (AS (ushape n)) (AS_mono hs) (AS_zero hs) 17 n rfl
    (fun v hv => band_spec hs (lt_of_lt_of_le hv (cut_le' hn))) s

theorem window_eq : ∑ s ∈ Finset.Ico 33 97, compP cut cost 13 s =
    30698186487542081244787668213344876 := by
  have ht : ∀ i ∈ Finset.range 64, compP cut cost 13 (33 + i) =
      (compTableP uprof 17 96 13).getD (33 + i) 0 := fun i hi =>
    (compTableP_getD _ _ uprof 17 96 13 compP_rec 13 le_rfl (33 + i)
      (by have := Finset.mem_range.mp hi; omega)).symm
  rw [Finset.sum_Ico_eq_sum_range, show 97 - 33 = 64 from rfl, Finset.sum_congr rfl ht,
    ← sum_map_range]
  decide +kernel

/-- The exact number of accepted indices, `189.19 · 2 ^ 107`. -/
theorem numValid_eq : params.numValid = 30698186487542081244787668213344876 := by
  rw [card_accepted, window_eq]

theorem numValid_ge : 188 * 2 ^ 107 ≤ params.numValid := by
  rw [numValid_eq]; norm_num

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

theorem cost_spec {u v : ℕ} (hv : v < 2 ^ shB (ushape u)) :
    AS (ushape u) (cost u v) ≤ v ∧ v < AS (ushape u) (cost u v + 1) :=
  band_spec (ushape_lt u) hv

theorem cost_lt {u v : ℕ} (hv : v < 2 ^ shB (ushape u)) : cost u v < 18 := by
  have h := (cost_spec hv).2
  by_contra hc
  rw [AS_ge (ushape_lt u) (by omega)] at h
  have := (cost_spec hv).1
  rw [AS_ge (ushape_lt u) (by omega)] at this
  omega

theorem gword_zero : gword 0 = LeanIsa.cellBits (ofK 1) := by
  show LeanIsa.cellBits (ofK (g ^ 0)) = _; rw [pow_zero]

theorem gword_one : gword 1 = LeanIsa.cellBits (ofK g) := by
  show LeanIsa.cellBits (ofK (g ^ 1)) = _; rw [pow_one]

/-! ## Availability -/

/-- **Signing availability of HL-GROUP-3.** -/
theorem signingFailure : scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) :=
  params.signingFailure chainMd_ne rootMd_ne numValid_ge

end Group3

end OptimalOTS.LeanIsaBaseline.Layer
