import Submissions.UpperLeanIsa.SplitIntervals

namespace OptimalOTS.LeanIsaBaseline.Layer.FourChildCodec
open SplitTables
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def shK := SplitTables.dim
def shB := SplitTables.bits
def shLen (_ _ : ℕ) : ℕ := 17
def nb (_ : ℕ) : ℕ := 18
def shCum (s : ℕ) : List ℕ :=
  [[0,0,3,9,19,34,55,83,119,164,219,285,363,454,512,512,512,512,512],
   [0,1,4,10,20,35,56,84,120,165,220,286,364,455,512,512,512,512,512],
   [0,1,4,10,20,35,56,84,120,165,220,286,364,455,512,512,512,512,512],
   [0,1,4,10,20,35,56,84,120,165,220,286,364,455,512,512,512,512,512],
   [0,1,4,10,20,35,56,84,120,165,220,286,364,455,512,512,512,512,512],
   [0,0,499,509,529,566,622,710,830,995,1215,1501,1877,2334,2894,3574,4096,4096,4096],
   [0,0,10,17,34,64,114,191,309,465,675,950,1302,1744,2048,2048,2048,2048,2048],
   [0,1,7,21,31,61,82,112,150,198,253,319,397,488,593,713,846,996,996],
   [0,0,9,27,60,75,96,124,160,205,260,326,404,495,600,720,866,1016,1024],
   [0,0,12,24,36,66,92,120,158,203,259,325,403,494,599,719,855,1005,1024],
   [0,0,27,39,49,64,99,127,163,208,263,329,407,498,603,723,859,1009,1024],
   [0,0,2,7,16,30,50,77,112,156,210,275,355,445,512,512,512,512,512],
   [0,0,145,153,162,176,196,223,258,302,356,429,506,596,700,819,954,1024,1024]].getD s []
def AS (s c : ℕ) : ℕ := (shCum s).getD (min c 18) 0
def cutS (s : ℕ) : ℕ := AS s 18
def selected (s v : ℕ) : SplitTables.Entry := select v (entries s)
def tupS (s v : ℕ) : List ℕ :=
  if v < cutS s then (selected s v).1 else List.replicate (shK s) 0
def costS (s v : ℕ) : ℕ := (tupS s v).sum
def band := costS
def lead (s v : ℕ) : ℕ := (selected s v).2.1
def multS (s v : ℕ) : ℕ := (selected s v).2.2

def codecOK (s : ℕ) : Bool :=
  keysUp s (entries s) && mass (entries s) == cutS s &&
  cutS s ≤ 2 ^ shB s && (entries s).all (fun e =>
    e.1.sum < 18 && AS s e.1.sum ≤ e.2.1 &&
      e.2.1 + e.2.2 ≤ AS s (e.1.sum + 1))

/-! ### Kernel-cheap codec checker

`codecOK` recomputes every tuple key twice and walks `shCum` per entry. `codecR` computes each
key once in a direct `List.rec` pass and takes the per-table cumulative row as an argument. -/

/-- `t.foldl (fun a b => a * 16 + b) a` as a direct recursor pass. -/
noncomputable def foldR (t : List ℕ) : ℕ → ℕ :=
  List.rec (fun a => a) (fun x _ ih a => ih (Nat.add (Nat.mul a 16) x)) t
/-- `tupleKey` with `visible u` supplied. -/
noncomputable def keyR (vis : ℕ) (t : List ℕ) : ℕ :=
  foldR t (Nat.add (Nat.mul (sumR t) 5) (zcR t vis))
/-- Strictly increasing keys after a previous key `p`. -/
noncomputable def keysR (vis : ℕ) (es : List Entry) : ℕ → Bool :=
  List.rec (fun _ => true) (fun e _ ih p => Nat.blt p (keyR vis e.1) && ih (keyR vis e.1)) es
noncomputable def keysStart (vis : ℕ) (es : List Entry) : Bool :=
  List.rec true (fun e es _ => keysR vis es (keyR vis e.1)) es
/-- `l.getD k 0` as a direct recursor pass. -/
noncomputable def getR (l : List ℕ) : ℕ → ℕ :=
  List.rec (fun _ => 0) (fun x _ ih k => Nat.casesOn (motive := fun _ => ℕ) k x ih) l
noncomputable def massR (es : List Entry) : ℕ := List.rec 0 (fun e _ ih => Nat.add e.2.2 ih) es
/-- Per-entry cost-band checks against the cumulative row `row = shCum s`. -/
noncomputable def boundsR (row : List ℕ) (es : List Entry) : Bool :=
  List.rec true (fun e _ ih => Nat.blt (sumR e.1) 18 && Nat.ble (getR row (sumR e.1)) e.2.1 &&
    Nat.ble (Nat.add e.2.1 e.2.2) (getR row (Nat.add (sumR e.1) 1)) && ih) es
noncomputable def codecR (s : ℕ) (row : List ℕ) (vis : ℕ) (es : List Entry) : Bool :=
  keysStart vis es && Nat.beq (massR es) (cutS s) && Nat.ble (cutS s) (2 ^ shB s) &&
    boundsR row es

theorem foldR_eq (t : List ℕ) (a : ℕ) : foldR t a = t.foldl (fun a b => a * 16 + b) a := by
  induction t generalizing a with
  | nil => rfl
  | cons x t ih => exact ih _

theorem keyR_eq (u : ℕ) (t : List ℕ) : keyR (visible u) t = tupleKey u t := by
  unfold keyR tupleKey
  rw [foldR_eq, sumR_eq, zcR_eq]; rfl

theorem keysR_eq (u : ℕ) (es : List Entry) (a : Entry) :
    keysR (visible u) es (tupleKey u a.1) = keysUp u (a :: es) := by
  induction es generalizing a with
  | nil => rfl
  | cons b es ih =>
    show (Nat.blt (tupleKey u a.1) (keyR (visible u) b.1) && keysR (visible u) es (keyR (visible u) b.1)) = _
    rw [keyR_eq, ih, blt_eq_decide]; rfl

theorem keysStart_eq (u : ℕ) (es : List Entry) : keysStart (visible u) es = keysUp u es := by
  cases es with
  | nil => rfl
  | cons a es =>
    show keysR (visible u) es (keyR (visible u) a.1) = _
    rw [keyR_eq, keysR_eq]

theorem getR_eq (l : List ℕ) (k : ℕ) : getR l k = l.getD k 0 := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons x l ih => cases k with
    | zero => rfl
    | succ k => exact ih k

theorem massR_eq (es : List Entry) : massR es = mass es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    show Nat.add e.2.2 (massR es) = _
    rw [ih]; unfold mass; rw [List.map_cons, List.sum_cons]; rfl

theorem boundsR_eq (s : ℕ) (es : List Entry) : boundsR (shCum s) es = es.all (fun e =>
    e.1.sum < 18 && AS s e.1.sum ≤ e.2.1 && e.2.1 + e.2.2 ≤ AS s (e.1.sum + 1)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    show (Nat.blt (sumR e.1) 18 && Nat.ble (getR (shCum s) (sumR e.1)) e.2.1 &&
      Nat.ble (Nat.add e.2.1 e.2.2) (getR (shCum s) (Nat.add (sumR e.1) 1)) && boundsR (shCum s) es) = _
    rw [ih, List.all_cons, getR_eq, getR_eq, sumR_eq]
    congr 1
    unfold AS
    by_cases h : e.1.sum < 18
    · rw [min_eq_left h.le, min_eq_left (by omega : e.1.sum + 1 ≤ 18)]
      simp only [blt_eq_decide, ble_eq_decide, Nat.add_eq]
    · simp only [blt_eq_decide, h, decide_false, Bool.false_and]

theorem codecOK_eq (s : ℕ) : codecOK s = codecR s (shCum s) (visible s) (entries s) := by
  unfold codecOK codecR
  rw [keysStart_eq, massR_eq, boundsR_eq, beq_eq_beq, ble_eq_decide]

theorem codec0_ok : codecOK 0 = true := by rw [codecOK_eq]; decide +kernel
theorem codec1_ok : codecOK 1 = true := by rw [codecOK_eq]; decide +kernel
theorem codec2_ok : codecOK 2 = true := by rw [codecOK_eq]; decide +kernel
theorem codec3_ok : codecOK 3 = true := by rw [codecOK_eq]; decide +kernel
theorem codec4_ok : codecOK 4 = true := by rw [codecOK_eq]; decide +kernel
theorem codec5_ok : codecOK 5 = true := by rw [codecOK_eq]; decide +kernel
theorem codec6_ok : codecOK 6 = true := by rw [codecOK_eq]; decide +kernel
theorem codec7_ok : codecOK 7 = true := by rw [codecOK_eq]; decide +kernel
theorem codec8_ok : codecOK 8 = true := by rw [codecOK_eq]; decide +kernel
theorem codec9_ok : codecOK 9 = true := by rw [codecOK_eq]; decide +kernel
theorem codec10_ok : codecOK 10 = true := by rw [codecOK_eq]; decide +kernel
theorem codec11_ok : codecOK 11 = true := by rw [codecOK_eq]; decide +kernel
theorem codec12_ok : codecOK 12 = true := by rw [codecOK_eq]; decide +kernel

theorem codec_ok {s : ℕ} (hs : s < 13) : codecOK s = true := by
  interval_cases s
  · exact codec0_ok
  · exact codec1_ok
  · exact codec2_ok
  · exact codec3_ok
  · exact codec4_ok
  · exact codec5_ok
  · exact codec6_ok
  · exact codec7_ok
  · exact codec8_ok
  · exact codec9_ok
  · exact codec10_ok
  · exact codec11_ok
  · exact codec12_ok

theorem codec_facts {s : ℕ} (hs : s < 13) :
    keysUp s (entries s) = true ∧ mass (entries s) = cutS s ∧
    cutS s ≤ 2 ^ shB s ∧ ∀ e ∈ entries s,
      e.1.sum < 18 ∧ AS s e.1.sum ≤ e.2.1 ∧
      e.2.1 + e.2.2 ≤ AS s (e.1.sum + 1) := by
  have h := codec_ok hs
  simpa only [codecOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, and_assoc] using h

theorem selected_spec {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    selected s v ∈ entries s ∧ lead s v ≤ v ∧ v < lead s v + multS s v := by
  have h := tables_ok s hs
  simp only [tableOK, Bool.and_eq_true] at h
  exact interval_spec (entries s) 0 v h.2 (Nat.zero_le _) (by
    rw [(codec_facts hs).2.1, Nat.zero_add]; exact hv)

theorem selected_entryOK {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    entryOK s (selected s v) = true := by
  have ht := tables_ok s hs
  simp only [tableOK, Bool.and_eq_true] at ht
  exact List.all_eq_true.mp ht.1 _ (selected_spec hs hv).1

theorem selected_length {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    (selected s v).1.length = shK s := by
  have h := selected_entryOK hs hv
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  exact h.1

theorem selected_digit_lt {s v i : ℕ} (hs : s < 13) (hv : v < cutS s)
    (hi : i < shK s) : (selected s v).1.getD i 0 < shLen s i := by
  have h := selected_entryOK hs hv
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  have hl := selected_length hs hv
  have hi' : i < (selected s v).1.length := by omega
  rw [List.getD_eq_getElem _ _ hi']
  have hb := List.all_eq_true.mp h.2.1 _ (List.getElem_mem hi')
  simp only [decide_eq_true_eq] at hb
  unfold shLen; omega

theorem cutS_le {s : ℕ} (hs : s < 13) : cutS s ≤ 2 ^ shB s :=
  (codec_facts hs).2.2.1

theorem tupS_length {s v : ℕ} (hs : s < 13) (hv : v < 2 ^ shB s) :
    (tupS s v).length = shK s := by
  unfold tupS
  split_ifs with h
  · exact selected_length hs h
  · exact List.length_replicate

theorem tupS_sum {s v : ℕ} (_ : s < 13) (_ : v < 2 ^ shB s) :
    (tupS s v).sum = costS s v := rfl

theorem tupS_lt {s v : ℕ} (hs : s < 13) (hv : v < 2 ^ shB s)
    {i : ℕ} (hi : i < shK s) : (tupS s v).getD i 0 < shLen s i := by
  unfold tupS
  split_ifs with h
  · exact selected_digit_lt hs h hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    unfold shLen
    split_ifs <;> simp

theorem lead_add_le {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    lead s v + multS s v ≤ cutS s := by
  have ht := tables_ok s hs
  simp only [tableOK, Bool.and_eq_true] at ht
  have h := (interval_bounds (entries s) 0 ht.2 _ (selected_spec hs hv).1).2
  simpa only [lead, multS, Nat.zero_add, (codec_facts hs).2.1] using h

theorem tupS_eq_iff {s v w : ℕ} (hs : s < 13) (hv : v < cutS s) (hw : w < cutS s) :
    tupS s w = tupS s v ↔ lead s v ≤ w ∧ w < lead s v + multS s v := by
  have hv' := selected_spec hs hv
  have hw' := selected_spec hs hw
  simp only [tupS, if_pos hv, if_pos hw]
  constructor
  · intro h
    have he := tuple_injective (codec_facts hs).1 hw'.1 hv'.1 h
    have hw'' := hw'.2
    change (selected s w).2.1 ≤ w ∧
      w < (selected s w).2.1 + (selected s w).2.2 at hw''
    simp only [lead, multS]
    rw [← he]
    exact hw''
  · intro h
    have ht := tables_ok s hs
    simp only [tableOK, Bool.and_eq_true] at ht
    exact congrArg Prod.fst (select_eq (entries s) 0 w ht.2 _ hv'.1 h.1 h.2)

theorem band_spec {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    AS s (band s v) ≤ v ∧ v < AS s (band s v + 1) ∧ band s v < nb s := by
  have hb := (codec_facts hs).2.2.2 _ (selected_spec hs hv).1
  have hv' := selected_spec hs hv
  simp only [band, costS, tupS, if_pos hv, nb]
  exact ⟨hb.2.1.trans hv'.2.1, hv'.2.2.trans_le hb.2.2, hb.1⟩

theorem visible_tuple_pos {s v : ℕ} (hs : s < 13) (hv : v < cutS s)
    (hb : SplitTables.binding s = true) :
    0 < ((tupS s v).take (SplitTables.visible s)).sum := by
  have h := selected_entryOK hs hv
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc,
    hb, Bool.not_true, Bool.false_or] at h
  obtain ⟨x,hx,hx0⟩ := List.any_eq_true.mp h.2.2.2.2.1
  simp only [bne_iff_ne] at hx0
  have hxle := List.single_le_sum (fun a _ => Nat.zero_le a) x hx
  simp only [tupS, if_pos hv]
  omega

theorem multS_pos {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    0 < multS s v := by
  have h := selected_spec hs hv
  omega

theorem ordinary_bound {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    SplitTables.ordinary s (selected s v) (v - lead s v) ≤ SplitTables.budget s := by
  have h := selected_spec hs hv
  exact SplitTables.block_ordinary_le hs h.1 (by change v - lead s v < multS s v; omega)

theorem ordinary_eq {s v : ℕ} (hs : s < 13) (hv : v < cutS s) :
    SplitTables.ordinary s (selected s v) (v - lead s v) =
      3 + (if s = 0 ∨ s = 11 ∨ v = 0 then 1 else 2) +
      (if s = 5 then 0 else SplitTables.zeroCount ((tupS s v).take (SplitTables.visible s))) +
      (if 14 < costS s v - (if SplitTables.binding s then 1 else 0) then 1 else 0) := by
  have h := selected_spec hs hv
  have he : (selected s v).2.1 + (v - lead s v) = v := by
    change lead s v + (v - lead s v) = v
    omega
  simp only [SplitTables.ordinary, he, costS, tupS, if_pos hv]

theorem AS_zero {s : ℕ} (hs : s < 13) : AS s 0 = 0 := by
  have h : ∀ s < 13, AS s 0 = 0 := by decide
  exact h s hs

theorem AS_ge {s c : ℕ} (hc : nb s ≤ c) : AS s c = cutS s := by
  change 18 ≤ c at hc
  unfold cutS AS
  rw [min_eq_right hc, min_self]

theorem AS_mono {s : ℕ} (hs : s < 13) : Monotone (AS s) := by
  apply monotone_nat_of_le_succ
  intro c
  by_cases hc : c < 18
  · have h : ∀ s < 13, ∀ c < 18, AS s c ≤ AS s (c + 1) := by decide
    exact h s hs c hc
  · rw [AS_ge (by unfold nb; omega), AS_ge (by unfold nb; omega)]

theorem AS_le_cut {s : ℕ} (hs : s < 13) (c : ℕ) : AS s c ≤ cutS s := by
  by_cases hc : c < 18
  · exact AS_mono hs hc.le
  · rw [AS_ge (by unfold nb; omega)]

end OptimalOTS.LeanIsaBaseline.Layer.FourChildCodec
