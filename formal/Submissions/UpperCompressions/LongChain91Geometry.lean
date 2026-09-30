import Submissions.UpperCompressions.ProofBundle00

/-!
# Global shared-DAG research geometry

One block has 42 length-24 chains and 213 hash nodes.
Binary and unary inputs are padded by repeating an existing input.
The private value has only one consuming hash node.
-/

open scoped BigOperators

noncomputable section

set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

/-! ## Block structure -/

/-- An input of a block hash node: the top of a chain or another hash value. -/
inductive Kid where
  | c (k : Fin 42)
  | h (j : Fin 213)
  deriving DecidableEq, Fintype

/-- Forty-two length-24 chains and the searched ternary DAG.
Slot `2` holds the exclusive kid of each hash node. -/
def kid : Fin 213 → Fin 3 → Kid := ![
  ![.c 32, .c 0, .c 22],
  ![.c 14, .c 2, .c 15],
  ![.c 32, .c 31, .h 1],
  ![.c 28, .c 30, .h 2],
  ![.c 16, .c 3, .h 3],
  ![.c 4, .c 0, .h 4],
  ![.c 30, .h 5, .c 27],
  ![.c 16, .c 14, .h 0],
  ![.c 2, .c 31, .c 38],
  ![.c 28, .c 14, .h 6],
  ![.c 14, .c 4, .h 8],
  ![.c 30, .c 28, .h 7],
  ![.c 2, .c 16, .h 9],
  ![.h 5, .c 31, .h 11],
  ![.c 4, .c 31, .h 12],
  ![.c 0, .c 3, .h 14],
  ![.c 4, .h 15, .h 13],
  ![.c 2, .c 3, .h 16],
  ![.c 32, .c 14, .c 1],
  ![.c 16, .c 0, .c 12],
  ![.c 31, .h 15, .h 18],
  ![.c 28, .h 5, .h 19],
  ![.h 5, .c 4, .h 20],
  ![.c 3, .c 0, .h 10],
  ![.c 32, .c 14, .h 21],
  ![.c 28, .c 30, .h 23],
  ![.c 16, .h 15, .h 25],
  ![.h 5, .h 17, .h 26],
  ![.c 2, .h 27, .h 22],
  ![.c 28, .c 30, .h 28],
  ![.c 3, .c 16, .h 29],
  ![.h 17, .c 0, .h 30],
  ![.c 4, .c 3, .h 24],
  ![.c 30, .c 31, .h 32],
  ![.c 2, .h 27, .h 33],
  ![.h 31, .h 15, .h 34],
  ![.h 17, .h 31, .c 23],
  ![.h 5, .c 30, .h 36],
  ![.c 0, .c 2, .h 37],
  ![.c 31, .c 3, .h 38],
  ![.c 4, .c 16, .h 39],
  ![.c 14, .h 15, .h 40],
  ![.h 17, .c 30, .c 36],
  ![.c 31, .c 0, .h 42],
  ![.c 28, .c 3, .h 43],
  ![.c 14, .h 5, .h 44],
  ![.h 15, .c 16, .h 45],
  ![.c 2, .c 4, .h 46],
  ![.h 31, .h 27, .h 47],
  ![.c 30, .c 32, .c 39],
  ![.c 16, .c 4, .h 49],
  ![.c 3, .c 2, .h 50],
  ![.h 17, .h 15, .h 51],
  ![.c 28, .h 27, .h 52],
  ![.c 31, .c 0, .h 53],
  ![.h 31, .c 17, .h 54],
  ![.c 14, .h 5, .h 55],
  ![.c 4, .c 3, .c 7],
  ![.c 30, .c 16, .h 57],
  ![.h 5, .c 0, .h 58],
  ![.h 15, .c 28, .h 59],
  ![.c 2, .h 31, .h 60],
  ![.c 31, .c 14, .h 61],
  ![.c 17, .h 27, .h 62],
  ![.c 30, .c 16, .c 5],
  ![.c 28, .c 3, .h 64],
  ![.h 15, .c 4, .h 65],
  ![.c 17, .c 2, .h 66],
  ![.c 0, .h 17, .h 67],
  ![.c 31, .h 31, .h 68],
  ![.h 5, .c 18, .h 69],
  ![.c 31, .c 0, .c 13],
  ![.h 15, .c 30, .h 71],
  ![.c 4, .c 3, .h 72],
  ![.h 5, .c 2, .h 73],
  ![.h 27, .c 16, .h 74],
  ![.h 70, .h 17, .h 75],
  ![.c 28, .h 31, .h 76],
  ![.c 17, .c 18, .h 77],
  ![.c 30, .h 17, .c 19],
  ![.c 32, .c 4, .h 79],
  ![.h 15, .c 2, .c 41],
  ![.c 16, .c 18, .h 81],
  ![.c 30, .c 0, .c 35],
  ![.c 30, .c 0, .h 82],
  ![.c 17, .h 31, .h 84],
  ![.c 16, .c 31, .h 83],
  ![.h 27, .h 5, .h 86],
  ![.c 28, .h 31, .h 87],
  ![.h 15, .c 2, .h 88],
  ![.c 3, .c 4, .h 89],
  ![.h 17, .h 70, .h 90],
  ![.h 5, .h 17, .h 85],
  ![.h 27, .c 28, .h 92],
  ![.h 70, .c 31, .h 93],
  ![.c 14, .h 91, .h 94],
  ![.c 3, .c 14, .h 80],
  ![.c 16, .c 2, .h 96],
  ![.h 91, .c 30, .c 25],
  ![.h 15, .c 31, .h 97],
  ![.c 14, .h 78, .h 98],
  ![.h 5, .c 31, .h 100],
  ![.c 16, .h 27, .h 101],
  ![.c 18, .h 31, .h 99],
  ![.h 17, .c 18, .h 102],
  ![.h 70, .c 32, .h 104],
  ![.c 28, .c 17, .h 103],
  ![.h 70, .h 78, .h 106],
  ![.h 95, .h 107, .h 105],
  ![.c 32, .h 108, .c 6],
  ![.c 18, .c 2, .h 109],
  ![.c 31, .h 5, .h 110],
  ![.c 17, .h 5, .c 21],
  ![.c 14, .h 91, .c 11],
  ![.c 18, .c 31, .h 113],
  ![.h 31, .h 70, .h 111],
  ![.c 16, .c 17, .h 115],
  ![.h 27, .c 16, .c 9],
  ![.c 14, .c 31, .h 117],
  ![.h 15, .c 2, .h 118],
  ![.c 17, .c 28, .c 37],
  ![.c 30, .h 91, .h 120],
  ![.h 31, .h 17, .h 114],
  ![.h 70, .h 78, .h 119],
  ![.c 14, .h 27, .h 116],
  ![.h 108, .h 108, .c 8],
  ![.h 107, .h 95, .h 124],
  ![.h 78, .h 91, .h 126],
  ![.h 70, .c 17, .h 125],
  ![.c 17, .c 16, .h 122],
  ![.c 17, .c 30, .h 123],
  ![.h 91, .h 95, .h 130],
  ![.c 32, .h 107, .h 131],
  ![.h 127, .h 108, .h 132],
  ![.h 70, .c 18, .h 112],
  ![.c 32, .c 30, .c 10],
  ![.c 31, .h 17, .h 134],
  ![.h 107, .h 27, .h 129],
  ![.h 95, .h 70, .h 137],
  ![.c 18, .h 91, .h 128],
  ![.c 18, .h 70, .h 135],
  ![.c 30, .c 16, .c 34],
  ![.h 27, .c 16, .h 136],
  ![.c 32, .c 17, .h 141],
  ![.h 95, .h 78, .h 142],
  ![.h 78, .c 28, .h 138],
  ![.c 30, .c 32, .h 145],
  ![.c 16, .h 70, .h 121],
  ![.c 28, .c 17, .h 140],
  ![.h 27, .h 78, .h 148],
  ![.c 30, .c 28, .h 144],
  ![.c 32, .h 107, .h 150],
  ![.h 91, .h 146, .h 151],
  ![.h 91, .h 107, .h 149],
  ![.h 152, .c 18, .c 40],
  ![.h 127, .h 95, .h 154],
  ![.h 152, .h 146, .h 143],
  ![.h 27, .h 108, .h 155],
  ![.h 78, .h 70, .h 156],
  ![.c 18, .h 91, .h 158],
  ![.h 146, .h 95, .h 153],
  ![.h 95, .h 107, .h 159],
  ![.h 127, .h 108, .h 161],
  ![.h 95, .h 95, .c 29],
  ![.c 30, .h 91, .c 33],
  ![.h 146, .c 32, .h 164],
  ![.h 91, .h 107, .h 163],
  ![.c 32, .h 108, .h 166],
  ![.h 17, .h 27, .h 167],
  ![.h 91, .h 95, .c 20],
  ![.c 18, .c 17, .h 169],
  ![.h 127, .h 108, .h 170],
  ![.h 146, .h 107, .h 171],
  ![.h 107, .c 18, .h 147],
  ![.h 78, .h 127, .h 173],
  ![.h 95, .h 108, .h 174],
  ![.h 146, .c 32, .h 175],
  ![.h 127, .h 108, .h 160],
  ![.c 30, .c 32, .c 24],
  ![.h 78, .h 107, .h 157],
  ![.c 17, .h 70, .h 168],
  ![.c 32, .h 107, .c 26],
  ![.c 32, .c 30, .h 172],
  ![.h 95, .h 78, .h 139],
  ![.c 17, .h 70, .h 181],
  ![.h 146, .h 78, .h 184],
  ![.h 108, .h 127, .h 185],
  ![.h 70, .c 17, .h 165],
  ![.h 91, .h 95, .h 178],
  ![.c 18, .h 78, .h 180],
  ![.c 18, .h 78, .h 188],
  ![.h 108, .h 127, .h 190],
  ![.h 146, .h 127, .h 189],
  ![.h 176, .h 152, .h 192],
  ![.h 152, .h 176, .h 182],
  ![.h 152, .h 107, .h 191],
  ![.h 146, .h 91, .h 179],
  ![.h 107, .h 146, .h 183],
  ![.h 194, .h 193, .h 197],
  ![.h 176, .h 152, .h 198],
  ![.c 18, .h 95, .h 186],
  ![.h 78, .h 127, .h 187],
  ![.h 176, .h 152, .h 201],
  ![.h 152, .h 176, .h 200],
  ![.h 193, .h 194, .h 203],
  ![.c 18, .h 108, .h 202],
  ![.h 176, .h 146, .h 195],
  ![.h 194, .h 193, .h 206],
  ![.h 199, .h 204, .h 207],
  ![.h 194, .h 193, .h 196],
  ![.h 199, .h 204, .h 209],
  ![.h 193, .h 194, .h 205],
  ![.h 199, .h 204, .h 211]]

/-- The eleven block tops, in root-slot order. -/
def top : Fin 11 → Fin 213 := ![48, 35, 63, 41, 177, 133, 162, 208, 210, 212, 56]

theorem top_injective : Function.Injective top := by
  decide

/-! ## Graph names and static costs -/

/-- Graph names: chain sources and stages, compress/hash/value triples of the
block hash nodes, and the root input and hash. -/
inductive Name where
  | src (b : Fin 1) (k : Fin 42)
  | ci (b : Fin 1) (k : Fin 42) (t : Fin 24)
  | ch (b : Fin 1) (k : Fin 42) (t : Fin 24)
  | cv (b : Fin 1) (k : Fin 42) (t : Fin 24)
  | hc (b : Fin 1) (j : Fin 213)
  | hh (b : Fin 1) (j : Fin 213)
  | hv (b : Fin 1) (j : Fin 213)
  | rc
  | rh
  deriving DecidableEq, Fintype

/-- Number of graph nodes. -/
def nodeCount : ℕ := 3707

namespace Name

/-- A compact topological numbering. -/
def idx : Name → ℕ
  | src b k => 42 * b + k
  | ci b k t => 42 + 126 * t + 42 * b + k
  | ch b k t => 84 + 126 * t + 42 * b + k
  | cv b k t => 126 + 126 * t + 42 * b + k
  | hc b j => 3066 + 639 * b + 3 * j
  | hh b j => 3067 + 639 * b + 3 * j
  | hv b j => 3068 + 639 * b + 3 * j
  | rc => 3705
  | rh => 3706

theorem idx_lt (n : Name) : n.idx < nodeCount := by
  cases n <;> simp only [idx, nodeCount] <;> omega

theorem idx_injective : Function.Injective idx := by
  intro m n h
  cases m <;> cases n <;> simp_all [idx, Fin.ext_iff] <;> omega

def fin (n : Name) : Fin nodeCount := ⟨n.idx, n.idx_lt⟩

theorem fin_injective : Function.Injective fin := by
  intro m n h
  apply idx_injective
  exact congrArg Fin.val h

/-- Bit length of the value stored at a node. -/
def len : Name → ℕ
  | src _ _ => 129
  | ci _ _ _ => 145
  | ch _ _ _ => 256
  | cv _ _ _ => 129
  | hc _ _ => 16 + 129 * 3
  | hh _ _ => 256
  | hv _ _ => 129
  | rc => 16 + 129 * 11
  | rh => 256

/-- SHA-256 compression cost at each hash-output node. -/
def cost : Name → ℕ
  | ch _ _ _ => 1
  | hh _ _ => 1
  | rh => 3
  | _ => 0

end Name

/-- The value node feeding chain stage `t`. -/
def prev (b : Fin 1) (k : Fin 42) (t : Fin 24) : Name :=
  if h : t.val = 0 then .src b k else .cv b k ⟨t.val - 1, by omega⟩

/-- Position zero discloses a source; positive position `p` discloses the
output of chain hash `p-1`. -/
def chainNode (b : Fin 1) (k : Fin 42) (p : Fin 25) : Name :=
  if h : p.val = 0 then .src b k else .cv b k ⟨p.val - 1, by omega⟩

theorem prev_eq_chainNode (b : Fin 1) (k : Fin 42) (t : Fin 24) :
    prev b k t = chainNode b k t.castSucc := by
  unfold prev chainNode
  split_ifs <;> simp_all

@[simp] theorem chainNode_len (b : Fin 1) (k : Fin 42) (p : Fin 25) :
    (chainNode b k p).len = 129 := by
  unfold chainNode
  split_ifs <;> rfl

theorem chainNode_pair_injective {b b' : Fin 1} {k k' : Fin 42} {p p' : Fin 25}
    (h : chainNode b k p = chainNode b' k' p') : b = b' ∧ k = k' ∧ p = p' := by
  unfold chainNode at h
  split_ifs at h with hp hp'
  · obtain ⟨hb, hk⟩ := Name.src.inj h
    exact ⟨hb, hk, Fin.ext (by omega)⟩
  · obtain ⟨hb, hk, ht⟩ := Name.cv.inj h
    have := congrArg Fin.val ht
    simp only at this
    exact ⟨hb, hk, Fin.ext (by omega)⟩

theorem hc_len_ne (b : Fin 1) (j : Fin 213) : (Name.hc b j).len ≠ 129 := by
  simp only [Name.len]
  omega

/-- The root input in slot `r`: top `r % 11` of block `r / 11`. -/
def rootIn (r : Fin 11) : Name :=
  .hv ⟨r.val / 11, by omega⟩ (top ⟨r.val % 11, by omega⟩)

theorem rootIn_mk (b : Fin 1) (s : Fin 11) :
    rootIn ⟨11 * b.val + s.val, by omega⟩ = .hv b (top s) := by
  have h1 : (11 * b.val + s.val) / 11 = b.val := by omega
  have h2 : (11 * b.val + s.val) % 11 = s.val := by omega
  simp only [rootIn, h1, h2]

theorem rootIn_injective : Function.Injective rootIn := by
  intro r r' h
  simp only [rootIn, Name.hv.injEq] at h
  obtain ⟨hb, hs⟩ := h
  have hb' := congrArg Fin.val hb
  have hs' := congrArg Fin.val (top_injective hs)
  simp only at hb' hs'
  exact Fin.ext (by omega)

/-- Static key-generation cost. -/
def keygenCost : ℕ := 42 * 24 + 213 + 3

theorem keygenCost_eq : keygenCost = 1224 := by norm_num [keygenCost]

theorem sum_name_cost : (∑ n : Name, n.cost) = keygenCost := by decide +kernel

/-! ## Needed kids and shapes -/

/-- The graph name holding a kid's 129-bit value in block `b`. -/
def Kid.name (b : Fin 1) : Kid → Name
  | .c k => .cv b k 23
  | .h j => .hv b j

def privateOwner : Kid → Option (Fin 213)
  | .c k => (![none, some 18, none, none, none, some 64, some 109, some 57, some 125, some 117, some 135, some 113, some 19, some 71, none, some 1, none, none, none, some 79, some 169, some 112, some 0, some 36, some 178, some 98, some 181, some 6, none, some 163, none, none, none, some 164, some 141, some 83, some 42, some 120, some 8, some 49, some 154, some 81] : Fin 42 → Option (Fin 213)) k
  | .h j => (![some 7, some 2, some 3, some 4, some 5, none, some 9, some 11, some 10, some 12, some 23, some 13, some 14, some 16, some 15, none, some 17, none, some 20, some 21, some 22, some 24, some 28, some 25, some 32, some 26, some 27, none, some 29, some 30, some 31, none, some 33, some 34, some 35, none, some 37, some 38, some 39, some 40, some 41, none, some 43, some 44, some 45, some 46, some 47, some 48, none, some 50, some 51, some 52, some 53, some 54, some 55, some 56, none, some 58, some 59, some 60, some 61, some 62, some 63, none, some 65, some 66, some 67, some 68, some 69, some 70, none, some 72, some 73, some 74, some 75, some 76, some 77, some 78, none, some 80, some 96, some 82, some 84, some 86, some 85, some 92, some 87, some 88, some 89, some 90, some 91, none, some 93, some 94, some 95, none, some 97, some 99, some 100, some 103, some 101, some 102, some 104, some 106, some 105, some 108, some 107, none, none, some 110, some 111, some 115, some 134, some 114, some 122, some 116, some 124, some 118, some 119, some 123, some 121, some 147, some 129, some 130, some 126, some 128, some 127, none, some 139, some 137, some 131, some 132, some 133, none, some 136, some 140, some 142, some 138, some 145, some 183, some 148, some 143, some 144, some 156, some 150, some 146, none, some 173, some 149, some 153, some 151, some 152, none, some 160, some 155, some 157, some 158, some 179, some 159, some 161, some 177, some 162, none, some 166, some 165, some 187, some 167, some 168, some 180, some 170, some 171, some 172, some 182, some 174, some 175, some 176, none, none, some 188, some 196, some 189, some 184, some 194, some 197, some 185, some 186, some 200, some 201, some 190, some 192, some 191, some 195, some 193, none, none, some 206, some 209, some 198, some 199, none, some 203, some 202, some 205, some 204, none, some 211, some 207, some 208, none, some 210, none, some 212, none] : Fin 213 → Option (Fin 213)) j

def kidOrdered (j : Fin 213) (i : Fin 3) : Bool :=
  match kid j i with
  | .c _ => true
  | .h k => decide (k < j)

theorem kid_ordered (j : Fin 213) (i : Fin 3) : kidOrdered j i = true := by
  revert j i
  decide +kernel

theorem kid_h_lt {j j' : Fin 213} {i : Fin 3} (h : kid j i = .h j') : j' < j := by
  have hh := kid_ordered j i
  simpa only [kidOrdered, h, decide_eq_true_eq] using hh

theorem owner_private (j : Fin 213) : privateOwner (kid j 2) = some j := by
  revert j
  decide +kernel

def ownerFits (e : Fin 213) (i : Fin 3) : Bool :=
  match privateOwner (kid e i) with
  | none => true
  | some j => decide (e = j)

theorem owner_kid (e : Fin 213) (i : Fin 3) : ownerFits e i = true := by
  revert e i
  decide +kernel

theorem kid_eq_kid_excl_iff (e j : Fin 213) (i : Fin 3) :
    kid e i = kid j 2 ↔ e = j ∧ kid j i = kid j 2 := by
  constructor
  · intro h
    have hp : privateOwner (kid e i) = some j := by rw [h, owner_private]
    have he := owner_kid e i
    simp only [ownerFits, hp, decide_eq_true_eq] at he
    exact ⟨he, by simpa only [he] using h⟩
  · rintro ⟨rfl, h⟩
    exact h

def kidIsTop : Kid → Bool
  | .c _ => false
  | .h j => (![false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true] : Fin 213 → Bool) j

theorem top_flag (s : Fin 11) : kidIsTop (.h (top s)) = true := by
  revert s
  decide +kernel

theorem input_not_top (j : Fin 213) (i : Fin 3) : kidIsTop (kid j i) = false := by
  revert j i
  decide +kernel

theorem kid_ne_top (j : Fin 213) (i : Fin 3) (s : Fin 11) : kid j i ≠ .h (top s) := by
  intro h
  have hn := input_not_top j i
  rw [h, top_flag] at hn
  contradiction


/-- A kid is needed when it is a block top or an input of an expanded node. -/
def Needed (E : Finset (Fin 213)) (x : Kid) : Prop :=
  (∃ s, x = .h (top s)) ∨ ∃ e ∈ E, ∃ i, kid e i = x

theorem needed_kid {E : Finset (Fin 213)} {e : Fin 213} (he : e ∈ E) (i : Fin 3) :
    Needed E (kid e i) :=
  Or.inr ⟨e, he, i, rfl⟩

/-- Binding rule: the exclusive kid of `j` is needed exactly when `j` is
expanded. -/
theorem needed_kid_excl_iff (E : Finset (Fin 213)) (j : Fin 213) :
    Needed E (kid j 2) ↔ j ∈ E := by
  constructor
  · rintro (⟨s, h⟩ | ⟨e, he, i, hi⟩)
    · exact absurd h (kid_ne_top j 2 s)
    · obtain ⟨rfl, -⟩ := (kid_eq_kid_excl_iff e j i).1 hi
      exact he
  · intro h
    exact needed_kid h _

def topSet : Finset (Fin 213) := {35, 41, 48, 56, 63, 133, 162, 177, 208, 210, 212}

theorem mem_topSet (j : Fin 213) : j ∈ topSet ↔ ∃ s, top s = j := by
  revert j
  decide

/-- Hash kids of each node, as literal finsets for cheap kernel evaluation. -/
def kidsH : Fin 213 → Finset (Fin 213) := ![
  ∅, ∅, {1}, {2}, {3}, {4}, {5}, {0}, ∅, {6}, {8}, {7}, {9}, {5, 11}, {12}, {14}, {13, 15}, {16}, ∅, ∅, {15, 18}, {5, 19}, {5, 20}, {10}, {21}, {23}, {15, 25}, {5, 17, 26}, {22, 27}, {28}, {29}, {17, 30}, {24}, {32}, {27, 33}, {15, 31, 34}, {17, 31}, {5, 36}, {37}, {38}, {39}, {15, 40}, {17}, {42}, {43}, {5, 44}, {15, 45}, {46}, {27, 31, 47}, ∅, {49}, {50}, {15, 17, 51}, {27, 52}, {53}, {31, 54}, {5, 55}, ∅, {57}, {5, 58}, {15, 59}, {31, 60}, {61}, {27, 62}, ∅, {64}, {15, 65}, {66}, {17, 67}, {31, 68}, {5, 69}, ∅, {15, 71}, {72}, {5, 73}, {27, 74}, {17, 70, 75}, {31, 76}, {77}, {17}, {79}, {15}, {81}, ∅, {82}, {31, 84}, {83}, {5, 27, 86}, {31, 87}, {15, 88}, {89}, {17, 70, 90}, {5, 17, 85}, {27, 92}, {70, 93}, {91, 94}, {80}, {96}, {91}, {15, 97}, {78, 98}, {5, 100}, {27, 101}, {31, 99}, {17, 102}, {70, 104}, {103}, {70, 78, 106}, {95, 105, 107}, {108}, {109}, {5, 110}, {5}, {91}, {113}, {31, 70, 111}, {115}, {27}, {117}, {15, 118}, ∅, {91, 120}, {17, 31, 114}, {70, 78, 119}, {27, 116}, {108}, {95, 107, 124}, {78, 91, 126}, {70, 125}, {122}, {123}, {91, 95, 130}, {107, 131}, {108, 127, 132}, {70, 112}, ∅, {17, 134}, {27, 107, 129}, {70, 95, 137}, {91, 128}, {70, 135}, ∅, {27, 136}, {141}, {78, 95, 142}, {78, 138}, {145}, {70, 121}, {140}, {27, 78, 148}, {144}, {107, 150}, {91, 146, 151}, {91, 107, 149}, {152}, {95, 127, 154}, {143, 146, 152}, {27, 108, 155}, {70, 78, 156}, {91, 158}, {95, 146, 153}, {95, 107, 159}, {108, 127, 161}, {95}, {91}, {146, 164}, {91, 107, 163}, {108, 166}, {17, 27, 167}, {91, 95}, {169}, {108, 127, 170}, {107, 146, 171}, {107, 147}, {78, 127, 173}, {95, 108, 174}, {146, 175}, {108, 127, 160}, ∅, {78, 107, 157}, {70, 168}, {107}, {172}, {78, 95, 139}, {70, 181}, {78, 146, 184}, {108, 127, 185}, {70, 165}, {91, 95, 178}, {78, 180}, {78, 188}, {108, 127, 190}, {127, 146, 189}, {152, 176, 192}, {152, 176, 182}, {107, 152, 191}, {91, 146, 179}, {107, 146, 183}, {193, 194, 197}, {152, 176, 198}, {95, 186}, {78, 127, 187}, {152, 176, 201}, {152, 176, 200}, {193, 194, 203}, {108, 202}, {146, 176, 195}, {193, 194, 206}, {199, 204, 207}, {193, 194, 196}, {199, 204, 209}, {193, 194, 205}, {199, 204, 211}]

/-- Chain kids of each node. -/
def kidsC : Fin 213 → Finset (Fin 42) := ![
  {0, 22, 32}, {2, 14, 15}, {31, 32}, {28, 30}, {3, 16}, {0, 4}, {27, 30}, {14, 16}, {2, 31, 38}, {14, 28}, {4, 14}, {28, 30}, {2, 16}, {31}, {4, 31}, {0, 3}, {4}, {2, 3}, {1, 14, 32}, {0, 12, 16}, {31}, {28}, {4}, {0, 3}, {14, 32}, {28, 30}, {16}, ∅, {2}, {28, 30}, {3, 16}, {0}, {3, 4}, {30, 31}, {2}, ∅, {23}, {30}, {0, 2}, {3, 31}, {4, 16}, {14}, {30, 36}, {0, 31}, {3, 28}, {14}, {16}, {2, 4}, ∅, {30, 32, 39}, {4, 16}, {2, 3}, ∅, {28}, {0, 31}, {17}, {14}, {3, 4, 7}, {16, 30}, {0}, {28}, {2}, {14, 31}, {17}, {5, 16, 30}, {3, 28}, {4}, {2, 17}, {0}, {31}, {18}, {0, 13, 31}, {30}, {3, 4}, {2}, {16}, ∅, {28}, {17, 18}, {19, 30}, {4, 32}, {2, 41}, {16, 18}, {0, 30, 35}, {0, 30}, {17}, {16, 31}, ∅, {28}, {2}, {3, 4}, ∅, ∅, {28}, {31}, {14}, {3, 14}, {2, 16}, {25, 30}, {31}, {14}, {31}, {16}, {18}, {18}, {32}, {17, 28}, ∅, ∅, {6, 32}, {2, 18}, {31}, {17, 21}, {11, 14}, {18, 31}, ∅, {16, 17}, {9, 16}, {14, 31}, {2}, {17, 28, 37}, {30}, ∅, ∅, {14}, {8}, ∅, ∅, {17}, {16, 17}, {17, 30}, ∅, {32}, ∅, {18}, {10, 30, 32}, {31}, ∅, ∅, {18}, {18}, {16, 30, 34}, {16}, {17, 32}, ∅, {28}, {30, 32}, {16}, {17, 28}, ∅, {28, 30}, {32}, ∅, ∅, {18, 40}, ∅, ∅, ∅, ∅, {18}, ∅, ∅, ∅, {29}, {30, 33}, {32}, ∅, {32}, ∅, {20}, {17, 18}, ∅, ∅, {18}, ∅, ∅, {32}, ∅, {24, 30, 32}, ∅, {17}, {26, 32}, {30, 32}, ∅, {17}, ∅, ∅, {17}, ∅, {18}, {18}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {18}, ∅, ∅, ∅, ∅, {18}, ∅, ∅, ∅, ∅, ∅, ∅, ∅]

def hashKidSet : Kid → Finset (Fin 213)
  | .c _ => ∅
  | .h j => {j}

def chainKidSet : Kid → Finset (Fin 42)
  | .c k => {k}
  | .h _ => ∅

theorem hashKidSet_mem (x : Kid) (j : Fin 213) : j ∈ hashKidSet x ↔ x = .h j := by
  cases x <;> simp [hashKidSet, eq_comm]

theorem chainKidSet_mem (x : Kid) (k : Fin 42) : k ∈ chainKidSet x ↔ x = .c k := by
  cases x <;> simp [chainKidSet, eq_comm]

theorem kidsH_eq (e : Fin 213) :
    kidsH e = Finset.univ.biUnion fun i : Fin 3 => hashKidSet (kid e i) := by
  revert e
  decide +kernel

theorem kidsC_eq (e : Fin 213) :
    kidsC e = Finset.univ.biUnion fun i : Fin 3 => chainKidSet (kid e i) := by
  revert e
  decide +kernel

theorem mem_kidsH (e j : Fin 213) : j ∈ kidsH e ↔ ∃ i, kid e i = .h j := by
  rw [kidsH_eq]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hashKidSet_mem]

theorem mem_kidsC (e : Fin 213) (k : Fin 42) : k ∈ kidsC e ↔ ∃ i, kid e i = .c k := by
  rw [kidsC_eq]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, chainKidSet_mem]


theorem kidsH_lt (e j : Fin 213) (h : j ∈ kidsH e) : j < e := by
  obtain ⟨i, hi⟩ := (mem_kidsH e j).1 h
  exact kid_h_lt hi

def neededH (E : Finset (Fin 213)) : Finset (Fin 213) := topSet ∪ E.biUnion kidsH

def neededC (E : Finset (Fin 213)) : Finset (Fin 42) := E.biUnion kidsC

@[simp] theorem mem_neededH (E : Finset (Fin 213)) (j : Fin 213) :
    j ∈ neededH E ↔ Needed E (.h j) := by
  simp only [neededH, Finset.mem_union, mem_topSet, Finset.mem_biUnion, mem_kidsH, Needed,
    Kid.h.injEq]
  constructor
  · rintro (⟨s, rfl⟩ | h)
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inr h
  · rintro (⟨s, rfl⟩ | h)
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inr h

@[simp] theorem mem_neededC (E : Finset (Fin 213)) (k : Fin 42) :
    k ∈ neededC E ↔ Needed E (.c k) := by
  simp only [neededC, Finset.mem_biUnion, mem_kidsC, Needed, reduceCtorEq, exists_false,
    false_or]

theorem top_mem_neededH (E : Finset (Fin 213)) (s : Fin 11) : top s ∈ neededH E :=
  (mem_neededH E _).2 (Or.inl ⟨s, rfl⟩)

/-- Every expanded node is needed. -/
def ShapeValid (E : Finset (Fin 213)) : Prop := E ⊆ neededH E

instance : DecidablePred ShapeValid := by
  intro E
  unfold ShapeValid
  infer_instance

def validShapes : Finset (Finset (Fin 213)) := Finset.univ.filter ShapeValid

attribute [irreducible] validShapes

theorem mem_validShapes (E : Finset (Fin 213)) : E ∈ validShapes ↔ ShapeValid E := by
  rw [validShapes, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

/-- Disclosed words of a block shape: needed unexpanded hash values plus one
value per needed chain. -/
def shapeWords (E : Finset (Fin 213)) : ℕ := (neededH E \ E).card + (neededC E).card

/-! ## Top-down shape recursion

`dfs a u g n need needC` handles hash nodes `n-1, …, 0`.  A node is needed
when its bit is set in `need`; a needed node is either kept (weight `u`, one
disclosed word) or expanded (weight `a`), which marks its kids as needed.  At
the bottom each needed chain gets weight `g`.  Kids have smaller indices, so a
node's neededness is fixed once the nodes above it are decided. -/

def khMask (i : ℕ) : ℕ :=
  if i < 213 then (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 0 else 2)) else (if i < 4 then 4 else (if i < 5 then 8 else 16))) else (if i < 9 then (if i < 7 then 32 else (if i < 8 then 1 else 0)) else (if i < 11 then (if i < 10 then 64 else 256) else (if i < 12 then 128 else 512)))) else (if i < 19 then (if i < 16 then (if i < 14 then 2080 else (if i < 15 then 4096 else 16384)) else (if i < 17 then 40960 else (if i < 18 then 65536 else 0))) else (if i < 22 then (if i < 20 then 0 else (if i < 21 then 294912 else 524320)) else (if i < 24 then (if i < 23 then 1048608 else 1024) else (if i < 25 then 2097152 else 8388608))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 33587200 else (if i < 28 then 67239968 else 138412032)) else (if i < 30 then 268435456 else (if i < 31 then 536870912 else 1073872896))) else (if i < 35 then (if i < 33 then 16777216 else (if i < 34 then 4294967296 else 8724152320)) else (if i < 37 then (if i < 36 then 19327385600 else 2147614720) else (if i < 38 then 68719476768 else 137438953472)))) else (if i < 46 then (if i < 42 then (if i < 40 then 274877906944 else (if i < 41 then 549755813888 else 1099511660544)) else (if i < 44 then (if i < 43 then 131072 else 4398046511104) else (if i < 45 then 8796093022208 else 17592186044448))) else (if i < 49 then (if i < 47 then 35184372121600 else (if i < 48 then 70368744177664 else 140739770056704)) else (if i < 51 then (if i < 50 then 0 else 562949953421312) else (if i < 52 then 1125899906842624 else 2251799813849088)))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then 4503599761588224 else (if i < 55 then 9007199254740992 else 18014400656965632)) else (if i < 57 then 36028797018964000 else (if i < 58 then 0 else 144115188075855872))) else (if i < 62 then (if i < 60 then 288230376151711776 else (if i < 61 then 576460752303456256 else 1152921506754330624)) else (if i < 64 then (if i < 63 then 2305843009213693952 else 4611686018561605632) else (if i < 65 then 0 else 18446744073709551616)))) else (if i < 72 then (if i < 69 then (if i < 67 then 36893488147419136000 else (if i < 68 then 73786976294838206464 else 147573952589676544000)) else (if i < 70 then 295147905181500309504 else (if i < 71 then 590295810358705651744 else 0))) else (if i < 75 then (if i < 73 then 2361183241434822639616 else (if i < 74 then 4722366482869645213696 else 9444732965739290427424)) else (if i < 77 then (if i < 76 then 18889465931478715072512 else 38959523483674573144064) else (if i < 78 then 75557863725916470902784 else 151115727451828646838272))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then 131072 else (if i < 81 then 604462909807314587353088 else 32768)) else (if i < 83 then 2417851639229258349412352 else (if i < 84 then 0 else 4835703278458516698824704))) else (if i < 88 then (if i < 86 then 19342813113834068942782464 else (if i < 87 then 9671406556917033397649408 else 77371252455336267315413024)) else (if i < 90 then (if i < 89 then 154742504910672536509874176 else 309485009821345068724813824) else (if i < 91 then 618970019642690137449562112 else 1237941219877000992310558720)))) else (if i < 99 then (if i < 95 then (if i < 93 then 38685626227668133590728736 else (if i < 94 then 4951760157141521099730714624 else 9903521494874662916604297216)) else (if i < 97 then (if i < 96 then 22282920707136844948184236032 else 1208925819614629174706176) else (if i < 98 then 79228162514264337593543950336 else 2475880078570760549798248448))) else (if i < 102 then (if i < 100 then 158456325028528675187087933440 else (if i < 101 then 316912952288512254031469477888 else 1267650600228229401496703205408)) else (if i < 104 then (if i < 103 then 2535301200456458802993540628480 else 633825300114114700750499086336) else (if i < 105 then 5070602400912917605986812952576 else 20282409604832262044664662589440))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then 10141204801825835211973625643008 else (if i < 108 then 81129638718018728220163710124032 else 202863710117773836408269284835328)) else (if i < 110 then 324518553658426726783156020576256 else (if i < 111 then 649037107316853453566312041152512 else 1298074214633706907132624082305056))) else (if i < 115 then (if i < 113 then 32 else (if i < 114 then 2475880078570760549798248448 else 10384593717069655257060992658440192)) else (if i < 117 then (if i < 116 then 2596148429268594405885967723397120 else 41538374868278621028243970633760768) else (if i < 118 then 134217728 else 166153499473114484112975882535043072)))) else (if i < 125 then (if i < 122 then (if i < 120 then 332306998946228968225951765070118912 else (if i < 121 then 0 else 1329227998260795951474567610078593024)) else (if i < 123 then 20769187434139310514121987464495104 else (if i < 124 then 664613997892761348498427904845152256 else 83076749736557242056487941401739264))) else (if i < 128 then (if i < 126 then 324518553658426726783156020576256 else (if i < 127 then 21267810231449564436956473339267776512 else 85070591732710798175869316065033977856)) else (if i < 130 then (if i < 129 then 42535295865117309113513446646382329856 else 5316911983139663491615228241121378304) else (if i < 131 then 10633823966279326983230456482242756608 else 1361129467725843815189201359073643069440))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then 2722259097626784536920360251032155979776 else (if i < 134 then 5614659378714038305572407805780196065280 else 5192296858536008220151213740523520)) else (if i < 136 then 0 else (if i < 137 then 21778071482940061661655974875633165664256 else 680564896101153756140112606441680928768))) else (if i < 141 then (if i < 139 then 174224571863560107375685522794579507544064 else (if i < 140 then 340282366923414343541945367981566459904 else 43556142965880123324492541371983742369792)) else (if i < 143 then (if i < 142 then 0 else 87112285931760246646623899502532796350464) else (if i < 144 then 2787593149816327892691964784081045188247552 else 5575186299632695399767418155234544442146816)))) else (if i < 152 then (if i < 148 then (if i < 146 then 348449143727040986888727052913787942207488 else (if i < 147 then 44601490397061246283071436545296723011960832 else 2658455991569832926399234837971992576)) else (if i < 150 then (if i < 149 then 1393796574908163946345982392040522594123776 else 356811923176489970264873723817277441523580928) else (if i < 151 then 22300745198530623141535718272648361505980416 else 1427247692706122140335115182812886714393034752))) else (if i < 155 then (if i < 153 then 2943698366206042257158594890560344268587663360 else (if i < 154 then 713623846353142202281852276658899695999909888 else 5708990770823839524233143877797980545530986496)) else (if i < 157 then (if i < 156 then 22835963253436541597015888500011394694780026880 else 5809344124217227328370054610024898172307898368) else (if i < 158 then 45671926166591040712418809449110627520402685952 else 91343852333181432387730605456814213103200763904)))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then 365375409332725729553397088257641515463781384192 else (if i < 161 then 11507184522441801580646511885818723333857869824 else 730750818665451621400733326828637070202748534784)) else (if i < 163 then 2923003274831947344386392555590980126183769767936 else (if i < 164 then 39614081257132168796771975168 else 2475880078570760549798248448))) else (if i < 168 then (if i < 166 then 23384115400275240813751523466333618907940944609280 else (if i < 167 then 11692013098647223507891231371022198309375268880384 else 93536104789177787089554382952268840041135703326720)) else (if i < 170 then (if i < 169 then 187072209578355573530071658587684226515959499849728 else 42089961335702929346570223616) else (if i < 171 then 748288838313422294120286634350736906063837462003712 else 1496577676627014729748552291591632226214546828689408)))) else (if i < 179 then (if i < 175 then (if i < 173 then 2993155442456669970765898380375034078240373882224640 else (if i < 174 then 178405961588407244409114959544578470058131456 else 11972621413014926847108046619145753639228772569841664)) else (if i < 177 then (if i < 176 then 23945242826029513412173730466963264852994751576670208 else 47890485741262007617820837164590035078679043592159232) else (if i < 178 then 1461501637501044426182707722874697106527837224960 else 0))) else (if i < 182 then (if i < 180 then 182687704666363027034737735534353672692295532544 else (if i < 181 then 374144419156711147060143317176549044652636142305280 else 162259276829213363391578010288128)) else (if i < 184 then (if i < 183 then 5986310706507378352962293074805895248510699696029696 else 696898287454121587556479783092715362713600) else (if i < 185 then 3064991081731777716716694054300619547829098961778507776 else 24519928653943424714527674926971392042445323058255233024))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then 49039857307708443637608612847832784034213738781779951616 else (if i < 188 then 46768052394588893382517914648101648249707252678656 else 383123885216472214589586798877538631607614127116124160)) else (if i < 190 then 1532495540865888858358347027150611415073642779477278720 else (if i < 191 then 392318858461667547739736838950479453237852118936295833600 else 1569275433846670191129088863780939494184002947987913310208))) else (if i < 195 then (if i < 193 then 784637716923424298630408983853993676617572327719912341504 else (if i < 194 then 6277197516363693872660260659421096454304129596204701974528 else 6225763140476664257904624322031274936249108229401870336)) else (if i < 197 then (if i < 196 then 3138550867699049372688718713387343181142339094355558531072 else 766247770522147409973296008617177543470723556913971200) else (if i < 198 then 12259964327016313847661060969045445555403898001503027200 else 238529865944693869025759998081891323811889506889633311490048)))) else (if i < 206 then (if i < 202 then (if i < 200 then 401734606845724581994314994321504080668752522597438876286976 else (if i < 201 then 98079714615416886934934209777233869008731472616522514432 else 196159429230833774040009602935709109466340815012678860800)) else (if i < 204 then (if i < 203 then 3213876184298957564192748655918538635082607761717326338064384 else 1606938140039967288650786563577376032560404767934533502763008) else (if i < 205 then 12893166964484242288918711475268546818674238082929126889488384 else 6427752177035961102167848369689168963747238701914327361781760))) else (if i < 209 then (if i < 207 then 50216909664064839431720756904843094366015910320353436499968 else (if i < 208 then 102881697442987697719268588646373652559917605734765525666365440 else 232202547395424094815813522343297996064458332601613564701048832)) else (if i < 211 then (if i < 210 then 138096238178506976804387367310568661154251819778208759283712 else 849266756390876360623926965802304435432984282214206013456777216) else (if i < 212 then 51459680026700008901925801691456449279207109933716154936721408 else 3317523592372685423856380739638330192907088080664575808479690752)))))))) else 0

def kcMask (i : ℕ) : ℕ :=
  if i < 213 then (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 4299161601 else (if i < 2 then 49156 else 6442450944)) else (if i < 4 then 1342177280 else (if i < 5 then 65544 else 17))) else (if i < 9 then (if i < 7 then 1207959552 else (if i < 8 then 81920 else 277025390596)) else (if i < 11 then (if i < 10 then 268451840 else 16400) else (if i < 12 then 1342177280 else 65540)))) else (if i < 19 then (if i < 16 then (if i < 14 then 2147483648 else (if i < 15 then 2147483664 else 9)) else (if i < 17 then 16 else (if i < 18 then 12 else 4294983682))) else (if i < 22 then (if i < 20 then 69633 else (if i < 21 then 2147483648 else 268435456)) else (if i < 24 then (if i < 23 then 16 else 9) else (if i < 25 then 4294983680 else 1342177280))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 65536 else (if i < 28 then 0 else 4)) else (if i < 30 then 1342177280 else (if i < 31 then 65544 else 1))) else (if i < 35 then (if i < 33 then 24 else (if i < 34 then 3221225472 else 4)) else (if i < 37 then (if i < 36 then 0 else 8388608) else (if i < 38 then 1073741824 else 5)))) else (if i < 46 then (if i < 42 then (if i < 40 then 2147483656 else (if i < 41 then 65552 else 16384)) else (if i < 44 then (if i < 43 then 69793218560 else 2147483649) else (if i < 45 then 268435464 else 16384))) else (if i < 49 then (if i < 47 then 65536 else (if i < 48 then 20 else 0)) else (if i < 51 then (if i < 50 then 555124523008 else 65552) else (if i < 52 then 12 else 0)))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then 268435456 else (if i < 55 then 2147483649 else 131072)) else (if i < 57 then 16384 else (if i < 58 then 152 else 1073807360))) else (if i < 62 then (if i < 60 then 1 else (if i < 61 then 268435456 else 4)) else (if i < 64 then (if i < 63 then 2147500032 else 131072) else (if i < 65 then 1073807392 else 268435464)))) else (if i < 72 then (if i < 69 then (if i < 67 then 16 else (if i < 68 then 131076 else 1)) else (if i < 70 then 2147483648 else (if i < 71 then 262144 else 2147491841))) else (if i < 75 then (if i < 73 then 1073741824 else (if i < 74 then 24 else 4)) else (if i < 77 then (if i < 76 then 65536 else 0) else (if i < 78 then 268435456 else 393216))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then 1074266112 else (if i < 81 then 4294967312 else 2199023255556)) else (if i < 83 then 327680 else (if i < 84 then 35433480193 else 1073741825))) else (if i < 88 then (if i < 86 then 131072 else (if i < 87 then 2147549184 else 0)) else (if i < 90 then (if i < 89 then 268435456 else 4) else (if i < 91 then 24 else 0)))) else (if i < 99 then (if i < 95 then (if i < 93 then 0 else (if i < 94 then 268435456 else 2147483648)) else (if i < 97 then (if i < 96 then 16384 else 16392) else (if i < 98 then 65540 else 1107296256))) else (if i < 102 then (if i < 100 then 2147483648 else (if i < 101 then 16384 else 2147483648)) else (if i < 104 then (if i < 103 then 65536 else 262144) else (if i < 105 then 262144 else 4294967296))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then 268566528 else (if i < 108 then 0 else 0)) else (if i < 110 then 4294967360 else (if i < 111 then 262148 else 2147483648))) else (if i < 115 then (if i < 113 then 2228224 else (if i < 114 then 18432 else 2147745792)) else (if i < 117 then (if i < 116 then 0 else 196608) else (if i < 118 then 66048 else 2147500032)))) else (if i < 125 then (if i < 122 then (if i < 120 then 4 else (if i < 121 then 137707520000 else 1073741824)) else (if i < 123 then 0 else (if i < 124 then 0 else 16384))) else (if i < 128 then (if i < 126 then 256 else (if i < 127 then 0 else 0)) else (if i < 130 then (if i < 129 then 131072 else 196608) else (if i < 131 then 1073872896 else 0))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then 4294967296 else (if i < 134 then 0 else 262144)) else (if i < 136 then 5368710144 else (if i < 137 then 2147483648 else 0))) else (if i < 141 then (if i < 139 then 0 else (if i < 140 then 262144 else 262144)) else (if i < 143 then (if i < 142 then 18253676544 else 65536) else (if i < 144 then 4295098368 else 0)))) else (if i < 152 then (if i < 148 then (if i < 146 then 268435456 else (if i < 147 then 5368709120 else 65536)) else (if i < 150 then (if i < 149 then 268566528 else 0) else (if i < 151 then 1342177280 else 4294967296))) else (if i < 155 then (if i < 153 then 0 else (if i < 154 then 0 else 1099511889920)) else (if i < 157 then (if i < 156 then 0 else 0) else (if i < 158 then 0 else 0)))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then 262144 else (if i < 161 then 0 else 0)) else (if i < 163 then 0 else (if i < 164 then 536870912 else 9663676416))) else (if i < 168 then (if i < 166 then 4294967296 else (if i < 167 then 0 else 4294967296)) else (if i < 170 then (if i < 169 then 0 else 1048576) else (if i < 171 then 393216 else 0)))) else (if i < 179 then (if i < 175 then (if i < 173 then 0 else (if i < 174 then 262144 else 0)) else (if i < 177 then (if i < 176 then 0 else 4294967296) else (if i < 178 then 0 else 5385486336))) else (if i < 182 then (if i < 180 then 0 else (if i < 181 then 131072 else 4362076160)) else (if i < 184 then (if i < 183 then 5368709120 else 0) else (if i < 185 then 131072 else 0))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then 0 else (if i < 188 then 131072 else 0)) else (if i < 190 then 262144 else (if i < 191 then 262144 else 0))) else (if i < 195 then (if i < 193 then 0 else (if i < 194 then 0 else 0)) else (if i < 197 then (if i < 196 then 0 else 0) else (if i < 198 then 0 else 0)))) else (if i < 206 then (if i < 202 then (if i < 200 then 0 else (if i < 201 then 262144 else 0)) else (if i < 204 then (if i < 203 then 0 else 0) else (if i < 205 then 0 else 262144))) else (if i < 209 then (if i < 207 then 0 else (if i < 208 then 0 else 0)) else (if i < 211 then (if i < 210 then 0 else 0) else (if i < 212 then 0 else 0)))))))) else 0

/-- Bit mask of the eleven block tops. -/
def topMask : ℕ := 8638898926127899509928384528368297814323313644943866452418494464

def hashKidBit : Kid → ℕ
  | .c _ => 0
  | .h j => 2^j.val

def chainKidBit : Kid → ℕ
  | .c k => 2^k.val
  | .h _ => 0

theorem hashKidBit_test (x : Kid) (j : Fin 213) :
    (hashKidBit x).testBit j = true ↔ x = .h j := by
  cases x <;> simp [hashKidBit, Nat.testBit_two_pow, Fin.ext_iff]

theorem chainKidBit_test (x : Kid) (k : Fin 42) :
    (chainKidBit x).testBit k = true ↔ x = .c k := by
  cases x <;> simp [chainKidBit, Nat.testBit_two_pow, Fin.ext_iff]

theorem khMask_eq_bits (e : Fin 213) : khMask e =
    hashKidBit (kid e 0) ||| hashKidBit (kid e 1) ||| hashKidBit (kid e 2) := by
  revert e
  decide +kernel

theorem kcMask_eq_bits (e : Fin 213) : kcMask e =
    chainKidBit (kid e 0) ||| chainKidBit (kid e 1) ||| chainKidBit (kid e 2) := by
  revert e
  decide +kernel

theorem exists_three (P : Fin 3 → Prop) : (∃ i, P i) ↔ P 0 ∨ P 1 ∨ P 2 := by
  simp [Fin.exists_fin_succ]

theorem testBit_khMask (e j : Fin 213) :
    (khMask e).testBit j = true ↔ j ∈ kidsH e := by
  rw [khMask_eq_bits, mem_kidsH, exists_three]
  simp [Nat.testBit_or, hashKidBit_test, or_assoc]

theorem testBit_kcMask (e : Fin 213) (k : Fin 42) :
    (kcMask e).testBit k = true ↔ k ∈ kidsC e := by
  rw [kcMask_eq_bits, mem_kidsC, exists_three]
  simp [Nat.testBit_or, chainKidBit_test, or_assoc]


theorem testBit_topMask (j : Fin 213) : topMask.testBit j = true ↔ j ∈ topSet := by
  revert j
  decide +kernel

/-- Chain kids of each node as bit lists, in increasing order. -/
def kcList (i : ℕ) : List (Fin 42) :=
  if i < 213 then (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then [0, 22, 32] else (if i < 2 then [2, 14, 15] else [31, 32])) else (if i < 4 then [28, 30] else (if i < 5 then [3, 16] else [0, 4]))) else (if i < 9 then (if i < 7 then [27, 30] else (if i < 8 then [14, 16] else [2, 31, 38])) else (if i < 11 then (if i < 10 then [14, 28] else [4, 14]) else (if i < 12 then [28, 30] else [2, 16])))) else (if i < 19 then (if i < 16 then (if i < 14 then [31] else (if i < 15 then [4, 31] else [0, 3])) else (if i < 17 then [4] else (if i < 18 then [2, 3] else [1, 14, 32]))) else (if i < 22 then (if i < 20 then [0, 12, 16] else (if i < 21 then [31] else [28])) else (if i < 24 then (if i < 23 then [4] else [0, 3]) else (if i < 25 then [14, 32] else [28, 30]))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then [16] else (if i < 28 then [] else [2])) else (if i < 30 then [28, 30] else (if i < 31 then [3, 16] else [0]))) else (if i < 35 then (if i < 33 then [3, 4] else (if i < 34 then [30, 31] else [2])) else (if i < 37 then (if i < 36 then [] else [23]) else (if i < 38 then [30] else [0, 2])))) else (if i < 46 then (if i < 42 then (if i < 40 then [3, 31] else (if i < 41 then [4, 16] else [14])) else (if i < 44 then (if i < 43 then [30, 36] else [0, 31]) else (if i < 45 then [3, 28] else [14]))) else (if i < 49 then (if i < 47 then [16] else (if i < 48 then [2, 4] else [])) else (if i < 51 then (if i < 50 then [30, 32, 39] else [4, 16]) else (if i < 52 then [2, 3] else [])))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then [28] else (if i < 55 then [0, 31] else [17])) else (if i < 57 then [14] else (if i < 58 then [3, 4, 7] else [16, 30]))) else (if i < 62 then (if i < 60 then [0] else (if i < 61 then [28] else [2])) else (if i < 64 then (if i < 63 then [14, 31] else [17]) else (if i < 65 then [5, 16, 30] else [3, 28])))) else (if i < 72 then (if i < 69 then (if i < 67 then [4] else (if i < 68 then [2, 17] else [0])) else (if i < 70 then [31] else (if i < 71 then [18] else [0, 13, 31]))) else (if i < 75 then (if i < 73 then [30] else (if i < 74 then [3, 4] else [2])) else (if i < 77 then (if i < 76 then [16] else []) else (if i < 78 then [28] else [17, 18]))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then [19, 30] else (if i < 81 then [4, 32] else [2, 41])) else (if i < 83 then [16, 18] else (if i < 84 then [0, 30, 35] else [0, 30]))) else (if i < 88 then (if i < 86 then [17] else (if i < 87 then [16, 31] else [])) else (if i < 90 then (if i < 89 then [28] else [2]) else (if i < 91 then [3, 4] else [])))) else (if i < 99 then (if i < 95 then (if i < 93 then [] else (if i < 94 then [28] else [31])) else (if i < 97 then (if i < 96 then [14] else [3, 14]) else (if i < 98 then [2, 16] else [25, 30]))) else (if i < 102 then (if i < 100 then [31] else (if i < 101 then [14] else [31])) else (if i < 104 then (if i < 103 then [16] else [18]) else (if i < 105 then [18] else [32]))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then [17, 28] else (if i < 108 then [] else [])) else (if i < 110 then [6, 32] else (if i < 111 then [2, 18] else [31]))) else (if i < 115 then (if i < 113 then [17, 21] else (if i < 114 then [11, 14] else [18, 31])) else (if i < 117 then (if i < 116 then [] else [16, 17]) else (if i < 118 then [9, 16] else [14, 31])))) else (if i < 125 then (if i < 122 then (if i < 120 then [2] else (if i < 121 then [17, 28, 37] else [30])) else (if i < 123 then [] else (if i < 124 then [] else [14]))) else (if i < 128 then (if i < 126 then [8] else (if i < 127 then [] else [])) else (if i < 130 then (if i < 129 then [17] else [16, 17]) else (if i < 131 then [17, 30] else []))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then [32] else (if i < 134 then [] else [18])) else (if i < 136 then [10, 30, 32] else (if i < 137 then [31] else []))) else (if i < 141 then (if i < 139 then [] else (if i < 140 then [18] else [18])) else (if i < 143 then (if i < 142 then [16, 30, 34] else [16]) else (if i < 144 then [17, 32] else [])))) else (if i < 152 then (if i < 148 then (if i < 146 then [28] else (if i < 147 then [30, 32] else [16])) else (if i < 150 then (if i < 149 then [17, 28] else []) else (if i < 151 then [28, 30] else [32]))) else (if i < 155 then (if i < 153 then [] else (if i < 154 then [] else [18, 40])) else (if i < 157 then (if i < 156 then [] else []) else (if i < 158 then [] else [])))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then [18] else (if i < 161 then [] else [])) else (if i < 163 then [] else (if i < 164 then [29] else [30, 33]))) else (if i < 168 then (if i < 166 then [32] else (if i < 167 then [] else [32])) else (if i < 170 then (if i < 169 then [] else [20]) else (if i < 171 then [17, 18] else [])))) else (if i < 179 then (if i < 175 then (if i < 173 then [] else (if i < 174 then [18] else [])) else (if i < 177 then (if i < 176 then [] else [32]) else (if i < 178 then [] else [24, 30, 32]))) else (if i < 182 then (if i < 180 then [] else (if i < 181 then [17] else [26, 32])) else (if i < 184 then (if i < 183 then [30, 32] else []) else (if i < 185 then [17] else []))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then [] else (if i < 188 then [17] else [])) else (if i < 190 then [18] else (if i < 191 then [18] else []))) else (if i < 195 then (if i < 193 then [] else (if i < 194 then [] else [])) else (if i < 197 then (if i < 196 then [] else []) else (if i < 198 then [] else [])))) else (if i < 206 then (if i < 202 then (if i < 200 then [] else (if i < 201 then [18] else [])) else (if i < 204 then (if i < 203 then [] else []) else (if i < 205 then [] else [18]))) else (if i < 209 then (if i < 207 then [] else (if i < 208 then [] else [])) else (if i < 211 then (if i < 210 then [] else []) else (if i < 212 then [] else [])))))))) else []

theorem kcList_eq (j : Fin 213) :
    kcList j = (List.finRange 42).filter fun k : Fin 42 => (kcMask j).testBit k.val := by
  revert j
  decide +kernel

/-- Weight `g` for each chain kid of node `j` not yet marked in `needC`. -/
def newW (g needC j : ℕ) : ℕ :=
  ((kcList j).map fun k : Fin 42 => if needC.testBit k.val then 1 else g).prod

theorem list_prod_map_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).prod = (l.map fun x => if p x then f x else 1).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      by_cases h : p x = true <;> simp [h, ih]

theorem newW_eq (g needC : ℕ) (j : Fin 213) :
    newW g needC j =
      ∏ k : Fin 42, if k ∈ kidsC j ∧ needC.testBit k = false then g else 1 := by
  rw [newW, kcList_eq, list_prod_map_filter, Fin.prod_univ_def]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  have hk := testBit_kcMask j k
  by_cases h1 : k ∈ kidsC j <;> by_cases h2 : needC.testBit k = true <;>
    simp_all

/-- Top-down sum over expanded sets.  An expansion pays `a` and `g` per newly
needed chain; a kept needed node pays `u`. -/
def dfs (a u g : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, need, needC =>
      if need.testBit n then
        u * dfs a u g n need needC +
          a * newW g needC n * dfs a u g n (need ||| khMask n) (needC ||| kcMask n)
      else dfs a u g n need needC

attribute [irreducible] dfs

/-- Neededness of a hash node under an initial mask and an expanded set. -/
def NdH (need : ℕ) (E : Finset (Fin 213)) (j : Fin 213) : Prop :=
  need.testBit j = true ∨ ∃ e ∈ E, j ∈ kidsH e

def NdC (needC : ℕ) (E : Finset (Fin 213)) (k : Fin 42) : Prop :=
  needC.testBit k = true ∨ ∃ e ∈ E, k ∈ kidsC e

instance (need : ℕ) (E : Finset (Fin 213)) (j : Fin 213) : Decidable (NdH need E j) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (needC : ℕ) (E : Finset (Fin 213)) (k : Fin 42) : Decidable (NdC needC E k) :=
  inferInstanceAs (Decidable (_ ∨ _))

def low (n : ℕ) : Finset (Fin 213) := Finset.univ.filter fun j => j.val < n

/-- Product weight of an expanded set among the nodes below `n`; zero when an
expanded node is not needed. -/
def wt (a u g need needC n : ℕ) (E : Finset (Fin 213)) : ℕ :=
  (∏ j ∈ low n, if j ∈ E then (if NdH need E j then a else 0)
    else (if NdH need E j then u else 1)) *
  ∏ k : Fin 42, if NdC needC E k ∧ needC.testBit k = false then g else 1

theorem dfs_eq (a u g : ℕ) : ∀ n, n ≤ 213 → ∀ need needC,
    dfs a u g n need needC = ∑ E ∈ (low n).powerset, wt a u g need needC n E
  | 0, _, need, needC => by
      have hlow : low 0 = ∅ := by
        ext j
        simp [low]
      rw [hlow, Finset.powerset_empty, Finset.sum_singleton, dfs, wt, hlow,
        Finset.prod_empty, one_mul]
      symm
      refine Finset.prod_eq_one fun k _ => if_neg ?_
      rintro ⟨h | ⟨e, he, _⟩, h'⟩
      · rw [h] at h'
        exact Bool.noConfusion h'
      · exact absurd he (Finset.notMem_empty e)
  | n + 1, hn, need, needC => by
      have ih := dfs_eq a u g n (by omega)
      let jn : Fin 213 := ⟨n, by omega⟩
      have hlow : low (n + 1) = insert jn (low n) := by
        ext j
        simp only [low, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          jn, Fin.ext_iff]
        omega
      have hnot : jn ∉ low n := by simp [low, jn]
      have hbelow : ∀ E ∈ (low n).powerset, ∀ e ∈ E, jn ∉ kidsH e := by
        intro E hE e he hk
        have he' := Finset.mem_powerset.1 hE he
        have h1 := kidsH_lt e jn hk
        simp only [low, Finset.mem_filter, Finset.mem_univ, true_and] at he'
        have h2 : n < e.val := h1
        omega
      have hself : jn ∉ kidsH jn := fun hk => lt_irrefl _ (kidsH_lt jn jn hk)
      have hE1 : ∀ E ∈ (low n).powerset, wt a u g need needC (n + 1) E =
          (if need.testBit n then u else 1) * wt a u g need needC n E := by
        intro E hE
        have hjE : jn ∉ E := fun h => hnot (Finset.mem_powerset.1 hE h)
        have hnd : NdH need E jn ↔ need.testBit n = true := by
          constructor
          · rintro (h | ⟨e, he, hk⟩)
            · exact h
            · exact absurd hk (hbelow E hE e he)
          · exact Or.inl
        unfold wt
        rw [hlow, Finset.prod_insert hnot, if_neg hjE]
        simp only [hnd]
        ring
      have hE2 : ∀ E ∈ (low n).powerset, wt a u g need needC (n + 1) (insert jn E) =
          ((if need.testBit n then a else 0) * newW g needC n) *
            wt a u g (need ||| khMask n) (needC ||| kcMask n) n E := by
        intro E hE
        have hnd : NdH need (insert jn E) jn ↔ need.testBit n = true := by
          constructor
          · rintro (h | ⟨e, he, hk⟩)
            · exact h
            · rcases Finset.mem_insert.1 he with rfl | he
              · exact absurd hk hself
              · exact absurd hk (hbelow E hE e he)
          · exact Or.inl
        have hndj : ∀ j : Fin 213,
            NdH need (insert jn E) j ↔ NdH (need ||| khMask n) E j := by
          intro j
          have hk := testBit_khMask jn j
          simp only [NdH, Finset.mem_insert, exists_eq_or_imp, Nat.testBit_or,
            Bool.or_eq_true]
          change _ ↔ (_ ∨ (khMask jn).testBit j = true) ∨ _
          rw [hk]
          tauto
        have hndc : ∀ k : Fin 42,
            (if NdC needC (insert jn E) k ∧ needC.testBit k = false then g else 1) =
              (if k ∈ kidsC jn ∧ needC.testBit k = false then g else 1) *
              (if NdC (needC ||| kcMask n) E k ∧
                (needC ||| kcMask n).testBit k = false then g else 1) := by
          intro k
          have hk : (kcMask n).testBit k = true ↔ k ∈ kidsC jn := testBit_kcMask jn k
          simp only [NdC, Finset.mem_insert, exists_eq_or_imp, Nat.testBit_or]
          by_cases h1 : needC.testBit k = true <;> by_cases h2 : k ∈ kidsC jn <;>
            by_cases h3 : ∃ e ∈ E, k ∈ kidsC e <;> simp_all
        have hrest : ∀ j ∈ low n,
            (if j ∈ insert jn E then (if NdH need (insert jn E) j then a else 0)
              else (if NdH need (insert jn E) j then u else 1)) =
            (if j ∈ E then (if NdH (need ||| khMask n) E j then a else 0)
              else (if NdH (need ||| khMask n) E j then u else 1)) := by
          intro j hj
          have hne : j ≠ jn := fun h => hnot (h ▸ hj)
          simp only [Finset.mem_insert, hne, false_or, hndj]
        unfold wt
        rw [hlow, Finset.prod_insert hnot, if_pos (Finset.mem_insert_self _ _),
          Finset.prod_congr rfl hrest]
        have hnw : newW g needC n =
            ∏ k : Fin 42, if k ∈ kidsC jn ∧ needC.testBit k = false then g else 1 :=
          newW_eq g needC jn
        rw [Finset.prod_congr rfl fun k _ => hndc k, Finset.prod_mul_distrib, ← hnw]
        simp only [hnd]
        ring
      rw [hlow, Finset.sum_powerset_insert hnot, Finset.sum_congr rfl hE1,
        Finset.sum_congr rfl hE2, ← Finset.mul_sum, ← Finset.mul_sum, ← ih need needC,
        ← ih (need ||| khMask n) (needC ||| kcMask n), dfs]
      by_cases h : need.testBit n = true <;> simp [h]

theorem low_213 : low 213 = Finset.univ := by
  ext j
  simp [low]

theorem wt_top (a u g : ℕ) (E : Finset (Fin 213)) :
    wt a u g topMask 0 213 E = if ShapeValid E then
      a ^ E.card * u ^ (neededH E \ E).card * g ^ (neededC E).card else 0 := by
  have hH : ∀ j, NdH topMask E j ↔ j ∈ neededH E := by
    intro j
    simp only [NdH, testBit_topMask, neededH, Finset.mem_union, Finset.mem_biUnion]
  have hC : ∀ k : Fin 42, (NdC 0 E k ∧ Nat.testBit 0 k = false) ↔ k ∈ neededC E := by
    intro k
    simp [NdC, neededC]
  unfold wt
  simp only [hH, hC, low_213]
  rw [Finset.prod_ite, Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const, Finset.prod_const]
  have hsd : (Finset.univ.filter fun j => j ∉ E) ∩ neededH E = neededH E \ E := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    tauto
  have hE : (Finset.univ.filter fun j => j ∈ E) = E := by
    ext j
    simp
  rw [hsd, hE]
  split_ifs with hv
  · rw [Finset.prod_congr rfl fun j hj => if_pos (hv hj), Finset.prod_const]
  · obtain ⟨j, hj, hjn⟩ := Finset.not_subset.1 hv
    rw [Finset.prod_eq_zero hj (if_neg hjn), zero_mul, zero_mul]

theorem sum_validShapes_eq_dfs (a u g : ℕ) :
    ∑ E ∈ validShapes, a ^ E.card * u ^ (neededH E \ E).card * g ^ (neededC E).card =
      dfs a u g 213 topMask 0 := by
  rw [dfs_eq a u g 213 le_rfl, low_213, Finset.powerset_univ, validShapes, Finset.sum_filter]
  exact Finset.sum_congr rfl fun E _ => (wt_top a u g E).symm

/-! ## Merged-state evaluation of `dfs`

`dfs` depends only on the bits of `need` below the current level and on the
chain bits that nodes below the level can still read (`chainMask n`).  A
forward pass keeps a list of weighted states, prunes those bits, and merges
equal states; the recursion collapses to at most 255 states per
level. -/

/-- Chain bits read by the nodes below level `n`. -/
def chainMask (i : ℕ) : ℕ :=
  if i < 214 then (if i < 107 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 4299161601 else 4299210757)) else (if i < 4 then 6446694405 else (if i < 5 then 7788871685 else 7788937229))) else (if i < 9 then (if i < 7 then 7788937245 else (if i < 8 then 7923154973 else 7923154973)) else (if i < 11 then (if i < 10 then 282801061917 else 282801061917) else (if i < 12 then 282801061917 else 282801061917)))) else (if i < 19 then (if i < 16 then (if i < 14 then 282801061917 else (if i < 15 then 282801061917 else 282801061917)) else (if i < 17 then 282801061917 else (if i < 18 then 282801061917 else 282801061917))) else (if i < 22 then (if i < 20 then 282801061919 else (if i < 21 then 282801066015 else 282801066015)) else (if i < 24 then (if i < 23 then 282801066015 else 282801066015) else (if i < 25 then 282801066015 else 282801066015))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 282801066015 else (if i < 28 then 282801066015 else 282801066015)) else (if i < 30 then 282801066015 else (if i < 31 then 282801066015 else 282801066015))) else (if i < 35 then (if i < 33 then 282801066015 else (if i < 34 then 282801066015 else 282801066015)) else (if i < 37 then (if i < 36 then 282801066015 else 282801066015) else (if i < 38 then 282809454623 else 282809454623)))) else (if i < 46 then (if i < 42 then (if i < 40 then 282809454623 else (if i < 41 then 282809454623 else 282809454623)) else (if i < 44 then (if i < 43 then 282809454623 else 351528931359) else (if i < 45 then 351528931359 else 351528931359))) else (if i < 49 then (if i < 47 then 351528931359 else (if i < 48 then 351528931359 else 351528931359)) else (if i < 51 then (if i < 50 then 351528931359 else 901284745247) else (if i < 52 then 901284745247 else 901284745247)))))) else (if i < 80 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then 901284745247 else (if i < 55 then 901284745247 else 901284745247)) else (if i < 57 then 901284876319 else (if i < 58 then 901284876319 else 901284876447))) else (if i < 62 then (if i < 60 then 901284876447 else (if i < 61 then 901284876447 else 901284876447)) else (if i < 64 then (if i < 63 then 901284876447 else 901284876447) else (if i < 65 then 901284876447 else 901284876479)))) else (if i < 73 then (if i < 69 then (if i < 67 then 901284876479 else (if i < 68 then 901284876479 else 901284876479)) else (if i < 71 then (if i < 70 then 901284876479 else 901284876479) else (if i < 72 then 901285138623 else 901285146815))) else (if i < 76 then (if i < 74 then 901285146815 else (if i < 75 then 901285146815 else 901285146815)) else (if i < 78 then (if i < 77 then 901285146815 else 901285146815) else (if i < 79 then 901285146815 else 901285146815))))) else (if i < 93 then (if i < 86 then (if i < 83 then (if i < 81 then 901285671103 else (if i < 82 then 901285671103 else 3100308926655)) else (if i < 84 then 3100308926655 else (if i < 85 then 3134668665023 else 3134668665023))) else (if i < 89 then (if i < 87 then 3134668665023 else (if i < 88 then 3134668665023 else 3134668665023)) else (if i < 91 then (if i < 90 then 3134668665023 else 3134668665023) else (if i < 92 then 3134668665023 else 3134668665023)))) else (if i < 100 then (if i < 96 then (if i < 94 then 3134668665023 else (if i < 95 then 3134668665023 else 3134668665023)) else (if i < 98 then (if i < 97 then 3134668665023 else 3134668665023) else (if i < 99 then 3134668665023 else 3134702219455))) else (if i < 103 then (if i < 101 then 3134702219455 else (if i < 102 then 3134702219455 else 3134702219455)) else (if i < 105 then (if i < 104 then 3134702219455 else 3134702219455) else (if i < 106 then 3134702219455 else 3134702219455))))))) else (if i < 160 then (if i < 133 then (if i < 120 then (if i < 113 then (if i < 110 then (if i < 108 then 3134702219455 else (if i < 109 then 3134702219455 else 3134702219455)) else (if i < 111 then 3134702219519 else (if i < 112 then 3134702219519 else 3134702219519))) else (if i < 116 then (if i < 114 then 3134704316671 else (if i < 115 then 3134704318719 else 3134704318719)) else (if i < 118 then (if i < 117 then 3134704318719 else 3134704318719) else (if i < 119 then 3134704319231 else 3134704319231)))) else (if i < 126 then (if i < 123 then (if i < 121 then 3134704319231 else (if i < 122 then 3272143272703 else 3272143272703)) else (if i < 124 then 3272143272703 else (if i < 125 then 3272143272703 else 3272143272703))) else (if i < 129 then (if i < 127 then 3272143272959 else (if i < 128 then 3272143272959 else 3272143272959)) else (if i < 131 then (if i < 130 then 3272143272959 else 3272143272959) else (if i < 132 then 3272143272959 else 3272143272959))))) else (if i < 146 then (if i < 139 then (if i < 136 then (if i < 134 then 3272143272959 else (if i < 135 then 3272143272959 else 3272143272959)) else (if i < 137 then 3272143273983 else (if i < 138 then 3272143273983 else 3272143273983))) else (if i < 142 then (if i < 140 then 3272143273983 else (if i < 141 then 3272143273983 else 3272143273983)) else (if i < 144 then (if i < 143 then 3289323143167 else 3289323143167) else (if i < 145 then 3289323143167 else 3289323143167)))) else (if i < 153 then (if i < 149 then (if i < 147 then 3289323143167 else (if i < 148 then 3289323143167 else 3289323143167)) else (if i < 151 then (if i < 150 then 3289323143167 else 3289323143167) else (if i < 152 then 3289323143167 else 3289323143167))) else (if i < 156 then (if i < 154 then 3289323143167 else (if i < 155 then 3289323143167 else 4388834770943)) else (if i < 158 then (if i < 157 then 4388834770943 else 4388834770943) else (if i < 159 then 4388834770943 else 4388834770943)))))) else (if i < 187 then (if i < 173 then (if i < 166 then (if i < 163 then (if i < 161 then 4388834770943 else (if i < 162 then 4388834770943 else 4388834770943)) else (if i < 164 then 4388834770943 else (if i < 165 then 4389371641855 else 4397961576447))) else (if i < 169 then (if i < 167 then 4397961576447 else (if i < 168 then 4397961576447 else 4397961576447)) else (if i < 171 then (if i < 170 then 4397961576447 else 4397962625023) else (if i < 172 then 4397962625023 else 4397962625023)))) else (if i < 180 then (if i < 176 then (if i < 174 then 4397962625023 else (if i < 175 then 4397962625023 else 4397962625023)) else (if i < 178 then (if i < 177 then 4397962625023 else 4397962625023) else (if i < 179 then 4397962625023 else 4397979402239))) else (if i < 183 then (if i < 181 then 4397979402239 else (if i < 182 then 4397979402239 else 4398046511103)) else (if i < 185 then (if i < 184 then 4398046511103 else 4398046511103) else (if i < 186 then 4398046511103 else 4398046511103))))) else (if i < 200 then (if i < 193 then (if i < 190 then (if i < 188 then 4398046511103 else (if i < 189 then 4398046511103 else 4398046511103)) else (if i < 191 then 4398046511103 else (if i < 192 then 4398046511103 else 4398046511103))) else (if i < 196 then (if i < 194 then 4398046511103 else (if i < 195 then 4398046511103 else 4398046511103)) else (if i < 198 then (if i < 197 then 4398046511103 else 4398046511103) else (if i < 199 then 4398046511103 else 4398046511103)))) else (if i < 207 then (if i < 203 then (if i < 201 then 4398046511103 else (if i < 202 then 4398046511103 else 4398046511103)) else (if i < 205 then (if i < 204 then 4398046511103 else 4398046511103) else (if i < 206 then 4398046511103 else 4398046511103))) else (if i < 210 then (if i < 208 then 4398046511103 else (if i < 209 then 4398046511103 else 4398046511103)) else (if i < 212 then (if i < 211 then 4398046511103 else 4398046511103) else (if i < 213 then 4398046511103 else 4398046511103)))))))) else 4398046511103

theorem chainMask_succ (j : Fin 213) :
    chainMask (j.val + 1) = chainMask j.val ||| kcMask j.val := by
  revert j
  decide +kernel

theorem newW_congr (g y y' n : ℕ) (hn : n < 213)
    (h : ∀ k, (kcMask n).testBit k = true → y.testBit k = y'.testBit k) :
    newW g y n = newW g y' n := by
  have e1 : newW g y n = _ := newW_eq g y ⟨n, hn⟩
  have e2 : newW g y' n = _ := newW_eq g y' ⟨n, hn⟩
  rw [e1, e2]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ kidsC ⟨n, hn⟩
  · rw [h k ((testBit_kcMask ⟨n, hn⟩ k).2 hk)]
  · simp [hk]

theorem dfs_congr (a u g : ℕ) : ∀ n, n ≤ 213 → ∀ x x' y y' : ℕ,
    (∀ k < n, x.testBit k = x'.testBit k) →
    (∀ k, (chainMask n).testBit k = true → y.testBit k = y'.testBit k) →
    dfs a u g n x y = dfs a u g n x' y'
  | 0, _, _, _, _, _, _, _ => by rw [dfs, dfs]
  | n + 1, hn, x, x', y, y', hx, hy => by
      have hcm : ∀ k, (chainMask (n + 1)).testBit k =
          ((chainMask n).testBit k || (kcMask n).testBit k) := fun k => by
        rw [chainMask_succ ⟨n, by omega⟩, Nat.testBit_or]
      have hx' : ∀ k < n, x.testBit k = x'.testBit k := fun k hk => hx k (by omega)
      have hy' : ∀ k, (chainMask n).testBit k = true → y.testBit k = y'.testBit k :=
        fun k hk => hy k (by rw [hcm, hk, Bool.true_or])
      have h1 := dfs_congr a u g n (by omega) x x' y y' hx' hy'
      have h2 := dfs_congr a u g n (by omega) (x ||| khMask n) (x' ||| khMask n)
        (y ||| kcMask n) (y' ||| kcMask n)
        (fun k hk => by rw [Nat.testBit_or, Nat.testBit_or, hx' k hk])
        (fun k hk => by rw [Nat.testBit_or, Nat.testBit_or, hy' k hk])
      have h3 := newW_congr g y y' n (by omega)
        (fun k hk => hy k (by rw [hcm, hk, Bool.or_true]))
      rw [dfs, dfs, hx n (by omega), h1, h2, h3]

abbrev DfsState := ℕ × ℕ × ℕ

/-- Weighted value of a state list `(need, needC, weight)` at level `n`. -/
def stVal (a u g n : ℕ) (L : List DfsState) : ℕ :=
  (L.map fun s => s.2.2 * dfs a u g n s.1 s.2.1).sum

theorem stVal_cons (a u g n : ℕ) (s : DfsState) (L : List DfsState) :
    stVal a u g n (s :: L) = s.2.2 * dfs a u g n s.1 s.2.1 + stVal a u g n L := by
  simp [stVal]

def stStops (u n : ℕ) : List DfsState → List DfsState
  | [] => []
  | (x, y, w) :: L =>
      (x, y, if x.testBit n then w * u else w) :: stStops u n L

def stExpands (a g n : ℕ) : List DfsState → List DfsState
  | [] => []
  | (x, y, w) :: L =>
      if x.testBit n then
        (x ||| khMask n, y ||| kcMask n, w * (a * newW g y n)) :: stExpands a g n L
      else stExpands a g n L

def stStep (a u g n : ℕ) (L : List DfsState) : List DfsState :=
  stStops u n L ++ stExpands a g n L

theorem stVal_append (a u g n : ℕ) (L K : List DfsState) :
    stVal a u g n (L ++ K) = stVal a u g n L + stVal a u g n K := by
  simp [stVal, List.map_append, List.sum_append]

theorem stVal_split (a u g n : ℕ) (L : List DfsState) :
    stVal a u g (n + 1) L =
      stVal a u g n (stStops u n L) + stVal a u g n (stExpands a g n L) := by
  induction L with
  | nil => rfl
  | cons s L ih =>
      obtain ⟨x, y, w⟩ := s
      rw [stVal_cons, ih, dfs, stStops, stExpands, stVal_cons]
      by_cases h : x.testBit n = true
      · simp only [h, ↓reduceIte, stVal_cons]
        ring
      · simp only [h, ↓reduceIte, stVal_cons, Bool.false_eq_true]
        omega

theorem stVal_step (a u g n : ℕ) (L : List DfsState) :
    stVal a u g (n + 1) L = stVal a u g n (stStep a u g n L) := by
  rw [stStep, stVal_append, stVal_split]


def stIns (e : DfsState) : List DfsState → List DfsState
  | [] => [e]
  | f :: L => if e.1 = f.1 ∧ e.2.1 = f.2.1 then (f.1, f.2.1, e.2.2 + f.2.2) :: L
      else f :: stIns e L

theorem stVal_ins (a u g n : ℕ) (e : DfsState) (L : List DfsState) :
    stVal a u g n (stIns e L) = e.2.2 * dfs a u g n e.1 e.2.1 + stVal a u g n L := by
  induction L with
  | nil => simp [stIns, stVal]
  | cons f L ih =>
      rw [stIns]
      split_ifs with h
      · obtain ⟨h1, h2⟩ := h
        rw [stVal_cons, stVal_cons, h1, h2]
        dsimp only
        ring
      · rw [stVal_cons, stVal_cons, ih]
        ring

def stCombine (e : DfsState) : List DfsState → List DfsState
  | [] => [e]
  | f :: L =>
      if e.1 = f.1 ∧ e.2.1 = f.2.1 then
        stCombine (f.1, f.2.1, e.2.2 + f.2.2) L
      else e :: stCombine f L

theorem stVal_combine (a u g n : ℕ) (e : DfsState) (L : List DfsState) :
    stVal a u g n (stCombine e L) =
      e.2.2 * dfs a u g n e.1 e.2.1 + stVal a u g n L := by
  induction L generalizing e with
  | nil => simp [stCombine, stVal]
  | cons f L ih =>
      rw [stCombine]
      split_ifs with h
      · obtain ⟨h1, h2⟩ := h
        rw [ih, stVal_cons, h1, h2]
        dsimp only
        ring
      · rw [stVal_cons, stVal_cons, ih]

def stOrder (e f : DfsState) : Bool :=
  e.1 < f.1 || (e.1 == f.1 && e.2.1 ≤ f.2.1)

def stJoin : ℕ → List DfsState → List DfsState → List DfsState
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      if x.1 = y.1 ∧ x.2.1 = y.2.1 then
        (x.1, x.2.1, x.2.2 + y.2.2) :: stJoin fuel xs ys
      else if stOrder x y then x :: stJoin fuel xs (y :: ys)
      else y :: stJoin fuel (x :: xs) ys

theorem stVal_join (a u g n fuel : ℕ) (xs ys : List DfsState) :
    stVal a u g n (stJoin fuel xs ys) = stVal a u g n xs + stVal a u g n ys := by
  induction fuel generalizing xs ys with
  | zero => simp [stJoin, stVal]
  | succ fuel ih =>
      cases xs with
      | nil => simp [stJoin, stVal]
      | cons x xs =>
          cases ys with
          | nil => simp [stJoin, stVal]
          | cons y ys =>
              rw [stJoin]
              split_ifs with h ho
              · obtain ⟨h1, h2⟩ := h
                simp only [stVal_cons, ih, h1, h2]
                ring
              · simp only [stVal_cons, ih]
                omega
              · simp only [stVal_cons, ih]
                omega

def stPairRuns : List (List DfsState) → List (List DfsState)
  | x :: y :: rest => stJoin (x.length + y.length) x y :: stPairRuns rest
  | runs => runs

def stTotal (a u g n : ℕ) (runs : List (List DfsState)) : ℕ :=
  (runs.map (stVal a u g n)).sum

theorem stTotal_pair (a u g n : ℕ) : ∀ runs,
    stTotal a u g n (stPairRuns runs) = stTotal a u g n runs
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
      simp only [stPairRuns, stTotal, List.map_cons, List.sum_cons]
      rw [stVal_join, ← stTotal, stTotal_pair, stTotal]
      omega

theorem stVal_flatten (a u g n : ℕ) (runs : List (List DfsState)) :
    stVal a u g n runs.flatten = stTotal a u g n runs := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
      simpa [stVal, stTotal, List.sum_append] using ih

def stSortRuns : ℕ → List (List DfsState) → List DfsState
  | 0, runs => runs.flatten
  | _ + 1, [] => []
  | _ + 1, [run] => run
  | fuel + 1, runs => stSortRuns fuel (stPairRuns runs)

theorem stVal_sortRuns (a u g n fuel : ℕ) (runs : List (List DfsState)) :
    stVal a u g n (stSortRuns fuel runs) = stTotal a u g n runs := by
  induction fuel generalizing runs with
  | zero => exact stVal_flatten a u g n runs
  | succ fuel ih =>
      cases runs with
      | nil => rfl
      | cons run rest =>
          cases rest with
          | nil => simp [stSortRuns, stTotal]
          | cons run' rest => rw [stSortRuns, ih, stTotal_pair] <;> simp

def stRunsAux (prev : DfsState) (acc : List DfsState) :
    List DfsState → List (List DfsState)
  | [] => [(prev :: acc).reverse]
  | e :: L => if stOrder prev e then stRunsAux e (prev :: acc) L
      else (prev :: acc).reverse :: stRunsAux e [] L

theorem stVal_reverse (a u g n : ℕ) (L : List DfsState) :
    stVal a u g n L.reverse = stVal a u g n L := by
  simp [stVal, List.map_reverse, List.sum_reverse]

theorem stTotal_runsAux (a u g n : ℕ) (prev : DfsState) (acc L : List DfsState) :
    stTotal a u g n (stRunsAux prev acc L) =
      stVal a u g n (prev :: acc) + stVal a u g n L := by
  induction L generalizing prev acc with
  | nil => simp [stRunsAux, stTotal, stVal, Nat.add_comm]
  | cons e L ih =>
      rw [stRunsAux]
      split
      · rw [ih]
        simp only [stVal_cons]
        omega
      · change stVal a u g n ((prev :: acc).reverse) +
          stTotal a u g n (stRunsAux e [] L) = _
        rw [stVal_reverse, ih]
        simp only [stVal_cons]
        have hz : stVal a u g n [] = 0 := rfl
        rw [hz]
        omega

def stRuns : List DfsState → List (List DfsState)
  | [] => []
  | e :: L => stRunsAux e [] L

theorem stTotal_runs (a u g n : ℕ) (L : List DfsState) :
    stTotal a u g n (stRuns L) = stVal a u g n L := by
  cases L with
  | nil => rfl
  | cons e L =>
      rw [stRuns, stTotal_runsAux, stVal_cons, stVal_cons]
      simp [stVal]

def stSort (L : List DfsState) : List DfsState :=
  stSortRuns L.length (stRuns L)

theorem stVal_sort (a u g n : ℕ) (L : List DfsState) :
    stVal a u g n (stSort L) = stVal a u g n L := by
  rw [stSort, stVal_sortRuns]
  exact stTotal_runs a u g n L

def stMerge (L : List DfsState) : List DfsState :=
  match stSort L with
  | [] => []
  | e :: rest => stCombine e rest

theorem stVal_merge (a u g n : ℕ) (L : List DfsState) :
    stVal a u g n (stMerge L) = stVal a u g n L := by
  rw [← stVal_sort a u g n L]
  cases h : stSort L with
  | nil => simp only [stMerge, h]
  | cons e rest => simp only [stMerge, h, stVal_combine, stVal_cons]

example : stMerge [(4, 2, 7), (1, 3, 4), (4, 2, 9)] =
    [(1, 3, 4), (4, 2, 16)] := by decide +kernel


def stPrune (n : ℕ) (L : List DfsState) : List DfsState :=
  L.map fun s => (s.1 % 2 ^ n, s.2.1 &&& chainMask n, s.2.2)

theorem stVal_prune (a u g n : ℕ) (hn : n ≤ 213) (L : List DfsState) :
    stVal a u g n (stPrune n L) = stVal a u g n L := by
  simp only [stVal, stPrune, List.map_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [Function.comp_apply]
  rw [dfs_congr a u g n hn (s.1 % 2 ^ n) s.1 (s.2.1 &&& chainMask n) s.2.1
    (fun k hk => by simp [Nat.testBit_mod_two_pow, hk])
    (fun k hk => by simp [Nat.testBit_and, hk])]

def stRun (a u g : ℕ) : ℕ → List DfsState → List DfsState
  | 0, L => L
  | n + 1, L => stRun a u g n (stMerge (stPrune n (stStep a u g n L)))

attribute [irreducible] stRun

theorem stVal_run (a u g : ℕ) : ∀ n, n ≤ 213 → ∀ L : List DfsState,
    stVal a u g n L = stVal a u g 0 (stRun a u g n L)
  | 0, _, _ => by rw [stRun]
  | n + 1, hn, L => by
      rw [stVal_step, stRun, ← stVal_run a u g n (by omega), stVal_merge,
        stVal_prune a u g n (by omega)]

theorem stVal_zero (a u g : ℕ) (L : List DfsState) :
    stVal a u g 0 L = (L.map fun s => s.2.2).sum := by
  induction L with
  | nil => rfl
  | cons s L ih => rw [stVal_cons, ih, dfs, mul_one, List.map_cons, List.sum_cons]

theorem dfs_top_eq_run (a u g : ℕ) :
    dfs a u g 213 topMask 0 = ((stRun a u g 213 [(topMask, 0, 1)]).map fun s => s.2.2).sum := by
  rw [← stVal_zero, ← stVal_run a u g 213 le_rfl, stVal_cons]
  simp [stVal]

def stClip (m : ℕ) : List DfsState → List DfsState
  | [] => []
  | s :: L => if s.2.2 % m = 0 then stClip m L
      else (s.1, s.2.1, s.2.2 % m) :: stClip m L

theorem stVal_clip (a u g n m : ℕ) (L : List DfsState) :
    stVal a u g n (stClip m L) % m = stVal a u g n L % m := by
  induction L with
  | nil => rfl
  | cons s L ih =>
      rw [stClip]
      split_ifs with h
      · rw [ih, stVal_cons]
        simp only [Nat.add_mod, Nat.mul_mod, h, Nat.zero_mul, Nat.zero_mod,
          Nat.zero_add, Nat.mod_mod]
      · rw [stVal_cons, stVal_cons]
        simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ih]

def stRunMod (m a u g : ℕ) : ℕ → List DfsState → List DfsState
  | 0, L => L
  | n + 1, L => stRunMod m a u g n (stMerge (stClip m (stPrune n (stStep a u g n L))))

attribute [irreducible] stRunMod

theorem stVal_runMod (m a u g : ℕ) : ∀ n, n ≤ 213 → ∀ L : List DfsState,
    stVal a u g n L % m = stVal a u g 0 (stRunMod m a u g n L) % m
  | 0, _, _ => by rw [stRunMod]
  | n + 1, hn, L => by
      rw [stVal_step, stRunMod, ← stVal_runMod m a u g n (by omega), stVal_merge,
        stVal_clip, stVal_prune a u g n (by omega)]

theorem dfs_top_mod (m a u g : ℕ) :
    dfs a u g 213 topMask 0 % m =
      ((stRunMod m a u g 213 [(topMask, 0, 1)]).map fun s => s.2.2).sum % m := by
  rw [← stVal_zero, ← stVal_runMod m a u g 213 le_rfl, stVal_cons]
  simp [stVal]

theorem dfs_top_digit_mod (a u g b d : ℕ) :
    dfs a u g 213 topMask 0 / b ^ d % b =
      (((stRunMod (b^(d+1)) a u g 213 [(topMask, 0, 1)]).map fun s => s.2.2).sum %
        b^(d+1)) / b^d := by
  rw [← Nat.mod_mul_right_div_self, ← pow_succ, dfs_top_mod]


theorem dfs_drop (a u g n k x y : ℕ) (hk : k ≤ n) (hx : x < 2^k) :
    dfs a u g n x y = dfs a u g k x y := by
  induction n with
  | zero =>
      have : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases hkn : k ≤ n
      · have hbit : x.testBit n = false := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hkn))
        rw [dfs, hbit]
        exact ih hkn
      · have : k = n + 1 := by omega
        subst k
        rfl

theorem dfs_jump (a u g n k x y : ℕ) (hn : n ≤ 213) (hk : k ≤ n)
    (hx : x % 2^n < 2^k) :
    dfs a u g n x y = dfs a u g k (x % 2^n) (y &&& chainMask k) := by
  calc
    dfs a u g n x y = dfs a u g n (x % 2^n) y :=
      dfs_congr a u g n hn _ _ _ _
        (fun i hi => by simp [Nat.testBit_mod_two_pow, hi]) (fun _ _ => rfl)
    _ = dfs a u g k (x % 2^n) y := dfs_drop a u g n k _ _ hk hx
    _ = dfs a u g k (x % 2^n) (y &&& chainMask k) :=
      dfs_congr a u g k (by omega) _ _ _ _ (fun _ _ => rfl)
        (fun i hi => by simp [Nat.testBit_and, hi])

def memoBounds (p n x y kl kr xl yl xr yr : ℕ) : Bool :=
  p == n+1 && n < 213 && kl ≤ n && kr ≤ n && x.testBit n &&
    xl == x % 2^n && yl == (y &&& chainMask kl) &&
    xr == (x ||| khMask n) % 2^n && yr == ((y ||| kcMask n) &&& chainMask kr) &&
    xl < 2^kl && xr < 2^kr

theorem memoBounds_sound (p n x y kl kr xl yl xr yr : ℕ)
    (h : memoBounds p n x y kl kr xl yl xr yr = true) :
    p = n+1 ∧ n < 213 ∧ kl ≤ n ∧ kr ≤ n ∧ x.testBit n = true ∧
      xl = x % 2^n ∧ yl = (y &&& chainMask kl) ∧
      xr = (x ||| khMask n) % 2^n ∧ yr = ((y ||| kcMask n) &&& chainMask kr) ∧
      xl < 2^kl ∧ xr < 2^kr := by
  simpa only [memoBounds, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    and_assoc] using h

theorem dfs_memo_step (m a g p n x y kl kr xl yl xr yr l r v : ℕ)
    (bounds : memoBounds p n x y kl kr xl yl xr yr = true)
    (left : dfs a 1 g kl xl yl % m = l)
    (right : dfs a 1 g kr xr yr % m = r)
    (arithmetic : (l + a * newW g y n * r) % m = v) :
    dfs a 1 g p x y % m = v := by
  obtain ⟨hp, hn, hkl, hkr, hb, hxl, hyl, hxr, hyr, hl, hr⟩ :=
    memoBounds_sound p n x y kl kr xl yl xr yr bounds
  subst p xl yl xr yr
  simp only [dfs, hb, ↓reduceIte, one_mul]
  rw [dfs_jump a 1 g n kl x y (by omega) hkl hl,
      dfs_jump a 1 g n kr (x ||| khMask n) (y ||| kcMask n) (by omega) hkr hr]
  calc
    _ = (l + a * newW g y n * r) % m := by
      simp only [Nat.add_mod, Nat.mul_mod, left, right, Nat.mod_mod]
    _ = v := arithmetic

structure DfsMemoKey where
  h : Nat
  c : Nat
deriving BEq

instance : Hashable DfsMemoKey where
  hash k := mixHash (mixHash (mixHash (mixHash
    (UInt64.ofNat k.h) (UInt64.ofNat (k.h >>> 64)))
    (UInt64.ofNat (k.h >>> 128))) (UInt64.ofNat (k.h >>> 192)))
    (UInt64.ofNat k.c)

theorem dfs_memo_h_congr (m a g n h h' c v : Nat) (hh : h = h')
    (proof : dfs a 1 g n h' c % m = v) : dfs a 1 g n h c % m = v := by
  subst h
  exact proof

open Lean Meta Elab Tactic in
def memoMaskExpr (h : Nat) : Expr :=
  if h == 0 then mkNatLit 0 else
    mkApp2 (mkConst ``Nat.shiftRight)
      (mkRawNatLit ((h <<< 64) + (hash (DfsMemoKey.mk h 0)).toNat)) (mkNatLit 64)

open Lean Meta Elab Tactic in
structure DfsMemoState where
  cache : Std.HashMap DfsMemoKey (Nat × Lean.Name) := {}
  entries : Nat := 0

open Lean Meta Elab Tactic in
partial def buildDfsMemo (m a g : Nat) (h c : Nat) :
    StateRefT DfsMemoState MetaM (Nat × Expr) := do
  if h == 0 then
    let v := 1 % m
    return (v, ← mkEqRefl (mkRawNatLit v))
  let n := h.log2 + 1
  let c := c &&& chainMask n
  if let some (v, name) := (← get).cache[DfsMemoKey.mk h c]? then
    return (v, mkConst name)
  let j := n - 1
  let lh := h % 2^j
  let rh := (h ||| khMask j) % 2^j
  let kl := if lh == 0 then 0 else lh.log2 + 1
  let kr := if rh == 0 then 0 else rh.log2 + 1
  let lc := c &&& chainMask kl
  let rc := (c ||| kcMask j) &&& chainMask kr
  let (l, lp) ← buildDfsMemo m a g lh c
  let (r, rp) ← buildDfsMemo m a g rh (c ||| kcMask j)
  let v := (l + a * newW g c j * r) % m
  -- A distinct low word gives each large literal a useful expression hash.
  -- Right-shifting removes it, so the kernel checks exactly the same Nat.
  let tag := (← get).entries + 1
  let ve := mkApp2 (mkConst ``Nat.shiftRight)
    (mkRawNatLit ((v <<< 64) + tag)) (mkNatLit 64)
  let le := (← inferType lp).getAppArgs[2]!
  let re := (← inferType rp).getAppArgs[2]!
  let args := (#[m,a,g,n,j,h,c,kl,kr,lh,lc,rh,rc].map mkNatLit)
    |>.set! 5 (memoMaskExpr h) |>.set! 9 (memoMaskExpr lh) |>.set! 11 (memoMaskExpr rh)
  let step := mkAppN (mkConst ``dfs_memo_step) (args ++ #[le,re,ve])
  let bp ← mkEqRefl (mkConst ``Bool.true)
  let ap ← mkEqRefl ve
  let proof := mkAppN step #[bp,lp,rp,ap]
  -- Preserve the helper's exact expression syntax. Rebuilding its remainder
  -- with `Nat.mod` would mismatch the elaborated `%` notation and can force
  -- the kernel to unfold a closed `dfs` while comparing premise types.
  let type ← inferType proof
  let name ← mkAuxDeclName (kind := `_dfs_memo)
  addDecl (.thmDecl {name := name, levelParams := [], type := type, value := proof})
  modify fun s => {cache := s.cache.insert ⟨h,c⟩ (v,name), entries := s.entries+1}
  return (v,mkConst name)

open Lean Meta Elab Tactic in
elab "memo_count" m:num a:num g:num h:num : tactic => do
  let ((_, proof), _) ← withOptions (Elab.async.set · false) do
    (buildDfsMemo m.getNat a.getNat g.getNat h.getNat 0).run {}
  let rhs := (← inferType proof).getAppArgs[2]!
  let heq ← mkEqRefl (mkRawNatLit h.getNat)
  let n := if h.getNat == 0 then 0 else h.getNat.log2 + 1
  let bridge := mkAppN (mkConst ``dfs_memo_h_congr)
    #[mkNatLit m.getNat, mkNatLit a.getNat, mkNatLit g.getNat, mkNatLit n,
      mkNatLit h.getNat, memoMaskExpr h.getNat, mkNatLit 0, rhs, heq, proof]
  closeMainGoalUsing `memo_count fun _ _ => pure bridge


/-! ## Structural disclosure bound -/

theorem shapeWords_le : ∀ E ∈ validShapes, shapeWords E ≤ 42 := by
  classical
  intro E hE
  let needed : Finset Kid := Finset.univ.filter (Needed E)
  have hcard : needed.card = (neededH E).card + (neededC E).card := by
    have heq : needed = (neededH E).image Kid.h ∪ (neededC E).image Kid.c := by
      ext x
      cases x <;> simp [needed]
    have hd : Disjoint ((neededH E).image Kid.h) ((neededC E).image Kid.c) := by
      simp [Finset.disjoint_left]
    rw [heq, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (fun _ _ h => Kid.h.inj h),
      Finset.card_image_of_injective _ (fun _ _ h => Kid.c.inj h)]
  have hinj : Function.Injective (fun j : Fin 213 => kid j 2) := by
    intro j k h
    exact ((kid_eq_kid_excl_iff j k 2).1 h).1
  have hsub : ((Finset.univ \ E).image fun j => kid j 2) ⊆
      (Finset.univ \ needed) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj ⊢
    simpa [needed, needed_kid_excl_iff] using hj
  have bound := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_sdiff_of_subset (Finset.subset_univ E),
    Finset.card_sdiff_of_subset (Finset.subset_univ needed)] at bound
  have cardK : Fintype.card Kid = 255 := by decide
  simp only [Finset.card_univ, Fintype.card_fin, cardK, hcard] at bound
  have hv : E ⊆ neededH E := (mem_validShapes E).1 hE
  have hEc := Finset.card_le_card hv
  have hNc : needed.card ≤ 255 := by
    simpa only [Finset.card_univ, cardK] using
      Finset.card_le_card (Finset.subset_univ needed)
  rw [hcard] at hNc
  rw [shapeWords, Finset.card_sdiff_of_subset hv]
  omega


/-! ## Base-`B` digit counting -/

/-- Digit `n` of `∑ B ^ e x` counts the elements with exponent `n`, provided
the finset has fewer than `B` elements. -/
theorem digit_sum_pow {ι : Type*} (T : Finset ι) (e : ι → ℕ) {B : ℕ} (n : ℕ)
    (hB : T.card < B) :
    (∑ x ∈ T, B ^ e x) / B ^ n % B = (T.filter fun x => e x = n).card := by
  have hB0 : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hB
  let lo : ι → ℕ := fun x => if e x < n then B ^ e x else 0
  let mid : ι → ℕ := fun x => if e x = n then 1 else 0
  let hi : ι → ℕ := fun x => if n < e x then B ^ (e x - n - 1) else 0
  have hpt : ∀ x, B ^ e x = lo x + B ^ n * (mid x + B * hi x) := by
    intro x
    rcases lt_trichotomy (e x) n with h | h | h
    · simp [lo, mid, hi, h, h.ne, not_lt.2 h.le]
    · simp [lo, mid, hi, h]
    · have h1 : ¬ e x < n := by omega
      have h2 : e x ≠ n := by omega
      simp only [lo, mid, hi, h1, h2, h, if_false, if_true, zero_add]
      rw [← mul_assoc, ← pow_succ, ← pow_add]
      congr 1
      omega
  have hsum : ∑ x ∈ T, B ^ e x =
      (∑ x ∈ T, lo x) + B ^ n * ((∑ x ∈ T, mid x) + B * ∑ x ∈ T, hi x) := by
    rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmid : ∑ x ∈ T, mid x = (T.filter fun x => e x = n).card := by
    simp only [mid]
    rw [Finset.sum_boole]
    simp
  have hlo : ∑ x ∈ T, lo x < B ^ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : ∑ x ∈ T, lo x = 0 :=
        Finset.sum_eq_zero fun x _ => by simp [lo]
      rw [this]
      simp
    · have hle : ∀ x ∈ T, lo x ≤ B ^ (n - 1) := by
        intro x _
        simp only [lo]
        split_ifs with h
        · exact Nat.pow_le_pow_right hB0 (by omega)
        · exact Nat.zero_le _
      calc ∑ x ∈ T, lo x ≤ T.card * B ^ (n - 1) := by
            simpa using Finset.sum_le_sum hle
        _ < B * B ^ (n - 1) :=
            Nat.mul_lt_mul_of_pos_right hB (pow_pos hB0 _)
        _ = B ^ n := by
            rw [← pow_succ']
            congr 1
            omega
  have hmidB : (T.filter fun x => e x = n).card < B :=
    lt_of_le_of_lt (Finset.card_filter_le _ _) hB
  rw [hsum, Nat.add_mul_div_left _ _ (pow_pos hB0 _),
    Nat.div_eq_of_lt hlo, zero_add, hmid, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hmidB]

/-- A shape discloses a word: a top when nothing is expanded, else the
exclusive kid of the lowest expanded node. -/
theorem shapeWords_pos : ∀ E ∈ validShapes, 1 ≤ shapeWords E := by
  intro E _
  unfold shapeWords
  rcases E.eq_empty_or_nonempty with rfl | hne
  · have h : (48 : Fin 213) ∈ neededH ∅ \ ∅ := by simp [neededH, topSet]
    have := Finset.card_pos.2 ⟨_, h⟩
    omega
  · have he : E.min' hne ∈ E := E.min'_mem hne
    cases hk : kid (E.min' hne) 2 with
    | c k =>
        have h : k ∈ neededC E := (mem_neededC E k).2 (Or.inr ⟨_, he, 2, hk⟩)
        have := Finset.card_pos.2 ⟨k, h⟩
        omega
    | h j =>
        have hjE : j ∉ E := fun h => absurd (E.min'_le j h) (not_le.2 (kid_h_lt hk))
        have h : j ∈ neededH E \ E :=
          Finset.mem_sdiff.2 ⟨(mem_neededH E j).2 (Or.inr ⟨_, he, 2, hk⟩), hjE⟩
        have := Finset.card_pos.2 ⟨j, h⟩
        omega

/-! ## Per-block and full choices -/

/-- A block choice: expanded hash nodes and one position per local chain. -/
abbrev Local := Finset (Fin 213) × (Fin 42 → Fin 25)

def localWords (v : Local) : ℕ := shapeWords v.1

def localChainCost (v : Local) : ℕ := ∑ k ∈ neededC v.1, (24 - (v.2 k).val)

/-- Block reconstruction cost: one compression per expanded hash node plus
the walked chain suffixes. -/
def localCost (v : Local) : ℕ := v.1.card + localChainCost v

/-- Allowed positions: free on needed chains, fixed to `24` elsewhere. -/
def posSet (E : Finset (Fin 213)) (k : Fin 42) : Finset (Fin 25) :=
  if k ∈ neededC E then Finset.univ else {24}

def localSet : Finset Local :=
  (validShapes.sigma fun E => Fintype.piFinset (posSet E)).map
    (Equiv.sigmaEquivProd _ _).toEmbedding

attribute [irreducible] localSet

theorem mem_localSet (v : Local) : v ∈ localSet ↔
    ShapeValid v.1 ∧ ∀ k, k ∉ neededC v.1 → v.2 k = 24 := by
  rw [localSet]
  constructor
  · intro h
    obtain ⟨⟨E, p⟩, hx, rfl⟩ := Finset.mem_map.1 h
    obtain ⟨hE, hp⟩ := Finset.mem_sigma.1 hx
    refine ⟨(mem_validShapes E).1 hE, fun k hk => ?_⟩
    have := Fintype.mem_piFinset.1 hp k
    have hk' : ¬ Needed E (.c k) := by simpa using hk
    simpa [posSet, hk'] using this
  · rintro ⟨hE, hp⟩
    refine Finset.mem_map.2 ⟨⟨v.1, v.2⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
    · exact (mem_validShapes _).2 hE
    · refine Fintype.mem_piFinset.2 fun k => ?_
      by_cases hk : k ∈ neededC v.1
      · simp [posSet, hk]
      · simp [posSet, hk, hp k hk]

/-- A full choice: one block choice per block. -/
abbrev Choice := Fin 1 → Local

def choiceCost (c : Choice) : ℕ := ∑ b, localCost (c b)

def choiceWords (c : Choice) : ℕ := ∑ b, localWords (c b)

/-- Root cost plus the block costs. -/
def reconstructionCost (c : Choice) : ℕ := 3 + choiceCost c

def choiceTuples : Finset Choice := Fintype.piFinset fun _ : Fin 1 => localSet

theorem mem_choiceTuples (c : Choice) : c ∈ choiceTuples ↔ ∀ b, c b ∈ localSet := by
  rw [choiceTuples, Fintype.mem_piFinset]

/-- The supported layer: valid blocks and graph cost exactly 86. -/
def supportedChoices : Finset Choice :=
  choiceTuples.filter fun c => choiceCost c = 82

attribute [irreducible] supportedChoices

theorem mem_supportedChoices (c : Choice) : c ∈ supportedChoices ↔
    (∀ b, c b ∈ localSet) ∧ choiceCost c = 82 := by
  rw [supportedChoices, Finset.mem_filter, mem_choiceTuples]

theorem shapeValid_of_supported {c : Choice} (hc : c ∈ supportedChoices) (b : Fin 1) :
    ShapeValid (c b).1 :=
  ((mem_localSet _).1 (((mem_supportedChoices c).1 hc).1 b)).1

theorem canonical_of_supported {c : Choice} (hc : c ∈ supportedChoices) (b : Fin 1)
    (k : Fin 42) (hk : k ∉ neededC (c b).1) : (c b).2 k = 24 :=
  ((mem_localSet _).1 (((mem_supportedChoices c).1 hc).1 b)).2 k hk

theorem reconstructionCost_eq {c : Choice} (hc : c ∈ supportedChoices) :
    reconstructionCost c = 85 := by
  rw [reconstructionCost, ((mem_supportedChoices c).1 hc).2]

theorem choiceWords_le {c : Choice} (hc : c ∈ supportedChoices) : choiceWords c ≤ 42 := by
  have h : ∀ b, localWords (c b) ≤ 42 := fun b =>
    shapeWords_le _ ((mem_validShapes _).2 (shapeValid_of_supported hc b))
  calc choiceWords c ≤ ∑ _b : Fin 1, 42 := Finset.sum_le_sum fun b _ => h b
    _ = 42 := by simp

/-! ## Cost generating number -/

/-- Digit base strictly exceeds the private-path upper bound on all canonical choices. -/
def digitBase : ℕ := 2 ^ 206

attribute [irreducible] digitBase

def blockGen : ℕ := ∑ v ∈ localSet, digitBase ^ localCost v

attribute [irreducible] blockGen

/-- Generating number of one needed chain: positions `24 - t` steps deep. -/
def chainGen : ℕ := ∑ t : Fin 25, digitBase ^ (24 - t.val)

theorem blockGen_eq : blockGen = dfs digitBase 1 chainGen 213 topMask 0 := by
  rw [← sum_validShapes_eq_dfs]
  unfold blockGen localSet
  rw [Finset.sum_map, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun E _ => ?_
  have hfac : ∀ p : Fin 42 → Fin 25,
      digitBase ^ localCost ((Equiv.sigmaEquivProd _ _).toEmbedding ⟨E, p⟩) =
        digitBase ^ E.card *
          ∏ k : Fin 42, (if k ∈ neededC E then digitBase ^ (24 - (p k).val) else 1) := by
    intro p
    simp only [Equiv.toEmbedding_apply, Equiv.sigmaEquivProd_apply, localCost,
      localChainCost]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow_eq_pow_sum, ← pow_add]
  rw [Finset.sum_congr rfl fun p _ => hfac p, ← Finset.mul_sum, one_pow, mul_one]
  congr 1
  refine (Finset.prod_univ_sum (posSet E) fun k (t : Fin 25) =>
    if k ∈ neededC E then digitBase ^ (24 - t.val) else 1).symm.trans ?_
  rw [← Finset.prod_const, show (∏ _k ∈ neededC E, chainGen) =
    ∏ k : Fin 42, (if k ∈ neededC E then chainGen else 1) by
      rw [Finset.prod_ite_mem, Finset.univ_inter]]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ neededC E
  · simp [posSet, hk, chainGen]
  · simp [posSet, hk]

theorem card_localSet_eq_dfs : localSet.card = dfs 1 1 25 213 topMask 0 := by
  rw [← sum_validShapes_eq_dfs]
  unfold localSet
  rw [Finset.card_map, Finset.card_sigma]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Fintype.card_piFinset]
  have hpos : ∀ k, (posSet E k).card = if k ∈ neededC E then 25 else 1 := by
    intro k
    by_cases hk : k ∈ neededC E <;> simp [posSet, hk]
  simp_rw [hpos]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  simp


def pathCode8 (b : Fin 8 → Bool) (p : Fin 25) : Nat :=
  (List.ofFn b).countP id + (24 - p.val)

def pathValid8 (n : Fin 9) (b : Fin 8 → Bool) (p : Fin 25) : Prop :=
  (∀ i, n.val ≤ i.val → b i = false) ∧
  (∀ i : Fin 7, i.val + 1 < n.val → b i.castSucc = true → b i.succ = true) ∧
  (0 < n.val → b 0 = false → p = 24)

instance (n b p) : Decidable (pathValid8 n b p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem pathCode8_decode : ∀ n b p, pathValid8 n b p →
    pathCode8 b p < n.val + 25 ∧
    (∀ i : Fin 8, b i = decide (i.val < n.val ∧ n.val ≤ pathCode8 b p + i.val)) ∧
    p.val = 24 - (pathCode8 b p - n.val) := by
  decide +kernel


def privatePathLen : Fin 42 → Fin 9 := ![0, 7, 0, 0, 0, 7, 8, 7, 7, 8, 7, 8, 7, 8, 0, 5, 0, 0, 0, 8, 6, 8, 6, 6, 8, 7, 7, 5, 0, 8, 0, 0, 0, 8, 7, 7, 7, 7, 6, 8, 7, 8]
def privatePathAt : Fin 42 → Fin 8 → Fin 213 := ![
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![18, 20, 22, 28, 29, 30, 31, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![64, 65, 66, 67, 68, 69, 70, 0],
  ![109, 110, 111, 115, 116, 124, 126, 127],
  ![57, 58, 59, 60, 61, 62, 63, 0],
  ![125, 128, 139, 183, 197, 198, 199, 0],
  ![117, 118, 119, 123, 130, 131, 132, 133],
  ![135, 140, 148, 149, 153, 160, 177, 0],
  ![113, 114, 122, 129, 137, 138, 145, 146],
  ![19, 21, 24, 32, 33, 34, 35, 0],
  ![71, 72, 73, 74, 75, 76, 77, 78],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 2, 3, 4, 5, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![79, 80, 96, 97, 99, 103, 106, 107],
  ![169, 170, 171, 172, 182, 194, 0, 0],
  ![112, 134, 136, 142, 144, 150, 151, 152],
  ![0, 7, 11, 13, 16, 17, 0, 0],
  ![36, 37, 38, 39, 40, 41, 0, 0],
  ![178, 188, 190, 191, 195, 206, 207, 208],
  ![98, 100, 101, 102, 104, 105, 108, 0],
  ![181, 184, 185, 186, 200, 203, 204, 0],
  ![6, 9, 12, 14, 15, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![163, 166, 167, 168, 180, 189, 192, 193],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![164, 165, 187, 201, 202, 205, 211, 212],
  ![141, 143, 156, 158, 159, 161, 162, 0],
  ![83, 86, 87, 88, 89, 90, 91, 0],
  ![42, 43, 44, 45, 46, 47, 48, 0],
  ![120, 121, 147, 173, 174, 175, 176, 0],
  ![8, 10, 23, 25, 26, 27, 0, 0],
  ![49, 50, 51, 52, 53, 54, 55, 56],
  ![154, 155, 157, 179, 196, 209, 210, 0],
  ![81, 82, 84, 85, 92, 93, 94, 95]]
def privatePathIndex : Fin 213 → Fin 42 := ![22, 15, 15, 15, 15, 15, 27, 22, 38, 27, 38, 22, 27, 22, 27, 27, 22, 22, 1, 12, 1, 12, 1, 38, 12, 38, 38, 38, 1, 1, 1, 1, 12, 12, 12, 12, 23, 23, 23, 23, 23, 23, 36, 36, 36, 36, 36, 36, 36, 39, 39, 39, 39, 39, 39, 39, 39, 7, 7, 7, 7, 7, 7, 7, 5, 5, 5, 5, 5, 5, 5, 13, 13, 13, 13, 13, 13, 13, 13, 19, 19, 41, 41, 35, 41, 41, 35, 35, 35, 35, 35, 35, 41, 41, 41, 41, 19, 19, 25, 19, 25, 25, 25, 19, 25, 25, 19, 19, 25, 6, 6, 6, 21, 11, 11, 6, 6, 9, 9, 9, 37, 37, 11, 9, 6, 8, 6, 6, 8, 11, 9, 9, 9, 9, 21, 10, 21, 11, 11, 8, 10, 34, 21, 34, 21, 11, 11, 37, 10, 10, 21, 21, 21, 10, 40, 40, 34, 40, 34, 34, 10, 34, 34, 29, 33, 33, 29, 29, 29, 20, 20, 20, 20, 37, 37, 37, 37, 10, 24, 40, 29, 26, 20, 8, 26, 26, 26, 33, 24, 29, 24, 24, 29, 29, 20, 24, 40, 8, 8, 8, 26, 33, 33, 26, 26, 33, 24, 24, 24, 40, 40, 33, 33]
def privatePathDepth : Fin 213 → Fin 8 := ![0, 0, 1, 2, 3, 4, 0, 1, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 0, 0, 1, 1, 2, 2, 2, 3, 4, 5, 3, 4, 5, 6, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 0, 1, 0, 2, 3, 1, 2, 3, 4, 5, 6, 4, 5, 6, 7, 2, 3, 0, 4, 1, 2, 3, 5, 4, 5, 6, 7, 6, 0, 1, 2, 0, 0, 1, 3, 4, 0, 1, 2, 0, 1, 2, 3, 5, 0, 6, 7, 1, 3, 4, 5, 6, 7, 1, 0, 2, 4, 5, 2, 1, 0, 3, 1, 4, 6, 7, 2, 2, 3, 5, 6, 7, 4, 0, 1, 2, 2, 3, 4, 5, 5, 6, 0, 0, 1, 1, 2, 3, 0, 1, 2, 3, 3, 4, 5, 6, 6, 0, 3, 4, 0, 4, 3, 1, 2, 3, 2, 1, 5, 2, 3, 6, 7, 5, 4, 4, 4, 5, 6, 4, 3, 4, 5, 6, 5, 5, 6, 7, 5, 6, 6, 7]

theorem privatePath_cover (j : Fin 213) :
    (privatePathDepth j).val < (privatePathLen (privatePathIndex j)).val ∧
    privatePathAt (privatePathIndex j) (privatePathDepth j) = j := by
  revert j
  decide +kernel

theorem privatePath_base (k : Fin 42) (h : 0 < (privatePathLen k).val) :
    kid (privatePathAt k 0) 2 = .c k := by
  revert k
  decide +kernel

theorem privatePath_next (k : Fin 42) (i : Fin 7)
    (h : i.val + 1 < (privatePathLen k).val) :
    kid (privatePathAt k i.succ) 2 = .h (privatePathAt k i.castSucc) := by
  revert k i
  decide +kernel

def localPathFlags (v : Local) (k : Fin 42) : Fin 8 → Bool := fun i =>
  decide (i.val < (privatePathLen k).val ∧ privatePathAt k i ∈ v.1)

theorem localPath_valid (v : Local) (hv : v ∈ localSet) (k : Fin 42) :
    pathValid8 (privatePathLen k) (localPathFlags v k) (v.2 k) := by
  obtain ⟨hs, hp⟩ := (mem_localSet v).1 hv
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp [localPathFlags, show ¬ i.val < (privatePathLen k).val by omega]
  · intro i hi hb
    have hc : privatePathAt k i.castSucc ∈ v.1 := (of_decide_eq_true hb).2
    have hn := (mem_neededH v.1 _).1 (hs hc)
    have hparent : privatePathAt k i.succ ∈ v.1 :=
      (needed_kid_excl_iff v.1 _).1 (by rwa [privatePath_next k i hi])
    exact decide_eq_true (show i.succ.val < (privatePathLen k).val ∧
      privatePathAt k i.succ ∈ v.1 from ⟨hi, hparent⟩)
  · intro hi hb
    apply hp k
    intro hn
    have hparent : privatePathAt k 0 ∈ v.1 :=
      (needed_kid_excl_iff v.1 _).1 (by
        rw [privatePath_base k hi]
        exact (mem_neededC v.1 k).1 hn)
    have htrue : localPathFlags v k 0 = true := by simp [localPathFlags, hi, hparent]
    rw [hb] at htrue
    contradiction

def localPathCode (v : Local) (k : Fin 42) : Nat :=
  pathCode8 (localPathFlags v k) (v.2 k)

theorem localPathCode_injective {v w : Local} (hv : v ∈ localSet) (hw : w ∈ localSet)
    (hc : localPathCode v = localPathCode w) : v = w := by
  have hcode (k : Fin 42) : pathCode8 (localPathFlags v k) (v.2 k) =
      pathCode8 (localPathFlags w k) (w.2 k) := congrFun hc k
  have hdv (k : Fin 42) := pathCode8_decode _ _ _ (localPath_valid v hv k)
  have hdw (k : Fin 42) := pathCode8_decode _ _ _ (localPath_valid w hw k)
  apply Prod.ext
  · ext j
    obtain ⟨hdepth, hslot⟩ := privatePath_cover j
    have hb : localPathFlags v (privatePathIndex j) (privatePathDepth j) =
        localPathFlags w (privatePathIndex j) (privatePathDepth j) := by
      rw [(hdv _).2.1, (hdw _).2.1, hcode]
    simpa [localPathFlags, hdepth, hslot] using hb
  · funext k
    apply Fin.ext
    rw [(hdv k).2.2, (hdw k).2.2, hcode]

def pathPopulationBound : Nat := ∏ k : Fin 42, ((privatePathLen k).val + 25)

theorem card_localSet_path_le : localSet.card ≤ pathPopulationBound := by
  classical
  let f : ↥localSet → (k : Fin 42) → Fin ((privatePathLen k).val + 25) := fun v k =>
    ⟨localPathCode v.val k, (pathCode8_decode _ _ _ (localPath_valid v.val v.property k)).1⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply localPathCode_injective v.property w.property
    funext k
    exact congrArg Fin.val (congrFun h k)
  calc
    localSet.card = Fintype.card ↥localSet := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ((k : Fin 42) → Fin ((privatePathLen k).val + 25)) :=
      Fintype.card_le_of_injective f hf
    _ = pathPopulationBound := by simp [pathPopulationBound, Fintype.card_pi]

theorem pathPopulationBound_eq : pathPopulationBound =
    92378827480372645324209297898969497600000000000000000000000000 := by
  decide +kernel


theorem card_localSet_le : localSet.card ≤ 2 ^ 213 * 25 ^ 42 := by
  have h := Finset.card_le_univ localSet
  simpa [Fintype.card_prod, Fintype.card_finset, Fintype.card_fun] using h

theorem card_choiceTuples_lt : choiceTuples.card < digitBase := by
  have h : choiceTuples.card = localSet.card ^ 1 := by
    rw [choiceTuples, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [h, pow_one]
  exact lt_of_le_of_lt card_localSet_path_le (by rw [pathPopulationBound_eq, digitBase]; decide +kernel)

theorem blockGen_pow :
    blockGen ^ 1 = ∑ c ∈ choiceTuples, digitBase ^ choiceCost c := by
  rw [blockGen, ← Fin.prod_const, Finset.prod_univ_sum, choiceTuples]
  exact Finset.sum_congr rfl fun c _ => Finset.prod_pow_eq_pow_sum _ _ _

theorem card_supportedChoices_eq_digit :
    supportedChoices.card = blockGen ^ 1 / digitBase ^ 82 % digitBase := by
  rw [blockGen_pow, digit_sum_pow _ _ _ card_choiceTuples_lt, supportedChoices]

theorem digit_from_mod (x b d k y z : Nat) (hk : k = d + 1)
    (hm : x % b^k = y) (hy : y / b^d = z) :
    x^1 / b^d % b = z := by
  subst k
  rw [pow_one, ← Nat.mod_mul_right_div_self, ← pow_succ, hm]
  exact hy


theorem digitBase_exact : digitBase = 102844034832575377634685573909834406561420991602098741459288064 := by
  rw [digitBase]
  decide +kernel

theorem digitMod_exact : digitBase ^ 83 = 102533518982044169998980114553215110391404875609116627453005203260922362346048001872815548256200680988264899465217017316086016368864326063454230947961924300245416263860189617183220749555408994147619514361880653011486501878854728811466767360046244535134718530572668230331170983012330751501631418109843177864878937506114082458971166530841894979622862434627670293881750043049400578470142865398808845296029887513241269932422004422888435142400557335672877570404837593782580751704972240323102045106489348140109934747245188630519333955324998569919138851714834427638736603744242347527656719825589255700549656688850415256149837901235729035990198655591634564836223128960203057791722501035644575712652281811312331096885251672810536108056051417378336304889024036058796217265342278872706415508820006195475860636187868469934775446639281851246174725836326591754355224633770182702252868846725900951089536102054643538996757384793759672118284720553664067558899783140428242261306722990830776781790306679918262194200190021648240544421418268762283537508618140611848578762961430402629505854761607382358193733094377917510414272387571712454619130804660208391099142273575419341057548797320083406559727798024521407109598132557850489227825122842505656793606356479705302166331398547321537125735458897100426387656172186194321942248373663443376200962772500939505951046990986123464499145338842996500837041138178380346448824968681770780773407450991087966017246740269812827482750000210907601647648729567339197861958002815803591090210451769057428372047444239574931725748749066578581548692633769082014182833871169385275899365876815525452177289136438085468871518768427758844256660726062881055292054536669755502994576086803903118119657922334776885716280033283784972797662061352084785107618988648640587071013400919576134871039407237252787998213657517700388164894685153871464658457350656351280390877275384604788309382014667719931762989063771053841631670511861628689165508269958580825298904722925592808210239199307920229611901630107150782195238432163361220520264235442192265363139025985819838540794835388734929224716876705152654243081373352797835491264836388892585399156039871259169012344632907614482282150804377330546182173770221854562084181397911772754091024804393354502505482168792714630604994701275428957683235177628411786293512997307534304032281313130622590796418852646400601778358735543189922189059392911489233769365642035595114448586048602955397508292719125607071079360929372524730639619564471515214137266619073758682531400499524474277173300788798932608968006997154999452747353327453607134472304745029918955804545171729748796201184470456088197720309318016168796206527980549699696482403730588557099973178109080857440092228150442094338382095597762438191321304602668252982070280595245556588699556891773853877861728218154513950969116744608473502861385761636513706918252717091095475599864518372175557565851927581869939375685246287771296776049378009303515312183178655702595208444836636587773476431076969075636320369173455669689035255478325619028461335147092166656182518909963608073980516299752147554838038806269403679190580717713776293805422041661533702462900198942858726579883241107502190666876236047074297174514289397610373848409050211974237172483630676856920172571432907963488300861766887756058503955914529377187808020260163931039735162878900779935567976908235413977903953424022281355680339798044883864695886446304810134143567027154711038429299574816757032446455395683991769064717792381770820978601886324603586491182185567585507075876762619584042996662136348430239247251461774762135035192432567546222111395329848361023776445419994579411152378410656213577054774967302238259276049510085456393455452217413199028822595532853713657320940330782366508329330046550335191107356030778094248437623541294737287667967878958259291364840967369005373335617526693458376204921590441520352777913104559742833827718001867303030611110791664636225163172738106231739885530076837648870130860503682014069269755561880896721987879608350617094569112443368037468095184588271626918288016887822635571863207165327655647102620223464977083018944163438320149009263409653177403672952365933826766873977419050218334092880873817538059542037690417066822114792902257805939684285698995099006504486732385598326676827076267758253193716888633605553792870948553213060942758076826130752639222257023893477683972954468237988903920970213151775104330675188290814029903460263606431583293635806666156640254076764426831025436233377338235609580794084458076441353915553795201414980670088552991589996602835806453879551119011388149302714054743018136161788029129210440127647434712965074844001174676833212833119728529897799789273757365423220684769722458657873862923154018394777930646891993721825059100561047150240423692222774530257238176497689829896495945799122415611636057693431187463737793224239138010886515940277521297810563824927878815580241149603811333885976558581402672729238078911676500255495671343427209678589858196097221855284624555361095536853337704093307338076227196932151410739154606196467590538990578174532205759183523213165087103934823370744819634716236467003239784713224865843642051422556300274363075305371244822229293996749881344 := by
  rw [digitBase]
  decide +kernel

theorem chainGen_exact : chainGen = 1960191775756439709392800012388784666279706557757341207645207652997524910275077950366396980409511203974427996552949090724728529988920704959307932189651064232727090574374447144938701837275266594693384427384350511181597471269240044244734147286306699585303167712618829535062858985193572441879703336832993037202329979047924224410022302290265463128793424176087029022165212396390597733640195282450777374300320146589948146555439152101381522540854261393491420699782789704208382847701459316581145723872736579459017932477844875190903876617522040473217340822470996668835757567701239298195010056925618544207980884899554826207944332106071578780048514141391684824489313420977540613697796217578686829848606452073995446468791886472338872103991887507827789940987231071412165706505388502017423555370276918632818638778243459948131388560340223482422318336933594651978232096826671550187201803549522660257830574613526355806331499401718098559330609208841818871558014538509262176198619015419647755569362579512836600722266163163278884539049175791357938338874798912137150230455252033100548275521643548505056869457145863928589357501392886600888086508304765599798994974596869093707052080885686882055162365635568675143184961422288746215874168092065444059936627649943144082555016563342673547115719291661660738321113998203538224315990534224109118678721790555619005286356712145709866877375937037783881400219870110341334822495839012111438258262454717310364968615121447234910900685834890591261135363895083836523154631557121 := by
  rw [chainGen, digitBase]
  decide +kernel

theorem blockGen_mod_exact : dfs digitBase 1 chainGen 213 topMask 0 %
    digitBase ^ 83 = 674709128734898423562674069107726144933486007320326490086370059845618646117891466567869306849327428008547559161684070441490796675761309664877145354597314104812745707148030386607380079269299494765552365263409514730472343163808349126281470147959513373666855490468124507075494315042625062209917256509339420072627683177589480659324576186057714936570811576537587384045989142670172950844500835919667343124098253684866827990308671157653205275629948975440151180133207596801053754544124575765238219515495456587224679325019126931909958536086891379360740327026112679733503161112799989479768963771990982034010006646087114624497465265482513917861819281326455687594162347176113632736330922041175052242882898350098692377337766577722647230762265988492367212348486020754186479005947691940232043076123624572198540729930146426170524796239998807301034486739901992369309626485239158831690671209823194829232516143615681356456593122793881529641029042803865816957525581199589682963039110742081124073503513001593017408009408801425294741481721911434174552151231525716006084192811492849336119955104527413210790799472811620736673152579601969608321597720512834391978376165711751704196380074629241539891961875350792420266575844593521838066732836745197153467777897008587015462903431795980179620671777346603216350039287433015682805216529776682647891078852457707690571244888327206968401517702829911543834941786111548068444075123722092966301296125835424889927228926042089340154155771850524189601864597001254595725382379690919343219123313361691630690212148427336011253901758708239077054690897184498401442301840297513409429393860812626090846010993968811407321273871180596340906089498929983816141919815628380906558557310068526400298884920568435074518048166877792913868223895605140803632663122510094203823391448602115412984108656012399619781157815702997472481388091035545391036963597906815314772889313833975584224511925581898873083331063005714636044574543122367648666951593974375509890901142780561425329362300365338022676441957609503425658035518642114332322732527303334646393798449270003921794639276419022333863512945794225806749558555087560237200061977732663304116862865561448249927681622833967342131856203249353197761698992487645062604150211194932681985333186065987269423594132899345062458999537298442592626832416137262265669709474921504144338264746600689773458449655590612458140142992108422558351558354023503741001551928721086511359403909318050383476063324334542008438028862187359113522328946886468283439894731020202014007057314247412717716174332374184025699815404294172273816799522750034262463815977345053717077469068108582336939626738839656216622767948630333923249271304392456230520103755039123925868393509052672217907065033909874163569641125527027389043179802796562152719358573694684317090128128904746947070528013010335845820276062153446639755082966645838050512044078095291698402721803154469095632837919555366038977404056802528747073417736465711110038814225417703756646716231979192848789130422565467835326328254679885029028295712405202460479970538309279840691249450512185145277748203283675803729826042186418138957968453804538794708254935079729967090916357156792453456628771430685470995972715360487322002292987176696827517059189452840969414625090307986552928335915577972081852261390450485534872889305203436090189184334925484266691658542325562292747489027410346885194670052508462006930791181602790389120041913622737231012474368785766322486248163723013096970951419945436812792492892243205023271135743476119565604754724052808870289870142398802228862433232734236377473870560859014810128884241601396198088688517383801088949810426792424339716405017000207562243041176158710315161123134009275549990024453328414872673775107754328038665383572403169375729077514391706327063579025764093050227582921259924935182215993204799120913789951763312809785202708405327700241591672120454823123977433439112447769965900681015649483439272579850193143527594297865664169144836645431882364358499952113961390955939289819979186963707787391890275669802228551535318765774673219482082971753663042898003886850963495544214505779196318409731421604556474219506212163971606203470683730586530483229803321856606684418644411695024128953046058983629297528232874740495947681236029933906010538914069995652231355417412689368169515867829295905324573593535551345587113092788251031450292026734326078760665977213658887036820748660498963800168647941845774854654010364865516699283320894223571959842755121279811202463360709682058824360313215847897069800366095590383342768728233987669316386026976411774949061537139894087323742867484409337145789983575601848885165065664900528983794971905369979852528855230392483517631262505623099490701523370025360237911223105097136962490125939997819766617001674337469604214656716682735027931630150022023280733346085409715214354093930759972304273118835253201102029425498635145753606929314857755425591609512974224812532873870368336669370388171604793355599371736656235327776641184689097127771430928404047384183068762471665473475410247061072288814249011089012202892570353664311365935533553485153572247177522648661397121296899606736758319564786614375177376826867865320870117377 := by
  rw [digitMod_exact, chainGen_exact, digitBase_exact, topMask]
  memo_count 102533518982044169998980114553215110391404875609116627453005203260922362346048001872815548256200680988264899465217017316086016368864326063454230947961924300245416263860189617183220749555408994147619514361880653011486501878854728811466767360046244535134718530572668230331170983012330751501631418109843177864878937506114082458971166530841894979622862434627670293881750043049400578470142865398808845296029887513241269932422004422888435142400557335672877570404837593782580751704972240323102045106489348140109934747245188630519333955324998569919138851714834427638736603744242347527656719825589255700549656688850415256149837901235729035990198655591634564836223128960203057791722501035644575712652281811312331096885251672810536108056051417378336304889024036058796217265342278872706415508820006195475860636187868469934775446639281851246174725836326591754355224633770182702252868846725900951089536102054643538996757384793759672118284720553664067558899783140428242261306722990830776781790306679918262194200190021648240544421418268762283537508618140611848578762961430402629505854761607382358193733094377917510414272387571712454619130804660208391099142273575419341057548797320083406559727798024521407109598132557850489227825122842505656793606356479705302166331398547321537125735458897100426387656172186194321942248373663443376200962772500939505951046990986123464499145338842996500837041138178380346448824968681770780773407450991087966017246740269812827482750000210907601647648729567339197861958002815803591090210451769057428372047444239574931725748749066578581548692633769082014182833871169385275899365876815525452177289136438085468871518768427758844256660726062881055292054536669755502994576086803903118119657922334776885716280033283784972797662061352084785107618988648640587071013400919576134871039407237252787998213657517700388164894685153871464658457350656351280390877275384604788309382014667719931762989063771053841631670511861628689165508269958580825298904722925592808210239199307920229611901630107150782195238432163361220520264235442192265363139025985819838540794835388734929224716876705152654243081373352797835491264836388892585399156039871259169012344632907614482282150804377330546182173770221854562084181397911772754091024804393354502505482168792714630604994701275428957683235177628411786293512997307534304032281313130622590796418852646400601778358735543189922189059392911489233769365642035595114448586048602955397508292719125607071079360929372524730639619564471515214137266619073758682531400499524474277173300788798932608968006997154999452747353327453607134472304745029918955804545171729748796201184470456088197720309318016168796206527980549699696482403730588557099973178109080857440092228150442094338382095597762438191321304602668252982070280595245556588699556891773853877861728218154513950969116744608473502861385761636513706918252717091095475599864518372175557565851927581869939375685246287771296776049378009303515312183178655702595208444836636587773476431076969075636320369173455669689035255478325619028461335147092166656182518909963608073980516299752147554838038806269403679190580717713776293805422041661533702462900198942858726579883241107502190666876236047074297174514289397610373848409050211974237172483630676856920172571432907963488300861766887756058503955914529377187808020260163931039735162878900779935567976908235413977903953424022281355680339798044883864695886446304810134143567027154711038429299574816757032446455395683991769064717792381770820978601886324603586491182185567585507075876762619584042996662136348430239247251461774762135035192432567546222111395329848361023776445419994579411152378410656213577054774967302238259276049510085456393455452217413199028822595532853713657320940330782366508329330046550335191107356030778094248437623541294737287667967878958259291364840967369005373335617526693458376204921590441520352777913104559742833827718001867303030611110791664636225163172738106231739885530076837648870130860503682014069269755561880896721987879608350617094569112443368037468095184588271626918288016887822635571863207165327655647102620223464977083018944163438320149009263409653177403672952365933826766873977419050218334092880873817538059542037690417066822114792902257805939684285698995099006504486732385598326676827076267758253193716888633605553792870948553213060942758076826130752639222257023893477683972954468237988903920970213151775104330675188290814029903460263606431583293635806666156640254076764426831025436233377338235609580794084458076441353915553795201414980670088552991589996602835806453879551119011388149302714054743018136161788029129210440127647434712965074844001174676833212833119728529897799789273757365423220684769722458657873862923154018394777930646891993721825059100561047150240423692222774530257238176497689829896495945799122415611636057693431187463737793224239138010886515940277521297810563824927878815580241149603811333885976558581402672729238078911676500255495671343427209678589858196097221855284624555361095536853337704093307338076227196932151410739154606196467590538990578174532205759183523213165087103934823370744819634716236467003239784713224865843642051422556300274363075305371244822229293996749881344 102844034832575377634685573909834406561420991602098741459288064 1960191775756439709392800012388784666279706557757341207645207652997524910275077950366396980409511203974427996552949090724728529988920704959307932189651064232727090574374447144938701837275266594693384427384350511181597471269240044244734147286306699585303167712618829535062858985193572441879703336832993037202329979047924224410022302290265463128793424176087029022165212396390597733640195282450777374300320146589948146555439152101381522540854261393491420699782789704208382847701459316581145723872736579459017932477844875190903876617522040473217340822470996668835757567701239298195010056925618544207980884899554826207944332106071578780048514141391684824489313420977540613697796217578686829848606452073995446468791886472338872103991887507827789940987231071412165706505388502017423555370276918632818638778243459948131388560340223482422318336933594651978232096826671550187201803549522660257830574613526355806331499401718098559330609208841818871558014538509262176198619015419647755569362579512836600722266163163278884539049175791357938338874798912137150230455252033100548275521643548505056869457145863928589357501392886600888086508304765599798994974596869093707052080885686882055162365635568675143184961422288746215874168092065444059936627649943144082555016563342673547115719291661660738321113998203538224315990534224109118678721790555619005286356712145709866877375937037783881400219870110341334822495839012111438258262454717310364968615121447234910900685834890591261135363895083836523154631557121 8638898926127899509928384528368297814323313644943866452418494464

set_option maxRecDepth 100000 in
theorem blockGen_digit_exact :
    (dfs digitBase 1 chainGen 213 topMask 0) ^ 1 / digitBase ^ 82 % digitBase =
      676752439849646922507063152752853 := by
  refine digit_from_mod (dfs digitBase 1 chainGen 213 topMask 0) digitBase 82 83
    674709128734898423562674069107726144933486007320326490086370059845618646117891466567869306849327428008547559161684070441490796675761309664877145354597314104812745707148030386607380079269299494765552365263409514730472343163808349126281470147959513373666855490468124507075494315042625062209917256509339420072627683177589480659324576186057714936570811576537587384045989142670172950844500835919667343124098253684866827990308671157653205275629948975440151180133207596801053754544124575765238219515495456587224679325019126931909958536086891379360740327026112679733503161112799989479768963771990982034010006646087114624497465265482513917861819281326455687594162347176113632736330922041175052242882898350098692377337766577722647230762265988492367212348486020754186479005947691940232043076123624572198540729930146426170524796239998807301034486739901992369309626485239158831690671209823194829232516143615681356456593122793881529641029042803865816957525581199589682963039110742081124073503513001593017408009408801425294741481721911434174552151231525716006084192811492849336119955104527413210790799472811620736673152579601969608321597720512834391978376165711751704196380074629241539891961875350792420266575844593521838066732836745197153467777897008587015462903431795980179620671777346603216350039287433015682805216529776682647891078852457707690571244888327206968401517702829911543834941786111548068444075123722092966301296125835424889927228926042089340154155771850524189601864597001254595725382379690919343219123313361691630690212148427336011253901758708239077054690897184498401442301840297513409429393860812626090846010993968811407321273871180596340906089498929983816141919815628380906558557310068526400298884920568435074518048166877792913868223895605140803632663122510094203823391448602115412984108656012399619781157815702997472481388091035545391036963597906815314772889313833975584224511925581898873083331063005714636044574543122367648666951593974375509890901142780561425329362300365338022676441957609503425658035518642114332322732527303334646393798449270003921794639276419022333863512945794225806749558555087560237200061977732663304116862865561448249927681622833967342131856203249353197761698992487645062604150211194932681985333186065987269423594132899345062458999537298442592626832416137262265669709474921504144338264746600689773458449655590612458140142992108422558351558354023503741001551928721086511359403909318050383476063324334542008438028862187359113522328946886468283439894731020202014007057314247412717716174332374184025699815404294172273816799522750034262463815977345053717077469068108582336939626738839656216622767948630333923249271304392456230520103755039123925868393509052672217907065033909874163569641125527027389043179802796562152719358573694684317090128128904746947070528013010335845820276062153446639755082966645838050512044078095291698402721803154469095632837919555366038977404056802528747073417736465711110038814225417703756646716231979192848789130422565467835326328254679885029028295712405202460479970538309279840691249450512185145277748203283675803729826042186418138957968453804538794708254935079729967090916357156792453456628771430685470995972715360487322002292987176696827517059189452840969414625090307986552928335915577972081852261390450485534872889305203436090189184334925484266691658542325562292747489027410346885194670052508462006930791181602790389120041913622737231012474368785766322486248163723013096970951419945436812792492892243205023271135743476119565604754724052808870289870142398802228862433232734236377473870560859014810128884241601396198088688517383801088949810426792424339716405017000207562243041176158710315161123134009275549990024453328414872673775107754328038665383572403169375729077514391706327063579025764093050227582921259924935182215993204799120913789951763312809785202708405327700241591672120454823123977433439112447769965900681015649483439272579850193143527594297865664169144836645431882364358499952113961390955939289819979186963707787391890275669802228551535318765774673219482082971753663042898003886850963495544214505779196318409731421604556474219506212163971606203470683730586530483229803321856606684418644411695024128953046058983629297528232874740495947681236029933906010538914069995652231355417412689368169515867829295905324573593535551345587113092788251031450292026734326078760665977213658887036820748660498963800168647941845774854654010364865516699283320894223571959842755121279811202463360709682058824360313215847897069800366095590383342768728233987669316386026976411774949061537139894087323742867484409337145789983575601848885165065664900528983794971905369979852528855230392483517631262505623099490701523370025360237911223105097136962490125939997819766617001674337469604214656716682735027931630150022023280733346085409715214354093930759972304273118835253201102029425498635145753606929314857755425591609512974224812532873870368336669370388171604793355599371736656235327776641184689097127771430928404047384183068762471665473475410247061072288814249011089012202892570353664311365935533553485153572247177522648661397121296899606736758319564786614375177376826867865320870117377 676752439849646922507063152752853 ?_ blockGen_mod_exact ?_
  · decide +kernel
  · rw [digitBase]
    decide +kernel

theorem card_supportedChoices :
    supportedChoices.card = 676752439849646922507063152752853 := by
  rw [card_supportedChoices_eq_digit, blockGen_eq, blockGen_digit_exact]

/-- The record's schedule class count. -/
def K91 : ℕ := 676013856769711926075368867014708

theorem K91_le_card_supportedChoices : K91 ≤ supportedChoices.card := by
  rw [card_supportedChoices, K91]
  norm_num

/-! ## Cut codec -/

/-- Disclosures of one block: needed unexpanded hash values and one value on
each needed chain. -/
def blockCut (b : Fin 1) (v : Local) : Finset Name :=
  (neededH v.1 \ v.1).image (Name.hv b) ∪
    (neededC v.1).image fun k => chainNode b k (v.2 k)

def cutOf (c : Choice) : Finset Name :=
  Finset.univ.biUnion fun b => blockCut b (c b)

theorem mem_cutOf (c : Choice) (n : Name) : n ∈ cutOf c ↔
    (∃ b j, j ∈ neededH (c b).1 ∧ j ∉ (c b).1 ∧ n = .hv b j) ∨
      ∃ b k, k ∈ neededC (c b).1 ∧ n = chainNode b k ((c b).2 k) := by
  simp only [cutOf, blockCut, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨b, ⟨j, ⟨hj, hjE⟩, rfl⟩ | ⟨k, hk, rfl⟩⟩
    · exact Or.inl ⟨b, j, hj, hjE, rfl⟩
    · exact Or.inr ⟨b, k, hk, rfl⟩
  · rintro (⟨b, j, hj, hjE, rfl⟩ | ⟨b, k, hk, rfl⟩)
    · exact ⟨b, Or.inl ⟨j, ⟨hj, hjE⟩, rfl⟩⟩
    · exact ⟨b, Or.inr ⟨k, hk, rfl⟩⟩

theorem hv_ne_chainNode (b b' : Fin 1) (j : Fin 213) (k : Fin 42) (p : Fin 25) :
    Name.hv b j ≠ chainNode b' k p := by
  unfold chainNode
  split_ifs <;> simp

@[simp] theorem hv_mem_cutOf (c : Choice) (b : Fin 1) (j : Fin 213) :
    Name.hv b j ∈ cutOf c ↔ j ∈ neededH (c b).1 ∧ j ∉ (c b).1 := by
  rw [mem_cutOf]
  constructor
  · rintro (⟨b', j', hj, hjE, h⟩ | ⟨b', k, _, h⟩)
    · obtain ⟨rfl, rfl⟩ := Name.hv.inj h
      exact ⟨hj, hjE⟩
    · exact absurd h (hv_ne_chainNode _ _ _ _ _)
  · rintro ⟨hj, hjE⟩
    exact Or.inl ⟨b, j, hj, hjE, rfl⟩

theorem chainNode_mem_cutOf (c : Choice) (b : Fin 1) (k : Fin 42) (p : Fin 25) :
    chainNode b k p ∈ cutOf c ↔ k ∈ neededC (c b).1 ∧ (c b).2 k = p := by
  rw [mem_cutOf]
  constructor
  · rintro (⟨b', j, _, _, h⟩ | ⟨b', k', hk, h⟩)
    · exact absurd h.symm (hv_ne_chainNode _ _ _ _ _)
    · obtain ⟨rfl, rfl, rfl⟩ := chainNode_pair_injective h
      exact ⟨hk, rfl⟩
  · rintro ⟨hk, rfl⟩
    exact Or.inr ⟨b, k, hk, rfl⟩

theorem cutOf_values (c : Choice) : ∀ n ∈ cutOf c, n.len = 129 := by
  intro n hn
  rcases (mem_cutOf c n).1 hn with ⟨b, j, _, _, rfl⟩ | ⟨b, k, _, rfl⟩
  · rfl
  · exact chainNode_len _ _ _

/-- The block of a disclosed value. -/
def Name.blk : Name → Option (Fin 1)
  | src b _ | ci b _ _ | ch b _ _ | cv b _ _ | hc b _ | hh b _ | hv b _ => some b
  | rc | rh => none

theorem blk_of_mem_blockCut {b : Fin 1} {v : Local} {n : Name} (h : n ∈ blockCut b v) :
    n.blk = some b := by
  simp only [blockCut, Finset.mem_union, Finset.mem_image] at h
  rcases h with ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
  · rfl
  · unfold chainNode
    split_ifs <;> rfl

theorem card_blockCut (b : Fin 1) (v : Local) : (blockCut b v).card = localWords v := by
  rw [blockCut, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective]
  · rfl
  · intro k k' h
    exact (chainNode_pair_injective h).2.1
  · intro j j' h
    exact (Name.hv.inj h).2
  · rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨k, _, h⟩ := Finset.mem_image.1 hn'
    exact hv_ne_chainNode _ _ _ _ _ h.symm

theorem card_cutOf (c : Choice) : (cutOf c).card = choiceWords c := by
  rw [cutOf, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun b _ => card_blockCut b (c b)
  · intro b _ b' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    have h := (blk_of_mem_blockCut hn).symm.trans (blk_of_mem_blockCut hn')
    exact hne (Option.some.inj h)

/-! ## Arbitrary class numbering -/

/-- Select the first `M` members of a finite family using only its canonical
finite equivalence. -/
def selectCut {family : Finset (Finset Name)} {M : ℕ} (hM : M ≤ family.card) :
    Fin M → Finset Name := fun i => family.equivFin.symm (Fin.castLE hM i)

theorem selectCut_mem {family : Finset (Finset Name)} {M : ℕ}
    (hM : M ≤ family.card) (i : Fin M) : selectCut hM i ∈ family :=
  (family.equivFin.symm (Fin.castLE hM i)).property

theorem selectCut_injective {family : Finset (Finset Name)} {M : ℕ}
    (hM : M ≤ family.card) : Function.Injective (selectCut hM) := by
  intro i j hij
  have hs : family.equivFin.symm (Fin.castLE hM i) =
      family.equivFin.symm (Fin.castLE hM j) := Subtype.ext hij
  have hf : Fin.castLE hM i = Fin.castLE hM j := family.equivFin.symm.injective hs
  have hv : i.val = j.val := by
    change (Fin.castLE hM i).val = (Fin.castLE hM j).val
    exact congrArg Fin.val hf
  exact Fin.ext hv

end OptimalOTS.WeightedConstruction.LongChain91
