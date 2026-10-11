import Submissions.UpperCompressions.ProofBundle00

/-!
# Global shared-DAG research geometry

One block has 42 length-24 chains and 213 hash nodes under seven tops.
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
  ![.c 0, .c 0, .c 1],
  ![.c 0, .h 0, .c 2],
  ![.c 0, .c 0, .c 3],
  ![.h 0, .h 1, .h 2],
  ![.c 0, .h 0, .c 4],
  ![.h 1, .h 3, .h 4],
  ![.c 0, .c 0, .c 5],
  ![.h 0, .h 1, .h 6],
  ![.h 3, .h 5, .h 7],
  ![.c 0, .h 0, .c 6],
  ![.h 1, .h 3, .h 9],
  ![.h 5, .h 8, .h 10],
  ![.c 0, .c 0, .c 7],
  ![.h 0, .h 1, .h 12],
  ![.h 3, .h 5, .h 13],
  ![.h 8, .h 11, .h 14],
  ![.c 0, .h 0, .c 8],
  ![.h 1, .h 3, .h 16],
  ![.h 5, .h 8, .h 17],
  ![.h 11, .h 15, .h 18],
  ![.c 0, .c 0, .c 9],
  ![.h 0, .h 1, .h 20],
  ![.h 3, .h 5, .h 21],
  ![.h 8, .h 11, .h 22],
  ![.h 15, .h 19, .h 23],
  ![.c 0, .h 0, .c 10],
  ![.h 1, .h 3, .h 25],
  ![.h 5, .h 8, .h 26],
  ![.h 11, .h 15, .h 27],
  ![.h 19, .h 24, .h 28],
  ![.c 0, .c 0, .c 11],
  ![.h 0, .h 1, .h 30],
  ![.h 3, .h 5, .h 31],
  ![.h 8, .h 11, .h 32],
  ![.h 15, .h 19, .h 33],
  ![.h 24, .h 29, .h 34],
  ![.c 0, .h 0, .c 12],
  ![.h 1, .h 3, .h 36],
  ![.h 5, .h 8, .h 37],
  ![.h 11, .h 15, .h 38],
  ![.h 19, .h 24, .h 39],
  ![.h 29, .h 35, .h 40],
  ![.h 0, .h 1, .c 13],
  ![.h 3, .h 5, .h 42],
  ![.h 8, .h 11, .h 43],
  ![.h 15, .h 19, .h 44],
  ![.h 24, .h 29, .h 45],
  ![.h 35, .h 41, .h 46],
  ![.h 1, .h 3, .c 14],
  ![.h 5, .h 8, .h 48],
  ![.h 11, .h 15, .h 49],
  ![.h 19, .h 24, .h 50],
  ![.h 29, .h 35, .h 51],
  ![.h 41, .h 47, .h 52],
  ![.h 3, .h 5, .c 15],
  ![.h 8, .h 11, .h 54],
  ![.h 15, .h 19, .h 55],
  ![.h 24, .h 29, .h 56],
  ![.h 35, .h 41, .h 57],
  ![.h 47, .h 53, .h 58],
  ![.h 5, .h 8, .c 16],
  ![.h 11, .h 15, .h 60],
  ![.h 19, .h 24, .h 61],
  ![.h 29, .h 35, .h 62],
  ![.h 41, .h 47, .h 63],
  ![.h 53, .h 59, .h 64],
  ![.h 8, .h 11, .c 17],
  ![.h 15, .h 19, .h 66],
  ![.h 24, .h 29, .h 67],
  ![.h 35, .h 41, .h 68],
  ![.h 47, .h 53, .h 69],
  ![.h 59, .h 65, .h 70],
  ![.h 11, .h 15, .c 18],
  ![.h 19, .h 24, .h 72],
  ![.h 29, .h 35, .h 73],
  ![.h 41, .h 47, .h 74],
  ![.h 53, .h 59, .h 75],
  ![.h 65, .h 71, .h 76],
  ![.h 15, .h 19, .c 19],
  ![.h 24, .h 29, .h 78],
  ![.h 35, .h 41, .h 79],
  ![.h 47, .h 53, .h 80],
  ![.h 59, .h 65, .h 81],
  ![.h 71, .h 77, .h 82],
  ![.h 19, .h 24, .c 20],
  ![.h 29, .h 35, .h 84],
  ![.h 41, .h 47, .h 85],
  ![.h 53, .h 59, .h 86],
  ![.h 65, .h 71, .h 87],
  ![.h 77, .h 83, .h 88],
  ![.h 24, .h 29, .c 21],
  ![.h 35, .h 41, .h 90],
  ![.h 47, .h 53, .h 91],
  ![.h 59, .h 65, .h 92],
  ![.h 71, .h 77, .h 93],
  ![.h 83, .h 89, .h 94],
  ![.h 29, .h 35, .c 22],
  ![.h 41, .h 47, .h 96],
  ![.h 53, .h 59, .h 97],
  ![.h 65, .h 71, .h 98],
  ![.h 77, .h 83, .h 99],
  ![.h 89, .h 95, .h 100],
  ![.h 35, .h 41, .c 23],
  ![.h 47, .h 53, .h 102],
  ![.h 59, .h 65, .h 103],
  ![.h 71, .h 77, .h 104],
  ![.h 83, .h 89, .h 105],
  ![.h 41, .h 47, .c 24],
  ![.h 53, .h 59, .h 107],
  ![.h 65, .h 71, .h 108],
  ![.h 77, .h 83, .h 109],
  ![.h 89, .h 95, .h 110],
  ![.h 101, .h 106, .h 111],
  ![.h 47, .h 53, .c 25],
  ![.h 59, .h 65, .h 113],
  ![.h 71, .h 77, .h 114],
  ![.h 95, .h 101, .h 115],
  ![.h 106, .h 112, .h 116],
  ![.h 53, .h 59, .c 26],
  ![.h 65, .h 71, .h 118],
  ![.h 77, .h 83, .h 119],
  ![.h 89, .h 95, .h 120],
  ![.h 101, .h 106, .h 121],
  ![.h 112, .h 117, .h 122],
  ![.h 59, .h 65, .c 27],
  ![.h 71, .h 77, .h 124],
  ![.h 83, .h 89, .h 125],
  ![.h 95, .h 101, .h 126],
  ![.h 117, .h 123, .h 127],
  ![.h 65, .h 71, .c 28],
  ![.h 77, .h 83, .h 129],
  ![.h 89, .h 95, .h 130],
  ![.h 101, .h 106, .h 131],
  ![.h 112, .h 117, .h 132],
  ![.h 123, .h 128, .h 133],
  ![.h 71, .h 77, .c 29],
  ![.h 83, .h 89, .h 135],
  ![.h 95, .h 101, .h 136],
  ![.h 106, .h 112, .h 137],
  ![.h 117, .h 123, .h 138],
  ![.h 128, .h 134, .h 139],
  ![.h 77, .h 83, .c 30],
  ![.h 89, .h 95, .h 141],
  ![.h 101, .h 106, .h 142],
  ![.h 112, .h 117, .h 143],
  ![.h 123, .h 128, .h 144],
  ![.h 134, .h 140, .h 145],
  ![.h 83, .h 89, .c 31],
  ![.h 95, .h 101, .h 147],
  ![.h 106, .h 112, .h 148],
  ![.h 117, .h 123, .h 149],
  ![.h 128, .h 134, .h 150],
  ![.h 140, .h 146, .h 151],
  ![.h 83, .h 89, .c 32],
  ![.h 95, .h 101, .h 153],
  ![.h 106, .h 112, .h 154],
  ![.h 117, .h 123, .h 155],
  ![.h 134, .h 140, .h 156],
  ![.h 146, .h 152, .h 157],
  ![.h 83, .h 89, .c 33],
  ![.h 95, .h 101, .h 159],
  ![.h 106, .h 112, .h 160],
  ![.h 123, .h 128, .h 161],
  ![.h 140, .h 146, .h 162],
  ![.h 152, .h 158, .h 163],
  ![.h 83, .h 89, .c 34],
  ![.h 95, .h 101, .h 165],
  ![.h 106, .h 112, .h 166],
  ![.h 128, .h 134, .h 167],
  ![.h 140, .h 146, .h 168],
  ![.h 152, .h 158, .h 169],
  ![.h 89, .h 95, .c 35],
  ![.h 101, .h 112, .h 171],
  ![.h 117, .h 123, .h 172],
  ![.h 128, .h 134, .h 173],
  ![.h 140, .h 146, .h 174],
  ![.h 152, .h 158, .h 175],
  ![.h 89, .h 95, .c 36],
  ![.h 101, .h 112, .h 177],
  ![.h 117, .h 123, .h 178],
  ![.h 128, .h 134, .h 179],
  ![.h 140, .h 146, .h 180],
  ![.h 164, .h 170, .h 181],
  ![.h 95, .h 101, .c 37],
  ![.h 106, .h 112, .h 183],
  ![.h 117, .h 123, .h 184],
  ![.h 128, .h 134, .h 185],
  ![.h 146, .h 158, .h 186],
  ![.h 164, .h 170, .h 187],
  ![.h 95, .h 101, .c 38],
  ![.h 106, .h 112, .h 189],
  ![.h 117, .h 123, .h 190],
  ![.h 128, .h 134, .h 191],
  ![.h 146, .h 158, .h 192],
  ![.h 164, .h 170, .h 193],
  ![.h 95, .h 101, .c 39],
  ![.h 106, .h 112, .h 195],
  ![.h 117, .h 123, .h 196],
  ![.h 128, .h 134, .h 197],
  ![.h 152, .h 158, .h 198],
  ![.h 164, .h 170, .h 199],
  ![.h 95, .h 101, .c 40],
  ![.h 106, .h 112, .h 201],
  ![.h 117, .h 123, .h 202],
  ![.h 134, .h 140, .h 203],
  ![.h 152, .h 158, .h 204],
  ![.h 164, .h 170, .h 205],
  ![.h 95, .h 101, .c 41],
  ![.h 106, .h 112, .h 207],
  ![.h 117, .h 123, .h 208],
  ![.h 140, .h 146, .h 209],
  ![.h 152, .h 158, .h 210],
  ![.h 164, .h 170, .h 211]]

/-- The seven block tops, in root-slot order. -/
def top : Fin 7 → Fin 213 := ![176, 182, 188, 194, 200, 206, 212]

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
  | rc => 16 + 129 * 7
  | rh => 256

/-- SHA-256 compression cost at each hash-output node. -/
def cost : Name → ℕ
  | ch _ _ _ => 1
  | hh _ _ => 1
  | rh => 2
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

/-- The root input in slot `r`: top `r % 7` of block `r / 7`. -/
def rootIn (r : Fin 7) : Name :=
  .hv ⟨r.val / 7, by omega⟩ (top ⟨r.val % 7, by omega⟩)

theorem rootIn_mk (b : Fin 1) (s : Fin 7) :
    rootIn ⟨7 * b.val + s.val, by omega⟩ = .hv b (top s) := by
  have h1 : (7 * b.val + s.val) / 7 = b.val := by omega
  have h2 : (7 * b.val + s.val) % 7 = s.val := by omega
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
def keygenCost : ℕ := 42 * 24 + 213 + 2

theorem keygenCost_eq : keygenCost = 1223 := by norm_num [keygenCost]

theorem sum_name_cost : (∑ n : Name, n.cost) = keygenCost := by decide +kernel

/-! ## Needed kids and shapes -/

/-- The graph name holding a kid's 129-bit value in block `b`. -/
def Kid.name (b : Fin 1) : Kid → Name
  | .c k => .cv b k 23
  | .h j => .hv b j

def privateOwner : Kid → Option (Fin 213)
  | .c k => (![none, some 0, some 1, some 2, some 4, some 6, some 9, some 12, some 16, some 20, some 25, some 30, some 36, some 42, some 48, some 54, some 60, some 66, some 72, some 78, some 84, some 90, some 96, some 102, some 107, some 113, some 118, some 124, some 129, some 135, some 141, some 147, some 153, some 159, some 165, some 171, some 177, some 183, some 189, some 195, some 201, some 207] : Fin 42 → Option (Fin 213)) k
  | .h j => (![none, none, some 3, none, some 5, none, some 7, some 8, none, some 10, some 11, none, some 13, some 14, some 15, none, some 17, some 18, some 19, none, some 21, some 22, some 23, some 24, none, some 26, some 27, some 28, some 29, none, some 31, some 32, some 33, some 34, some 35, none, some 37, some 38, some 39, some 40, some 41, none, some 43, some 44, some 45, some 46, some 47, none, some 49, some 50, some 51, some 52, some 53, none, some 55, some 56, some 57, some 58, some 59, none, some 61, some 62, some 63, some 64, some 65, none, some 67, some 68, some 69, some 70, some 71, none, some 73, some 74, some 75, some 76, some 77, none, some 79, some 80, some 81, some 82, some 83, none, some 85, some 86, some 87, some 88, some 89, none, some 91, some 92, some 93, some 94, some 95, none, some 97, some 98, some 99, some 100, some 101, none, some 103, some 104, some 105, some 106, none, some 108, some 109, some 110, some 111, some 112, none, some 114, some 115, some 116, some 117, none, some 119, some 120, some 121, some 122, some 123, none, some 125, some 126, some 127, some 128, none, some 130, some 131, some 132, some 133, some 134, none, some 136, some 137, some 138, some 139, some 140, none, some 142, some 143, some 144, some 145, some 146, none, some 148, some 149, some 150, some 151, some 152, none, some 154, some 155, some 156, some 157, some 158, none, some 160, some 161, some 162, some 163, some 164, none, some 166, some 167, some 168, some 169, some 170, none, some 172, some 173, some 174, some 175, some 176, none, some 178, some 179, some 180, some 181, some 182, none, some 184, some 185, some 186, some 187, some 188, none, some 190, some 191, some 192, some 193, some 194, none, some 196, some 197, some 198, some 199, some 200, none, some 202, some 203, some 204, some 205, some 206, none, some 208, some 209, some 210, some 211, some 212, none] : Fin 213 → Option (Fin 213)) j

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
  | .h j => (![false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, true] : Fin 213 → Bool) j

theorem top_flag (s : Fin 7) : kidIsTop (.h (top s)) = true := by
  revert s
  decide +kernel

theorem input_not_top (j : Fin 213) (i : Fin 3) : kidIsTop (kid j i) = false := by
  revert j i
  decide +kernel

theorem kid_ne_top (j : Fin 213) (i : Fin 3) (s : Fin 7) : kid j i ≠ .h (top s) := by
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

def topSet : Finset (Fin 213) := {176, 182, 188, 194, 200, 206, 212}

theorem mem_topSet (j : Fin 213) : j ∈ topSet ↔ ∃ s, top s = j := by
  revert j
  decide

/-- Hash kids of each node, as literal finsets for cheap kernel evaluation. -/
def kidsH : Fin 213 → Finset (Fin 213) := ![
  ∅, {0}, ∅, {0, 1, 2}, {0}, {1, 3, 4}, ∅, {0, 1, 6}, {3, 5, 7}, {0}, {1, 3, 9}, {5, 8, 10}, ∅, {0, 1, 12}, {3, 5, 13}, {8, 11, 14}, {0}, {1, 3, 16}, {5, 8, 17}, {11, 15, 18}, ∅, {0, 1, 20}, {3, 5, 21}, {8, 11, 22}, {15, 19, 23}, {0}, {1, 3, 25}, {5, 8, 26}, {11, 15, 27}, {19, 24, 28}, ∅, {0, 1, 30}, {3, 5, 31}, {8, 11, 32}, {15, 19, 33}, {24, 29, 34}, {0}, {1, 3, 36}, {5, 8, 37}, {11, 15, 38}, {19, 24, 39}, {29, 35, 40}, {0, 1}, {3, 5, 42}, {8, 11, 43}, {15, 19, 44}, {24, 29, 45}, {35, 41, 46}, {1, 3}, {5, 8, 48}, {11, 15, 49}, {19, 24, 50}, {29, 35, 51}, {41, 47, 52}, {3, 5}, {8, 11, 54}, {15, 19, 55}, {24, 29, 56}, {35, 41, 57}, {47, 53, 58}, {5, 8}, {11, 15, 60}, {19, 24, 61}, {29, 35, 62}, {41, 47, 63}, {53, 59, 64}, {8, 11}, {15, 19, 66}, {24, 29, 67}, {35, 41, 68}, {47, 53, 69}, {59, 65, 70}, {11, 15}, {19, 24, 72}, {29, 35, 73}, {41, 47, 74}, {53, 59, 75}, {65, 71, 76}, {15, 19}, {24, 29, 78}, {35, 41, 79}, {47, 53, 80}, {59, 65, 81}, {71, 77, 82}, {19, 24}, {29, 35, 84}, {41, 47, 85}, {53, 59, 86}, {65, 71, 87}, {77, 83, 88}, {24, 29}, {35, 41, 90}, {47, 53, 91}, {59, 65, 92}, {71, 77, 93}, {83, 89, 94}, {29, 35}, {41, 47, 96}, {53, 59, 97}, {65, 71, 98}, {77, 83, 99}, {89, 95, 100}, {35, 41}, {47, 53, 102}, {59, 65, 103}, {71, 77, 104}, {83, 89, 105}, {41, 47}, {53, 59, 107}, {65, 71, 108}, {77, 83, 109}, {89, 95, 110}, {101, 106, 111}, {47, 53}, {59, 65, 113}, {71, 77, 114}, {95, 101, 115}, {106, 112, 116}, {53, 59}, {65, 71, 118}, {77, 83, 119}, {89, 95, 120}, {101, 106, 121}, {112, 117, 122}, {59, 65}, {71, 77, 124}, {83, 89, 125}, {95, 101, 126}, {117, 123, 127}, {65, 71}, {77, 83, 129}, {89, 95, 130}, {101, 106, 131}, {112, 117, 132}, {123, 128, 133}, {71, 77}, {83, 89, 135}, {95, 101, 136}, {106, 112, 137}, {117, 123, 138}, {128, 134, 139}, {77, 83}, {89, 95, 141}, {101, 106, 142}, {112, 117, 143}, {123, 128, 144}, {134, 140, 145}, {83, 89}, {95, 101, 147}, {106, 112, 148}, {117, 123, 149}, {128, 134, 150}, {140, 146, 151}, {83, 89}, {95, 101, 153}, {106, 112, 154}, {117, 123, 155}, {134, 140, 156}, {146, 152, 157}, {83, 89}, {95, 101, 159}, {106, 112, 160}, {123, 128, 161}, {140, 146, 162}, {152, 158, 163}, {83, 89}, {95, 101, 165}, {106, 112, 166}, {128, 134, 167}, {140, 146, 168}, {152, 158, 169}, {89, 95}, {101, 112, 171}, {117, 123, 172}, {128, 134, 173}, {140, 146, 174}, {152, 158, 175}, {89, 95}, {101, 112, 177}, {117, 123, 178}, {128, 134, 179}, {140, 146, 180}, {164, 170, 181}, {95, 101}, {106, 112, 183}, {117, 123, 184}, {128, 134, 185}, {146, 158, 186}, {164, 170, 187}, {95, 101}, {106, 112, 189}, {117, 123, 190}, {128, 134, 191}, {146, 158, 192}, {164, 170, 193}, {95, 101}, {106, 112, 195}, {117, 123, 196}, {128, 134, 197}, {152, 158, 198}, {164, 170, 199}, {95, 101}, {106, 112, 201}, {117, 123, 202}, {134, 140, 203}, {152, 158, 204}, {164, 170, 205}, {95, 101}, {106, 112, 207}, {117, 123, 208}, {140, 146, 209}, {152, 158, 210}, {164, 170, 211}]

/-- Chain kids of each node. -/
def kidsC : Fin 213 → Finset (Fin 42) := ![
  {0, 0, 1}, {0, 2}, {0, 0, 3}, ∅, {0, 4}, ∅, {0, 0, 5}, ∅, ∅, {0, 6}, ∅, ∅, {0, 0, 7}, ∅, ∅, ∅, {0, 8}, ∅, ∅, ∅, {0, 0, 9}, ∅, ∅, ∅, ∅, {0, 10}, ∅, ∅, ∅, ∅, {0, 0, 11}, ∅, ∅, ∅, ∅, ∅, {0, 12}, ∅, ∅, ∅, ∅, ∅, {13}, ∅, ∅, ∅, ∅, ∅, {14}, ∅, ∅, ∅, ∅, ∅, {15}, ∅, ∅, ∅, ∅, ∅, {16}, ∅, ∅, ∅, ∅, ∅, {17}, ∅, ∅, ∅, ∅, ∅, {18}, ∅, ∅, ∅, ∅, ∅, {19}, ∅, ∅, ∅, ∅, ∅, {20}, ∅, ∅, ∅, ∅, ∅, {21}, ∅, ∅, ∅, ∅, ∅, {22}, ∅, ∅, ∅, ∅, ∅, {23}, ∅, ∅, ∅, ∅, {24}, ∅, ∅, ∅, ∅, ∅, {25}, ∅, ∅, ∅, ∅, {26}, ∅, ∅, ∅, ∅, ∅, {27}, ∅, ∅, ∅, ∅, {28}, ∅, ∅, ∅, ∅, ∅, {29}, ∅, ∅, ∅, ∅, ∅, {30}, ∅, ∅, ∅, ∅, ∅, {31}, ∅, ∅, ∅, ∅, ∅, {32}, ∅, ∅, ∅, ∅, ∅, {33}, ∅, ∅, ∅, ∅, ∅, {34}, ∅, ∅, ∅, ∅, ∅, {35}, ∅, ∅, ∅, ∅, ∅, {36}, ∅, ∅, ∅, ∅, ∅, {37}, ∅, ∅, ∅, ∅, ∅, {38}, ∅, ∅, ∅, ∅, ∅, {39}, ∅, ∅, ∅, ∅, ∅, {40}, ∅, ∅, ∅, ∅, ∅, {41}, ∅, ∅, ∅, ∅, ∅]

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

theorem top_mem_neededH (E : Finset (Fin 213)) (s : Fin 7) : top s ∈ neededH E :=
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
  if i < 213 then (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 1 else 0)) else (if i < 4 then 7 else (if i < 5 then 1 else 26))) else (if i < 9 then (if i < 7 then 0 else (if i < 8 then 67 else 168)) else (if i < 11 then (if i < 10 then 1 else 522) else (if i < 12 then 1312 else 0)))) else (if i < 19 then (if i < 16 then (if i < 14 then 4099 else (if i < 15 then 8232 else 18688)) else (if i < 17 then 1 else (if i < 18 then 65546 else 131360))) else (if i < 22 then (if i < 20 then 296960 else (if i < 21 then 0 else 1048579)) else (if i < 24 then (if i < 23 then 2097192 else 4196608) else (if i < 25 then 8945664 else 1))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 33554442 else (if i < 28 then 67109152 else 134252544)) else (if i < 30 then 285736960 else (if i < 31 then 0 else 1073741827))) else (if i < 35 then (if i < 33 then 2147483688 else (if i < 34 then 4294969600 else 8590491648)) else (if i < 37 then (if i < 36 then 17733517312 else 1) else (if i < 38 then 68719476746 else 137438953760)))) else (if i < 46 then (if i < 42 then (if i < 40 then 274877941760 else (if i < 41 then 549773115392 else 1134408237056)) else (if i < 44 then (if i < 43 then 3 else 4398046511144) else (if i < 45 then 8796093024512 else 17592186601472))) else (if i < 49 then (if i < 47 then 35184925736960 else (if i < 48 then 72602127171584 else 10)) else (if i < 51 then (if i < 50 then 281474976710944 else 562949953456128) else (if i < 52 then 1125899924144128 else 2251834710294528)))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then 4646536138981376 else (if i < 55 then 40 else 18014398509484288)) else (if i < 57 then 36028797019521024 else (if i < 58 then 72057594591576064 else 144117421458849792))) else (if i < 62 then (if i < 60 then 297378312894808064 else (if i < 61 then 288 else 1152921504606881792)) else (if i < 64 then (if i < 63 then 2305843009230995456 else 4611686053323997184) else (if i < 65 then 9223514973366386688 else 19032212025267716096)))) else (if i < 72 then (if i < 69 then (if i < 67 then 2304 else (if i < 68 then 73786976294838763520 else 147573952590230061056)) else (if i < 70 then 295147907412735819776 else (if i < 71 then 590304958295448748032 else 1218061569617133830144))) else (if i < 75 then (if i < 73 then 34816 else (if i < 74 then 4722366482869662515200 else 9444732965774187036672)) else (if i < 77 then (if i < 76 then 18889466074415092465664 else 37779517330908719874048) else (if i < 78 then 77955940455496565129216 else 557056))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then 302231454903657847324672 else (if i < 81 then 604462909809547970347008 else 1208925828762565917802496)) else (if i < 83 then 2417889109178158071939072 else (if i < 84 then 4989180189151780168269824 else 17301504))) else (if i < 88 then (if i < 86 then 19342813113834101691908096 else (if i < 87 then 38685626227811070102208512 else 77371253040804218739359744)) else (if i < 90 then (if i < 89 then 154744902987402116604100608 else 319307532105713930769268736) else (if i < 91 then 553648128 else 1237940039285382508282118144)))) else (if i < 99 then (if i < 95 then (if i < 93 then 2475880078579908486541344768 else (if i < 94 then 4951760194611469999319023616 else 9903673791193735462662438912)) else (if i < 97 then (if i < 96 then 20435682054765691569233199104 else 34896609280) else (if i < 98 then 79228162514264480530055561216 else 158456325029114143138646065152))) else (if i < 102 then (if i < 100 then 316912652455134079956417511424 else (if i < 101 then 633835122636399069610396090368 else 1307883651505004260430924742656)) else (if i < 104 then (if i < 103 then 2233382993920 else 5070602400912926753923555917824) else (if i < 105 then 10141204801863305160873348169728 else 20282409757128581117210720731136))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then 40565447848729540455065349783552 else (if i < 108 then 142936511610880 else 162259276829213948859529568452608)) else (if i < 110 then 324518553660824803512738262286336 else (if i < 111 then 649037117139375737935174085640192 else 1298114447684983681991558303842304))) else (if i < 115 then (if i < 113 then 2679813368882476954764030576164864 else (if i < 114 then 9147936743096320 else 10384593717069692727009892380966912)) else (if i < 117 then (if i < 116 then 20769187434292787424815248786325504 else 41540949783560334619215760812146688) else (if i < 118 then 88350176233506676366714226601885696 else 585467951558164480)))) else (if i < 125 then (if i < 122 then (if i < 120 then 332306998946231366302681347311796224 else (if i < 121 then 664613997902280458736272392184659968 else 1329228036017967149678665994501881856)) else (if i < 123 then 2658539656509446808948112902972243968 else (if i < 124 then 5488257779471312803356734619985641472 else 37469948899722526720))) else (if i < 128 then (if i < 126 then 21267647932558807443371606227954958336 else (if i < 127 then 42535295865745949359121433099818237952 else 85070594305149897579434623648120438784)) else (if i < 130 then (if i < 129 then 180941160926221673199030736080661905408 else 2398076729582241710080) else (if i < 131 then 680564733841886749449033583725580910592 else 1361129467723986905130273288661294383104))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then 2722259019032447322770137358236557246464 else (if i < 134 then 5444689216531347064725735225287155646464 else 11239951932357248621274592501730593734656)) else (if i < 136 then 153476910693263469445120 else (if i < 137 then 43556142965880751964738149358437178277888 else 87112285934335161928337490474322840518656))) else (if i < 141 then (if i < 139 then 174224577136946990242682109231350658629632 else (if i < 140 then 348459943704506739027962941442495426330624 else 719016641303942973298110545503326230806528)) else (if i < 143 then (if i < 142 then 9822522284368862044487680 else 2787593149816368125743241558939979409784832) else (if i < 144 then 5575186299716320724998992708660872788049920 else 11150372770611107902417170877830559617253376)))) else (if i < 152 then (if i < 148 then (if i < 146 then 22301096114721510359326164877712275516948480 else (if i < 147 then 46017065043452350291079074912212878771617792 else 628641426199607170847211520)) else (if i < 150 then (if i < 149 then 178405961588247560047567459772158682226229248 else 356811923181763396761520926672600069430050816) else (if i < 151 then 713623857152957406281584452068179932969172992 else 1427269811059809742058411088798978201316491264))) else (if i < 155 then (if i < 153 then 2945092162780950418629060794381624241383538688 else (if i < 154 then 628641426199607170847211520 else 11417981541647681623381569469186932881240358912)) else (if i < 157 then (if i < 156 then 22835963083300631523429524945502148467458310144 else 45671926177390693659617592489727276729025691648) else (if i < 158 then 91345267907827823491738309683134604884255440896 else 188485898417980826792259890840423951448546476032)))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then 628641426199607170847211520 else (if i < 161 then 730750818665451461676757698071732481618144657408 else 1461501637330908191630181782150593245941266907136)) else (if i < 163 then 2923003275012722027294587455879171103225876054016 else (if i < 164 then 5846097146100980703471251819720614712592348217344 else 12063097498750772914704633013787132892706974466048))) else (if i < 168 then (if i < 166 then 628641426199607170847211520 else (if i < 167 then 46768052394588893385092829928634647600780019761152 else 93536104789177792038462326243276423484265017114624)) else (if i < 170 then (if i < 169 then 187072209600473927379932658712803575999024299245568 else 374144509753488516090799829664223935665887349047296) else (if i < 171 then 748659922713525843689361788702793774799296976125952 else 40233051276774858934221537280)))) else (if i < 179 then (if i < 175 then (if i < 173 then 2993155353253689181675978697138231711588839583645696 else (if i < 174 then 5986310706507389152939758827247362591943064473829376 else 11972621413036875059774447149736909846504464325804032)) else (if i < 177 then (if i < 176 then 23945242916626290780879828811712436476676767402164224 else 47890856736459130373267419752799218856821057082359808) else (if i < 178 then 40233051276774858934221537280 else 191561942608236107299988210553523932039675880008581120))) else (if i < 182 then (if i < 180 then 383123885216472225389564222540018763248117145323700224 else (if i < 181 then 766247770432966547533023374575279711158852626025545728 else 1532495540956485635727377683662798039101373090801647616)) else (if i < 184 then (if i < 183 then 3066511043434601855751625886526643301577920414211899392 else 2574915281713590971790178385920) else (if i < 185 then 12259964326927110866872049643699422903260139262803181568 else 24519928653854221744533529900157388405243258319715434496))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then 49039857307708465585820954729810018995149134974809014272 else (if i < 188 then 98079714980881499248454061781107138803760652179757596672 else 196160949192536598008903351307465600437539049809345773568)) else (if i < 190 then 2574915281713590971790178385920 else (if i < 191 then 784637716923335095479478951327455251447104656843338678272 else 1569275433846670190969747333267669045492932293480786427904))) else (if i < 195 then (if i < 193 then 3138550867693340404036248561464833333170527205296951001088 else (if i < 194 then 6277101735752145376149309275251153767154516792824041570304 else 12554204990735064351810613778247558857139051331097913720832)) else (if i < 197 then (if i < 196 then 2574915281713590971790178385920 else 50216813883093446110686320659087828278253153781997610467328) else (if i < 198 then 100433627766186892221383430748788415099105030543789330006016 else 200867255532373784464863615392506325440394723705914038157312)))) else (if i < 206 then (if i < 202 then (if i < 200 then 401734511065118653285594072654365804982607617181157722947584 else (if i < 201 then 803469023649456840595120081102413527286035837333566262345728 else 2574915281713590971790178385920)) else (if i < 204 then (if i < 203 then 3213876088517980551083924189955751701993840297791871004966912 else 6427752177035961102167859169342116162530279318563536119005184) else (if i < 205 then 12855504354071922205751271385120404828185262317178498442067968 else 25711008708144215493071497027027676794707304769260144878944256))) else (if i < 209 then (if i < 207 then 51422017417807650520166925989849035506735430141491540574339072 else (if i < 208 then 2574915281713590971790178385920 else 205688069665150755269371147824942239619791417514423768252940288)) else (if i < 211 then (if i < 210 then 411376139330301510538742306439315091998125433751827330614951936 else 822752278660603021168081368647705909003856788299423900292349952) else (if i < 212 then 1645504557321206413239369286106919580137087922502315322862731264 else 3291009114643932046012762504149632842191496665607601896541913088)))))))) else 0

def kcMask (i : ℕ) : ℕ :=
  if i < 213 then (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 3 else (if i < 2 then 5 else 9)) else (if i < 4 then 0 else (if i < 5 then 17 else 0))) else (if i < 9 then (if i < 7 then 33 else (if i < 8 then 0 else 0)) else (if i < 11 then (if i < 10 then 65 else 0) else (if i < 12 then 0 else 129)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0 else (if i < 15 then 0 else 0)) else (if i < 17 then 257 else (if i < 18 then 0 else 0))) else (if i < 22 then (if i < 20 then 0 else (if i < 21 then 513 else 0)) else (if i < 24 then (if i < 23 then 0 else 0) else (if i < 25 then 0 else 1025))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 0 else (if i < 28 then 0 else 0)) else (if i < 30 then 0 else (if i < 31 then 2049 else 0))) else (if i < 35 then (if i < 33 then 0 else (if i < 34 then 0 else 0)) else (if i < 37 then (if i < 36 then 0 else 4097) else (if i < 38 then 0 else 0)))) else (if i < 46 then (if i < 42 then (if i < 40 then 0 else (if i < 41 then 0 else 0)) else (if i < 44 then (if i < 43 then 8192 else 0) else (if i < 45 then 0 else 0))) else (if i < 49 then (if i < 47 then 0 else (if i < 48 then 0 else 16384)) else (if i < 51 then (if i < 50 then 0 else 0) else (if i < 52 then 0 else 0)))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then 0 else (if i < 55 then 32768 else 0)) else (if i < 57 then 0 else (if i < 58 then 0 else 0))) else (if i < 62 then (if i < 60 then 0 else (if i < 61 then 65536 else 0)) else (if i < 64 then (if i < 63 then 0 else 0) else (if i < 65 then 0 else 0)))) else (if i < 72 then (if i < 69 then (if i < 67 then 131072 else (if i < 68 then 0 else 0)) else (if i < 70 then 0 else (if i < 71 then 0 else 0))) else (if i < 75 then (if i < 73 then 262144 else (if i < 74 then 0 else 0)) else (if i < 77 then (if i < 76 then 0 else 0) else (if i < 78 then 0 else 524288))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then 0 else (if i < 81 then 0 else 0)) else (if i < 83 then 0 else (if i < 84 then 0 else 1048576))) else (if i < 88 then (if i < 86 then 0 else (if i < 87 then 0 else 0)) else (if i < 90 then (if i < 89 then 0 else 0) else (if i < 91 then 2097152 else 0)))) else (if i < 99 then (if i < 95 then (if i < 93 then 0 else (if i < 94 then 0 else 0)) else (if i < 97 then (if i < 96 then 0 else 4194304) else (if i < 98 then 0 else 0))) else (if i < 102 then (if i < 100 then 0 else (if i < 101 then 0 else 0)) else (if i < 104 then (if i < 103 then 8388608 else 0) else (if i < 105 then 0 else 0))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then 0 else (if i < 108 then 16777216 else 0)) else (if i < 110 then 0 else (if i < 111 then 0 else 0))) else (if i < 115 then (if i < 113 then 0 else (if i < 114 then 33554432 else 0)) else (if i < 117 then (if i < 116 then 0 else 0) else (if i < 118 then 0 else 67108864)))) else (if i < 125 then (if i < 122 then (if i < 120 then 0 else (if i < 121 then 0 else 0)) else (if i < 123 then 0 else (if i < 124 then 0 else 134217728))) else (if i < 128 then (if i < 126 then 0 else (if i < 127 then 0 else 0)) else (if i < 130 then (if i < 129 then 0 else 268435456) else (if i < 131 then 0 else 0))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then 0 else (if i < 134 then 0 else 0)) else (if i < 136 then 536870912 else (if i < 137 then 0 else 0))) else (if i < 141 then (if i < 139 then 0 else (if i < 140 then 0 else 0)) else (if i < 143 then (if i < 142 then 1073741824 else 0) else (if i < 144 then 0 else 0)))) else (if i < 152 then (if i < 148 then (if i < 146 then 0 else (if i < 147 then 0 else 2147483648)) else (if i < 150 then (if i < 149 then 0 else 0) else (if i < 151 then 0 else 0))) else (if i < 155 then (if i < 153 then 0 else (if i < 154 then 4294967296 else 0)) else (if i < 157 then (if i < 156 then 0 else 0) else (if i < 158 then 0 else 0)))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then 8589934592 else (if i < 161 then 0 else 0)) else (if i < 163 then 0 else (if i < 164 then 0 else 0))) else (if i < 168 then (if i < 166 then 17179869184 else (if i < 167 then 0 else 0)) else (if i < 170 then (if i < 169 then 0 else 0) else (if i < 171 then 0 else 34359738368)))) else (if i < 179 then (if i < 175 then (if i < 173 then 0 else (if i < 174 then 0 else 0)) else (if i < 177 then (if i < 176 then 0 else 0) else (if i < 178 then 68719476736 else 0))) else (if i < 182 then (if i < 180 then 0 else (if i < 181 then 0 else 0)) else (if i < 184 then (if i < 183 then 0 else 137438953472) else (if i < 185 then 0 else 0))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then 0 else (if i < 188 then 0 else 0)) else (if i < 190 then 274877906944 else (if i < 191 then 0 else 0))) else (if i < 195 then (if i < 193 then 0 else (if i < 194 then 0 else 0)) else (if i < 197 then (if i < 196 then 549755813888 else 0) else (if i < 198 then 0 else 0)))) else (if i < 206 then (if i < 202 then (if i < 200 then 0 else (if i < 201 then 0 else 1099511627776)) else (if i < 204 then (if i < 203 then 0 else 0) else (if i < 205 then 0 else 0))) else (if i < 209 then (if i < 207 then 0 else (if i < 208 then 2199023255552 else 0)) else (if i < 211 then (if i < 210 then 0 else 0) else (if i < 212 then 0 else 0)))))))) else 0

/-- Bit mask of the seven block tops. -/
def topMask : ℕ := 6686494709113221679688380836206894168037833131400321806700118016

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
  if i < 213 then (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then [0, 1] else (if i < 2 then [0, 2] else [0, 3])) else (if i < 4 then [] else (if i < 5 then [0, 4] else []))) else (if i < 9 then (if i < 7 then [0, 5] else (if i < 8 then [] else [])) else (if i < 11 then (if i < 10 then [0, 6] else []) else (if i < 12 then [] else [0, 7])))) else (if i < 19 then (if i < 16 then (if i < 14 then [] else (if i < 15 then [] else [])) else (if i < 17 then [0, 8] else (if i < 18 then [] else []))) else (if i < 22 then (if i < 20 then [] else (if i < 21 then [0, 9] else [])) else (if i < 24 then (if i < 23 then [] else []) else (if i < 25 then [] else [0, 10]))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then [] else (if i < 28 then [] else [])) else (if i < 30 then [] else (if i < 31 then [0, 11] else []))) else (if i < 35 then (if i < 33 then [] else (if i < 34 then [] else [])) else (if i < 37 then (if i < 36 then [] else [0, 12]) else (if i < 38 then [] else [])))) else (if i < 46 then (if i < 42 then (if i < 40 then [] else (if i < 41 then [] else [])) else (if i < 44 then (if i < 43 then [13] else []) else (if i < 45 then [] else []))) else (if i < 49 then (if i < 47 then [] else (if i < 48 then [] else [14])) else (if i < 51 then (if i < 50 then [] else []) else (if i < 52 then [] else [])))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then [] else (if i < 55 then [15] else [])) else (if i < 57 then [] else (if i < 58 then [] else []))) else (if i < 62 then (if i < 60 then [] else (if i < 61 then [16] else [])) else (if i < 64 then (if i < 63 then [] else []) else (if i < 65 then [] else [])))) else (if i < 72 then (if i < 69 then (if i < 67 then [17] else (if i < 68 then [] else [])) else (if i < 70 then [] else (if i < 71 then [] else []))) else (if i < 75 then (if i < 73 then [18] else (if i < 74 then [] else [])) else (if i < 77 then (if i < 76 then [] else []) else (if i < 78 then [] else [19]))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then [] else (if i < 81 then [] else [])) else (if i < 83 then [] else (if i < 84 then [] else [20]))) else (if i < 88 then (if i < 86 then [] else (if i < 87 then [] else [])) else (if i < 90 then (if i < 89 then [] else []) else (if i < 91 then [21] else [])))) else (if i < 99 then (if i < 95 then (if i < 93 then [] else (if i < 94 then [] else [])) else (if i < 97 then (if i < 96 then [] else [22]) else (if i < 98 then [] else []))) else (if i < 102 then (if i < 100 then [] else (if i < 101 then [] else [])) else (if i < 104 then (if i < 103 then [23] else []) else (if i < 105 then [] else []))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then [] else (if i < 108 then [24] else [])) else (if i < 110 then [] else (if i < 111 then [] else []))) else (if i < 115 then (if i < 113 then [] else (if i < 114 then [25] else [])) else (if i < 117 then (if i < 116 then [] else []) else (if i < 118 then [] else [26])))) else (if i < 125 then (if i < 122 then (if i < 120 then [] else (if i < 121 then [] else [])) else (if i < 123 then [] else (if i < 124 then [] else [27]))) else (if i < 128 then (if i < 126 then [] else (if i < 127 then [] else [])) else (if i < 130 then (if i < 129 then [] else [28]) else (if i < 131 then [] else []))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then [] else (if i < 134 then [] else [])) else (if i < 136 then [29] else (if i < 137 then [] else []))) else (if i < 141 then (if i < 139 then [] else (if i < 140 then [] else [])) else (if i < 143 then (if i < 142 then [30] else []) else (if i < 144 then [] else [])))) else (if i < 152 then (if i < 148 then (if i < 146 then [] else (if i < 147 then [] else [31])) else (if i < 150 then (if i < 149 then [] else []) else (if i < 151 then [] else []))) else (if i < 155 then (if i < 153 then [] else (if i < 154 then [32] else [])) else (if i < 157 then (if i < 156 then [] else []) else (if i < 158 then [] else [])))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then [33] else (if i < 161 then [] else [])) else (if i < 163 then [] else (if i < 164 then [] else []))) else (if i < 168 then (if i < 166 then [34] else (if i < 167 then [] else [])) else (if i < 170 then (if i < 169 then [] else []) else (if i < 171 then [] else [35])))) else (if i < 179 then (if i < 175 then (if i < 173 then [] else (if i < 174 then [] else [])) else (if i < 177 then (if i < 176 then [] else []) else (if i < 178 then [36] else []))) else (if i < 182 then (if i < 180 then [] else (if i < 181 then [] else [])) else (if i < 184 then (if i < 183 then [] else [37]) else (if i < 185 then [] else []))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then [] else (if i < 188 then [] else [])) else (if i < 190 then [38] else (if i < 191 then [] else []))) else (if i < 195 then (if i < 193 then [] else (if i < 194 then [] else [])) else (if i < 197 then (if i < 196 then [39] else []) else (if i < 198 then [] else [])))) else (if i < 206 then (if i < 202 then (if i < 200 then [] else (if i < 201 then [] else [40])) else (if i < 204 then (if i < 203 then [] else []) else (if i < 205 then [] else []))) else (if i < 209 then (if i < 207 then [] else (if i < 208 then [41] else [])) else (if i < 211 then (if i < 210 then [] else []) else (if i < 212 then [] else [])))))))) else []

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
  if i < 214 then (if i < 107 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0 else (if i < 2 then 3 else 7)) else (if i < 4 then 15 else (if i < 5 then 15 else 31))) else (if i < 9 then (if i < 7 then 31 else (if i < 8 then 63 else 63)) else (if i < 11 then (if i < 10 then 63 else 127) else (if i < 12 then 127 else 127)))) else (if i < 19 then (if i < 16 then (if i < 14 then 255 else (if i < 15 then 255 else 255)) else (if i < 17 then 255 else (if i < 18 then 511 else 511))) else (if i < 22 then (if i < 20 then 511 else (if i < 21 then 511 else 1023)) else (if i < 24 then (if i < 23 then 1023 else 1023) else (if i < 25 then 1023 else 1023))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 2047 else (if i < 28 then 2047 else 2047)) else (if i < 30 then 2047 else (if i < 31 then 2047 else 4095))) else (if i < 35 then (if i < 33 then 4095 else (if i < 34 then 4095 else 4095)) else (if i < 37 then (if i < 36 then 4095 else 4095) else (if i < 38 then 8191 else 8191)))) else (if i < 46 then (if i < 42 then (if i < 40 then 8191 else (if i < 41 then 8191 else 8191)) else (if i < 44 then (if i < 43 then 8191 else 16383) else (if i < 45 then 16383 else 16383))) else (if i < 49 then (if i < 47 then 16383 else (if i < 48 then 16383 else 16383)) else (if i < 51 then (if i < 50 then 32767 else 32767) else (if i < 52 then 32767 else 32767)))))) else (if i < 80 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then 32767 else (if i < 55 then 32767 else 65535)) else (if i < 57 then 65535 else (if i < 58 then 65535 else 65535))) else (if i < 62 then (if i < 60 then 65535 else (if i < 61 then 65535 else 131071)) else (if i < 64 then (if i < 63 then 131071 else 131071) else (if i < 65 then 131071 else 131071)))) else (if i < 73 then (if i < 69 then (if i < 67 then 131071 else (if i < 68 then 262143 else 262143)) else (if i < 71 then (if i < 70 then 262143 else 262143) else (if i < 72 then 262143 else 262143))) else (if i < 76 then (if i < 74 then 524287 else (if i < 75 then 524287 else 524287)) else (if i < 78 then (if i < 77 then 524287 else 524287) else (if i < 79 then 524287 else 1048575))))) else (if i < 93 then (if i < 86 then (if i < 83 then (if i < 81 then 1048575 else (if i < 82 then 1048575 else 1048575)) else (if i < 84 then 1048575 else (if i < 85 then 1048575 else 2097151))) else (if i < 89 then (if i < 87 then 2097151 else (if i < 88 then 2097151 else 2097151)) else (if i < 91 then (if i < 90 then 2097151 else 2097151) else (if i < 92 then 4194303 else 4194303)))) else (if i < 100 then (if i < 96 then (if i < 94 then 4194303 else (if i < 95 then 4194303 else 4194303)) else (if i < 98 then (if i < 97 then 4194303 else 8388607) else (if i < 99 then 8388607 else 8388607))) else (if i < 103 then (if i < 101 then 8388607 else (if i < 102 then 8388607 else 8388607)) else (if i < 105 then (if i < 104 then 16777215 else 16777215) else (if i < 106 then 16777215 else 16777215))))))) else (if i < 160 then (if i < 133 then (if i < 120 then (if i < 113 then (if i < 110 then (if i < 108 then 16777215 else (if i < 109 then 33554431 else 33554431)) else (if i < 111 then 33554431 else (if i < 112 then 33554431 else 33554431))) else (if i < 116 then (if i < 114 then 33554431 else (if i < 115 then 67108863 else 67108863)) else (if i < 118 then (if i < 117 then 67108863 else 67108863) else (if i < 119 then 67108863 else 134217727)))) else (if i < 126 then (if i < 123 then (if i < 121 then 134217727 else (if i < 122 then 134217727 else 134217727)) else (if i < 124 then 134217727 else (if i < 125 then 134217727 else 268435455))) else (if i < 129 then (if i < 127 then 268435455 else (if i < 128 then 268435455 else 268435455)) else (if i < 131 then (if i < 130 then 268435455 else 536870911) else (if i < 132 then 536870911 else 536870911))))) else (if i < 146 then (if i < 139 then (if i < 136 then (if i < 134 then 536870911 else (if i < 135 then 536870911 else 536870911)) else (if i < 137 then 1073741823 else (if i < 138 then 1073741823 else 1073741823))) else (if i < 142 then (if i < 140 then 1073741823 else (if i < 141 then 1073741823 else 1073741823)) else (if i < 144 then (if i < 143 then 2147483647 else 2147483647) else (if i < 145 then 2147483647 else 2147483647)))) else (if i < 153 then (if i < 149 then (if i < 147 then 2147483647 else (if i < 148 then 2147483647 else 4294967295)) else (if i < 151 then (if i < 150 then 4294967295 else 4294967295) else (if i < 152 then 4294967295 else 4294967295))) else (if i < 156 then (if i < 154 then 4294967295 else (if i < 155 then 8589934591 else 8589934591)) else (if i < 158 then (if i < 157 then 8589934591 else 8589934591) else (if i < 159 then 8589934591 else 8589934591)))))) else (if i < 187 then (if i < 173 then (if i < 166 then (if i < 163 then (if i < 161 then 17179869183 else (if i < 162 then 17179869183 else 17179869183)) else (if i < 164 then 17179869183 else (if i < 165 then 17179869183 else 17179869183))) else (if i < 169 then (if i < 167 then 34359738367 else (if i < 168 then 34359738367 else 34359738367)) else (if i < 171 then (if i < 170 then 34359738367 else 34359738367) else (if i < 172 then 34359738367 else 68719476735)))) else (if i < 180 then (if i < 176 then (if i < 174 then 68719476735 else (if i < 175 then 68719476735 else 68719476735)) else (if i < 178 then (if i < 177 then 68719476735 else 68719476735) else (if i < 179 then 137438953471 else 137438953471))) else (if i < 183 then (if i < 181 then 137438953471 else (if i < 182 then 137438953471 else 137438953471)) else (if i < 185 then (if i < 184 then 137438953471 else 274877906943) else (if i < 186 then 274877906943 else 274877906943))))) else (if i < 200 then (if i < 193 then (if i < 190 then (if i < 188 then 274877906943 else (if i < 189 then 274877906943 else 274877906943)) else (if i < 191 then 549755813887 else (if i < 192 then 549755813887 else 549755813887))) else (if i < 196 then (if i < 194 then 549755813887 else (if i < 195 then 549755813887 else 549755813887)) else (if i < 198 then (if i < 197 then 1099511627775 else 1099511627775) else (if i < 199 then 1099511627775 else 1099511627775)))) else (if i < 207 then (if i < 203 then (if i < 201 then 1099511627775 else (if i < 202 then 1099511627775 else 2199023255551)) else (if i < 205 then (if i < 204 then 2199023255551 else 2199023255551) else (if i < 206 then 2199023255551 else 2199023255551))) else (if i < 210 then (if i < 208 then 2199023255551 else (if i < 209 then 4398046511103 else 4398046511103)) else (if i < 212 then (if i < 211 then 4398046511103 else 4398046511103) else (if i < 213 then 4398046511103 else 4398046511103)))))))) else 4398046511103

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
  · have h : (176 : Fin 213) ∈ neededH ∅ \ ∅ := by simp [neededH, topSet]
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
def reconstructionCost (c : Choice) : ℕ := 2 + choiceCost c

def choiceTuples : Finset Choice := Fintype.piFinset fun _ : Fin 1 => localSet

theorem mem_choiceTuples (c : Choice) : c ∈ choiceTuples ↔ ∀ b, c b ∈ localSet := by
  rw [choiceTuples, Fintype.mem_piFinset]

/-- The supported layer: valid blocks and in-graph cost exactly 82. -/
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
    reconstructionCost c = 84 := by
  rw [reconstructionCost, ((mem_supportedChoices c).1 hc).2]

theorem choiceWords_le {c : Choice} (hc : c ∈ supportedChoices) : choiceWords c ≤ 42 := by
  have h : ∀ b, localWords (c b) ≤ 42 := fun b =>
    shapeWords_le _ ((mem_validShapes _).2 (shapeValid_of_supported hc b))
  calc choiceWords c ≤ ∑ _b : Fin 1, 42 := Finset.sum_le_sum fun b _ => h b
    _ = 42 := by simp

/-! ## Cost generating number -/

/-- Digit base exceeds the proved bound on all canonical choices of cost at most 82. -/
def digitBase : ℕ := 2 ^ 111

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


def privatePathLen : Fin 42 → Fin 9 := ![0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 6, 5, 6, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]
def privatePathAt : Fin 42 → Fin 8 → Fin 213 := ![
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![2, 3, 0, 0, 0, 0, 0, 0],
  ![4, 5, 0, 0, 0, 0, 0, 0],
  ![6, 7, 8, 0, 0, 0, 0, 0],
  ![9, 10, 11, 0, 0, 0, 0, 0],
  ![12, 13, 14, 15, 0, 0, 0, 0],
  ![16, 17, 18, 19, 0, 0, 0, 0],
  ![20, 21, 22, 23, 24, 0, 0, 0],
  ![25, 26, 27, 28, 29, 0, 0, 0],
  ![30, 31, 32, 33, 34, 35, 0, 0],
  ![36, 37, 38, 39, 40, 41, 0, 0],
  ![42, 43, 44, 45, 46, 47, 0, 0],
  ![48, 49, 50, 51, 52, 53, 0, 0],
  ![54, 55, 56, 57, 58, 59, 0, 0],
  ![60, 61, 62, 63, 64, 65, 0, 0],
  ![66, 67, 68, 69, 70, 71, 0, 0],
  ![72, 73, 74, 75, 76, 77, 0, 0],
  ![78, 79, 80, 81, 82, 83, 0, 0],
  ![84, 85, 86, 87, 88, 89, 0, 0],
  ![90, 91, 92, 93, 94, 95, 0, 0],
  ![96, 97, 98, 99, 100, 101, 0, 0],
  ![102, 103, 104, 105, 106, 0, 0, 0],
  ![107, 108, 109, 110, 111, 112, 0, 0],
  ![113, 114, 115, 116, 117, 0, 0, 0],
  ![118, 119, 120, 121, 122, 123, 0, 0],
  ![124, 125, 126, 127, 128, 0, 0, 0],
  ![129, 130, 131, 132, 133, 134, 0, 0],
  ![135, 136, 137, 138, 139, 140, 0, 0],
  ![141, 142, 143, 144, 145, 146, 0, 0],
  ![147, 148, 149, 150, 151, 152, 0, 0],
  ![153, 154, 155, 156, 157, 158, 0, 0],
  ![159, 160, 161, 162, 163, 164, 0, 0],
  ![165, 166, 167, 168, 169, 170, 0, 0],
  ![171, 172, 173, 174, 175, 176, 0, 0],
  ![177, 178, 179, 180, 181, 182, 0, 0],
  ![183, 184, 185, 186, 187, 188, 0, 0],
  ![189, 190, 191, 192, 193, 194, 0, 0],
  ![195, 196, 197, 198, 199, 200, 0, 0],
  ![201, 202, 203, 204, 205, 206, 0, 0],
  ![207, 208, 209, 210, 211, 212, 0, 0]]
def privatePathIndex : Fin 213 → Fin 42 := ![1, 2, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 31, 31, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 38, 38, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41]
def privatePathDepth : Fin 213 → Fin 8 := ![0, 0, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5]

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
    113099319634659274675770978562076933073277537738880106720000000 := by
  decide +kernel


theorem privatePath_inverse (k : Fin 42) (i : Fin 8)
    (h : i.val < (privatePathLen k).val) :
    privatePathIndex (privatePathAt k i) = k ∧
    privatePathDepth (privatePathAt k i) = i := by
  revert k i
  decide +kernel


theorem privatePath_sum (f : Fin 213 → Nat) :
    (∑ k : Fin 42, ∑ i : Fin 8,
      if i.val < (privatePathLen k).val then f (privatePathAt k i) else 0) = ∑ j, f j := by
  rw [← Finset.sum_product', ← Finset.sum_filter]
  refine Finset.sum_bij (fun p _ => privatePathAt p.1 p.2)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p hp q hq he
    have hp' := privatePath_inverse p.1 p.2 (Finset.mem_filter.1 hp).2
    have hq' := privatePath_inverse q.1 q.2 (Finset.mem_filter.1 hq).2
    apply Prod.ext
    · exact hp'.1.symm.trans ((congrArg privatePathIndex he).trans hq'.1)
    · exact hp'.2.symm.trans ((congrArg privatePathDepth he).trans hq'.2)
  · intro j _
    exact ⟨(privatePathIndex j, privatePathDepth j),
      Finset.mem_filter.2 ⟨by simp, (privatePath_cover j).1⟩, (privatePath_cover j).2⟩


theorem localPathFlags_count (v : Local) :
    (∑ k : Fin 42, (List.ofFn (localPathFlags v k)).countP id) = v.1.card := by
  have h (b : Fin 8 → Bool) : (List.ofFn b).countP id =
      ∑ i : Fin 8, if b i then 1 else 0 := by
    have hc (l : List Bool) : l.countP id = (l.map fun b => if b then 1 else 0).sum := by
      induction l with
      | nil => rfl
      | cons b l ih => cases b <;> simp [ih, Nat.add_comm]
    rw [hc, List.map_ofFn, List.sum_ofFn]
    rfl
  simp only [h, localPathFlags, decide_eq_true_eq]
  have hs := privatePath_sum (fun j => if j ∈ v.1 then 1 else 0)
  convert hs.trans (by simp : (∑ j : Fin 213, if j ∈ v.1 then 1 else 0) = v.1.card) using 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all


theorem localPathCode_sum (v : Local) (hv : v ∈ localSet) :
    (∑ k : Fin 42, localPathCode v k) = localCost v := by
  have ht : (∑ k ∈ neededC v.1, (24 - (v.2 k).val)) =
      ∑ k : Fin 42, (24 - (v.2 k).val) := by
    apply Finset.sum_subset (Finset.subset_univ (neededC v.1))
    intro k _ hk
    rw [((mem_localSet v).1 hv).2 k hk]
    rfl
  calc
    (∑ k : Fin 42, localPathCode v k) =
        (∑ k : Fin 42, (List.ofFn (localPathFlags v k)).countP id) +
        ∑ k : Fin 42, (24 - (v.2 k).val) := Finset.sum_add_distrib
    _ = v.1.card + ∑ k ∈ neededC v.1, (24 - (v.2 k).val) := by
      rw [localPathFlags_count, ← ht]
    _ = localCost v := rfl


-- Generic stars-and-bars bound, with one slack coordinate for sum ≤ r.
theorem card_cost_layer_le {α : Type*} (T : Finset α) (z : α → Fin 42 → Nat)
    (cost : α → Nat) (r : Nat)
    (hinj : ∀ v ∈ T, ∀ w ∈ T, z v = z w → v = w)
    (hsum : ∀ v ∈ T, ∑ k, z v k = cost v) :
    (T.filter fun v => cost v ≤ r).card ≤ (42 + r).choose r := by
  classical
  let S := T.filter fun v => cost v ≤ r
  let z' (v : ↥S) : Fin 43 → Nat := Fin.cons (r - cost v.val) (z v.val)
  let f (v : ↥S) : Fin 43 →₀ Nat := Finsupp.equivFunOnFinite.symm (z' v)
  have hf (v : ↥S) : f v ∈ (Finset.univ : Finset (Fin 43)).finsuppAntidiag r := by
    apply Finset.mem_finsuppAntidiag.2
    refine ⟨?_, Finset.subset_univ _⟩
    change (∑ k, z' v k) = r
    rw [Fin.sum_cons, hsum v.val (Finset.mem_filter.1 v.property).1]
    exact Nat.sub_add_cancel (Finset.mem_filter.1 v.property).2
  have hi : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply hinj v.val (Finset.mem_filter.1 v.property).1 w.val (Finset.mem_filter.1 w.property).1
    funext k
    exact congrArg (fun p : Fin 43 →₀ Nat => p k.succ) h
  calc
    S.card = (S.attach.image f).card := by simp [Finset.card_image_of_injective _ hi]
    _ ≤ ((Finset.univ : Finset (Fin 43)).finsuppAntidiag r).card :=
      Finset.card_le_card (by intro x hx; obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hx; exact hf v)
    _ = (42 + r).choose r := by
      rw [Finset.card_finsuppAntidiag_nat_eq_choose]
      simp only [Finset.card_univ, Fintype.card_fin]
      congr 1
      omega

theorem card_localSet_cost_le (r : Nat) :
    (localSet.filter fun v => localCost v ≤ r).card ≤ (42 + r).choose r :=
  card_cost_layer_le localSet localPathCode localCost r
    (fun _ hv _ hw h => localPathCode_injective hv hw h) localPathCode_sum

theorem card_choiceTuples_cost_le (r : Nat) :
    (choiceTuples.filter fun c => choiceCost c ≤ r).card ≤ (42 + r).choose r := by
  apply card_cost_layer_le choiceTuples (fun c => localPathCode (c 0)) choiceCost r
  · intro v hv w hw h
    have he : v 0 = w 0 := localPathCode_injective
      ((mem_choiceTuples v).1 hv 0) ((mem_choiceTuples w).1 hw 0) h
    funext b
    have hb : b = 0 := Subsingleton.elim _ _
    simpa [hb] using he
  · intro v hv
    simpa [choiceCost] using localPathCode_sum (v 0) ((mem_choiceTuples v).1 hv 0)

theorem card_choiceTuples_cost_lt_small :
    (choiceTuples.filter fun c => choiceCost c ≤ 82).card < 2^111 := by
  apply lt_of_le_of_lt (card_choiceTuples_cost_le 82)
  rw [Nat.choose_eq_factorial_div_factorial (by decide)]
  decide +kernel


theorem card_localSet_le : localSet.card ≤ 2 ^ 213 * 25 ^ 42 := by
  have h := Finset.card_le_univ localSet
  simpa [Fintype.card_prod, Fintype.card_finset, Fintype.card_fun] using h

theorem card_choiceTuples_cost_lt :
    (choiceTuples.filter fun c => choiceCost c ≤ 82).card < digitBase := by
  rw [digitBase]
  exact card_choiceTuples_cost_lt_small

theorem blockGen_pow :
    blockGen ^ 1 = ∑ c ∈ choiceTuples, digitBase ^ choiceCost c := by
  rw [blockGen, ← Fin.prod_const, Finset.prod_univ_sum, choiceTuples]
  exact Finset.sum_congr rfl fun c _ => Finset.prod_pow_eq_pow_sum _ _ _

theorem digit_sum_pow_truncated {ι : Type*} (T : Finset ι) (e : ι → Nat)
    {B : Nat} (n : Nat) (hB : (T.filter fun x => e x ≤ n).card < B) :
    (∑ x ∈ T, B ^ e x) / B ^ n % B = (T.filter fun x => e x = n).card := by
  have hm : (∑ x ∈ T, B ^ e x) % B ^ (n+1) =
      (∑ x ∈ T.filter (fun x => e x ≤ n), B ^ e x) % B ^ (n+1) := by
    rw [Finset.sum_filter]
    conv_lhs => rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : e x ≤ n
    · simp [hx]
    · simp only [hx, if_false, Nat.zero_mod]
      exact Nat.mod_eq_zero_of_dvd (pow_dvd_pow B (by omega))
  have hd := digit_sum_pow (T.filter fun x => e x ≤ n) e n hB
  rw [← Nat.mod_mul_right_div_self, ← pow_succ, hm,
    pow_succ, Nat.mod_mul_right_div_self, hd]
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, and_assoc]
  exact and_congr_right fun _ => ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩


theorem card_supportedChoices_eq_digit :
    supportedChoices.card = blockGen ^ 1 / digitBase ^ 82 % digitBase := by
  rw [blockGen_pow, digit_sum_pow_truncated _ _ _ card_choiceTuples_cost_lt, supportedChoices]

theorem digit_from_mod (x b d k y z : Nat) (hk : k = d + 1)
    (hm : x % b^k = y) (hy : y / b^d = z) :
    x^1 / b^d % b = z := by
  subst k
  rw [pow_one, ← Nat.mod_mul_right_div_self, ← pow_succ, hm]
  exact hy


theorem digitBase_exact : digitBase = 2596148429267413814265248164610048 := by
  rw [digitBase]
  decide +kernel

theorem digitMod_exact : digitBase ^ 83 = 24510380440836179026956737688548869385898448254776479188571588190665972822956737164150450354267335973625794882057983265228411976794174864655864632282941174899331463958802396621618762736094519107024738264995988900927457228604499630640393666369142277672818978314911972518523103782203505942620629404201349403306668175652488797079739689377453430638029125262938234677403733790176679864561913330605550414331041270371949979830247918320774616049454235169860644073301860113161023857741635706192929674083549548164423268603459483788650691364873378040236620589434965419582445494489711563477319473887815929523582144123096001876957255497065214621830590721025358500326965270194009711384353775989279723416548189518891769317351941955062113532874770296565598385557085714354406375911656632554531317019149692758306671919800222968898193725435948980261050925315962719517287474868970812369965012956169174282648234767025524689131138609857461789896084841878065877565489157791803125661927492991131582047937300930233218834901744549816304826237488996752232647883338705165176143848405055986850900408831730312162179280943933708370779547120878969031303766519941425377331575755881046949811479399141725998193826498248988214453941555203171446181330692707210943049557725555466875020189704900885318416950773838053616990621556462554436714057734335335658022679942785285742390166126177342827164826185851835758826331914207057742625458637142688509064700927912654080708366747896340924947462720785550735348416946142749570304557524408455909393393650701307991173009854961178262941602769565839296952962132458046579099251569659960461680996530758150320323957128765235307001771246165738692761673332130605944955022479821975459036049305937781763165014250969923977909992300086282458869267059134711644493572989352072690833181152651464779659363259252182698231630984819228806506489296814718961823348180249348380923486877045450178291022845905060162252754009919296959225979955233043954908485668271285407576397399209505606056151696146154404059311581780638881373098546018434408740483439758031565230259361410910991031179612068843509750644816390825174052746592832786327440850409297910839768954730642358714659503412361151904744665842732860635209905427149324936203509227958559378146018369132251181409894109149368323649639829750086697363418421576338175463385615014082641533371729191797547051701409318609314967818274832554421113955232185798749596369987852385778848498458722044474963115736728560634335859528402326108069206658214647595244301762514457635610497882785661160668329547325526841262560082126352493898085687233312595260986508237133624865716389378967920285426115345360538503624497100049215898014580596356443282782890159535131472641575851720663995341755663153275628415113768812384869360423327149397498223546559781800180975566367752192 := by
  rw [digitBase]
  decide +kernel

theorem chainGen_exact : chainGen = 8788372346144463110347539719818278287999105535016750545324410661246296886546677339504845164845647763307921604512700703091893715189175533602193656289476236430242469204778120668995288243324931643955004461461803433600806780893669755440859092104951635029554165430888810519375063116386915425619148249426455551327976632600679342385725697258794699770952593716892958883838009291196837790959626201800792608609845036039774463519513989080450751030760550462611814457154637935906535834675545605838268913947569526004054235242373322513972698632963543495541042432413289740679476719041879540872482729647184393630977588343545445836956854971128617827494847038659992176319242639755596104992054128767150083446317051104262319705139704069982281601321533995188982054012419522651018333350519671470799087024244906265476763484161 := by
  rw [chainGen, digitBase]
  decide +kernel

theorem blockGen_mod_exact : dfs digitBase 1 chainGen 213 topMask 0 %
    digitBase ^ 83 = 6657403899266174364494878313996408850656953878876485412482551865638729526545581812532294823430786455391167233138714580998401917864754310588516655382049141243493684760243704044471430098525569254203051198129926444230748349652457053422798871965320235578985845447800614915737416394321727674013415794578195487020536467782272947912762428521725158970500433039866079391644657133996497162898577072083206612704186218718202937485672270411383245330672784070990528245685846694695128322781647941569514564683697318505230639621092801022641395163362028220842495276593129471921477563246641713563012518843910506231820658564039608704421319842984101640720822613469450500329207850627745026888491193931034693591076938268454794317590502562200091602615601383037945233368346228952427587721724307639494133249192297180036446268755459165444529298197039883934422155865255138978582317802611174755727752772098797210882528205436629700887365616250810714459587181008984984929180177397150142393918599690944571098305860105309581622853496034931717309961287742980767255085460509502727446352528115945930214088960592910934764731149077530098194191722440861093268997053700679722013707568209037843019576130471656029207711620280949137135246134236813809122606102214263460689499484603567439091681220657345238588731347996209309676044005084385324152323431955146831849043495315668320048616463118399364742026692567500024434007789954884132203950275748013597570063887869061365567538733769302280981616815577293563662332738385986368155604265733856710818739320414507040416633825271955778287179008786071191830083089122215879708441396525373366969594756070912633545515840332988789291452705693936278794012883786238101903483690371743245907739510340157407287542130900410689303270071229813338560251672505822269893033688077801553404781530959256409477223925096532823571016135630956052399680701674874582153447732684620265803686452833373290766163665996676990311235100640419483226942649458720436814965074122399334613561816803779202121104661751917900316100679779367054145905449921416005242443731047958241710634590987613638168984832232988846448266501507006822756963100386893701559654201488378818139595399061372014771655808058041701210676145837153618036876619427933758857785044948465149668392693171078873173276926913382192597987915417095619361376857494679798869887721234322786286900878794175470162729167450682210953664249613543549564831192011818760961741020666901902081379405459726188500730449827912030930528738857752980987778894205391563331930764068114580150638562428710375545438924996227282054384387306644571477092633196717737253263437227232546931452331737790009399222680245391714142098218412305416512022721023032792302128742848445622389446461173177128111692157977268955866442455354353371934919242080285275370234750448106581721522392187011073 := by
  rw [digitMod_exact, chainGen_exact, digitBase_exact, topMask]
  memo_count 24510380440836179026956737688548869385898448254776479188571588190665972822956737164150450354267335973625794882057983265228411976794174864655864632282941174899331463958802396621618762736094519107024738264995988900927457228604499630640393666369142277672818978314911972518523103782203505942620629404201349403306668175652488797079739689377453430638029125262938234677403733790176679864561913330605550414331041270371949979830247918320774616049454235169860644073301860113161023857741635706192929674083549548164423268603459483788650691364873378040236620589434965419582445494489711563477319473887815929523582144123096001876957255497065214621830590721025358500326965270194009711384353775989279723416548189518891769317351941955062113532874770296565598385557085714354406375911656632554531317019149692758306671919800222968898193725435948980261050925315962719517287474868970812369965012956169174282648234767025524689131138609857461789896084841878065877565489157791803125661927492991131582047937300930233218834901744549816304826237488996752232647883338705165176143848405055986850900408831730312162179280943933708370779547120878969031303766519941425377331575755881046949811479399141725998193826498248988214453941555203171446181330692707210943049557725555466875020189704900885318416950773838053616990621556462554436714057734335335658022679942785285742390166126177342827164826185851835758826331914207057742625458637142688509064700927912654080708366747896340924947462720785550735348416946142749570304557524408455909393393650701307991173009854961178262941602769565839296952962132458046579099251569659960461680996530758150320323957128765235307001771246165738692761673332130605944955022479821975459036049305937781763165014250969923977909992300086282458869267059134711644493572989352072690833181152651464779659363259252182698231630984819228806506489296814718961823348180249348380923486877045450178291022845905060162252754009919296959225979955233043954908485668271285407576397399209505606056151696146154404059311581780638881373098546018434408740483439758031565230259361410910991031179612068843509750644816390825174052746592832786327440850409297910839768954730642358714659503412361151904744665842732860635209905427149324936203509227958559378146018369132251181409894109149368323649639829750086697363418421576338175463385615014082641533371729191797547051701409318609314967818274832554421113955232185798749596369987852385778848498458722044474963115736728560634335859528402326108069206658214647595244301762514457635610497882785661160668329547325526841262560082126352493898085687233312595260986508237133624865716389378967920285426115345360538503624497100049215898014580596356443282782890159535131472641575851720663995341755663153275628415113768812384869360423327149397498223546559781800180975566367752192 2596148429267413814265248164610048 8788372346144463110347539719818278287999105535016750545324410661246296886546677339504845164845647763307921604512700703091893715189175533602193656289476236430242469204778120668995288243324931643955004461461803433600806780893669755440859092104951635029554165430888810519375063116386915425619148249426455551327976632600679342385725697258794699770952593716892958883838009291196837790959626201800792608609845036039774463519513989080450751030760550462611814457154637935906535834675545605838268913947569526004054235242373322513972698632963543495541042432413289740679476719041879540872482729647184393630977588343545445836956854971128617827494847038659992176319242639755596104992054128767150083446317051104262319705139704069982281601321533995188982054012419522651018333350519671470799087024244906265476763484161 6686494709113221679688380836206894168037833131400321806700118016

set_option maxRecDepth 100000 in
theorem blockGen_digit_exact :
    (dfs digitBase 1 chainGen 213 topMask 0) ^ 1 / digitBase ^ 82 % digitBase =
      705154647346183708283501533499397 := by
  refine digit_from_mod (dfs digitBase 1 chainGen 213 topMask 0) digitBase 82 83
    6657403899266174364494878313996408850656953878876485412482551865638729526545581812532294823430786455391167233138714580998401917864754310588516655382049141243493684760243704044471430098525569254203051198129926444230748349652457053422798871965320235578985845447800614915737416394321727674013415794578195487020536467782272947912762428521725158970500433039866079391644657133996497162898577072083206612704186218718202937485672270411383245330672784070990528245685846694695128322781647941569514564683697318505230639621092801022641395163362028220842495276593129471921477563246641713563012518843910506231820658564039608704421319842984101640720822613469450500329207850627745026888491193931034693591076938268454794317590502562200091602615601383037945233368346228952427587721724307639494133249192297180036446268755459165444529298197039883934422155865255138978582317802611174755727752772098797210882528205436629700887365616250810714459587181008984984929180177397150142393918599690944571098305860105309581622853496034931717309961287742980767255085460509502727446352528115945930214088960592910934764731149077530098194191722440861093268997053700679722013707568209037843019576130471656029207711620280949137135246134236813809122606102214263460689499484603567439091681220657345238588731347996209309676044005084385324152323431955146831849043495315668320048616463118399364742026692567500024434007789954884132203950275748013597570063887869061365567538733769302280981616815577293563662332738385986368155604265733856710818739320414507040416633825271955778287179008786071191830083089122215879708441396525373366969594756070912633545515840332988789291452705693936278794012883786238101903483690371743245907739510340157407287542130900410689303270071229813338560251672505822269893033688077801553404781530959256409477223925096532823571016135630956052399680701674874582153447732684620265803686452833373290766163665996676990311235100640419483226942649458720436814965074122399334613561816803779202121104661751917900316100679779367054145905449921416005242443731047958241710634590987613638168984832232988846448266501507006822756963100386893701559654201488378818139595399061372014771655808058041701210676145837153618036876619427933758857785044948465149668392693171078873173276926913382192597987915417095619361376857494679798869887721234322786286900878794175470162729167450682210953664249613543549564831192011818760961741020666901902081379405459726188500730449827912030930528738857752980987778894205391563331930764068114580150638562428710375545438924996227282054384387306644571477092633196717737253263437227232546931452331737790009399222680245391714142098218412305416512022721023032792302128742848445622389446461173177128111692157977268955866442455354353371934919242080285275370234750448106581721522392187011073 705154647346183708283501533499397 ?_ blockGen_mod_exact ?_
  · decide +kernel
  · rw [digitBase]
    decide +kernel

theorem card_supportedChoices :
    supportedChoices.card = 705154647346183708283501533499397 := by
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
