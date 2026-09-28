import OptimalOTS.Dag
import Submissions.UpperRiscv.Semantics
import Submissions.UpperRiscv.Digits

/-!
# The mixed-width chain graph

There are 33 chains of 32 hash steps, indexed in execution order. Chain 0 carries the free
digit; chains `2q+1` and `2q+2` form digit pair `q`. Chains 21–32 carry 192-bit states, the
others 144-bit states. Every hash returns 256 bits; the next state of chain `k` is the
`chainBits k`-bit slice at bit `truncOff k` of the answer. A source is already state-width.

The top `tp k` of chain `k` is the slice of its last answer that the machine leaves in the
chain's root slot: `topBits k` bits at bit `topOff k`. For cap chain 32 the
top is the state slice itself, so its zero digit may reveal its top. The root input `rc` is the
800-byte region of the 33 root slots in address order (`rootRegion`, 6400 bits). The key-generation
input lengths 144, 192 and 6400 differ from the 512-bit index input.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag

namespace Forest

/-- Width of chain states, indexed in execution order. -/
def chainBits (k : Fin 33) : ℕ :=
  if 21 ≤ k.val then 192 else 144

theorem chainBits_cases (k : Fin 33) :
    chainBits k = 144 ∨ chainBits k = 192 := by
  unfold chainBits; split_ifs <;> simp

theorem chainBits_ge (k : Fin 33) : 144 ≤ chainBits k := by
  rcases chainBits_cases k with h | h <;> omega

theorem chainBits_le (k : Fin 33) : chainBits k ≤ 192 := by
  rcases chainBits_cases k with h | h <;> omega

/-- Bit offset of a chain's next state inside a 256-bit answer. -/
def truncOff (k : Fin 33) : ℕ :=
  8 * [0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8].getD k.val 0

theorem truncOff_add_le' : ∀ k : Fin 33, truncOff k + chainBits k ≤ 256 := by
  decide +kernel

theorem truncOff_add_le (k : Fin 33) : truncOff k + chainBits k ≤ 256 := truncOff_add_le' k

theorem truncOff_mod8 (k : Fin 33) : truncOff k % 8 = 0 := by
  unfold truncOff; omega

/-- The final cap chain: its top is its last state. -/
def isCap (k : Fin 33) : Prop := k.val = 32

instance : DecidablePred isCap := fun k => by unfold isCap; infer_instance

/-- Width of the root slot of chain `k`. -/
def topBits (k : Fin 33) : ℕ :=
  8 * [24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 32, 24].getD k.val 0

/-- Bit offset of the root slot of chain `k` inside its last answer. -/
def topOff (k : Fin 33) : ℕ :=
  8 * [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 8].getD k.val 0

theorem topOff_add_le' : ∀ k : Fin 33, topOff k + topBits k ≤ 256 := by
  decide +kernel

theorem topOff_add_le (k : Fin 33) : topOff k + topBits k ≤ 256 := topOff_add_le' k

theorem topBits_ge' : ∀ k : Fin 33, 144 ≤ topBits k := by
  decide +kernel

theorem topBits_ge (k : Fin 33) : 144 ≤ topBits k := topBits_ge' k

theorem topBits_le (k : Fin 33) : topBits k ≤ 256 := by
  have := topOff_add_le k; omega

theorem cap_top' : ∀ k : Fin 33, isCap k → topOff k = truncOff k ∧ topBits k = chainBits k := by
  decide +kernel

theorem topBits_cap {k : Fin 33} (h : isCap k) : topBits k = chainBits k := (cap_top' k h).2

theorem topOff_cap {k : Fin 33} (h : isCap k) : topOff k = truncOff k := (cap_top' k h).1

/-- Node names. -/
inductive Name where
  | src (k : Fin 33)
  | ci (k : Fin 33) (t : Fin 32)
  | ch (k : Fin 33) (t : Fin 32)
  | cv (k : Fin 33) (t : Fin 32)
  | tp (k : Fin 33)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 3236

namespace Name

/-- Topological index. Chain `k` occupies `98 k, …, 98 k + 97`: its source, then input, hash and
value of each of its 32 levels, then its top. -/
def idx : Name → ℕ
  | src k => 98 * k
  | ci k t => 98 * k + 1 + 3 * t
  | ch k t => 98 * k + 2 + 3 * t
  | cv k t => 98 * k + 3 + 3 * t
  | tp k => 98 * k + 97
  | rc => 3234
  | rh => 3235

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- The width of the root input. -/
def rootBits : ℕ := 6400

/-- Output length. -/
def len : Name → ℕ
  | src k => chainBits k
  | ci k _ => chainBits k
  | ch _ _ => 256
  | cv _ _ => 256
  | tp k => topBits k
  | rc => rootBits
  | rh => 256

/-- Query cost of a node: one compression for every chain hash, thirteen for the root. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | rh => 13
  | _ => 0

/-- The value node feeding the chain input `ci k t`: the source for `t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 33) (t : Fin 32) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ci k 0)
  | ci k t => some (ch k t)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 31 then some (tp k) else some (ci k ⟨t + 1, by omega⟩)
  | tp _ => some rc
  | rc => some rh
  | rh => none

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ci k t => {prev k t}
  | ch k t => {ci k t}
  | cv k t => {ch k t}
  | tp k => {cv k 31}
  | rc => Finset.univ.image tp
  | rh => {rc}

theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  cases n <;> cases m <;>
    simp only [parents, child, prev, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.notMem_empty, Option.some.injEq,
      reduceCtorEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.tp.injEq, Fin.ext_iff,
      Fin.val_zero, iff_true, iff_false, false_iff, or_false, exists_false, exists_eq] <;>
    (try split_ifs) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Name.src.injEq, Name.ci.injEq,
      Name.cv.injEq, Name.tp.injEq, Fin.ext_iff, iff_false, false_iff, not_false_eq_true]) <;>
    first | omega | exact ⟨_, rfl⟩ | (constructor <;> intro h <;> first | trivial | omega | (obtain ⟨_, h1, h2⟩ := h; omega) | exact ⟨_, rfl, by omega⟩)

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  rw [mem_parents_iff] at h
  cases m <;> simp only [child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;> subst h <;>
    simp only [idx, Fin.val_zero] <;> omega

end Name

/-- The inverse of `Name.fin`. -/
def ofFin (v : Fin N) : Name :=
  if h₁ : v.val < 3234 then
    let k : Fin 33 := ⟨v.val / 98, by omega⟩
    let r := v.val % 98
    if h₂ : r = 0 then .src k
    else if h₄ : r = 97 then .tp k
    else
      let t : Fin 32 := ⟨(r - 1) / 3, by omega⟩
      if h₃ : (r - 1) % 3 = 0 then .ci k t
      else if h₃' : (r - 1) % 3 = 1 then .ch k t
      else .cv k t
  else if h₁₀ : v.val < 3235 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.tp.injEq,
      Fin.ext_iff, reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 3236 := v.isLt
  rw [Fin.ext_iff]
  simp only [ofFin]
  split_ifs <;> simp only [Name.fin, Name.idx] <;> omega

theorem ofFin_fin (n : Name) : ofFin n.fin = n :=
  Name.idx_injective (congrArg Fin.val (fin_ofFin_aux n.fin))

theorem fin_ofFin (v : Fin N) : (ofFin v).fin = v := fin_ofFin_aux v

def nameEquiv : Name ≃ Fin N where
  toFun := Name.fin
  invFun := ofFin
  left_inv := ofFin_fin
  right_inv := fin_ofFin

theorem Name.fin_injective : Function.Injective Name.fin := nameEquiv.injective

abbrev NameSum := Fin 33 ⊕ (Fin 33 × Fin 32) ⊕ (Fin 33 × Fin 32) ⊕ (Fin 33 × Fin 32) ⊕
  Fin 33 ⊕ Unit ⊕ Unit

def Name.toSum : Name → NameSum
  | src k => .inl k
  | ci k t => .inr (.inl (k, t))
  | ch k t => .inr (.inr (.inl (k, t)))
  | cv k t => .inr (.inr (.inr (.inl (k, t))))
  | tp k => .inr (.inr (.inr (.inr (.inl k))))
  | rc => .inr (.inr (.inr (.inr (.inr (.inl ())))))
  | rh => .inr (.inr (.inr (.inr (.inr (.inr ())))))

def Name.ofSum : NameSum → Name
  | .inl k => src k
  | .inr (.inl (k, t)) => ci k t
  | .inr (.inr (.inl (k, t))) => ch k t
  | .inr (.inr (.inr (.inl (k, t)))) => cv k t
  | .inr (.inr (.inr (.inr (.inl k)))) => tp k
  | .inr (.inr (.inr (.inr (.inr (.inl ()))))) => rc
  | .inr (.inr (.inr (.inr (.inr (.inr ()))))) => rh

def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | ⟨k, t⟩ | k | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ci k t)) + (∑ k, ∑ t, f (ch k t)) +
      (∑ k, ∑ t, f (cv k t)) + (∑ k, f (tp k)) + f rc + f rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## The root input -/

/-- The chain whose root slot is the `j`-th in address order. -/
def slotChainN (j : ℕ) : ℕ :=
  [32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0].getD j 0

def slotChain (j : ℕ) : Fin 33 := ⟨slotChainN j % 33, Nat.mod_lt _ (by norm_num)⟩

/-- The address rank of the root slot of chain `k`. -/
def slotOf (k : Fin 33) : ℕ :=
  [32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0].getD k.val 0

theorem slotChain_slotOf' : ∀ k : Fin 33, slotChain (slotOf k) = k := by decide +kernel

theorem slotChain_slotOf (k : Fin 33) : slotChain (slotOf k) = k := slotChain_slotOf' k

theorem slotOf_lt' : ∀ k : Fin 33, slotOf k < 33 := by decide +kernel

theorem slotOf_lt (k : Fin 33) : slotOf k < 33 := slotOf_lt' k

theorem slotOf_slotChain' : ∀ j : Fin 33, slotOf (slotChain j.val) = j.val := by decide +kernel

theorem slotOf_slotChain {j : ℕ} (hj : j < 33) : slotOf (slotChain j) = j :=
  slotOf_slotChain' ⟨j, hj⟩

/-- Widths of the root slots in address order. -/
def slotW (j : ℕ) : ℕ := if j < 33 then topBits (slotChain j) else 0

/-- Bit offset of the root slot of chain `k` in the region. -/
def slotPos (k : Fin 33) : ℕ := posW slotW (slotOf k)

theorem posW_slotW_33 : posW slotW 33 = Name.rootBits := by decide +kernel

theorem slotPos_add_le' : ∀ k : Fin 33, slotPos k + topBits k ≤ Name.rootBits := by decide +kernel

theorem slotPos_add_le (k : Fin 33) : slotPos k + topBits k ≤ Name.rootBits := slotPos_add_le' k

theorem slotW_slotOf (k : Fin 33) : slotW (slotOf k) = topBits k := by
  rw [slotW, if_pos (slotOf_lt k), slotChain_slotOf]

theorem slotPos_last : slotPos 32 = 0 := by decide +kernel

/-- The slot values as digits of the region. -/
def slotDigit (tops : (k : Fin 33) → BitVec (topBits k)) (j : ℕ) : ℕ :=
  if j < 33 then (tops (slotChain j)).toNat else 0

theorem slotDigit_lt (tops : (k : Fin 33) → BitVec (topBits k)) (j : ℕ) :
    slotDigit tops j < 2 ^ slotW j := by
  unfold slotDigit slotW
  split_ifs
  · exact (tops _).isLt
  · positivity

/-- The 800 bytes of the root slots, chain slots in address order, lowest address lowest. -/
def rootRegion (tops : (k : Fin 33) → BitVec (topBits k)) : BitVec Name.rootBits :=
  BitVec.ofNat Name.rootBits (ofDigitsW slotW (slotDigit tops) 33)

theorem rootRegion_toNat (tops : (k : Fin 33) → BitVec (topBits k)) :
    (rootRegion tops).toNat = ofDigitsW slotW (slotDigit tops) 33 := by
  unfold rootRegion
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [← posW_slotW_33]
  exact ofDigitsW_lt slotW _ (slotDigit_lt tops) 33

theorem slotDigit_slotOf (tops : (k : Fin 33) → BitVec (topBits k)) (k : Fin 33) :
    slotDigit tops (slotOf k) = (tops k).toNat := by
  unfold slotDigit
  rw [if_pos (slotOf_lt k)]
  generalize hc : slotChain (slotOf k) = c
  rw [slotChain_slotOf] at hc
  subst hc
  rfl

/-- The slot of chain `k` in the region is its top. -/
theorem rootRegion_slot (tops : (k : Fin 33) → BitVec (topBits k)) (k : Fin 33) :
    (rootRegion tops).extractLsb' (slotPos k) (topBits k) = tops k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, rootRegion_toNat, Nat.shiftRight_eq_div_pow]
  have h := digitW_ofDigitsW slotW (slotDigit tops) (slotDigit_lt tops) 33 (slotOf k) (slotOf_lt k)
  unfold digitW at h
  rw [slotW_slotOf] at h
  rw [slotPos, h, slotDigit_slotOf]

theorem rootRegion_injective : Function.Injective rootRegion := by
  intro a b h
  funext k
  rw [← rootRegion_slot a k, ← rootRegion_slot b k, h]

/-! ## The graph -/

def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- Retain the state slice starting `truncOff k` bits into a hash output, or the entire
state when the input already has the chain's width. -/
def trunc (k : Fin 33) {w : ℕ} (x : BitVec w) : BitVec (chainBits k) :=
  x.extractLsb' (min (truncOff k) (w - chainBits k)) (chainBits k)

/-- The root slot of chain `k` in a last answer. -/
def topSlice (k : Fin 33) (x : BitVec 256) : BitVec (topBits k) :=
  x.extractLsb' (topOff k) (topBits k)

abbrev Asg := (v : Fin N) → BitVec (lenF v)

theorem lenF_ch (k : Fin 33) (t : Fin 32) : lenF (Name.ch k t).fin = (Name.cv k t).len := lenF_fin _

/-- The deterministic value of a node, as a function of the assignment. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .ci k t => trunc k (x (Name.prev k t).fin)
  | .cv k t => (x (Name.ch k t).fin).cast (lenF_ch k t)
  | .tp k => topSlice k ((x (Name.cv k 31).fin).cast (lenF_fin _))
  | .rc => rootRegion fun k => (x (Name.tp k).fin).cast (lenF_fin _)
  | _ => 0

theorem detVal_ci (k : Fin 33) (t : Fin 32) (x : Asg) :
    detVal (.ci k t) x = trunc k (x (Name.prev k t).fin) := rfl

theorem detVal_cv (k : Fin 33) (t : Fin 32) (x : Asg) :
    detVal (.cv k t) x = (x (Name.ch k t).fin).cast (lenF_ch k t) := rfl

theorem detVal_tp (k : Fin 33) (x : Asg) :
    detVal (.tp k) x = topSlice k ((x (Name.cv k 31).fin).cast (lenF_fin _)) := rfl

theorem detVal_rc (x : Asg) :
    detVal .rc x = rootRegion fun k => (x (Name.tp k).fin).cast (lenF_fin _) := rfl

theorem eq_fin_of_ofFin_eq {v : Fin N} {n : Name} (h : ofFin v = n) : v = n.fin := by
  rw [← h, fin_ofFin]

theorem Name.fin_lt_fin_of_mem_parents {m n : Name} (h : m ∈ Name.parents n) : m.fin < n.fin :=
  Name.idx_lt_of_mem_parents h

theorem hash_parent_lt {v : Fin N} {n m : Name} (h : ofFin v = n) (hm : m ∈ Name.parents n) :
    m.fin < v := by
  rw [eq_fin_of_ofFin_eq h]
  exact Name.fin_lt_fin_of_mem_parents hm

theorem det_parents_lt {v : Fin N} {n : Name} (h : ofFin v = n) :
    ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, w < v := by
  intro w hw
  rw [Finset.mem_map] at hw
  obtain ⟨m, hm, rfl⟩ := hw
  exact hash_parent_lt h hm

theorem detVal_local (n : Name) (x y : Asg)
    (hxy : ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, x w = y w) :
    detVal n x = detVal n y := by
  have key : ∀ m ∈ Name.parents n, x m.fin = y m.fin := fun m hm =>
    hxy m.fin (Finset.mem_map_of_mem _ hm)
  cases n with
  | ci k t =>
    show trunc k (x (Name.prev k t).fin) = trunc k (y (Name.prev k t).fin)
    rw [key (Name.prev k t) (by simp [Name.parents])]
  | cv k t =>
    show (x (Name.ch k t).fin).cast (lenF_ch k t) = (y (Name.ch k t).fin).cast (lenF_ch k t)
    rw [key (Name.ch k t) (by simp [Name.parents])]
  | tp k =>
    show topSlice k ((x (Name.cv k 31).fin).cast (lenF_fin _)) =
      topSlice k ((y (Name.cv k 31).fin).cast (lenF_fin _))
    rw [key (Name.cv k 31) (by simp [Name.parents])]
  | rc =>
    show rootRegion (fun k => (x (Name.tp k).fin).cast (lenF_fin _)) =
      rootRegion (fun k => (y (Name.tp k).fin).cast (lenF_fin _))
    exact congrArg rootRegion (funext fun k => by
      rw [key (Name.tp k) (Finset.mem_image_of_mem _ (Finset.mem_univ _))])
  | src _ => rfl
  | ch _ _ => rfl
  | rh => rfl

/-- The kind of the node `v = n.fin`. -/
def kindOf (v : Fin N) : (n : Name) → ofFin v = n → NodeKind N lenF v
  | .src _, _ => .source
  | .ci k t, h => .det ((Name.parents (.ci k t)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.ci k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .ch k t, h => .hash (Name.ci k t).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .cv k t, h => .det ((Name.parents (.cv k t)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.cv k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .tp k, h => .det ((Name.parents (.tp k)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.tp k) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .rc, h => .det ((Name.parents .rc).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal .rc x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .rh, h => .hash Name.rc.fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)

theorem kindOf_isHash (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsHash ↔ n.cost ≠ 0 := by
  cases n <;> simp [kindOf, NodeKind.IsHash, Name.cost]

theorem kindOf_isSource (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsSource ↔ ∃ k, n = .src k := by
  cases n <;> simp [kindOf, NodeKind.IsSource]

theorem kindOf_parents (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  cases n <;> simp [kindOf, NodeKind.parents, Name.parents, nameEquiv]

/-- The computation graph of the scheme. -/
def graph : Graph where
  size := N
  len := lenF
  kind v := kindOf v (ofFin v) rfl
  root := Name.rh.fin
  root_isHash := (kindOf_isHash _ _ rfl).2 (by rw [ofFin_fin]; decide)

theorem graph_kind_eq (v : Fin N) (n : Name) (h : ofFin v = n) : graph.kind v = kindOf v n h := by
  subst h; rfl

theorem graph_kind_fin (n : Name) : graph.kind n.fin = kindOf n.fin n (ofFin_fin n) :=
  graph_kind_eq _ _ _

theorem graph_len_fin (n : Name) : graph.len n.fin = n.len := lenF_fin n

theorem graph_parents_fin (n : Name) :
    (graph.kind n.fin).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  rw [graph_kind_fin]; exact kindOf_parents _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ k, n = .src k := by
  rw [graph_kind_fin]; exact kindOf_isSource _ _ _

theorem Name.len_prev (k : Fin 33) (t : Fin 32) : (Name.prev k t).len = if t.val = 0 then chainBits k else 256 := by
  unfold Name.prev; split_ifs <;> rfl

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, Name.rootBits, blockCost, blockBits, chainBits]
  split_ifs <;> norm_num

theorem graph_keygenCost : graph.keygenCost = 1069 := by
  show ∑ v : Fin N, graph.nodeCost v = 1069
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

end Forest

end OptimalOTS
