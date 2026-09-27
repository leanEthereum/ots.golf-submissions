import Mathlib

/-! The abstract graph numbers chains in execution order and reveals their values in that
order. On the wire the 33 values lie at the byte offsets of the machine's memory layout,
followed by the tag. `index` gives the wire position of a graph payload bit and `coindex` the
graph position of a wire bit; they are mutually inverse on payloads of at least 5328 bits (the
values), and the identity from bit 5328 on. -/

set_option maxRecDepth 100000

namespace OptimalOTS.Payload

/-- Bits of the 33 revealed values. -/
def valueBits : ℕ := 5328

/-- Width of the value of chain `k`. -/
def width (k : ℕ) : ℕ := if 21 ≤ k then 192 else 144

/-- Graph offset of the value of chain `k`. -/
def graphOff (k : ℕ) : ℕ :=
  if k < 21 then 144 * k else 3024 + 192 * (k - 21)

/-- Wire offset of the value of chain `k`: its payload byte in memory. -/
def wireOff (k : ℕ) : ℕ :=
  8 * [612, 594, 324, 540, 522, 648, 630, 468, 576, 558, 396, 504, 486, 450, 432, 414, 378, 360, 342, 306, 288, 264, 240, 216, 192, 168, 144, 120, 96, 72, 48, 24, 0].getD k 0

/-- The chain of graph payload bit `i`. -/
def graphChain (i : ℕ) : ℕ :=
  if i < 3024 then i / 144 else 21 + (i - 3024) / 192

/-- The chain of wire bit `j`. -/
def wireChain (j : ℕ) : ℕ :=
  ((List.range 33).find? fun k => wireOff k ≤ j ∧ j < wireOff k + width k).getD 0

/-- Wire position of graph bit `i` of the values. -/
def index' (i : ℕ) : ℕ := wireOff (graphChain i) + (i - graphOff (graphChain i))

/-- Graph position of wire bit `j` of the values. -/
def coindex' (j : ℕ) : ℕ := graphOff (wireChain j) + (j - wireOff (wireChain j))

private theorem index'_lt : ∀ i < 5328, index' i < 5328 := by decide +kernel
private theorem coindex'_lt : ∀ j < 5328, coindex' j < 5328 := by decide +kernel
private theorem coindex'_index' : ∀ i < 5328, coindex' (index' i) = i := by decide +kernel
private theorem index'_coindex' : ∀ j < 5328, index' (coindex' j) = j := by decide +kernel

/-- Wire offset (in bits) of graph payload bit `i`. -/
def index (len i : ℕ) : ℕ :=
  if valueBits ≤ len ∧ i < valueBits then index' i else i

/-- Graph payload offset of wire bit `i`. -/
def coindex (len i : ℕ) : ℕ :=
  if valueBits ≤ len ∧ i < valueBits then coindex' i else i

theorem index_lt (len i : ℕ) (hi : i < len) : index len i < len := by
  unfold index
  split_ifs with h
  · have := index'_lt i h.2; unfold valueBits at h; omega
  · exact hi

theorem coindex_lt (len i : ℕ) (hi : i < len) : coindex len i < len := by
  unfold coindex
  split_ifs with h
  · have := coindex'_lt i h.2; unfold valueBits at h; omega
  · exact hi

theorem coindex_index (len i : ℕ) (_hi : i < len) : coindex len (index len i) = i := by
  unfold index
  split_ifs with h
  · unfold coindex
    rw [if_pos ⟨h.1, index'_lt i h.2⟩]
    exact coindex'_index' i h.2
  · unfold coindex
    rw [if_neg h]

theorem index_coindex (len i : ℕ) (_hi : i < len) : index len (coindex len i) = i := by
  unfold coindex
  split_ifs with h
  · unfold index
    rw [if_pos ⟨h.1, coindex'_lt i h.2⟩]
    exact index'_coindex' i h.2
  · unfold index
    rw [if_neg h]

/-- Graph payload from the wire: bit `j` is wire bit `index j`. -/
def permute (bits : List Bool) : List Bool :=
  List.ofFn fun i : Fin bits.length => bits[index bits.length i.val]'(index_lt _ _ i.isLt)

/-- Wire from the graph payload: bit `i` is payload bit `coindex i`. -/
def unpermute (bits : List Bool) : List Bool :=
  List.ofFn fun i : Fin bits.length => bits[coindex bits.length i.val]'(coindex_lt _ _ i.isLt)

@[simp] theorem length_permute (bits : List Bool) : (permute bits).length = bits.length := by
  simp [permute]

@[simp] theorem length_unpermute (bits : List Bool) : (unpermute bits).length = bits.length := by
  simp [unpermute]

@[simp] theorem getElem_permute (bits : List Bool) (i : ℕ) (hi : i < (permute bits).length) :
    (permute bits)[i] = bits[index bits.length i]'(index_lt _ _ (by simpa using hi)) := by
  simp [permute]

@[simp] theorem getElem_unpermute (bits : List Bool) (i : ℕ) (hi : i < (unpermute bits).length) :
    (unpermute bits)[i] = bits[coindex bits.length i]'(coindex_lt _ _ (by simpa using hi)) := by
  simp [unpermute]

@[simp] theorem permute_unpermute (bits : List Bool) : permute (unpermute bits) = bits := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [getElem_permute, getElem_unpermute, length_unpermute, coindex_index _ _ h2]

@[simp] theorem unpermute_permute (bits : List Bool) : unpermute (permute bits) = bits := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [getElem_unpermute, getElem_permute, length_permute, index_coindex _ _ h2]

private theorem index'_chain : ∀ k < 33, ∀ j < width k, index' (graphOff k + j) = wireOff k + j := by
  decide +kernel

private theorem chain_lt : ∀ k < 33, graphOff k + width k ≤ valueBits := by decide +kernel

/-- Bit `j` of the value of chain `k` in graph order is bit `j` of its wire value. -/
theorem getElem?_permute_chain (bits : List Bool) (hlen : valueBits ≤ bits.length) {k j : ℕ}
    (hk : k < 33) (hj : j < width k) :
    (permute bits)[graphOff k + j]? = bits[wireOff k + j]? := by
  have hb := chain_lt k hk
  have hi : graphOff k + j < bits.length := by omega
  rw [List.getElem?_eq_getElem (by simpa using hi), getElem_permute]
  have e : index bits.length (graphOff k + j) = wireOff k + j := by
    unfold index
    rw [if_pos ⟨hlen, by omega⟩, index'_chain k hk j hj]
  have hw : wireOff k + j < bits.length := by
    rw [← e]; exact index_lt _ _ hi
  rw [List.getElem?_eq_getElem hw]
  simp only [e]

/-- The permuted values depend only on the wire values. -/
theorem take_permute_congr {l l' : List Bool} (hl : valueBits ≤ l.length) (hl' : valueBits ≤ l'.length)
    (h : l.take valueBits = l'.take valueBits) :
    (permute l).take valueBits = (permute l').take valueBits := by
  apply List.ext_getElem
  · simp only [List.length_take, length_permute]; omega
  · intro i h1 h2
    simp only [List.length_take, length_permute] at h1
    have hi : i < valueBits := by omega
    simp only [List.getElem_take, getElem_permute]
    have e : ∀ len, valueBits ≤ len → index len i = index' i := fun len hlen => by
      unfold index; rw [if_pos ⟨hlen, hi⟩]
    have hb := index'_lt i hi
    have key := congrArg (fun m : List Bool => m[index' i]?) h
    simp only [List.getElem?_take, show index' i < valueBits from hb, ↓reduceIte] at key
    simp only [e _ hl, e _ hl']
    have b1 : index' i < l.length := by unfold valueBits at hl; omega
    have b2 : index' i < l'.length := by unfold valueBits at hl'; omega
    rw [List.getElem?_eq_getElem b1, List.getElem?_eq_getElem b2] at key
    exact Option.some.inj key

/-- The permutation moves no bit from `valueBits` on. -/
theorem drop_permute (bits : List Bool) :
    (permute bits).drop valueBits = bits.drop valueBits := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, getElem_permute]
    congr 1
    unfold index
    rw [if_neg (by omega)]

theorem injective : Function.Injective unpermute :=
  Function.LeftInverse.injective permute_unpermute

theorem permute_injective : Function.Injective permute :=
  Function.LeftInverse.injective unpermute_permute

end OptimalOTS.Payload
