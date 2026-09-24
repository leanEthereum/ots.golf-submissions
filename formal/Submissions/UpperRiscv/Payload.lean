import Mathlib

/-! The abstract graph numbers chains in execution order, which is also the order of their
24-byte working cells. The wire permutes sixteen 144-bit states, followed by
sixteen 192-bit states stored in place. Twenty-four wire values need no expansion. `index`
gives the wire position of a graph payload bit and `coindex` the graph position of a
wire bit; they are mutually inverse on 5376-bit payloads and the identity elsewhere. -/

set_option maxRecDepth 100000

namespace OptimalOTS.Payload

/-- Chain-index permutation and inverse on the sixteen narrow states. -/
def order (k : ℕ) : ℕ := [1,2,5,6,0,9,3,4,10,7,8,13,11,12,14,15].getD k 0
def inverseOrder (k : ℕ) : ℕ := [4,0,1,6,7,2,3,9,10,5,8,12,13,11,14,15].getD k 0

private theorem order_lt : ∀ k < 16, order k < 16 := by decide +kernel
private theorem inverseOrder_lt : ∀ k < 16, inverseOrder k < 16 := by decide +kernel
private theorem inverse_order : ∀ k < 16, inverseOrder (order k) = k := by decide +kernel
private theorem order_inverse : ∀ k < 16, order (inverseOrder k) = k := by decide +kernel

/-- Wire offset (in bits) of graph payload bit `i`. -/
def index (len i : ℕ) : ℕ :=
  if len = 5376 ∧ i < 2304 then
    144 * order (i / 144) + i % 144
  else i

/-- Graph payload offset of wire bit `i`. -/
def coindex (len i : ℕ) : ℕ :=
  if len = 5376 ∧ i < 2304 then
    144 * inverseOrder (i / 144) + i % 144
  else i

private theorem index_lt_5376 : ∀ i < 5376, index 5376 i < 5376 := by
  intro i hi
  unfold index
  split_ifs with h
  · have := order_lt (i / 144) (by omega); omega
  · exact hi

private theorem coindex_lt_5376 : ∀ i < 5376, coindex 5376 i < 5376 := by
  intro i hi
  unfold coindex
  split_ifs with h
  · have := inverseOrder_lt (i / 144) (by omega); omega
  · exact hi

theorem index_lt (len i : ℕ) (hi : i < len) : index len i < len := by
  by_cases h : len = 5376
  · subst h; exact index_lt_5376 i hi
  · simpa [index, h] using hi

theorem coindex_lt (len i : ℕ) (hi : i < len) : coindex len i < len := by
  by_cases h : len = 5376
  · subst h; exact coindex_lt_5376 i hi
  · simpa [coindex, h] using hi

theorem coindex_index_5376 : ∀ i < 5376, coindex 5376 (index 5376 i) = i := by
  intro i _
  by_cases h : i < 2304
  · have hk : i / 144 < 16 := by omega
    have hp := order_lt (i / 144) hk
    have hr : 144 * order (i / 144) + i % 144 < 2304 := by omega
    unfold index
    rw [if_pos ⟨rfl, h⟩]
    unfold coindex
    rw [if_pos ⟨rfl, hr⟩]
    rw [show (144 * order (i / 144) + i % 144) / 144 = order (i / 144) by omega,
      show (144 * order (i / 144) + i % 144) % 144 = i % 144 by omega,
      inverse_order _ hk]
    omega
  · simp [index, coindex, h]

theorem index_coindex_5376 : ∀ i < 5376, index 5376 (coindex 5376 i) = i := by
  intro i _
  by_cases h : i < 2304
  · have hk : i / 144 < 16 := by omega
    have hp := inverseOrder_lt (i / 144) hk
    have hr : 144 * inverseOrder (i / 144) + i % 144 < 2304 := by omega
    unfold coindex
    rw [if_pos ⟨rfl, h⟩]
    unfold index
    rw [if_pos ⟨rfl, hr⟩]
    rw [show (144 * inverseOrder (i / 144) + i % 144) / 144 = inverseOrder (i / 144) by omega,
      show (144 * inverseOrder (i / 144) + i % 144) % 144 = i % 144 by omega,
      order_inverse _ hk]
    omega
  · simp [index, coindex, h]

theorem coindex_index (len i : ℕ) (hi : i < len) : coindex len (index len i) = i := by
  by_cases h : len = 5376
  · subst h; exact coindex_index_5376 i hi
  · simp [index, coindex, h]

theorem index_coindex (len i : ℕ) (hi : i < len) : index len (coindex len i) = i := by
  by_cases h : len = 5376
  · subst h; exact index_coindex_5376 i hi
  · simp [index, coindex, h]

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

theorem injective : Function.Injective unpermute :=
  Function.LeftInverse.injective permute_unpermute

theorem permute_injective : Function.Injective permute :=
  Function.LeftInverse.injective unpermute_permute

end OptimalOTS.Payload
