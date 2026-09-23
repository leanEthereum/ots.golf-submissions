import Mathlib

/-! The abstract graph numbers chains in execution order, which is also the order of their
24-byte working cells. The wire stores chains 0–19 in four 768-bit blocks, each holding
one 152-bit chain on the cell grid followed by one 160-bit and three 152-bit chains, so
that sixteen wire values need no expansion; chains 20–31 are stored in place. `index`
gives the wire position of a graph payload bit and `coindex` the graph position of a
wire bit; they are mutually inverse on 5376-bit payloads and the identity elsewhere. -/

set_option maxRecDepth 100000

namespace OptimalOTS.Payload

/-- Wire offset (in bits) of graph payload bit `i`. -/
def index (len i : ℕ) : ℕ :=
  if len = 5376 ∧ i < 3072 then
    if i < 640 then 768 * (i / 160) + 152 + i % 160
    else 768 * ((i - 640) / 152 / 4) +
      (if (i - 640) / 152 % 4 = 0 then 0 else if (i - 640) / 152 % 4 = 1 then 312
        else if (i - 640) / 152 % 4 = 2 then 464 else 616) + (i - 640) % 152
  else i

/-- Graph payload offset of wire bit `i`. -/
def coindex (len i : ℕ) : ℕ :=
  if len = 5376 ∧ i < 3072 then
    if i % 768 < 152 then 640 + 608 * (i / 768) + i % 768
    else if i % 768 < 312 then 160 * (i / 768) + (i % 768 - 152)
    else if i % 768 < 464 then 640 + 608 * (i / 768) + 152 + (i % 768 - 312)
    else if i % 768 < 616 then 640 + 608 * (i / 768) + 304 + (i % 768 - 464)
    else 640 + 608 * (i / 768) + 456 + (i % 768 - 616)
  else i

theorem index_lt (len i : ℕ) (hi : i < len) : index len i < len := by
  unfold index
  split_ifs <;> omega

theorem coindex_lt (len i : ℕ) (hi : i < len) : coindex len i < len := by
  unfold coindex
  split_ifs <;> omega

theorem coindex_index_5376 : ∀ i < 5376, coindex 5376 (index 5376 i) = i := by
  decide +kernel

theorem index_coindex_5376 : ∀ i < 5376, index 5376 (coindex 5376 i) = i := by
  decide +kernel

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
