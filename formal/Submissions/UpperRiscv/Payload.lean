import Mathlib

/-! The abstract graph numbers chains in execution order. The wire stores them in
physical order, so its final 24 blocks of 160 bits are reversed. The transformation
is an involution, including on malformed payloads (which are left unchanged). -/

namespace OptimalOTS.Payload

def index (len i : ℕ) : ℕ :=
  if len = 5376 ∧ 1536 ≤ i then
    1536 + 160 * (23 - (i - 1536) / 160) + (i - 1536) % 160
  else i

theorem index_lt (len i : ℕ) (hi : i < len) : index len i < len := by
  unfold index
  split_ifs with h
  · obtain ⟨rfl, h⟩ := h
    omega
  · exact hi

theorem index_index (len i : ℕ) (hi : i < len) : index len (index len i) = i := by
  unfold index
  split_ifs <;> omega

def permute (bits : List Bool) : List Bool :=
  List.ofFn fun i : Fin bits.length => bits[index bits.length i.val]'(index_lt _ _ i.isLt)

@[simp] theorem length_permute (bits : List Bool) : (permute bits).length = bits.length := by
  simp [permute]

@[simp] theorem getElem_permute (bits : List Bool) (i : ℕ) (hi : i < (permute bits).length) :
    (permute bits)[i] = bits[index bits.length i]'(index_lt _ _ (by simpa using hi)) := by
  simp [permute]

@[simp] theorem permute_permute (bits : List Bool) : permute (permute bits) = bits := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [getElem_permute, length_permute, index_index _ _ h2]

theorem injective : Function.Injective permute :=
  Function.LeftInverse.injective permute_permute

end OptimalOTS.Payload
