import Mathlib

/-! The abstract graph numbers chains in execution order and reads their disclosed values in
that order: the 24 narrow values of 160 bits, then the 8 wide values of 192 bits. The wire
interleaves the values in memory order instead (narrow and wide values alternate, so that most
chains can be hashed in place). Every value is a whole number of 32-bit units: the value of the
chain executed `k`-th occupies graph units `graphUnit k, …` and wire units `wireUnit k, …`, and
the `u`-th graph unit is the `unitMap u`-th wire unit. `index` maps a graph-order bit to its wire
bit and `unindex` inverts it; malformed payloads (of any other length) are left unchanged. -/

namespace OptimalOTS.Payload

/-- Wire position, in 32-bit units, of the value of the chain executed `k`-th. -/
def wireUnit (k : ℕ) : ℕ :=
  [153, 138, 128, 108, 92, 76, 60, 44, 28, 12, 163, 123, 118, 17, 33, 49,
    65, 81, 97, 113, 133, 143, 148, 158, 6, 22, 38, 54, 70, 86, 102, 0].getD k 0

/-- Graph-payload position, in 32-bit units, of the value of chain `k`. -/
def graphUnit (k : ℕ) : ℕ := if k < 24 then 5 * k else 120 + 6 * (k - 24)

/-- Length of chain `k`'s value in 32-bit units. -/
def unitCount (k : ℕ) : ℕ := if k < 24 then 5 else 6

/-- Graph unit `u` ↦ the wire unit that holds it. -/
def unitMap (u : ℕ) : ℕ :=
  [153, 154, 155, 156, 157, 138, 139, 140, 141, 142, 128, 129, 130, 131, 132, 108,
    109, 110, 111, 112, 92, 93, 94, 95, 96, 76, 77, 78, 79, 80, 60, 61,
    62, 63, 64, 44, 45, 46, 47, 48, 28, 29, 30, 31, 32, 12, 13, 14,
    15, 16, 163, 164, 165, 166, 167, 123, 124, 125, 126, 127, 118, 119, 120, 121,
    122, 17, 18, 19, 20, 21, 33, 34, 35, 36, 37, 49, 50, 51, 52, 53,
    65, 66, 67, 68, 69, 81, 82, 83, 84, 85, 97, 98, 99, 100, 101, 113,
    114, 115, 116, 117, 133, 134, 135, 136, 137, 143, 144, 145, 146, 147, 148, 149,
    150, 151, 152, 158, 159, 160, 161, 162, 6, 7, 8, 9, 10, 11, 22, 23,
    24, 25, 26, 27, 38, 39, 40, 41, 42, 43, 54, 55, 56, 57, 58, 59,
    70, 71, 72, 73, 74, 75, 86, 87, 88, 89, 90, 91, 102, 103, 104, 105,
    106, 107, 0, 1, 2, 3, 4, 5].getD u 0

/-- Wire unit `u` ↦ the graph unit it holds. -/
def unitUnmap (u : ℕ) : ℕ :=
  [162, 163, 164, 165, 166, 167, 120, 121, 122, 123, 124, 125, 45, 46, 47, 48,
    49, 65, 66, 67, 68, 69, 126, 127, 128, 129, 130, 131, 40, 41, 42, 43,
    44, 70, 71, 72, 73, 74, 132, 133, 134, 135, 136, 137, 35, 36, 37, 38,
    39, 75, 76, 77, 78, 79, 138, 139, 140, 141, 142, 143, 30, 31, 32, 33,
    34, 80, 81, 82, 83, 84, 144, 145, 146, 147, 148, 149, 25, 26, 27, 28,
    29, 85, 86, 87, 88, 89, 150, 151, 152, 153, 154, 155, 20, 21, 22, 23,
    24, 90, 91, 92, 93, 94, 156, 157, 158, 159, 160, 161, 15, 16, 17, 18,
    19, 95, 96, 97, 98, 99, 60, 61, 62, 63, 64, 55, 56, 57, 58, 59,
    10, 11, 12, 13, 14, 100, 101, 102, 103, 104, 5, 6, 7, 8, 9, 105,
    106, 107, 108, 109, 110, 111, 112, 113, 114, 0, 1, 2, 3, 4, 115, 116,
    117, 118, 119, 50, 51, 52, 53, 54].getD u 0

theorem unitMap_lt' : ∀ u : Fin 168, unitMap u < 168 := by decide +kernel

theorem unitUnmap_lt' : ∀ u : Fin 168, unitUnmap u < 168 := by decide +kernel

theorem unitUnmap_unitMap' : ∀ u : Fin 168, unitUnmap (unitMap u) = u := by decide +kernel

theorem unitMap_unitUnmap' : ∀ u : Fin 168, unitMap (unitUnmap u) = u := by decide +kernel

/-- The units of one chain value stay consecutive on the wire. -/
theorem unitMap_chain' : ∀ k : Fin 32, ∀ t : Fin 6, t.val < unitCount k →
    unitMap (graphUnit k + t) = wireUnit k + t := by decide +kernel

theorem graphUnit_add' : ∀ k : Fin 32, graphUnit k + unitCount k ≤ 168 := by decide +kernel

theorem wireUnit_add' : ∀ k : Fin 32, wireUnit k + unitCount k ≤ 168 := by decide +kernel

theorem unitMap_lt (u : ℕ) (hu : u < 168) : unitMap u < 168 := unitMap_lt' ⟨u, hu⟩

theorem unitUnmap_lt (u : ℕ) (hu : u < 168) : unitUnmap u < 168 := unitUnmap_lt' ⟨u, hu⟩

theorem unitUnmap_unitMap (u : ℕ) (hu : u < 168) : unitUnmap (unitMap u) = u :=
  unitUnmap_unitMap' ⟨u, hu⟩

theorem unitMap_unitUnmap (u : ℕ) (hu : u < 168) : unitMap (unitUnmap u) = u :=
  unitMap_unitUnmap' ⟨u, hu⟩

theorem unitMap_chain (k : ℕ) (hk : k < 32) (t : ℕ) (ht6 : t < 6) (ht : t < unitCount k) :
    unitMap (graphUnit k + t) = wireUnit k + t :=
  unitMap_chain' ⟨k, hk⟩ ⟨t, ht6⟩ ht

theorem graphUnit_add (k : ℕ) (hk : k < 32) : graphUnit k + unitCount k ≤ 168 :=
  graphUnit_add' ⟨k, hk⟩

theorem wireUnit_add (k : ℕ) (hk : k < 32) : wireUnit k + unitCount k ≤ 168 :=
  wireUnit_add' ⟨k, hk⟩

/-- Graph-order (cursor) bit `i` ↦ the wire bit that holds it. -/
def index (len i : ℕ) : ℕ :=
  if len = 5376 ∧ i < 5376 then 32 * unitMap (i / 32) + i % 32 else i

/-- Wire bit `i` ↦ the graph-order bit it holds. -/
def unindex (len i : ℕ) : ℕ :=
  if len = 5376 ∧ i < 5376 then 32 * unitUnmap (i / 32) + i % 32 else i

theorem index_of (i : ℕ) (hi : i < 5376) : index 5376 i = 32 * unitMap (i / 32) + i % 32 := by
  have hc : 5376 = 5376 ∧ i < 5376 := ⟨rfl, hi⟩
  unfold index
  rw [if_pos hc]

theorem unindex_of (i : ℕ) (hi : i < 5376) :
    unindex 5376 i = 32 * unitUnmap (i / 32) + i % 32 := by
  have hc : 5376 = 5376 ∧ i < 5376 := ⟨rfl, hi⟩
  unfold unindex
  rw [if_pos hc]

theorem div_mod_32 (a r : ℕ) (hr : r < 32) :
    (32 * a + r) / 32 = a ∧ (32 * a + r) % 32 = r :=
  ⟨by omega, by omega⟩

theorem index_lt (len i : ℕ) (hi : i < len) : index len i < len := by
  by_cases h : len = 5376 ∧ i < 5376
  · obtain ⟨rfl, h2⟩ := h
    rw [index_of i h2]
    have ha := unitMap_lt (i / 32) (by omega)
    have hr := Nat.mod_lt i (show 32 > 0 by norm_num)
    omega
  · unfold index
    rw [if_neg h]
    exact hi

theorem unindex_lt (len i : ℕ) (hi : i < len) : unindex len i < len := by
  by_cases h : len = 5376 ∧ i < 5376
  · obtain ⟨rfl, h2⟩ := h
    rw [unindex_of i h2]
    have ha := unitUnmap_lt (i / 32) (by omega)
    have hr := Nat.mod_lt i (show 32 > 0 by norm_num)
    omega
  · unfold unindex
    rw [if_neg h]
    exact hi

theorem unindex_index (len i : ℕ) (hi : i < len) : unindex len (index len i) = i := by
  by_cases h : len = 5376 ∧ i < 5376
  · obtain ⟨rfl, h2⟩ := h
    have ha := unitMap_lt (i / 32) (by omega)
    have hr := Nat.mod_lt i (show 32 > 0 by norm_num)
    have hd := div_mod_32 (unitMap (i / 32)) (i % 32) hr
    rw [index_of i h2, unindex_of (32 * unitMap (i / 32) + i % 32) (by omega), hd.1, hd.2,
      unitUnmap_unitMap (i / 32) (by omega)]
    omega
  · have e : index len i = i := by
      unfold index
      rw [if_neg h]
    rw [e]
    unfold unindex
    rw [if_neg h]

theorem index_unindex (len i : ℕ) (hi : i < len) : index len (unindex len i) = i := by
  by_cases h : len = 5376 ∧ i < 5376
  · obtain ⟨rfl, h2⟩ := h
    have ha := unitUnmap_lt (i / 32) (by omega)
    have hr := Nat.mod_lt i (show 32 > 0 by norm_num)
    have hd := div_mod_32 (unitUnmap (i / 32)) (i % 32) hr
    rw [unindex_of i h2, index_of (32 * unitUnmap (i / 32) + i % 32) (by omega), hd.1, hd.2,
      unitMap_unitUnmap (i / 32) (by omega)]
    omega
  · have e : unindex len i = i := by
      unfold unindex
      rw [if_neg h]
    rw [e]
    unfold index
    rw [if_neg h]

/-- A chain value is read from consecutive wire bits. -/
theorem index_chain (k : ℕ) (hk : k < 32) (i : ℕ) (hi : i < 32 * unitCount k) :
    index 5376 (32 * graphUnit k + i) = 32 * wireUnit k + i := by
  have hg := graphUnit_add k hk
  have hu : unitCount k ≤ 6 := by
    unfold unitCount
    split_ifs <;> omega
  have ht : i / 32 < unitCount k := by omega
  have e := unitMap_chain k hk (i / 32) (by omega) ht
  have hd1 : (32 * graphUnit k + i) / 32 = graphUnit k + i / 32 := by omega
  have hd2 : (32 * graphUnit k + i) % 32 = i % 32 := by omega
  rw [index_of (32 * graphUnit k + i) (by omega), hd1, hd2, e]
  omega

/-- Graph-order payload of a wire payload (the decoding direction). -/
def permute (bits : List Bool) : List Bool :=
  List.ofFn fun i : Fin bits.length => bits[index bits.length i.val]'(index_lt _ _ i.isLt)

/-- Wire payload of a graph-order payload (the encoding direction). -/
def unpermute (bits : List Bool) : List Bool :=
  List.ofFn fun i : Fin bits.length => bits[unindex bits.length i.val]'(unindex_lt _ _ i.isLt)

@[simp] theorem length_permute (bits : List Bool) : (permute bits).length = bits.length := by
  simp [permute]

@[simp] theorem length_unpermute (bits : List Bool) : (unpermute bits).length = bits.length := by
  simp [unpermute]

@[simp] theorem getElem_permute (bits : List Bool) (i : ℕ) (hi : i < (permute bits).length) :
    (permute bits)[i] = bits[index bits.length i]'(index_lt _ _ (by simpa using hi)) := by
  simp [permute]

@[simp] theorem getElem_unpermute (bits : List Bool) (i : ℕ) (hi : i < (unpermute bits).length) :
    (unpermute bits)[i] = bits[unindex bits.length i]'(unindex_lt _ _ (by simpa using hi)) := by
  simp [unpermute]

@[simp] theorem permute_unpermute (bits : List Bool) : permute (unpermute bits) = bits := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [getElem_permute, getElem_unpermute, length_unpermute, unindex_index _ _ h2]

@[simp] theorem unpermute_permute (bits : List Bool) : unpermute (permute bits) = bits := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [getElem_unpermute, getElem_permute, length_permute, index_unindex _ _ h2]

theorem unpermute_injective : Function.Injective unpermute :=
  Function.LeftInverse.injective permute_unpermute

end OptimalOTS.Payload
