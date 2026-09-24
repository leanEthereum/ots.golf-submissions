import Submissions.UpperLeanIsa.RootBinding

/-! Exact, injective oracle-query layouts. Tags are actual paid input bits. -/

namespace OptimalOTS.LeanIsaBaseline

theorem bits_injective {n : ℕ} : Function.Injective (@toBits n) := by
  intro x y h
  exact (ofBits_bits x).symm.trans ((congrArg (ofBits n) h).trans (ofBits_bits y))

theorem hashInput_bits (cv : BitVec 256) (block : BitVec 512) (md : BitVec 128) :
    toBits (LeanIsa.hashInput cv block md) = toBits cv ++ toBits block ++ toBits md := by
  apply bits_ofBits
  simp only [List.length_append, length_bits]

theorem hashInput_eq_iff (cv cv' : BitVec 256) (block block' : BitVec 512)
    (md md' : BitVec 128) :
    LeanIsa.hashInput cv block md = LeanIsa.hashInput cv' block' md' ↔
      cv = cv' ∧ block = block' ∧ md = md' := by
  constructor
  · intro h
    have hb := congrArg toBits h
    rw [hashInput_bits, hashInput_bits] at hb
    obtain ⟨hab, hc⟩ := List.append_inj hb (by simp only [List.length_append, length_bits])
    obtain ⟨ha, hb⟩ := List.append_inj hab (by simp only [length_bits])
    exact ⟨bits_injective ha, bits_injective hb, bits_injective hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def rootInput (remaining : Fin 39) (cv : BitVec 256) (x : Word) : BitVec 896 :=
  LeanIsa.hashInput cv (x.setWidth 512) (BitVec.ofNat 128 (2 + remaining.val))

private theorem root_tag_injective {r s : Fin 39}
    (h : BitVec.ofNat 128 (2 + r.val) = BitVec.ofNat 128 (2 + s.val)) : r = s := by
  have hr : 2 + r.val < 2 ^ 128 := by have := r.isLt; omega
  have hs : 2 + s.val < 2 ^ 128 := by have := s.isLt; omega
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at hn
  apply Fin.ext
  omega

theorem rootInput_eq_iff (r s : Fin 39) (cv dv : BitVec 256) (x y : Word) :
    rootInput r cv x = rootInput s dv y ↔ r = s ∧ cv = dv ∧ x = y := by
  rw [rootInput, rootInput, hashInput_eq_iff]
  constructor
  · rintro ⟨hc, hx, ht⟩
    refine ⟨root_tag_injective ht, hc, ?_⟩
    have := congrArg (BitVec.setWidth 128) hx
    simpa using this
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

theorem chainInput_ne_rootInput (i j : ℕ) (x : Word) (r : Fin 39)
    (cv : BitVec 256) (y : Word) : chainInput i j x ≠ rootInput r cv y := by
  intro h
  have ht := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
  have hn := congrArg BitVec.toNat ht
  have hr : 2 + r.val < 2 ^ 128 := by have := r.isLt; omega
  change 1 = (2 + r.val) % 2 ^ 128 at hn
  rw [Nat.mod_eq_of_lt hr] at hn
  omega

private theorem append_injective {a b : ℕ} {x x' : BitVec a} {y y' : BitVec b}
    (h : x ++ y = x' ++ y') : x = x' ∧ y = y' := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun z : BitVec (a + b) => z.extractLsb' b a) h
  · simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (a + b) => z.extractLsb' 0 b) h

private theorem nat128_injective {a b : ℕ} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (h : BitVec.ofNat 128 a = BitVec.ofNat 128 b) : a = b := by
  have hn := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hn

theorem chainInput_eq_iff (i k : Fin 39) (j l : Fin 127) (x y : Word) :
    chainInput i.val j.val x = chainInput k.val l.val y ↔ i = k ∧ j = l ∧ x = y := by
  constructor
  · intro h
    have hb := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.1
    obtain ⟨hh, hx⟩ := append_injective hb
    obtain ⟨hh, hi⟩ := append_injective hh
    obtain ⟨_, hj⟩ := append_injective hh
    refine ⟨Fin.ext (nat128_injective ?_ ?_ hi), Fin.ext (nat128_injective ?_ ?_ hj), hx⟩
    all_goals omega
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

end OptimalOTS.LeanIsaBaseline
