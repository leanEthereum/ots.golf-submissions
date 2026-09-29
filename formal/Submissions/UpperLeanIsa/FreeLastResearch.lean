import Submissions.UpperLeanIsa.AffineFrames
import Submissions.UpperLeanIsa.CenteredChecksum

/-! Proof support for the free-last 1089 research design. These results prove
the product invariant and the conservative root arithmetic, not control-flow
soundness or a complete submission certificate. -/
namespace OptimalOTS.FreeLastResearch

open Polynomial

theorem exists_common_nonroot_weighted
    {F I : Type} [Field F] [Fintype F] [Fintype I]
    (polys : I → F[X]) (degrees : I → Nat)
    (hne : ∀ i, polys i ≠ 0) (hdeg : ∀ i, (polys i).natDegree ≤ degrees i)
    (hcard : (∑ i, degrees i) < Fintype.card F) :
    ∃ a : F, ∀ i, (polys i).eval a ≠ 0 := by
  classical
  let p : F[X] := ∏ i : I, polys i
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hb : p.natDegree ≤ ∑ i, degrees i :=
    (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => hdeg i)
  obtain ⟨a, ha⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card p hp (by
    rw [Cardinal.mk_fintype]
    exact_mod_cast hb.trans_lt hcard)
  have he : (∏ i : I, (polys i).eval a) ≠ 0 := by
    simpa only [p, Polynomial.eval_prod] using ha
  exact ⟨a, fun i => Finset.prod_ne_zero_iff.mp he i (Finset.mem_univ _)⟩

theorem product_invariant {F : Type} [Field F] {a : F} (ha : a ≠ 0)
    (cost : Nat → Nat) (gp : Nat → F) (h0 : gp 0 = a)
    (hs : ∀ u, CenteredChecksum.Step a (cost u) (gp u) (gp (u+1))) :
    gp 13 * a^78 = a^(1 + ∑ u ∈ Finset.range 13, cost u) := by
  have h := CenteredChecksum.invariant ha cost gp hs 13
  rw [h0] at h
  simpa only [show 6*13 = 78 by decide, pow_add, pow_one] using h

theorem zero_path_layer {charged costs : Nat} (h : charged + 8 = costs) :
    1 + charged = 78 ↔ costs = 85 := by omega

theorem positive_path_layer {s charged costs : Nat} (h : charged + 8 = costs) :
    s + 1 + charged = 78 ↔ s + costs = 85 := by omega

def groupCap : Nat := 2^18
def freeCap : Nat := 2079
def targetCells : Nat := 2^32

def stageDegrees : Nat :=
  ((List.range' 1 12).map (fun f => groupCap * max f 12 + freeCap * (f+63))).sum +
    groupCap*12 + freeCap*63

def freeDegrees : Nat :=
  ((List.range' 1 77).map (fun n => groupCap*(12+n) + freeCap*max n 63)).sum +
  ((List.range 105).map (fun n => groupCap*max n 12 + freeCap*(n+63))).sum

def exitDegrees : Nat := groupCap*12 + freeCap*63
def miscellaneous : Nat := (groupCap+301*301+301+14)*300+1
def rootBound : Nat := (stageDegrees+freeDegrees+exitDegrees)*targetCells+miscellaneous

theorem rootBound_value : rootBound = 11006439705738751537 := by decide +kernel
theorem rootBound_lt_field : rootBound < 2^64 := by decide +kernel
theorem candidate_accounting : 16+82+1+87*10+120 = (1089 : Nat) := by decide
theorem candidate_uniform_steps : 16+82+1+87 = (186 : Nat) := by decide

end OptimalOTS.FreeLastResearch
