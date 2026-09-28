import Submissions.UpperLeanIsa.SplitProfile
import Submissions.UpperLeanIsa.SplitTables

/-! Compressed profiles of the explicit tuple tables; aliases are retained. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitDP

def profile (u : ℕ) : List MProfile :=
  [[(1, 1, 3), (2, 1, 6), (3, 1, 10), (4, 1, 15), (5, 1, 21), (6, 1, 28), (7, 1, 36), (8, 1, 45), (9, 1, 55), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 58)],
   [(0, 1, 1), (1, 1, 3), (2, 1, 6), (3, 1, 10), (4, 1, 15), (5, 1, 21), (6, 1, 28), (7, 1, 36), (8, 1, 45), (9, 1, 55), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 57)],
   [(0, 1, 1), (1, 1, 3), (2, 1, 6), (3, 1, 10), (4, 1, 15), (5, 1, 21), (6, 1, 28), (7, 1, 36), (8, 1, 45), (9, 1, 55), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 57)],
   [(0, 1, 1), (1, 1, 3), (2, 1, 6), (3, 1, 10), (4, 1, 15), (5, 1, 21), (6, 1, 28), (7, 1, 36), (8, 1, 45), (9, 1, 55), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 57)],
   [(0, 1, 1), (1, 1, 3), (2, 1, 6), (3, 1, 10), (4, 1, 15), (5, 1, 21), (6, 1, 28), (7, 1, 36), (8, 1, 45), (9, 1, 55), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 57)],
   [(1, 496, 1), (1, 1, 3), (2, 1, 10), (3, 1, 20), (4, 2, 2), (4, 1, 33), (5, 1, 56), (6, 3, 2), (6, 1, 82), (7, 1, 120), (8, 1, 165), (9, 1, 220), (10, 1, 286), (11, 5, 3), (11, 1, 361), (12, 3, 1), (12, 1, 454), (13, 1, 560), (14, 1, 680), (15, 1, 522)],
   [(1, 9, 1), (1, 1, 1), (2, 1, 7), (3, 2, 1), (3, 1, 15), (4, 1, 30), (5, 1, 50), (6, 1, 77), (7, 4, 2), (7, 1, 110), (8, 1, 156), (9, 1, 210), (10, 1, 275), (11, 1, 352), (12, 1, 442), (13, 1, 304)],
   [(0, 1, 1), (1, 2, 3), (2, 3, 4), (2, 1, 2), (3, 1, 10), (4, 2, 15), (5, 1, 21), (6, 2, 2), (6, 1, 26), (7, 3, 1), (7, 1, 35), (8, 4, 1), (8, 1, 44), (9, 1, 55), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 105), (14, 1, 120), (15, 1, 133), (16, 1, 150)],
   [(1, 3, 3), (2, 3, 6), (3, 24, 1), (3, 1, 9), (4, 1, 15), (5, 1, 21), (6, 1, 28), (7, 1, 36), (8, 1, 45), (9, 1, 55), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 105), (14, 1, 120), (15, 6, 2), (15, 1, 134), (16, 1, 150), (17, 1, 8)],
   [(1, 4, 3), (2, 2, 6), (3, 2, 2), (3, 1, 8), (4, 2, 15), (5, 2, 5), (5, 1, 16), (6, 1, 28), (7, 3, 1), (7, 1, 35), (8, 1, 45), (9, 2, 1), (9, 1, 54), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 105), (14, 1, 120), (15, 1, 136), (16, 1, 150), (17, 1, 19)],
   [(1, 9, 3), (2, 2, 6), (3, 1, 10), (4, 1, 15), (5, 8, 2), (5, 1, 19), (6, 1, 28), (7, 1, 36), (8, 1, 45), (9, 1, 55), (10, 1, 66), (11, 1, 78), (12, 1, 91), (13, 1, 105), (14, 1, 120), (15, 1, 136), (16, 1, 150), (17, 1, 15)],
   [(1, 1, 2), (2, 1, 5), (3, 1, 9), (4, 1, 14), (5, 1, 20), (6, 1, 27), (7, 1, 35), (8, 1, 44), (9, 1, 54), (10, 1, 65), (11, 2, 3), (11, 1, 74), (12, 1, 90), (13, 1, 67)],
   [(1, 144, 1), (1, 1, 1), (2, 2, 3), (2, 1, 2), (3, 1, 9), (4, 1, 14), (5, 1, 20), (6, 1, 27), (7, 1, 35), (8, 1, 44), (9, 1, 54), (10, 9, 1), (10, 1, 64), (11, 1, 77), (12, 1, 90), (13, 1, 104), (14, 1, 119), (15, 1, 135), (16, 1, 70)]].getD u []

def expandedProfile (u : ℕ) : List (ℕ × ℕ) :=
  (profile u).flatMap fun x => List.replicate x.2.2 (x.1, x.2.1)

/-- Raw sum of a cost tuple, by `Nat.add`. -/
def sumR : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.add a (sumR l)

theorem sumR_eq : ∀ l : List ℕ, sumR l = l.sum
  | [] => rfl
  | a :: l => by rw [sumR, List.sum_cons, sumR_eq l]; rfl

/-- Consume `k` table entries of cost `c` and multiplicity `m`; `none` on a mismatch. -/
def takeRun (c m : ℕ) : ℕ → List SplitTables.Entry → Option (List SplitTables.Entry)
  | 0, E => some E
  | _ + 1, [] => none
  | k + 1, e :: E => bif Nat.beq (sumR e.1) c && Nat.beq e.2.2 m then takeRun c m k E else none

/-- Linear run-length check of a table against a compressed profile. -/
def rle : List MProfile → List SplitTables.Entry → Bool
  | [], E => E.isEmpty
  | x :: p, E => match takeRun x.1 x.2.1 x.2.2 E with
    | some E' => rle p E'
    | none => false

theorem takeRun_spec (c m : ℕ) : ∀ (k : ℕ) (E E' : List SplitTables.Entry),
    takeRun c m k E = some E' →
      E.map (fun e => (e.1.sum, e.2.2)) =
        List.replicate k (c, m) ++ E'.map (fun e => (e.1.sum, e.2.2))
  | 0, E, E', h => by
    simp only [takeRun, Option.some.injEq] at h
    subst h
    rfl
  | _ + 1, [], _, h => by simp [takeRun] at h
  | k + 1, e :: E, E', h => by
    simp only [takeRun] at h
    cases hb : (Nat.beq (sumR e.1) c && Nat.beq e.2.2 m) with
    | false => rw [hb] at h; simp at h
    | true =>
      rw [hb, cond_true] at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at hb
      rw [List.map_cons, takeRun_spec c m k E E' h, List.replicate_succ, List.cons_append,
        ← sumR_eq, hb.1, hb.2]

theorem rle_spec : ∀ (p : List MProfile) (E : List SplitTables.Entry), rle p E = true →
    E.map (fun e => (e.1.sum, e.2.2)) = p.flatMap (fun x => List.replicate x.2.2 (x.1, x.2.1))
  | [], E, h => by
    cases E with
    | nil => rfl
    | cons _ _ => simp [rle] at h
  | x :: p, E, h => by
    simp only [rle] at h
    split at h
    · rename_i E' hE
      rw [takeRun_spec _ _ _ E E' hE, rle_spec p E' h, List.flatMap_cons]
    · simp at h

theorem profile_entries0 :
    (SplitTables.entries 0).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 0 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries1 :
    (SplitTables.entries 1).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 1 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries2 :
    (SplitTables.entries 2).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 2 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries3 :
    (SplitTables.entries 3).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 3 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries4 :
    (SplitTables.entries 4).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 4 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries5 :
    (SplitTables.entries 5).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 5 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries6 :
    (SplitTables.entries 6).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 6 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries7 :
    (SplitTables.entries 7).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 7 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries8 :
    (SplitTables.entries 8).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 8 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries9 :
    (SplitTables.entries 9).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 9 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries10 :
    (SplitTables.entries 10).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 10 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries11 :
    (SplitTables.entries 11).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 11 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries12 :
    (SplitTables.entries 12).map (fun e => (e.1.sum, e.2.2)) = expandedProfile 12 :=
  rle_spec _ _ (by decide +kernel)

theorem profile_entries : ∀ u < 13,
    (SplitTables.entries u).map (fun e => (e.1.sum, e.2.2)) = expandedProfile u := by
  intro u hu
  interval_cases u <;> first | exact profile_entries0 | exact profile_entries1 | exact profile_entries2 | exact profile_entries3 | exact profile_entries4 | exact profile_entries5 | exact profile_entries6 | exact profile_entries7 | exact profile_entries8 | exact profile_entries9 | exact profile_entries10 | exact profile_entries11 | exact profile_entries12

theorem profile_expand {u : ℕ} (hu : u < 13) :
    (SplitTables.entries u).map (fun e => (e.1.sum, e.2.2)) =
      (profile u).flatMap (fun x => List.replicate x.2.2 (x.1, x.2.1)) :=
  profile_entries u hu

end OptimalOTS.LeanIsaBaseline.Layer.SplitDP
