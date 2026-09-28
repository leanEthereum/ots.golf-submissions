import Submissions.UpperLeanIsa.SplitProfiles

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitWindow

open SplitDP

def combined : List MProfile := [(2, 1, 2), (2, 144, 2), (3, 1, 9), (3, 2, 6), (3, 144, 5), (4, 1, 37), (4, 2, 15), (4, 144, 9), (5, 1, 105), (5, 2, 27), (5, 144, 14), (6, 1, 239), (6, 2, 42), (6, 144, 20), (7, 1, 473), (7, 2, 60), (7, 144, 27), (8, 1, 850), (8, 2, 81), (8, 144, 35), (9, 1, 1423), (9, 2, 105), (9, 144, 44), (10, 1, 2256), (10, 2, 132), (10, 144, 54), (11, 1, 3423), (11, 2, 162), (11, 9, 2), (11, 144, 65), (12, 1, 5011), (12, 2, 198), (12, 9, 5), (12, 144, 74), (12, 288, 3), (13, 1, 7126), (13, 2, 228), (13, 4, 9), (13, 9, 9), (13, 144, 90), (14, 1, 9831), (14, 2, 297), (14, 9, 14), (14, 144, 67), (15, 1, 13202), (15, 2, 243), (15, 9, 20), (16, 1, 17143), (16, 2, 60), (16, 9, 27), (17, 1, 21224), (17, 2, 81), (17, 9, 35), (18, 1, 25388), (18, 2, 105), (18, 9, 44), (19, 1, 29427), (19, 2, 132), (19, 9, 54), (20, 1, 33112), (20, 2, 162), (20, 9, 65), (21, 1, 36195), (21, 2, 192), (21, 9, 74), (21, 18, 3), (22, 1, 38393), (22, 2, 231), (22, 9, 90), (23, 1, 39454), (23, 2, 270), (23, 9, 67), (24, 1, 39060), (24, 2, 312), (25, 1, 36751), (25, 2, 357), (26, 1, 32218), (26, 2, 405), (27, 1, 25303), (27, 2, 210), (28, 1, 15345), (29, 1, 4690)]

/-- All pairs of entries of two profiles: costs add, multiplicities and counts multiply. -/
def prodProfile (p q : List MProfile) : List MProfile :=
  p.flatMap fun x => q.map fun y => (x.1 + y.1, x.2.1 * y.2.1, x.2.2 * y.2.2)

theorem profileSumM_prod (p q : List MProfile) (F : ℕ → ℕ → ℕ) :
    profileSumM (prodProfile p q) F =
      profileSumM p (fun c m => profileSumM q (fun d k => F (c + d) (m * k))) := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    have happ : ∀ A C : List MProfile,
        profileSumM (A ++ C) F = profileSumM A F + profileSumM C F := by
      intro A C
      simp [profileSumM]
    rw [prodProfile, List.flatMap_cons, ← prodProfile, happ, ih]
    simp only [profileSumM, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      ← List.sum_map_mul_left]
    congr 1
    congr 1
    apply List.map_congr_left
    intro y _
    ring

/-- Insert one entry into a profile sorted by `(cost, multiplicity)`, merging equal keys. -/
def insertP (z : MProfile) : List MProfile → List MProfile
  | [] => [z]
  | a :: l =>
    bif Nat.blt z.1 a.1 || (Nat.beq z.1 a.1 && Nat.blt z.2.1 a.2.1) then z :: a :: l
    else bif Nat.beq z.1 a.1 && Nat.beq z.2.1 a.2.1 then (a.1, a.2.1, a.2.2 + z.2.2) :: l
    else a :: insertP z l

theorem profileSumM_insertP (z : MProfile) (F : ℕ → ℕ → ℕ) : ∀ l : List MProfile,
    profileSumM (insertP z l) F = (z.2.2 * z.2.1) * F z.1 z.2.1 + profileSumM l F
  | [] => by simp [insertP, profileSumM]
  | a :: l => by
    unfold insertP
    cases h1 : (Nat.blt z.1 a.1 || (Nat.beq z.1 a.1 && Nat.blt z.2.1 a.2.1))
    · cases h2 : (Nat.beq z.1 a.1 && Nat.beq z.2.1 a.2.1)
      · simp only [cond_false]
        simp only [profileSumM, List.map_cons, List.sum_cons] at *
        rw [← profileSumM, ← profileSumM, profileSumM_insertP z F l]
        ring
      · simp only [Bool.and_eq_true, Nat.beq_eq] at h2
        simp only [cond_false, cond_true, profileSumM, List.map_cons, List.sum_cons, h2.1, h2.2]
        ring
    · simp [profileSumM]

/-- Canonical merged form of a profile. -/
def normP (l : List MProfile) : List MProfile := l.foldr insertP []

theorem profileSumM_normP (F : ℕ → ℕ → ℕ) : ∀ l : List MProfile,
    profileSumM (normP l) F = profileSumM l F
  | [] => rfl
  | z :: l => by
    rw [normP, List.foldr_cons, ← normP, profileSumM_insertP, profileSumM_normP F l]
    simp [profileSumM]

theorem combined_norm : normP (prodProfile (profile 12) (profile 11)) = combined := by
  decide +kernel

theorem combined_correct (F : ℕ → ℕ → ℕ) :
    profileSumM combined F =
      profileSumM (profile 12) (fun c m =>
        profileSumM (profile 11) (fun d k => F (c + d) (m * k))) := by
  rw [← combined_norm, profileSumM_normP, profileSumM_prod]


def applyProfile (p : List MProfile) (F : ℕ → ℕ → ℕ) (s w : ℕ) : ℕ :=
  profileSumM p fun c m => if c ≤ s ∧ m ∣ w then F (s - c) (w / m) else 0

theorem applyProfile_eq (p : List MProfile) (F : ℕ → ℕ → ℕ) (s w : ℕ) :
    applyProfile p F s w =
      (p.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * F (s - x.1) (w / x.2.1) else 0).sum := by
  unfold applyProfile profileSumM
  congr 1
  apply List.map_congr_left
  intro x _
  dsimp only
  split_ifs <;> simp_all

theorem applyProfile_compose (p q r : List MProfile)
    (hr : ∀ F : ℕ → ℕ → ℕ, profileSumM r F =
      profileSumM p fun c m => profileSumM q fun d k => F (c + d) (m * k))
    (F : ℕ → ℕ → ℕ) (s w : ℕ) :
    applyProfile p (applyProfile q F) s w = applyProfile r F s w := by
  unfold applyProfile
  rw [hr]
  unfold profileSumM
  congr 1
  apply List.map_congr_left
  intro x hx
  dsimp only
  by_cases hg : x.1 ≤ s ∧ x.2.1 ∣ w
  · rw [if_pos hg]
    congr 1
    congr 1
    apply List.map_congr_left
    intro y hy
    have he : (x.1 + y.1 ≤ s ∧ x.2.1 * y.2.1 ∣ w) ↔
        (y.1 ≤ s - x.1 ∧ y.2.1 ∣ w / x.2.1) := by
      rw [Nat.dvd_div_iff_mul_dvd hg.2]
      omega
    simp only [he, Nat.sub_sub, Nat.div_div_eq_div_mul]
  · rw [if_neg hg]
    have hz : (q.map fun y =>
        (y.2.2 * y.2.1) *
          (if x.1 + y.1 ≤ s ∧ x.2.1 * y.2.1 ∣ w then
            F (s - (x.1 + y.1)) (w / (x.2.1 * y.2.1)) else 0)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      rw [if_neg (fun h => hg ⟨by omega, dvd_trans (dvd_mul_right _ _) h.2⟩)]
      simp
    rw [hz]

theorem compM_two_profile (N : ℕ → ℕ) (f g : ℕ → ℕ → ℕ) (n : ℕ)
    (p q r : List MProfile)
    (hr : ∀ F : ℕ → ℕ → ℕ, profileSumM r F =
      profileSumM p fun c m => profileSumM q fun d k => F (c + d) (m * k))
    (hp : ∀ s w, compM N f g (n + 2) s w =
      (p.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g (n + 1) (s - x.1) (w / x.2.1) else 0).sum)
    (hq : ∀ s w, compM N f g (n + 1) s w =
      (q.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum) :
    ∀ s w, compM N f g (n + 2) s w =
      (r.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum := by
  intro s w
  rw [hp, ← applyProfile_eq, ← applyProfile_eq]
  have he : compM N f g (n + 1) = applyProfile q (compM N f g n) := by
    funext s w
    exact (hq s w).trans (applyProfile_eq q _ s w).symm
  rw [he]
  exact applyProfile_compose p q r hr (compM N f g n) s w

end OptimalOTS.LeanIsaBaseline.Layer.SplitWindow
