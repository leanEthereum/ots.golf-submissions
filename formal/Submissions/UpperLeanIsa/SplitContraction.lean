import Submissions.UpperLeanIsa.SplitWindow

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitWindow

open SplitDP

def combined : List MProfile := [(2, 1, 2), (2, 144, 2), (3, 1, 9), (3, 2, 6), (3, 144, 5), (4, 1, 37), (4, 2, 15), (4, 144, 9), (5, 1, 105), (5, 2, 27), (5, 144, 14), (6, 1, 239), (6, 2, 42), (6, 144, 20), (7, 1, 473), (7, 2, 60), (7, 144, 27), (8, 1, 850), (8, 2, 81), (8, 144, 35), (9, 1, 1423), (9, 2, 105), (9, 144, 44), (10, 1, 2256), (10, 2, 132), (10, 144, 54), (11, 1, 3423), (11, 2, 162), (11, 9, 2), (11, 144, 65), (12, 1, 5011), (12, 2, 198), (12, 9, 5), (12, 144, 74), (12, 288, 3), (13, 1, 7126), (13, 2, 228), (13, 4, 9), (13, 9, 9), (13, 144, 90), (14, 1, 9831), (14, 2, 297), (14, 9, 14), (14, 144, 67), (15, 1, 13202), (15, 2, 243), (15, 9, 20), (16, 1, 17143), (16, 2, 60), (16, 9, 27), (17, 1, 21224), (17, 2, 81), (17, 9, 35), (18, 1, 25388), (18, 2, 105), (18, 9, 44), (19, 1, 29427), (19, 2, 132), (19, 9, 54), (20, 1, 33112), (20, 2, 162), (20, 9, 65), (21, 1, 36195), (21, 2, 192), (21, 9, 74), (21, 18, 3), (22, 1, 38393), (22, 2, 231), (22, 9, 90), (23, 1, 39454), (23, 2, 270), (23, 9, 67), (24, 1, 39060), (24, 2, 312), (25, 1, 36751), (25, 2, 357), (26, 1, 32218), (26, 2, 405), (27, 1, 25303), (27, 2, 210), (28, 1, 15345), (29, 1, 4690)]

theorem combined_correct (F : ℕ → ℕ → ℕ) :
    profileSumM combined F =
      profileSumM (profile 12) (fun c m =>
        profileSumM (profile 11) (fun d k => F (c + d) (m * k))) := by
  norm_num [profileSumM, combined, profile]
  omega


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

theorem profileWindow_correct (F G : ℕ → ℕ → ℕ)
    (p : List MProfile) (S : ℕ) (keys : List ℕ) (rows : List (List ℕ))
    (hrec : ∀ s w, G s w =
      (p.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * F (s - x.1) (w / x.2.1) else 0).sum)
    (hprev : ∀ w s, s ≤ S → (rowM keys rows w).getD s 0 = F s w)
    (a b w : ℕ) (hb : b ≤ S + 1) :
    ∑ s ∈ Finset.Ico a b, G s w = stepWindow p keys rows a b w := by
  simp only [hrec]
  rw [sum_list_comm, stepWindow]
  congr 1
  apply List.map_congr_left
  intro x hx
  by_cases hd : x.2.1 ∣ w
  · simp only [hd, and_true, if_true]
    rw [window_eq, Finset.mul_sum]
    calc
      _ = ∑ s ∈ Finset.Ico a b, if x.1 ≤ s then
          (x.2.2 * x.2.1) * (rowM keys rows (w / x.2.1)).getD (s - x.1) 0 else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        split_ifs with hc
        · rw [hprev _ _ (by have := (Finset.mem_Ico.mp hs).2; omega)]
        · rfl
      _ = _ := shift_window (fun s =>
        (x.2.2 * x.2.1) * (rowM keys rows (w / x.2.1)).getD s 0) a b x.1
  · simp [hd]

end OptimalOTS.LeanIsaBaseline.Layer.SplitWindow
