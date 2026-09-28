import Submissions.UpperLeanIsa.SplitDPStage13

/-! Correctness and cost-window projection of the checked sparse checkpoints. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitDP

def keys (n : ℕ) : List ℕ :=
  [keys0, keys1, keys2, keys3, keys4, keys5, keys6, keys7, keys8, keys9, keys10, keys11].getD n []

def rows (n : ℕ) : List (List ℕ) :=
  [rows0, rows1, rows2, rows3, rows4, rows5, rows6, rows7, rows8, rows9, rows10, rows11].getD n []

theorem steps : ∀ n < 11, stepM (profile n) 85 (keys n) (keys (n + 1)) (rows n) = rows (n + 1) := by
  intro n hn
  interval_cases n
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11

theorem closed : ∀ n < 11, ∀ x ∈ profile n, ∀ w ∈ keys n, w * x.2.1 ∈ keys (n + 1) := by
  intro n hn
  interval_cases n
  · exact closed0
  · exact closed1
  · exact closed2
  · exact closed3
  · exact closed4
  · exact closed5
  · exact closed6
  · exact closed7
  · exact closed8
  · exact closed9
  · exact closed10

theorem rows_length : ∀ n ≤ 11, (rows n).length = (keys n).length := by
  intro n hn
  interval_cases n
  · exact rows_length0
  · exact rows_length1
  · exact rows_length2
  · exact rows_length3
  · exact rows_length4
  · exact rows_length5
  · exact rows_length6
  · exact rows_length7
  · exact rows_length8
  · exact rows_length9
  · exact rows_length10
  · exact rows_length11

variable (N : ℕ → ℕ) (f g : ℕ → ℕ → ℕ)

/-- The exact sparse table represents the full unrestricted multiplicative DP. -/
theorem rows_correct
    (hrec : ∀ n < 13, ∀ s w, compM N f g (n + 1) s w =
      ((profile n).map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum) :
    ∀ n ≤ 11, ∀ w s, s ≤ 85 → (rowM (keys n) (rows n) w).getD s 0 = compM N f g n s w := by
  intro n
  induction n with
  | zero =>
    intro _ w s hs
    exact rowM_initial N f g 85 w s hs
  | succ n ih =>
    intro hn w s hs
    rw [← steps n (by omega)]
    exact stepM_correct N f g (profile n) 85 n (keys n) (keys (n + 1)) (rows n)
      (hrec n (by omega)) (rows_length n (by omega)).le (ih (by omega)) (closed n (by omega)) w s hs

attribute [local irreducible] keys11 rows11 keys13 WL

theorem window_weight
    (hrec : ∀ n < 13, ∀ s w, compM N f g (n + 1) s w =
      ((profile n).map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum)
    (w : ℕ) :
    ∑ s ∈ Finset.Ico 22 86, compM N f g 13 s w = WL.getD (keys13.idxOf w) 0 := by
  have hrec2 := SplitWindow.compM_two_profile N f g 11 (profile 12) (profile 11)
    SplitWindow.combined SplitWindow.combined_correct (hrec 12 (by omega)) (hrec 11 (by omega))
  have hwindow := SplitWindow.profileWindow_correct (compM N f g 11) (compM N f g 13)
    SplitWindow.combined 85 keys11 rows11 hrec2 (rows_correct N f g hrec 11 le_rfl)
    22 86 w (by omega)
  rw [hwindow, ← stepDot_eq]
  by_cases hw : w ∈ keys13
  · have h := SplitWindow.map_idxOf keys13 (stepDot keys11 rows11) hw
    rw [window_table] at h
    exact h.symm
  · rw [stepDot_eq, SplitWindow.stepWindow_not_mem SplitWindow.combined keys11 keys13 rows11
      rows_length11.le combined_closed 22 86 w hw]
    symm
    apply List.getD_eq_default
    rw [List.idxOf_of_notMem hw, window_length]


end OptimalOTS.LeanIsaBaseline.Layer.SplitDP
