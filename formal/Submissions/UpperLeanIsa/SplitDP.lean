import Submissions.UpperLeanIsa.SplitDPStage13
import Submissions.UpperLeanIsa.SplitContraction
import Submissions.UpperLeanIsa.SplitPack

/-! Correctness and cost-window projection of the sparse multiplicative DP.

Stages `0 … 11` are packed sparse tables (`tab`): one `(weight, packed cost row)` entry per
support weight, each cost row packed into one natural number in base `SplitPack.B`.
Stages 12 and 13 are contracted into `SplitWindow.combined`, and the accepted-cost window
is read off each packed row. One kernel evaluation (`final_check`) computes the whole
chain from the single stage-0 entry and compares it with `keys13.zip WL`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitDP

open SplitPack

/-- The distinct multiplicities of `profile n`. -/
def mults (n : ℕ) : List ℕ :=
  [[1], [1], [1], [1], [1], [496, 2, 5, 3, 1], [9, 2, 4, 1], [2, 3, 4, 1], [3, 24, 6, 1],
    [4, 3, 2, 1], [9, 2, 8, 1], [2, 1], [144, 2, 9, 1]].getD n []

/-- The distinct multiplicities of the contracted last two profiles. -/
def multsLast : List ℕ := [1, 2, 4, 9, 18, 144, 288]

theorem mults_ok : ∀ n < 11, ((mults n).Nodup ∧ ∀ x ∈ profile n, x.2.1 ∈ mults n) ∧
    ∀ m ∈ mults n, 0 < m := by decide +kernel

theorem multsLast_ok : (multsLast.Nodup ∧ ∀ x ∈ SplitWindow.combined, x.2.1 ∈ multsLast) ∧
    ∀ m ∈ multsLast, 0 < m := by decide +kernel

/-- Packed sparse tables of stages `0 … 11`, rows truncated to costs `< 86`. -/
def tab : ℕ → List (ℕ × ℕ)
  | 0 => [(1, 1)]
  | n + 1 => modA (B ^ 86) (stepG (groupP (profile n) (mults n)) (tab n))

/-- Accepted-window counts of the contracted final step, keyed by final weight. -/
def finalTable : List (ℕ × ℕ) :=
  (stepG (groupP SplitWindow.combined multsLast) (tab 11)).map fun e =>
    (e.1, e.2 % B ^ 86 / B ^ 22 % (B - 1))

theorem final_check : finalTable = keys13.zip WL := by decide +kernel

theorem keys13_chain : ltChain keys13 = true := by decide +kernel

theorem keys13_nodup : keys13.Nodup := nodup_of_ltChain keys13 keys13_chain

theorem window_length : WL.length = keys13.length := by decide +kernel

/-- A-priori bound on every stage entry: the number of raw tuples so far. -/
def Mb : ℕ → ℕ
  | 0 => 1
  | n + 1 => tot (profile n) * Mb n

theorem Mb_lt : (∀ n < 14, Mb n < B) ∧ 64 * Mb 13 < B - 1 := by decide +kernel

variable (N : ℕ → ℕ) (f g : ℕ → ℕ → ℕ)

theorem compM_le
    (hrec : ∀ n < 13, ∀ s w, compM N f g (n + 1) s w =
      ((profile n).map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum) :
    ∀ n ≤ 13, ∀ s w, compM N f g n s w ≤ Mb n := by
  intro n
  induction n with
  | zero =>
    intro _ s w
    rw [compM]
    split_ifs <;> simp [Mb]
  | succ n ih =>
    intro hn s w
    exact bound_step (profile n) (compM N f g n) (compM N f g (n + 1)) (hrec n (by omega))
      (Mb n) (ih (by omega)) s w

theorem tab_inv
    (hrec : ∀ n < 13, ∀ s w, compM N f g (n + 1) s w =
      ((profile n).map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum)
    (hB : ∀ n ≤ 13, ∀ s w, compM N f g n s w < B) :
    ∀ n ≤ 11, Inv 86 (compM N f g n) (tab n) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact inv_zero 86 (by omega) _ fun s w => by rw [compM]
  | succ n ih =>
    intro hn w
    have hm := mults_ok n (by omega)
    rw [tab, evalA_modA]
    exact inv_step 86 (profile n) (mults n) hm.1.1 hm.1.2 hm.2 (compM N f g n)
      (compM N f g (n + 1)) (hrec n (by omega)) (hB (n + 1) (by omega)) (tab n)
      (ih (by omega)) w

/-- The exact sparse checkpoints represent the full unrestricted multiplicative DP,
and the accepted-cost window is the table `WL`. -/
theorem window_weight
    (hrec : ∀ n < 13, ∀ s w, compM N f g (n + 1) s w =
      ((profile n).map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum)
    (w : ℕ) :
    ∑ s ∈ Finset.Ico 22 86, compM N f g 13 s w = WL.getD (keys13.idxOf w) 0 := by
  have hle := compM_le N f g hrec
  have hB : ∀ n ≤ 13, ∀ s w, compM N f g n s w < B :=
    fun n hn s w => (hle n hn s w).trans_lt (Mb_lt.1 n (by omega))
  have hrec2 := SplitWindow.compM_two_profile N f g 11 (profile 12) (profile 11)
    SplitWindow.combined SplitWindow.combined_correct (hrec 12 (by omega)) (hrec 11 (by omega))
  have hlast := inv_step 86 SplitWindow.combined multsLast multsLast_ok.1.1 multsLast_ok.1.2
    multsLast_ok.2 (compM N f g 11) (compM N f g 13) hrec2 (hB 13 le_rfl) (tab 11)
    (tab_inv N f g hrec hB 11 (by omega))
  have hkeys : ((stepG (groupP SplitWindow.combined multsLast) (tab 11)).map Prod.fst).Nodup := by
    have h := congrArg (List.map Prod.fst) final_check
    rw [List.map_fst_zip window_length.ge, finalTable, List.map_map] at h
    exact h ▸ keys13_nodup
  have hsum : ∑ s ∈ Finset.Ico 22 86, compM N f g 13 s w < B - 1 := by
    calc
      _ ≤ ∑ _s ∈ Finset.Ico 22 86, Mb 13 := Finset.sum_le_sum fun s _ => hle 13 le_rfl s w
      _ = 64 * Mb 13 := by simp
      _ < B - 1 := Mb_lt.2
  have hval := evalA_map_nodup (fun X => X % B ^ 86 / B ^ 22 % (B - 1)) (by simp) _ hkeys w
  rw [← finalTable, final_check, evalA_zip keys13 WL keys13_nodup window_length, hlast,
    window_extract _ (fun t _ => hB 13 le_rfl t w) hsum] at hval
  exact hval.symm

end OptimalOTS.LeanIsaBaseline.Layer.SplitDP
