import Submissions.UpperLeanIsa.SplitTierBridge
import Submissions.UpperLeanIsa.SplitDP
import Submissions.UpperLeanIsa.FourChildNumeric
import Submissions.UpperLeanIsa.ListCert

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option Elab.async false

namespace OptimalOTS.LeanIsaBaseline.Layer.FourChildCodec
open scoped Classical
open FourChildNumeric

/-- The final sparse support is exactly the440 scheduled multiplicities. -/
theorem tier_keys : SplitDP.keys13 = SplitNumeric.tierA := by decide +kernel

theorem tier_size : SplitDP.keys13.length = 440 := by decide

theorem tier_distinct : SplitDP.keys13.Nodup := by
  rw [tier_keys]; exact ListCert.ascB_nodup SplitNumeric.tierA_asc

/-- One linear list equality: the window counts are the pointwise tier products. -/
theorem WL_eq : SplitDP.WL = SplitNumeric.tierN.zipWith (· * ·) SplitNumeric.tierA := by
  decide +kernel

theorem tier_counts : ∀ t < 440,
    SplitDP.WL.getD t 0 = SplitNumeric.tN t * SplitNumeric.tA t := by
  intro t ht
  rw [WL_eq, ListCert.getD_zipWith (by rw [SplitNumeric.tierN_length]; exact ht)
    (by rw [SplitNumeric.tierA_length]; exact ht)]
  rfl

theorem tier_window_length : SplitDP.WL.length ≤ SplitDP.keys13.length := by decide

attribute [local irreducible] SplitDP.keys13 SplitDP.WL

theorem card_weight_table (w : ℕ) :
    (Finset.univ.filter fun I : Index => params.Accepted I ∧ wprod I = w).card =
      SplitDP.WL.getD (SplitDP.keys13.idxOf w) 0 :=
  (card_weight_raw w).trans
    (SplitDP.window_weight cut cost mult (fun _ hn => compM_rec hn) w)

theorem tierHyp : params.TierHyp schedule :=
  tierHyp_of_count schedule SplitDP.keys13 SplitDP.WL rfl tier_size
    (fun t _ => by rw [tier_keys]; rfl) tier_distinct
    tier_window_length tier_counts card_weight_table

end OptimalOTS.LeanIsaBaseline.Layer.FourChildCodec
