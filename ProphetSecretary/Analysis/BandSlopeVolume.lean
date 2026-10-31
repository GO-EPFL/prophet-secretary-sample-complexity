import ProphetSecretary.Analysis.ThresholdBand

/-!
# Width from a slope bound on the band itself

Only pairs already inside the acceptance band need satisfy the lower
increment bound. This permits flat continuation outside the positive band
and monotone jumps when an identity is removed.
-/
open MeasureTheory Set
open scoped ENNReal
namespace ProphetSecretary.Analysis

theorem volume_thresholdBand_le_of_bandSlope {g : ℝ → ℝ} {a e : ℝ} (ha : 0 < a)
    (hslope : SlopeLowerBoundOn g a (thresholdBand g e)) :
    volume (thresholdBand g e) ≤ ENNReal.ofReal (2*e/a) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro t ht s hs
  have hgt := abs_le.mp (show |g t| ≤ e from ht.2)
  have hgs := abs_le.mp (show |g s| ≤ e from hs.2)
  rcases le_total t s with hts | hst
  · have h := hslope t ht s hs hts
    have hd : s-t ≤ 2*e/a := (le_div_iff₀ ha).mpr (by nlinarith)
    simpa only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub] using hd
  · have h := hslope s hs t ht hst
    have hd : t-s ≤ 2*e/a := (le_div_iff₀ ha).mpr (by nlinarith)
    simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hst)] using hd

end ProphetSecretary.Analysis
