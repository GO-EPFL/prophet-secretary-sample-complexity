import ProphetSecretary.Analysis.StoppingDecisionLoss

/-!
# Both Bellman losses under a threshold disagreement

The true loss of the empirical decision and the empirical loss of the true
decision are both at most the value error. Both vanish outside the band
around the TRUE gap, as required before the near/far integration in
`upstat:selected` and the separate fixed-weight optimism bound.
-/

open scoped Classical

namespace ProphetSecretary.Analysis

lemma gapLoss_threshold_zero (g : ℝ) : gapLoss (decide (0 ≤ g)) g = 0 := by
  by_cases hg : 0 ≤ g
  · simp only [hg, decide_true, gapLoss, if_true, max_eq_right (neg_nonpos.mpr hg)]
  · simp only [hg, decide_false, gapLoss, Bool.false_eq_true, if_false, max_eq_right (not_le.mp hg).le]

lemma gapLoss_vanishes_outside_target_band {accept : Bool} {g g' e : ℝ}
    (hzero : gapLoss accept g = 0) (hpert : |g' - g| ≤ e) (hout : e < |g'|) :
    gapLoss accept g' = 0 := by
  have hp := abs_le.mp hpert
  cases accept with
  | false =>
    have hg : g ≤ 0 := (le_max_left g 0).trans hzero.le
    have hg' : g' ≤ 0 := by
      by_contra hn
      have ht : 0 < g' := not_le.mp hn
      rw [abs_of_pos ht] at hout
      linarith only [hg, hp.2, hout]
    exact max_eq_right hg'
  | true =>
    have hg : 0 ≤ g := by have h := (le_max_left (-g) 0).trans hzero.le; linarith only [h]
    have hg' : 0 ≤ g' := by
      by_contra hn
      have ht : g' < 0 := not_le.mp hn
      rw [abs_of_neg ht] at hout
      linarith only [hg, hp.1, hout]
    exact max_eq_right (neg_nonpos.mpr hg')

/-- The first gap is true and the second estimated. The support band is the
first one for BOTH losses, including at exact threshold ties. -/
theorem paired_gapLoss_bound {g ĝ e : ℝ} (hpert : |g - ĝ| ≤ e) :
    gapLoss (decide (0 ≤ ĝ)) g ≤ (if |g| ≤ e then e else 0) ∧
      gapLoss (decide (0 ≤ g)) ĝ ≤ (if |g| ≤ e then e else 0) := by
  by_cases hband : |g| ≤ e
  · rw [if_pos hband]
    constructor
    · exact gapLoss_perturbation_bound (gapLoss_threshold_zero ĝ) hpert
    · exact gapLoss_perturbation_bound (gapLoss_threshold_zero g) (by simpa only [abs_sub_comm] using hpert)
  · rw [if_neg hband]
    have hout : e < |g| := not_le.mp hband
    have hfirst := gapLoss_vanishes_outside_target_band (gapLoss_threshold_zero ĝ) hpert hout
    have hsecond := gapLoss_vanishes_outside_band (gapLoss_threshold_zero g)
      (by simpa only [abs_sub_comm] using hpert) hout
    rw [hfirst, hsecond]
    exact ⟨le_rfl, le_rfl⟩

end ProphetSecretary.Analysis
