import Mathlib.Probability.Moments.Variance

/-! # Real-valued Chebyshev lower tails, capped by total probability -/

open MeasureTheory ProbabilityTheory Set

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma measure_le_neg_le_variance {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (hMean : (∫ ω, X ω ∂μ) = 0) {r : ℝ} (hr : 0 < r) :
    μ.real {ω | X ω ≤ -r} ≤ min 1 (variance X μ/r^2) := by
  apply le_min
  · have h := measureReal_mono (μ := μ) (subset_univ {ω | X ω ≤ -r})
    simpa only [probReal_univ] using h
  · have hSub : {ω | X ω ≤ -r} ⊆ {ω | r ≤ |X ω-(∫ z, X z ∂μ)|} := by
      intro ω hω
      change X ω ≤ -r at hω
      change r ≤ |X ω-(∫ z, X z ∂μ)|
      rw [hMean,sub_zero]
      have := neg_le_abs (X ω)
      linarith only [hω,this]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (meas_ge_le_variance_div_sq hX hr)
    have hNonnegative : 0 ≤ variance X μ/r^2 := div_nonneg (variance_nonneg X μ) (sq_nonneg r)
    exact (measureReal_mono hSub).trans (by
      simpa only [measureReal_def,ENNReal.toReal_ofReal hNonnegative] using h)

end ProphetSecretary.Probability
