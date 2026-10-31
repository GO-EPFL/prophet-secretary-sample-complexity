import ProphetSecretary.Statistics.Hoeffding.AlmostSureBound
import ProphetSecretary.Probability.VarianceLowerTail

/-!
# The pilot's higher-order lower tail

The literal empirical remainder has mean zero and variance at most 1/k².
The resulting Chebyshev term is capped by one, as in `eq:bayes-fixed-tail`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ProphetSecretary.Statistics.Hoeffding
open ProphetSecretary.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

theorem empiricalRemainder_lower_tail (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ 1)
    {s : ℝ} (hs : 0 < s) :
    (Measure.pi (fun q : ι × Fin k => μ q.1)).real
      {y | empiricalRemainder μ f y ≤ -s/4} ≤ min 1 (16/((k : ℝ)^2*s^2)) := by
  have h := measure_le_neg_le_variance (memLp_empiricalRemainder (k := k) μ hf 1 hb 2)
    (integral_empiricalRemainder μ hf 1 hb) (r := s/4) (by positivity)
  have hV := variance_empiricalRemainder_le (k := k) μ hf 1 hb
  have hRatio : variance (empiricalRemainder (k := k) μ f) (Measure.pi (fun q => μ q.1))/(s/4)^2 ≤
      16/((k : ℝ)^2*s^2) := by
    calc
      _ ≤ ((1 : ℝ)/(k : ℝ)^2)/(s/4)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        simpa only [NNReal.coe_one,one_pow] using hV
      _ = _ := by field_simp; ring
  simpa only [neg_div] using h.trans (min_le_min le_rfl hRatio)

end ProphetSecretary.Statistics.Hoeffding
