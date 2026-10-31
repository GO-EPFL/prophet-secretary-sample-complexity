import ProphetSecretary.Probability.WeakAlmostContinuousIntegral
import ProphetSecretary.Probability.CenteredBoundedScore

/-!
# Score-weighted payoff convergence for one individual observable

The observable defining the score is fixed and bounded continuous. Its
centering changes with the marginal law. A bounded payoff continuous almost
everywhere for the limiting law still has convergent score-weighted
expectations. This is the analytic individual-score transfer step; actual
configuration convergence and payoff continuity must be proved separately.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology

namespace ProphetSecretary.Probability

variable {Ω Γ : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- Product of the fixed observable and an almost continuous bounded payoff. -/
theorem centeredBoundedScore_payoff_tendsto [HasOuterApproxClosed Ω]
    {l : Filter Γ} [l.IsCountablyGenerated] {μs : Γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hweak : Tendsto μs l (𝓝 μ)) (f : Ω →ᵇ ℝ) {g : Ω → ℝ} (hg : Measurable g)
    {H : ℝ} (hbound : ∀ x, |g x| ≤ H) (hc : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt g x) :
    Tendsto (fun m => ∫ x, centeredBoundedScore (μs m : Measure Ω) f x * g x ∂(μs m : Measure Ω)) l
      (𝓝 (∫ x, centeredBoundedScore (μ : Measure Ω) f x * g x ∂(μ : Measure Ω))) := by
  have hfgm : Measurable (fun x => f x * g x) := f.continuous.measurable.mul hg
  have hfgBound (x : Ω) : |f x * g x| ≤ ‖f‖ * H := by
    rw [abs_mul]
    have hf := f.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at hf
    exact mul_le_mul hf (hbound x) (abs_nonneg _) (norm_nonneg f)
  have hfgc : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt (fun y => f y * g y) x :=
    hc.mono fun _ hx => f.continuous.continuousAt.mul hx
  have hfg := integral_tendsto_of_weak_ae_continuous_bounded hweak
    hfgm hfgBound hfgc
  have hgv := integral_tendsto_of_weak_ae_continuous_bounded hweak hg hbound hc
  have hfv := centeredScore_mean_tendsto hweak f
  have hgI (P : ProbabilityMeasure Ω) : Integrable g (P : Measure Ω) := by
    apply Integrable.of_bound hg.aestronglyMeasurable H
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x
  have hfgI (P : ProbabilityMeasure Ω) : Integrable (fun x => f x * g x) (P : Measure Ω) := by
    apply Integrable.of_bound hfgm.aestronglyMeasurable (‖f‖ * H)
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfgBound x
  have heq (P : ProbabilityMeasure Ω) :
      (∫ x, centeredBoundedScore (P : Measure Ω) f x * g x ∂(P : Measure Ω)) =
      ((∫ x, f x * g x ∂(P : Measure Ω)) -
        (∫ x, f x ∂(P : Measure Ω)) * (∫ x, g x ∂(P : Measure Ω))) / boundedScoreScale f := by
    have hfun : (fun x => centeredBoundedScore (P : Measure Ω) f x * g x) =
        fun x => (f x * g x - (∫ y, f y ∂(P : Measure Ω)) * g x) / boundedScoreScale f := by
      funext x
      unfold centeredBoundedScore centeredRangeScore
      ring
    rw [hfun, integral_div,
      integral_sub (hfgI P) ((hgI P).const_mul _), integral_const_mul]
  have h := (hfg.sub (hfv.mul hgv)).div_const (boundedScoreScale f)
  simpa only [heq] using h

end ProphetSecretary.Probability
