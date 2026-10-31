import ProphetSecretary.Probability.WeakCenteredScore
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Fixed scaling of a general continuous bounded individual score

The scale 2(‖f‖+1) is positive and independent of the marginal law. Thus
centering the same observable under a weakly convergent sequence gives
continuous centered scores bounded by one and converging uniformly. This is
the general individual-variable construction in `updual:scorelift`.
-/

open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology

namespace ProphetSecretary.Probability

variable {Ω Γ : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

noncomputable def boundedScoreScale (f : Ω →ᵇ ℝ) : ℝ := 2 * (‖f‖ + 1)

omit [MeasurableSpace Ω] [OpensMeasurableSpace Ω] in
lemma boundedScoreScale_positive (f : Ω →ᵇ ℝ) : 0 < boundedScoreScale f := by
  unfold boundedScoreScale
  positivity

noncomputable def centeredBoundedScore (μ : Measure Ω) (f : Ω →ᵇ ℝ) : Ω → ℝ :=
  centeredRangeScore μ f (boundedScoreScale f)

omit [OpensMeasurableSpace Ω] in
lemma continuous_centeredBoundedScore (μ : Measure Ω) (f : Ω →ᵇ ℝ) :
    Continuous (centeredBoundedScore μ f) :=
  (f.continuous.sub continuous_const).div_const _

lemma integrable_boundedObservable (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω →ᵇ ℝ) : Integrable f μ :=
  Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)

omit [OpensMeasurableSpace Ω] in
lemma centeredBoundedScore_abs_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω →ᵇ ℝ) (x : Ω) : |centeredBoundedScore μ f x| ≤ 1 := by
  have hn := norm_integral_le_of_norm_le_const (μ := μ) (f := f)
    (Eventually.of_forall f.norm_coe_le_norm)
  simp only [probReal_univ, mul_one] at hn
  have hfx := f.norm_coe_le_norm x
  have hdiff := abs_sub (f x) (∫ y, f y ∂μ)
  rw [Real.norm_eq_abs] at hn hfx
  unfold centeredBoundedScore centeredRangeScore
  rw [abs_div, abs_of_pos (boundedScoreScale_positive f)]
  apply (div_le_one (boundedScoreScale_positive f)).mpr
  unfold boundedScoreScale
  linarith only [hn, hfx, hdiff]

lemma centeredBoundedScore_mean (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω →ᵇ ℝ) :
    (∫ x, centeredBoundedScore μ f x ∂μ) = 0 := by
  unfold centeredBoundedScore centeredRangeScore
  rw [integral_div, integral_sub (integrable_boundedObservable μ f) (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul, sub_self, zero_div]

lemma centeredBoundedScore_tilt_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω →ᵇ ℝ) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    IsProbabilityMeasure (tiltLaw μ (centeredBoundedScore μ f) θ) :=
  tiltLaw_probability (continuous_centeredBoundedScore μ f).measurable
    (Eventually.of_forall (centeredBoundedScore_abs_le_one μ f)) (centeredBoundedScore_mean μ f) hθ

lemma centeredBoundedScore_secondMoment_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω →ᵇ ℝ) :
    (∫ x, centeredBoundedScore μ f x ^ 2 ∂μ) ≤ 1 := by
  have hi := integrable_pow_of_bound (μ := μ) (continuous_centeredBoundedScore μ f).measurable zero_le_one
    (Eventually.of_forall (centeredBoundedScore_abs_le_one μ f)) 2
  have hp (x : Ω) : centeredBoundedScore μ f x ^ 2 ≤ 1 := by
    have hx := abs_le.mp (centeredBoundedScore_abs_le_one μ f x)
    nlinarith only [hx.1, hx.2]
  have h := integral_mono hi (integrable_const (1 : ℝ)) hp
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Centering depends on the law, but its scale is fixed before choosing it. -/
theorem centeredBoundedScore_tendstoUniformly {l : Filter Γ} {μs : Γ → ProbabilityMeasure Ω}
    {μ : ProbabilityMeasure Ω} (hμ : Tendsto μs l (𝓝 μ)) (f : Ω →ᵇ ℝ) :
    TendstoUniformly (fun m x => centeredBoundedScore (μs m : Measure Ω) f x)
      (centeredBoundedScore (μ : Measure Ω) f) l :=
  centeredScore_tendstoUniformly hμ f (boundedScoreScale f)

end ProphetSecretary.Probability
