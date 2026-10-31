import ProphetSecretary.Probability.WeakCenteredScore
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The centered individual-value score

Offers supported in [0,H] use the score (x−EX)/H from `updual:scorelift`.
Clipping outside [0,H] extends this to a globally bounded continuous score.
The extension preserves the actual score almost surely and is compatible
with weak convergence, without any finite-support restriction.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal

namespace ProphetSecretary.Probability

noncomputable def boundedOfferValue (H : ℝ≥0) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (max 0 x) (H : ℝ))
    ((continuous_const.max continuous_id).min continuous_const) H
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_left _ _) H.coe_nonneg)]
      exact min_le_right _ _)

lemma boundedOfferValue_mem_range (H : ℝ≥0) (x : ℝ) : boundedOfferValue H x ∈ Icc (0 : ℝ) H :=
  ⟨le_min (le_max_left _ _) H.coe_nonneg, min_le_right _ _⟩

lemma boundedOfferValue_eq (H : ℝ≥0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) H) : boundedOfferValue H x = x := by
  change min (max 0 x) (H : ℝ) = x
  rw [max_eq_right hx.1, min_eq_left hx.2]

noncomputable def centeredValueScore (μ : Measure ℝ) (H : ℝ≥0) : ℝ → ℝ :=
  centeredRangeScore μ (boundedOfferValue H) H

lemma continuous_centeredValueScore (μ : Measure ℝ) (H : ℝ≥0) : Continuous (centeredValueScore μ H) :=
  ((boundedOfferValue H).continuous.sub continuous_const).div_const H

lemma centeredValueScore_abs_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : 0 < (H : ℝ)) (x : ℝ) : |centeredValueScore μ H x| ≤ 1 :=
  centeredRangeScore_abs_le_one μ (boundedOfferValue H).continuous.measurable hH (boundedOfferValue_mem_range H) x

lemma centeredValueScore_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    (∫ x, centeredValueScore μ H x ∂μ) = 0 :=
  centeredRangeScore_mean μ (boundedOfferValue H).continuous.measurable (boundedOfferValue_mem_range H)

lemma integral_boundedOfferValue (μ : Measure ℝ) {H : ℝ≥0}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) H) :
    (∫ x, boundedOfferValue H x ∂μ) = ∫ x, x ∂μ :=
  integral_congr_ae (hμ.mono fun _ hx => boundedOfferValue_eq H hx)

/-- The globally continuous extension is the manuscript's score on the support. -/
lemma centeredValueScore_eq_on_support (μ : Measure ℝ) {H : ℝ≥0}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) H) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) H) :
    centeredValueScore μ H x = (x - ∫ y, y ∂μ) / (H : ℝ) := by
  unfold centeredValueScore centeredRangeScore
  rw [boundedOfferValue_eq H hx, integral_boundedOfferValue μ hμ]

/-- Weak convergence supplies uniform convergence of these individual scores. -/
theorem centeredValueScore_tendstoUniformly {Γ : Type*} {l : Filter Γ}
    {μs : Γ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : Tendsto μs l (𝓝 μ)) (H : ℝ≥0) :
    TendstoUniformly (fun m x => centeredValueScore (μs m : Measure ℝ) H x)
      (centeredValueScore (μ : Measure ℝ) H) l :=
  centeredScore_tendstoUniformly hμ (boundedOfferValue H) H

end ProphetSecretary.Probability
