import ProphetSecretary.Limiting.ContinuousWeightedResidualLimit
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The ordered limit of the retained-prefix weighted residuals

Finite-prefix residuals converge as N tends to infinity to the constructed
positive weighted residual. This is the second limit after first extracting
weak limits for each fixed N; no exchange of the two limits is asserted.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal BigOperators
namespace ProphetSecretary.Limiting

/-- Continuity of the countable retained weighted sum at its finite prefixes,
proved from actual integrability under its dominated finite measure sum. -/
theorem extractedContinuousWeightedResidual_tendsto (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) :
    Tendsto ρ atTop (𝓝 (extractedContinuousWeightedResidual w Q ρ)) := by
  letI := retainedContinuousWeightedMeasure_isFinite w Q ρ hρ
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hsum := hasSum_integral_measure (μ := fun i => (continuousWeightedLaw (Q i) w : Measure ℝ))
    (f.integrable (retainedContinuousWeightedMeasure w Q))
  have hpartial := hsum.summable.tendsto_sum_tsum_nat
  rw [hsum.tsum_eq] at hpartial
  have hprefix (N : ℕ) : (∫ x, f x ∂(ρ N : Measure ℝ)) =
      (∫ x, f x ∂(ρ 0 : Measure ℝ)) - ∑ i ∈ Finset.range N, ∫ x, f x ∂(continuousWeightedLaw (Q i) w : Measure ℝ) := by
    have hp := continuousWeighted_residual_prefix_identity w Q ρ hρ N
    have he := congrArg (fun ν : FiniteMeasure ℝ => ∫ x, f x ∂(ν : Measure ℝ)) hp
    rw [FiniteMeasure.toMeasure_add,
      integral_add_measure (f.integrable (↑(∑ i ∈ Finset.range N, continuousWeightedLaw (Q i) w) : Measure ℝ)) (f.integrable (ρ N : Measure ℝ)),
      FiniteMeasure.toMeasure_sum,integral_finsetSum_measure (fun i _ => f.integrable (continuousWeightedLaw (Q i) w : Measure ℝ))] at he
    linarith only [he]
  have htotal : (∫ x, f x ∂(extractedContinuousWeightedResidual w Q ρ : Measure ℝ)) =
      (∫ x, f x ∂(ρ 0 : Measure ℝ)) - ∫ x, f x ∂retainedContinuousWeightedMeasure w Q := by
    have he := congrArg (fun ν : Measure ℝ => ∫ x, f x ∂ν) (extractedContinuousWeightedResidual_add_retained w Q ρ hρ)
    rw [integral_add_measure (f.integrable (extractedContinuousWeightedResidual w Q ρ : Measure ℝ))
      (f.integrable (retainedContinuousWeightedMeasure w Q))] at he
    linarith only [he]
  have ht : Tendsto (fun N => (∫ x, f x ∂(ρ 0 : Measure ℝ)) -
      ∑ i ∈ Finset.range N, ∫ x, f x ∂(continuousWeightedLaw (Q i) w : Measure ℝ)) atTop
      (𝓝 ((∫ x, f x ∂(ρ 0 : Measure ℝ)) - ∫ x, f x ∂retainedContinuousWeightedMeasure w Q)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ x, f x ∂(ρ 0 : Measure ℝ)) atTop
      (𝓝 (∫ x, f x ∂(ρ 0 : Measure ℝ)))).sub hpartial
  have heq : (fun N => (∫ x, f x ∂(ρ N : Measure ℝ))) =
      fun N => (∫ x, f x ∂(ρ 0 : Measure ℝ)) - ∑ i ∈ Finset.range N, ∫ x, f x ∂(continuousWeightedLaw (Q i) w : Measure ℝ) :=
    funext hprefix
  rw [← heq,← htotal] at ht
  exact ht

end ProphetSecretary.Limiting
