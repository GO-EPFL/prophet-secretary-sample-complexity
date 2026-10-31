import ProphetSecretary.Probability.CenteredRangeScore
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Weak convergence of centering constants and individual scores

A fixed bounded continuous observable has convergent means under weakly
convergent laws. Consequently its centered, fixed-scale scores converge
uniformly over the whole value domain. This is the individual-score centering
step in `updual:scorelift`; it is stronger than pointwise score convergence.
-/

open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology

namespace ProphetSecretary.Probability

variable {Ω Γ : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

lemma centeredScore_mean_tendsto {l : Filter Γ} {μs : Γ → ProbabilityMeasure Ω}
    {μ : ProbabilityMeasure Ω} (hμ : Tendsto μs l (𝓝 μ)) (f : Ω →ᵇ ℝ) :
    Tendsto (fun m => ∫ x, f x ∂(μs m : Measure Ω)) l (𝓝 (∫ x, f x ∂(μ : Measure Ω))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f

/-- The scaling R is fixed across the sequence, as required in the manuscript. -/
theorem centeredScore_tendstoUniformly {l : Filter Γ} {μs : Γ → ProbabilityMeasure Ω}
    {μ : ProbabilityMeasure Ω} (hμ : Tendsto μs l (𝓝 μ)) (f : Ω →ᵇ ℝ) (R : ℝ) :
    TendstoUniformly (fun m x => centeredRangeScore (μs m : Measure Ω) f R x)
      (centeredRangeScore (μ : Measure Ω) f R) l := by
  have hc := centeredScore_mean_tendsto hμ f
  have he : Tendsto (fun m => |(∫ x, f x ∂(μs m : Measure Ω)) - ∫ x, f x ∂(μ : Measure Ω)| / |R|)
      l (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_div] using
      ((hc.sub_const (∫ x, f x ∂(μ : Measure Ω))).abs.div_const |R|)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(tendsto_order.mp he).2 ε hε] with m hm
  intro x
  rw [dist_comm, Real.dist_eq, centeredRangeScore_abs_difference]
  exact hm

end ProphetSecretary.Probability
