import ProphetSecretary.Analysis.ContinuityLevelBoundary
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak convergence of level probabilities for almost continuous payoffs

At a level carrying no mass under the limiting payoff law, its threshold
event has null boundary when the payoff is continuous almost everywhere.
The actual continuity-set theorem then gives convergence of its probabilities.
This is the level-set step of bounded score-payoff transfer.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Probability

variable {Ω Γ : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

omit [OpensMeasurableSpace Ω] in
lemma level_frontier_null_of_continuousAt_ae (μ : Measure Ω) {f : Ω → ℝ} {a : ℝ}
    (hc : ∀ᵐ x ∂μ, ContinuousAt f x) (ha : μ {x | f x = a} = 0) :
    μ (frontier {x | a ≤ f x}) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hn := measure_eq_zero_iff_ae_notMem.mp ha
  filter_upwards [hc, hn] with x hcx hnx
  intro hx
  exact hnx (ProphetSecretary.Analysis.levelBoundary_eq_of_continuousAt hcx hx)

/-- The limiting law supplies the continuity/null-level conditions; the
approximating laws may place atoms elsewhere. -/
theorem level_probability_tendsto_of_continuousAt_ae [HasOuterApproxClosed Ω]
    {l : Filter Γ} {μs : Γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hweak : Tendsto μs l (𝓝 μ)) {f : Ω → ℝ} {a : ℝ}
    (hc : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt f x)
    (ha : (μ : Measure Ω) {x | f x = a} = 0) :
    Tendsto (fun m => (μs m : Measure Ω).real {x | a ≤ f x}) l
      (𝓝 ((μ : Measure Ω).real {x | a ≤ f x})) := by
  have hfront := level_frontier_null_of_continuousAt_ae (μ : Measure Ω) hc ha
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hfront
  exact (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure Ω) _)).comp he

end ProphetSecretary.Probability
