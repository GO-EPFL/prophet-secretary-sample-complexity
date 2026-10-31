import ProphetSecretary.Probability.WeakFiniteAlmostContinuousIntegral
import Mathlib.Topology.Algebra.Indicator

/-!
# Weak restriction to a continuity upper band

Bounded continuous tests restricted above a level are almost everywhere
continuous whenever the limiting finite measure has no atom at that level.
This includes a zero limiting measure.
-/
open MeasureTheory Set Filter
open scoped Topology Classical
namespace ProphetSecretary.Probability

theorem finite_upperRestriction_tendsto {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) (b : ℝ) (hAtom : (μ:Measure ℝ) {b}=0) :
    Tendsto (fun m => (μs m).restrict (Ioi b)) atTop (𝓝 (μ.restrict (Ioi b))) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hCont : ∀ᵐ x ∂(μ:Measure ℝ), ContinuousAt ((Ioi b).indicator f) x := by
    have hfront : (μ:Measure ℝ) (frontier (Ioi b))=0 := by rw [frontier_Ioi]; exact hAtom
    exact (measure_eq_zero_iff_ae_notMem.mp hfront).mono (fun x hx => f.continuous.continuousOn.continuousAt_indicator hx)
  have hBound (x : ℝ) : |(Ioi b).indicator f x|≤‖f‖ := by
    by_cases hx : x∈Ioi b
    · simpa only [Set.indicator_of_mem hx,Real.norm_eq_abs] using f.norm_coe_le_norm x
    · rw [Set.indicator_of_notMem hx,abs_zero]
      exact norm_nonneg f
  change Tendsto (fun m => ∫ x, f x ∂(μs m:Measure ℝ).restrict (Ioi b)) atTop
    (𝓝 (∫ x, f x ∂(μ:Measure ℝ).restrict (Ioi b)))
  simp_rw [← integral_indicator measurableSet_Ioi]
  exact finite_integral_tendsto_of_weak_ae_continuous_bounded hμ
    (f.continuous.measurable.indicator measurableSet_Ioi) hBound hCont
end ProphetSecretary.Probability
