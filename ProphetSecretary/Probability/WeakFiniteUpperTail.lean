import ProphetSecretary.Probability.WeakFiniteAlmostContinuousIntegral
import Mathlib.Topology.Algebra.Indicator

/-!
# Positive-band mass under weak finite-measure convergence

A strict upper-band indicator is discontinuous only at its lower endpoint.
A null atom there suffices, including when the limiting measure is zero.
-/
open MeasureTheory Set Filter
open scoped Topology Classical
namespace ProphetSecretary.Probability

theorem finite_upperTail_real_tendsto {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) (b : ℝ) (hAtom : (μ:Measure ℝ) {b}=0) :
    Tendsto (fun m => (μs m:Measure ℝ).real (Ioi b)) atTop (𝓝 ((μ:Measure ℝ).real (Ioi b))) := by
  have hCont : ∀ᵐ x ∂(μ:Measure ℝ), ContinuousAt ((Ioi b).indicator (fun _ : ℝ => (1:ℝ))) x := by
    have hfront : (μ:Measure ℝ) (frontier (Ioi b))=0 := by rw [frontier_Ioi]; exact hAtom
    exact (measure_eq_zero_iff_ae_notMem.mp hfront).mono (fun x hx =>
      (continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).continuousOn.continuousAt_indicator hx)
  have hBound (x : ℝ) : |(Ioi b).indicator (fun _ : ℝ => (1:ℝ)) x|≤1 := by
    by_cases hx : x∈Ioi b <;> simp [hx]
  have h := finite_integral_tendsto_of_weak_ae_continuous_bounded hμ
    (measurable_const.indicator measurableSet_Ioi) hBound hCont
  have he (κ : FiniteMeasure ℝ) :
      (∫ x, (Ioi b).indicator (fun _ : ℝ => (1:ℝ)) x ∂(κ:Measure ℝ))= (κ:Measure ℝ).real (Ioi b) := by
    rw [integral_indicator_const _ measurableSet_Ioi,smul_eq_mul,mul_one]
  simpa only [he] using h
end ProphetSecretary.Probability
