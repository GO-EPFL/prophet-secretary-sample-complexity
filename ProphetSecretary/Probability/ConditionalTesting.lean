import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Testing conditional expectation against an observed statistic

The multiplier is genuinely measurable in the observation sigma algebra.
All product integrability is explicit. Pull-out and tower then give the exact
testing identity used in the hypothetical-round posterior argument.
-/

open MeasureTheory
namespace ProphetSecretary.Probability
variable {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integral_observed_mul_condExp {m : MeasurableSpace Ω} (hm : m≤m0)
    {H f : Ω → ℝ} (hH : StronglyMeasurable[m] H) (hf : Integrable f μ)
    (hprod : Integrable (H*f) μ) :
    (∫ ω, H ω*f ω ∂μ)=(∫ ω, H ω*μ[f|m] ω ∂μ) := by
  have hPull := condExp_mul_of_stronglyMeasurable_left (μ:=μ) hH hprod hf
  calc
    _ = ∫ ω, μ[H*f|m] ω ∂μ := (integral_condExp hm).symm
    _ = _ := integral_congr_ae hPull

end ProphetSecretary.Probability
