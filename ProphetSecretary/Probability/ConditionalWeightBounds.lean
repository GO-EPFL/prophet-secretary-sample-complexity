import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Weighted expectations under a localized conditional bound

An observed nonnegative multiplier may select a critical prefix and multiply
its conditional moment bound. The pull-out and tower identities are the actual
library theorems; boundedness of the multiplier supplies all integrability.
-/

open MeasureTheory Filter

namespace ProphetSecretary.Probability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integral_weighted_condExp_bound {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {H f : Ω → ℝ} (hH : StronglyMeasurable[m] H) (hf : Integrable f μ)
    {D K : ℝ} (_hD : 0 ≤ D) (hHbound : ∀ᵐ ω ∂μ, 0 ≤ H ω ∧ H ω ≤ D)
    (hlocal : ∀ᵐ ω ∂μ, H ω ≠ 0 → μ[f | m] ω ≤ K) :
    (∫ ω, H ω * f ω ∂μ) ≤ K * ∫ ω, H ω ∂μ := by
  have hHg := hH.mono hm
  have hHI : Integrable H μ := by
    apply Integrable.of_bound hHg.aestronglyMeasurable D
    exact hHbound.mono fun ω hω => by simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have hprod : Integrable (H * f) μ := by
    apply (hf.norm.const_mul D).mono' (hHg.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    filter_upwards [hHbound] with ω hω
    change ‖H ω * f ω‖ ≤ D * ‖f ω‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact mul_le_mul_of_nonneg_right hω.2 (norm_nonneg _)
  have hPull := condExp_mul_of_stronglyMeasurable_left (μ := μ) hH hprod hf
  have hCI : Integrable (H * μ[f | m]) μ := integrable_condExp.congr hPull
  have hEq : (∫ ω, H ω * f ω ∂μ) = ∫ ω, H ω * μ[f | m] ω ∂μ := by
    calc
      _ = ∫ ω, μ[H*f | m] ω ∂μ := (integral_condExp hm).symm
      _ = _ := integral_congr_ae hPull
  have hpoint : (fun ω => H ω * μ[f | m] ω) ≤ᵐ[μ] (fun ω => K * H ω) := by
    filter_upwards [hHbound,hlocal] with ω hω hloc
    by_cases hz : H ω = 0
    · simp only [hz,mul_zero,zero_mul,le_refl]
    · have hl := mul_le_mul_of_nonneg_left (hloc hz) hω.1
      simpa only [mul_comm] using hl
  rw [hEq]
  have h := integral_mono_ae hCI (hHI.const_mul K) hpoint
  change (∫ ω, H ω * μ[f | m] ω ∂μ) ≤ (∫ ω, K * H ω ∂μ) at h
  rw [integral_const_mul] at h
  exact h

end ProphetSecretary.Probability
