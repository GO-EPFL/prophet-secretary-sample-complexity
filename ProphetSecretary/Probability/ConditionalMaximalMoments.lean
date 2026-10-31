import ProphetSecretary.Probability.MartingaleMoments
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Finite maximal moments of actual conditional expectations

The sampled conditional expectations form the martingale supplied by the tower
property. Finite Doob estimates and conditional Jensen give universal second
and sixth maximal moments, independent of the sample-time grid and a bound
used only for integrability.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Probability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma integral_condExp_evenPow_le {f : Ω → ℝ} {m : MeasurableSpace Ω} {p : ℕ}
    (hp : p = 2 ∨ p = 6) (hf : Integrable (fun ω => ‖f ω‖ ^ p) μ) :
    (∫ ω, μ[f | m] ω ^ p ∂μ) ≤ ∫ ω, ‖f ω‖ ^ p ∂μ := by
  have hj := integral_norm_condExp_rpow_le (μ := μ) (m := m) (f := f) (p := (p : ℝ))
    (by rcases hp with rfl | rfl <;> norm_num) (by simpa only [Real.rpow_natCast] using hf)
  rcases hp with rfl | rfl
  · simpa only [Real.rpow_natCast, Real.norm_eq_abs, sq_abs] using hj
  · simpa only [Real.rpow_natCast, Real.norm_eq_abs, show (6 : ℕ) = 2 * 3 from rfl, pow_mul, sq_abs] using hj

omit [IsProbabilityMeasure μ] in
lemma condExp_abs_bounded {f : Ω → ℝ} {m : MeasurableSpace Ω} {D : ℝ}
    (hD : 0 ≤ D) (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D) :
    ∀ᵐ ω ∂μ, |μ[f | m] ω| ≤ D := by
  filter_upwards [norm_condExp_le (μ := μ) (m := m) f,
    condExp_le_nonneg_const (μ := μ) (m := m) hD hf] with ω hnorm hbound
  have hn : |μ[f | m] ω| ≤ μ[(fun x => ‖f x‖) | m] ω := by
    simpa only [Real.norm_eq_abs] using hnorm
  exact hn.trans hbound

theorem condExp_runningAbsMaximum_secondMoment (ℱ : Filtration ℕ mΩ) (f : Ω → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D)
    (hf : Integrable (fun ω => ‖f ω‖ ^ 2) μ) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => |μ[f | ℱ j] ω|) N ^ 2 ∂μ) ≤
      4 * ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  have hm := martingale_condExp f ℱ μ
  have hmax := martingale_runningAbsMaximum_square_le hm hD (fun j => condExp_abs_bounded μ hD hbound) N
  exact hmax.trans (mul_le_mul_of_nonneg_left (integral_condExp_evenPow_le μ (m := ℱ N) (Or.inl rfl) hf) (by norm_num))

theorem condExp_runningAbsMaximum_sixthMoment (ℱ : Filtration ℕ mΩ) (f : Ω → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D)
    (hf : Integrable (fun ω => ‖f ω‖ ^ 6) μ) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => |μ[f | ℱ j] ω|) N ^ 6 ∂μ) ≤
      13 * ∫ ω, ‖f ω‖ ^ 6 ∂μ := by
  have hm := martingale_condExp f ℱ μ
  have hmax := martingale_runningAbsMaximum_sixth_le hm hD (fun j => condExp_abs_bounded μ hD hbound) N
  exact hmax.trans (mul_le_mul_of_nonneg_left (integral_condExp_evenPow_le μ (m := ℱ N) (Or.inr rfl) hf) (by norm_num))

end ProphetSecretary.Probability
