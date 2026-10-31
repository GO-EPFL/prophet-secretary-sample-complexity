import ProphetSecretary.Probability.LowerLimitEnvelope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Weighted moments pass to a limiting envelope

Fatou is applied to nonnegative extended-real products only after proving the
limiting envelope finite almost surely. The multiplier converges under the
actual observation law and need not be independent of any error variable.
Dimension-dependent bounds are used solely to justify real integrability.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem weighted_lowerLimitEnvelope_moment {E W : ℕ → Ω → ℝ} {w : Ω → ℝ}
    (hEm : ∀ m, Measurable (E m)) (hWm : ∀ m, Measurable (W m)) (hwm : Measurable w)
    (hE0 : ∀ m ω, 0 ≤ E m ω) (hW0 : ∀ m ω, 0 ≤ W m ω) (hw0 : ∀ ω, 0 ≤ w ω)
    {D C K : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hEBound : ∀ m, ∀ᵐ ω ∂μ, E m ω ≤ D) (hwBound : ∀ᵐ ω ∂μ, w ω ≤ C)
    (hWlim : ∀ᵐ ω ∂μ, Tendsto (fun m => W m ω) atTop (𝓝 (w ω)))
    {p : ℕ} (hp : 0<p)
    (hInt : ∀ m, Integrable (fun ω => W m ω * E m ω^p) μ)
    (hMoment : ∀ m, (∫ ω, W m ω * E m ω^p ∂μ) ≤ K) :
    Integrable (fun ω => w ω * lowerLimitEnvelope E ω^p) μ ∧
      (∫ ω, w ω * lowerLimitEnvelope E ω^p ∂μ) ≤ K := by
  have hAll : ∀ᵐ ω ∂μ, ∀ m, E m ω ≤ D := ae_all_iff.mpr hEBound
  have hLimBound : ∀ᵐ ω ∂μ, lowerLimitEnvelope E ω ≤ D :=
    hAll.mono fun ω hω => lowerLimitEnvelope_le E ω hD hω
  have hNN : ∀ ω, 0 ≤ w ω * lowerLimitEnvelope E ω^p :=
    fun ω => mul_nonneg (hw0 ω) (pow_nonneg (lowerLimitEnvelope_nonnegative E ω) p)
  have hI : Integrable (fun ω => w ω * lowerLimitEnvelope E ω^p) μ := by
    apply Integrable.of_bound (hwm.mul ((measurable_lowerLimitEnvelope hEm).pow_const p)).aestronglyMeasurable (C*D^p)
    filter_upwards [hwBound,hLimBound] with ω hω hEω
    change ‖w ω * lowerLimitEnvelope E ω^p‖ ≤ C*D^p
    rw [Real.norm_eq_abs,abs_of_nonneg (hNN ω)]
    exact mul_le_mul hω (pow_le_pow_left₀ (lowerLimitEnvelope_nonnegative E ω) hEω p)
      (pow_nonneg (lowerLimitEnvelope_nonnegative E ω) p) hC
  refine ⟨hI,?_⟩
  have hPoint : (fun ω => ENNReal.ofReal (w ω * lowerLimitEnvelope E ω^p)) ≤ᵐ[μ]
      (fun ω => liminf (fun m => ENNReal.ofReal (W m ω * E m ω^p)) atTop) := by
    filter_upwards [hAll,hWlim] with ω hω hlim
    exact weighted_lowerLimitEnvelope_le (fun m => hE0 m ω) (fun m => hW0 m ω) (hw0 ω) hω hlim hp
  have hFatou : (∫⁻ ω, liminf (fun m => ENNReal.ofReal (W m ω * E m ω^p)) atTop ∂μ) ≤
      liminf (fun m => ∫⁻ ω, ENNReal.ofReal (W m ω * E m ω^p) ∂μ) atTop :=
    lintegral_liminf_le (fun m => ENNReal.continuous_ofReal.measurable.comp ((hWm m).mul ((hEm m).pow_const p)))
  have hEach (m : ℕ) : (∫⁻ ω, ENNReal.ofReal (W m ω * E m ω^p) ∂μ) ≤ ENNReal.ofReal K := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt m)
      (Eventually.of_forall fun ω => mul_nonneg (hW0 m ω) (pow_nonneg (hE0 m ω) p))]
    exact ENNReal.ofReal_le_ofReal (hMoment m)
  have hFinal : (∫⁻ ω, ENNReal.ofReal (w ω * lowerLimitEnvelope E ω^p) ∂μ) ≤ ENNReal.ofReal K :=
    (lintegral_mono_ae hPoint).trans (hFatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall hEach)))
  have hR := (ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hNN)).trans_le hFinal
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hR
  rw [ENNReal.toReal_ofReal (integral_nonneg hNN),ENNReal.toReal_ofReal hK] at h
  exact h

end ProphetSecretary.Probability
