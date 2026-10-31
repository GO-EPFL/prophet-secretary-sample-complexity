import ProphetSecretary.Reach.IndependentReachBounds

open MeasureTheory Set

namespace ProphetSecretary.Reach

/-- Almost-sure version of the strict quadratic analytic comparison. Only
residual outcomes of positive probability matter. Slice integrability follows
from joint integrability by Fubini, rather than being an extra assumption.

Here `a` is a conditional selection density and `σ` the pending execution's
duration. The pathwise gap inequality is supplied by monotonicity of the
policy's thresholds. -/
theorem quadratic_gap_product_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {σ : Ω → ℝ} {τ a : Ω × ℝ → ℝ}
    (hσ01 : ∀ᵐ ω ∂μ, σ ω ∈ Icc (0 : ℝ) 1)
    (hσ : Integrable σ μ)
    (ha : Integrable a (μ.prod (volume.restrict (Icc 0 1))))
    (hτ : Integrable τ (μ.prod (volume.restrict (Icc 0 1))))
    (hW : Integrable (fun z ↦ (σ z.1 - z.2) * a z)
      (μ.prod (volume.restrict (Icc 0 1))))
    (ha01 : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, a (ω, t) ∈ Icc (0 : ℝ) 1)
    (hsupport : ∀ᵐ ω ∂μ, ∀ t ∈ Ioo (σ ω) 1, a (ω, t) = 0)
    (hgap : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1,
      (σ ω - t) * a (ω, t) ≤ σ ω - τ (ω, t)) :
    (∫ z, a z ∂μ.prod (volume.restrict (Icc 0 1))) ^ 2 / 2 ≤
      (∫ ω, σ ω ∂μ) - ∫ z, τ z ∂μ.prod (volume.restrict (Icc 0 1)) := by
  let A : Ω → ℝ := fun ω ↦ ∫ t in (0 : ℝ)..1, a (ω, t)
  let B : Ω → ℝ := fun ω ↦ ∫ t in (0 : ℝ)..1, (σ ω - t) * a (ω, t)
  let T : Ω → ℝ := fun ω ↦ ∫ t in (0 : ℝ)..1, τ (ω, t)
  have haI : ∀ᵐ ω ∂μ, IntervalIntegrable (fun t ↦ a (ω, t)) volume 0 1 := by
    filter_upwards [ha.prod_right_ae] with ω hω
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).mpr hω
  have hτI : ∀ᵐ ω ∂μ, IntervalIntegrable (fun t ↦ τ (ω, t)) volume 0 1 := by
    filter_upwards [hτ.prod_right_ae] with ω hω
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).mpr hω
  have hAI : Integrable A μ := by
    simpa only [A, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using ha.integral_prod_left
  have hBI : Integrable B μ := by
    simpa only [B, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using hW.integral_prod_left
  have hTI : Integrable T μ := by
    simpa only [T, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc] using hτ.integral_prod_left
  have hA01 : ∀ᵐ ω ∂μ, A ω ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [haI, ha01] with ω hI hab
    constructor
    · exact intervalIntegral.integral_nonneg zero_le_one (fun t ht ↦ (hab t ht).1)
    · have h := intervalIntegral.integral_mono_on zero_le_one hI intervalIntegrable_const
        (fun t ht ↦ (hab t ht).2)
      simpa only [A, intervalIntegral.integral_const, sub_zero, one_smul] using h
  have hA2 : Integrable (fun ω ↦ A ω ^ 2) μ := by
    apply integrable_of_ae_unit μ (hAI.aestronglyMeasurable.pow 2)
    filter_upwards [hA01] with ω hω
    change A ω ^ 2 ∈ Icc (0 : ℝ) 1
    exact ⟨sq_nonneg _, by nlinarith [hω.1, hω.2]⟩
  have hmin : ∀ᵐ ω ∂μ, A ω ^ 2 / 2 ≤ B ω := by
    filter_upwards [hσ01, haI, ha01, hsupport] with ω hs hI hab hz
    have hshortI : IntervalIntegrable (fun t ↦ a (ω, t)) volume 0 (σ ω) :=
      hI.mono_set (by simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), uIcc_of_le hs.1] using Icc_subset_Icc le_rfl hs.2)
    have heA := integral_until_eq_full hs.1 hs.2 hI hz
    have hWI : IntervalIntegrable (fun t ↦ (σ ω - t) * a (ω, t)) volume 0 1 :=
      hI.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
    have heB := integral_until_eq_full hs.1 hs.2 hWI (fun t ht ↦ by rw [hz t ht, mul_zero])
    have h := selection_duration_integral hs.1 hshortI
      (fun t ht ↦ (hab t ⟨ht.1, ht.2.trans hs.2⟩).1)
      (fun t ht ↦ (hab t ⟨ht.1, ht.2.trans hs.2⟩).2)
    simpa only [heA, heB, A, B] using h
  have hquad : (∫ ω, A ω ∂μ) ^ 2 / 2 ≤ ∫ ω, B ω ∂μ := by
    have hJ := sq_integral_le_integral_sq μ hAI hA2
    have hm := integral_mono_ae (hA2.div_const 2) hBI hmin
    rw [integral_div] at hm
    exact (div_le_div_of_nonneg_right hJ (by norm_num)).trans hm
  have hinner : ∀ᵐ ω ∂μ, B ω ≤ σ ω - T ω := by
    filter_upwards [haI, hτI, hgap] with ω hI hτi hg
    have hWI : IntervalIntegrable (fun t ↦ (σ ω - t) * a (ω, t)) volume 0 1 :=
      hI.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
    have h := intervalIntegral.integral_mono_on zero_le_one hWI
      (intervalIntegrable_const.sub hτi) hg
    simpa only [B, T, intervalIntegral.integral_sub intervalIntegrable_const hτi,
      intervalIntegral.integral_const, sub_zero, one_smul] using h
  have hbound := integral_mono_ae hBI (hσ.sub hTI) hinner
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub (f := σ) (g := T) hσ hTI] at hbound
  have hfinish := hquad.trans hbound
  simp only [A, T, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at hfinish
  simpa only [integral_prod _ ha, integral_prod _ hτ] using hfinish

end ProphetSecretary.Reach
