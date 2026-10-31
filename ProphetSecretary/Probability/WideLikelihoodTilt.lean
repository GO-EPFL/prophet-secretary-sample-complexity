import ProphetSecretary.Probability.PolicyLikelihood

/-!
# A wider probability-law neighborhood for likelihood calculus

The manuscript's quarter interval sits strictly inside this half interval.
The density stays at least one half, so re-centering at every manuscript
parameter is legitimate without using a discontinuous total extension.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

lemma tiltLaw_probability_half {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) (hm : ∫ x, h x ∂μ = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : IsProbabilityMeasure (tiltLaw μ h θ) := by
  have hi : Integrable h μ := Integrable.of_bound hh.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hb)
  apply probability_withDensity_ofReal ((integrable_const 1).add (hi.const_mul θ))
  · exact hb.mono (fun x hx ↦ (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (tiltFactor_half_bounds hθ hx).1)
  · change (∫ x, 1 + θ * h x ∂μ) = 1
    rw [integral_add (integrable_const 1) (hi.const_mul θ), integral_const_mul, hm]
    simp

lemma tiltedScore_half_centered {μ : Measure ℝ} {h : ℝ → ℝ} (hh : Measurable h)
    (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) (hm : ∫ x, h x ∂μ = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : ∫ x, tiltedScore h θ x ∂tiltLaw μ h θ = 0 := by
  have h0 : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x := hb.mono (fun x hx ↦
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (tiltFactor_half_bounds hθ hx).1)
  rw [integral_tiltLaw hh h0]
  calc
    _ = ∫ x, h x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hb] with x hx
      have hp : 0 < tiltFactor h θ x := by
        have hlow := (tiltFactor_half_bounds hθ hx).1
        change 0 < 1 + θ * h x
        linarith
      unfold tiltedScore
      field_simp
    _ = 0 := hm

lemma tiltedScore_half_secondMoment_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    (∫ x, tiltedScore h θ x ^ 2 ∂tiltLaw μ h θ) ≤ (2) * ∫ x, h x ^ 2 ∂μ := by
  have h0 : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x :=
    hb.mono fun x hx => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (tiltFactor_half_bounds hθ hx).1
  have hi2 : Integrable (fun x => h x ^ 2) μ := integrable_pow_of_bound hh zero_le_one hb 2
  have hdom : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x * tiltedScore h θ x ^ 2 ∧
      tiltFactor h θ x * tiltedScore h θ x ^ 2 ≤ (2) * h x ^ 2 := by
    filter_upwards [hb] with x hx
    have hlow : (1 / 2 : ℝ) ≤ tiltFactor h θ x := (tiltFactor_half_bounds hθ hx).1
    have hp : 0 < tiltFactor h θ x := by linarith
    refine ⟨mul_nonneg hp.le (sq_nonneg _), ?_⟩
    have he : tiltFactor h θ x * tiltedScore h θ x ^ 2 = h x ^ 2 / tiltFactor h θ x := by
      unfold tiltedScore
      field_simp
    rw [he]
    apply (div_le_iff₀ hp).mpr
    have hmul := mul_nonneg (sq_nonneg (h x)) (sub_nonneg.mpr hlow)
    nlinarith
  have hiL : Integrable (fun x => tiltFactor h θ x * tiltedScore h θ x ^ 2) μ := by
    apply (hi2.const_mul (2)).mono' ((measurable_tiltFactor hh θ).mul (measurable_tiltedScore hh θ |>.pow_const 2)).aestronglyMeasurable
    exact hdom.mono fun x hx => by simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  rw [integral_tiltLaw hh h0]
  exact (integral_mono_ae hiL (hi2.const_mul _) (hdom.mono fun _ hx => hx.2)).trans_eq (integral_const_mul _ _)

end ProphetSecretary.Probability

namespace ProphetSecretary.Model.Instance

open ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def likelihoodWideTilt (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ) (hθ : |θ| ≤ 1 / 2) : Instance n where
  law i := tiltLaw (P.law i) (h i) θ
  probability i := tiltLaw_probability_half (hh i) (hb i) (hm i) hθ
  nonnegative i := (tiltLaw_absolutelyContinuous (P.law i) (h i) θ).ae_le (P.nonnegative i)

lemma likelihoodWideTilt_eq_quarter (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ) (hθ : |θ| ≤ 1 / 4) :
    P.likelihoodWideTilt h hh hb hm θ (hθ.trans (by norm_num)) = P.likelihoodTilt h hh hb hm θ hθ := by
  rfl

lemma likelihoodWideTilt_bounded (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ) (hθ : |θ| ≤ 1 / 2)
    {H : ℝ} (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ i, ∀ᵐ x ∂(P.likelihoodWideTilt h hh hb hm θ hθ).law i, x ≤ H :=
  fun i ↦ (tiltLaw_absolutelyContinuous (P.law i) (h i) θ).ae_le (hbound i)

end ProphetSecretary.Model.Instance
