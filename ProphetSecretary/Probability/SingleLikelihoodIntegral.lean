import ProphetSecretary.Probability.LikelihoodTilt

/-!
# Exact fixed-payoff identity for one centered likelihood direction

The payoff remains fixed while the measure changes. No optimization or
parameter-dependent choice of payoff is differentiated here.
-/

open MeasureTheory Filter

namespace ProphetSecretary.Probability

lemma integral_tiltLaw_eq_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s f : Ω → ℝ} (hs : Measurable s) (hBound : ∀ᵐ x ∂μ, |s x| ≤ 1)
    (hf : Integrable f μ) {θ : ℝ} (hθ : |θ| ≤ 1/4) :
    (∫ x, f x ∂tiltLaw μ s θ)=(∫ x, f x ∂μ)+θ*(∫ x, f x*s x ∂μ) := by
  have hNonnegative : ∀ᵐ x ∂μ, 0 ≤ tiltFactor s θ x := hBound.mono (fun x hx =>
    (show (0 : ℝ) ≤ 3/4 by norm_num).trans (tiltFactor_bounds hθ hx).1)
  have hProduct : Integrable (fun x => f x*s x) μ := hf.mul_bdd hs.aestronglyMeasurable
    (hBound.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx))
  rw [integral_tiltLaw hs hNonnegative]
  calc
    _ = ∫ x, f x+θ*(f x*s x) ∂μ := integral_congr_ae (Eventually.of_forall (fun x => by
      simp only [tiltFactor]
      ring))
    _ = _ := by rw [integral_add hf (hProduct.const_mul θ),integral_const_mul]

end ProphetSecretary.Probability
