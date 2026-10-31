import ProphetSecretary.Limiting.GeneratingFunctional

/-!
# Intensity form of the actual generating functional

Writing the exponent as an intensity integral removes the normalization of
the mark law and also covers zero total intensity. This form is suited to
finite superposition and restriction of the anonymous counting measure.
-/

open MeasureTheory Set Complex
open scoped NNReal ENNReal

namespace ProphetSecretary.Limiting

lemma generating_functional_intensity (μ : FiniteMeasure ℝ) (g : Point → ℂ)
    (hg : Measurable g) (hb : ∀ p, ‖g p‖ ≤ 1) :
    (∫ ω, pointProd g ω ∂configurationLaw μ) =
      Complex.exp (∫ p, (g p-1) ∂intensity μ) := by
  have hi : Integrable g (pointLaw μ) :=
    Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)
  have hm : ((μ : Measure ℝ) univ).toReal = (μ.mass : ℝ) := by
    rw [← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
  rw [generating_functional μ g hg hb,intensity_eq_mass_smul_pointLaw,integral_smul_measure,
    integral_sub hi (integrable_const (1 : ℂ)),integral_const]
  simp [Complex.real_smul,hm]

end ProphetSecretary.Limiting
