import ProphetSecretary.Limiting.Campbell
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Complex.Norm

/-!
# Generating functional of the finite marked process

The actual Poisson mixture and conditional iid array law give its generating
functional. This identity is the basis for deriving thinning and independent
increments, rather than including those laws as unproved structure fields.
-/

open MeasureTheory ProbabilityTheory Set Complex
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

noncomputable def pointProd (g : Point → ℂ) (ω : Configuration) : ℂ :=
  ∏ j : Fin ω.1, g (ω.2 j)

lemma measurable_pointProd {g : Point → ℂ} (hg : Measurable g) : Measurable (pointProd g) := by
  apply measurable_of_configuration_branches
  intro N
  change Measurable (fun v : Fin N → Point => ∏ j : Fin N, g (v j))
  exact Finset.measurable_fun_prod _ (fun j _ => hg.comp (measurable_pi_apply j))

lemma pointProd_norm_le_one (g : Point → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1) (ω : Configuration) :
    ‖pointProd g ω‖ ≤ 1 := by
  unfold pointProd
  rw [Complex.norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hg (ω.2 j))

lemma integrable_pointProd (μ : FiniteMeasure ℝ) (g : Point → ℂ)
    (hg : Measurable g) (hb : ∀ p, ‖g p‖ ≤ 1) : Integrable (pointProd g) (configurationLaw μ) :=
  Integrable.of_bound (measurable_pointProd hg).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (pointProd_norm_le_one g hb))

lemma integral_pointProd_fiber (μ : FiniteMeasure ℝ) (N : ℕ) (g : Point → ℂ) (hg : Measurable g) :
    (∫ ω, pointProd g ω ∂fiberLaw μ N) = (∫ p, g p ∂pointLaw μ) ^ N := by
  rw [fiberLaw, integral_map (measurable_configuration_mk N).aemeasurable (measurable_pointProd hg).aestronglyMeasurable]
  change (∫ v : Fin N → Point, ∏ j : Fin N, g (v j) ∂arrayLaw μ N) = _
  rw [arrayLaw, integral_fintype_prod_eq_prod]
  simp

lemma poisson_complex_generating (r : ℝ≥0) (z : ℂ) :
    (∑' N : ℕ, (poissonWeight r N : ℂ) * z ^ N) =
      Complex.exp (((r : ℝ) : ℂ) * (z - 1)) := by
  calc
    _ = ∑' N : ℕ, (Real.exp (-(r : ℝ)) : ℂ) * ((((r : ℝ) : ℂ) * z) ^ N / (N.factorial : ℂ)) := by
      congr 1
      funext N
      unfold poissonWeight
      push_cast
      rw [mul_pow]
      ring
    _ = (Real.exp (-(r : ℝ)) : ℂ) * ∑' N : ℕ, ((((r : ℝ) : ℂ) * z) ^ N / (N.factorial : ℂ)) := tsum_mul_left
    _ = (Real.exp (-(r : ℝ)) : ℂ) * Complex.exp (((r : ℝ) : ℂ) * z) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp (((r : ℝ) : ℂ) * z)).tsum_eq, ← Complex.exp_eq_exp_ℂ]
    _ = _ := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- Generating functional of the constructed actual finite point configuration.
Only actual points appear in the product, including actual points after stopping. -/
lemma generating_functional (μ : FiniteMeasure ℝ) (g : Point → ℂ)
    (hg : Measurable g) (hb : ∀ p, ‖g p‖ ≤ 1) :
    (∫ ω, pointProd g ω ∂configurationLaw μ) =
      Complex.exp (((μ.mass : ℝ) : ℂ) * ((∫ p, g p ∂pointLaw μ) - 1)) := by
  have hi := integrable_pointProd μ g hg hb
  have hw (N : ℕ) : 0 ≤ poissonWeight μ.mass N := by unfold poissonWeight; positivity
  rw [configurationLaw, integral_sum_measure hi]
  simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (hw _), integral_pointProd_fiber μ _ g hg, Complex.real_smul]
  exact poisson_complex_generating μ.mass _

end ProphetSecretary.Limiting
