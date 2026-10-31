import ProphetSecretary.Limiting.RareMarginalNormalization

/-!
# Absorbing mapped zero marks into the finite no-offer atom

For a nonnegative finite measure, removing its atom at zero does not change
the fixed-q rare offer law: that mass is absorbed into the existing δ₀ term.
This is a finite probability-law identity, not the introduction or removal of
observed zero marks in a Poisson process.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

lemma positiveRestriction_mass_le (μ : FiniteMeasure ℝ) : (μ.restrict (Ioi 0)).mass ≤ μ.mass := by
  rw [FiniteMeasure.restrict_mass]
  exact μ.apply_le_mass _

lemma integral_centered_test_positiveRestriction (μ : FiniteMeasure ℝ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x-f 0 ∂(μ.restrict (Ioi 0) : Measure ℝ)) = ∫ x, f x-f 0 ∂(μ : Measure ℝ) := by
  change (∫ x, f x-f 0 ∂(μ : Measure ℝ).restrict (Ioi 0)) = _
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [hμ] with x hx
  by_cases hpos : 0 < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hpos)]
  · have he : x = 0 := le_antisymm (not_lt.mp hpos) hx
    subst x
    simp

/-- The actual finite probability law is unchanged by discarding zero mass
from the analytical mark intensity before normalizing positive Poisson marks. -/
theorem rareProbabilityLaw_positiveRestriction (μ : FiniteMeasure ℝ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) :
    rareProbabilityLaw μ q hq hm =
      rareProbabilityLaw (μ.restrict (Ioi 0)) q hq ((positiveRestriction_mass_le μ).trans hm) := by
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding ℝ).injective
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  change (∫ x, f x ∂(rareProbabilityLaw μ q hq hm : Measure ℝ)) =
    ∫ x, f x ∂(rareProbabilityLaw (μ.restrict (Ioi 0)) q hq ((positiveRestriction_mass_le μ).trans hm) : Measure ℝ)
  rw [integral_rareProbabilityLaw,integral_rareProbabilityLaw]
  have hc := integral_centered_test_positiveRestriction μ hμ f
  rw [integral_sub (f.integrable (μ.restrict (Ioi 0) : Measure ℝ)) (integrable_const _),
    integral_sub (f.integrable (μ : Measure ℝ)) (integrable_const _),integral_const,integral_const] at hc
  change (∫ x, f x ∂(μ.restrict (Ioi 0) : Measure ℝ))-((μ.restrict (Ioi 0)).mass : ℝ)*f 0 =
    (∫ x, f x ∂(μ : Measure ℝ))-(μ.mass : ℝ)*f 0 at hc
  rw [hc]

end ProphetSecretary.Limiting
