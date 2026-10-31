import ProphetSecretary.Probability.CenteredValueScore
import ProphetSecretary.Limiting.FiniteMeasureSubsequence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bounded value-weighted offer measures

Weighting a cap-supported marginal by its value produces a finite measure with
mass equal to its first moment. The clipping extension defines this weighting
on all probability laws, and makes its weak continuity an actual bounded-
continuous test-function statement. These are measure data for extraction,
not assertions about policies or scalar-value convergence.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

noncomputable def valueWeightedLaw (p : ProbabilityMeasure ℝ) (H : ℝ≥0) : FiniteMeasure ℝ := by
  refine ⟨(p : Measure ℝ).withDensity (fun x => ENNReal.ofReal (boundedOfferValue H x)),?_⟩
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal ((boundedOfferValue H).integrable (p : Measure ℝ))
    (Eventually.of_forall fun x => (boundedOfferValue_mem_range H x).1)]
  exact ENNReal.ofReal_ne_top

lemma valueWeightedLaw_mass (p : ProbabilityMeasure ℝ) (H : ℝ≥0) :
    ((valueWeightedLaw p H).mass : ℝ) = ∫ x, boundedOfferValue H x ∂(p : Measure ℝ) := by
  have hm : ((valueWeightedLaw p H).mass : ℝ) = ((valueWeightedLaw p H : Measure ℝ) Set.univ).toReal := by
    simpa only [ENNReal.coe_toReal] using congrArg ENNReal.toReal (FiniteMeasure.ennreal_mass (μ := valueWeightedLaw p H))
  rw [hm]
  change ((p : Measure ℝ).withDensity (fun x => ENNReal.ofReal (boundedOfferValue H x)) Set.univ).toReal = _
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (boundedOfferValue_mem_range H x).1)
    (boundedOfferValue H).continuous.measurable.aestronglyMeasurable).symm

lemma valueWeightedLaw_mass_eq_mean (p : ProbabilityMeasure ℝ) (H : ℝ≥0)
    (hcap : ∀ᵐ x ∂(p : Measure ℝ), x ∈ Icc (0 : ℝ) H) :
    ((valueWeightedLaw p H).mass : ℝ) = ∫ x, x ∂(p : Measure ℝ) := by
  rw [valueWeightedLaw_mass,integral_boundedOfferValue _ hcap]

lemma valueWeightedLaw_supported_interval (p : ProbabilityMeasure ℝ) (H : ℝ≥0)
    (hcap : (p : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    (valueWeightedLaw p H : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 :=
  (withDensity_absolutelyContinuous _ _) hcap

/-- Actual change-of-measure identity; clipping is an extension off the offer
support and agrees with x on the cap interval. -/
lemma valueWeightedLaw_integral (p : ProbabilityMeasure ℝ) (H : ℝ≥0) (f : ℝ → ℝ) :
    (∫ x, f x ∂(valueWeightedLaw p H : Measure ℝ)) =
      ∫ x, boundedOfferValue H x * f x ∂(p : Measure ℝ) := by
  change (∫ x, f x ∂(p : Measure ℝ).withDensity (fun x => ENNReal.ofReal (boundedOfferValue H x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul (boundedOfferValue H).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (boundedOfferValue_mem_range H x).1,smul_eq_mul]

/-- Weak convergence is preserved by the actual value-weighted measures. -/
theorem valueWeightedLaw_tendsto {Γ : Type*} {l : Filter Γ}
    {ps : Γ → ProbabilityMeasure ℝ} {p : ProbabilityMeasure ℝ} (hp : Tendsto ps l (𝓝 p)) (H : ℝ≥0) :
    Tendsto (fun m => valueWeightedLaw (ps m) H) l (𝓝 (valueWeightedLaw p H)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  simp_rw [valueWeightedLaw_integral]
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hp) (boundedOfferValue H * f)

end ProphetSecretary.Limiting
