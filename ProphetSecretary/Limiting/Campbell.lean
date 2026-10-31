import ProphetSecretary.Limiting.FiniteIntensityPoisson
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Campbell expectation for finite marked Poisson configurations

The first count moment and the actual conditional iid array law give the
nonnegative Campbell formula. No compensator or independent-increment identity
is assumed as part of the point-process interface.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

noncomputable def intensity (μ : FiniteMeasure ℝ) : Measure Point :=
  ProphetSecretary.Model.Instance.uniformClock.prod (μ : Measure ℝ)

instance intensity_isFinite (μ : FiniteMeasure ℝ) : IsFiniteMeasure (intensity μ) := by
  unfold intensity
  infer_instance

lemma intensity_eq_mass_smul_pointLaw (μ : FiniteMeasure ℝ) :
    intensity μ = (μ.mass : ℝ≥0∞) • pointLaw μ := by
  have hm : (μ : Measure ℝ) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure ℝ) := by
    exact congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) μ.self_eq_mass_smul_normalize
  unfold intensity pointLaw
  rw [hm, Measure.prod_smul_right]

noncomputable def pointSum (f : Point → ℝ≥0∞) (ω : Configuration) : ℝ≥0∞ :=
  ∑ j : Fin ω.1, f (ω.2 j)

lemma measurable_pointSum {f : Point → ℝ≥0∞} (hf : Measurable f) : Measurable (pointSum f) := by
  apply measurable_of_configuration_branches
  intro N
  change Measurable (fun v : Fin N → Point => ∑ j : Fin N, f (v j))
  exact Finset.measurable_fun_sum _ (fun j _ => hf.comp (measurable_pi_apply j))

lemma lintegral_countingMeasure (f : Point → ℝ≥0∞) (ω : Configuration) :
    (∫⁻ p, f p ∂countingMeasure ω) = pointSum f ω := by
  simp only [countingMeasure, pointSum, lintegral_finsetSum_measure, lintegral_dirac]

lemma lintegral_pointSum_fiber (μ : FiniteMeasure ℝ) (N : ℕ) (f : Point → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, pointSum f ω ∂fiberLaw μ N) = (N : ℝ≥0∞) * ∫⁻ p, f p ∂pointLaw μ := by
  rw [fiberLaw, lintegral_map (measurable_pointSum hf) (measurable_configuration_mk N)]
  change (∫⁻ v : Fin N → Point, ∑ j : Fin N, f (v j) ∂arrayLaw μ N) = _
  rw [lintegral_finsetSum' (Finset.univ : Finset (Fin N))
    (f := fun (j : Fin N) (v : Fin N → Point) => f (v j))
    (fun j _ => (hf.comp (measurable_pi_apply j)).aemeasurable)]
  have he (j : Fin N) : (∫⁻ v : Fin N → Point, f (v j) ∂arrayLaw μ N) = ∫⁻ p, f p ∂pointLaw μ :=
    (measurePreserving_eval (fun _ : Fin N => pointLaw μ) j).lintegral_comp hf
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma lintegral_pointSum (μ : FiniteMeasure ℝ) (f : Point → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, pointSum f ω ∂configurationLaw μ) = ∫⁻ p, f p ∂intensity μ := by
  rw [configurationLaw, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_pointSum_fiber μ _ f hf]
  calc
    _ = ∑' N : ℕ, (ENNReal.ofReal (poissonWeight μ.mass N) * (N : ℝ≥0∞)) *
        (∫⁻ p, f p ∂pointLaw μ) := by simp only [mul_assoc]
    _ = (∑' N : ℕ, ENNReal.ofReal (poissonWeight μ.mass N) * (N : ℝ≥0∞)) *
        (∫⁻ p, f p ∂pointLaw μ) := ENNReal.tsum_mul_right
    _ = (μ.mass : ℝ≥0∞) * ∫⁻ p, f p ∂pointLaw μ := by rw [poisson_weights_first_ennreal]
    _ = _ := by rw [intensity_eq_mass_smul_pointLaw, lintegral_smul_measure, smul_eq_mul]

/-- Nonnegative Campbell formula, derived for the constructed finite-intensity
marked Poisson law. The complete configuration includes arrivals after stopping. -/
lemma campbell_nonnegative (μ : FiniteMeasure ℝ) (f : Point → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ p, f p ∂countingMeasure ω ∂configurationLaw μ) = ∫⁻ p, f p ∂intensity μ := by
  simp_rw [lintegral_countingMeasure]
  exact lintegral_pointSum μ f hf

lemma expected_count (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) :
    (∫⁻ ω, countingMeasure ω S ∂configurationLaw μ) = intensity μ S := by
  have h := campbell_nonnegative μ (S.indicator 1) (measurable_const.indicator hS)
  simpa only [lintegral_indicator_one hS] using h

lemma expected_count_rectangle (μ : FiniteMeasure ℝ) {T B : Set ℝ}
    (hT : MeasurableSet T) (hB : MeasurableSet B) :
    (∫⁻ ω, countingMeasure ω (T ×ˢ B) ∂configurationLaw μ) =
      ProphetSecretary.Model.Instance.uniformClock T * (μ : Measure ℝ) B := by
  rw [expected_count μ (hT.prod hB)]
  exact Measure.prod_prod T B

end ProphetSecretary.Limiting
