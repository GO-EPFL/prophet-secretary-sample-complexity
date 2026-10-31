import ProphetSecretary.Limiting.ExcessIntensity
import ProphetSecretary.Limiting.HybridScalarObjectives

/-!
# A valid hybrid excess state

Retained laws are pushed through the excess map. The anonymous intensity is
pushed forward and then restricted to positive values, so the hybrid model's
positive-mark support obligation is actually satisfied. Zero mapped marks are
not silently included in the positive Poisson state.
-/

open MeasureTheory Set Filter
open scoped NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.excessState (B : FiniteIntensityHybridInstance n) (a : ℝ≥0) :
    FiniteIntensityHybridInstance n where
  cap := B.cap
  terminal := 0
  terminal_le_cap := by positivity
  individuals := B.individuals.excessOffers a
  individual_bounded := by
    intro i
    change ∀ᵐ y ∂(B.individuals.law i).map (Model.excessValueMap a), y ≤ (B.cap : ℝ)
    apply (ae_map_iff (Model.measurable_excessValueMap a).aemeasurable measurableSet_Iic).mpr
    filter_upwards [B.individual_bounded i] with x hx
    have hn : 0 ≤ min (a : ℝ) (max x 0) := le_min a.property (le_max_right _ _)
    change x - min (a : ℝ) (max x 0) ≤ (B.cap : ℝ)
    linarith only [hx,hn]
  intensity := excessIntensity B.intensity a
  intensity_supported := excessIntensity_supported B.intensity a.property B.intensity_supported

lemma FiniteIntensityHybridInstance.excessState_markBounds (B : FiniteIntensityHybridInstance n) (a : ℝ≥0) :
    ∀ᵐ x ∂normalizedMarkOrZero (B.excessState a).intensity, x ∈ Icc (0 : ℝ) (B.cap : ℝ) :=
  normalizedMarkOrZero_bounds _ B.cap.property (B.excessState a).intensity_supported

lemma FiniteIntensityHybridInstance.excessState_markIntegrable (B : FiniteIntensityHybridInstance n) (a : ℝ≥0) :
    Integrable id (normalizedMarkOrZero (B.excessState a).intensity) :=
  normalizedMarkOrZero_integrable _ B.cap.property (B.excessState a).intensity_supported

lemma FiniteIntensityHybridInstance.excessState_premiumBalance (B : FiniteIntensityHybridInstance n) (a : ℝ≥0)
    {w v : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) :
    ((B.excessState a).intensity : Measure ℝ).real univ *
      Model.positivePremium (normalizedMarkOrZero (B.excessState a).intensity) w v =
    (B.intensity : Measure ℝ).real univ *
      Model.positivePremium (Model.excessLaw (B.intensity.normalize : Measure ℝ) a) w v :=
  excessIntensity_normalized_premium B.intensity hw hv a

end ProphetSecretary.Limiting
