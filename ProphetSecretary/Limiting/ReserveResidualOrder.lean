import ProphetSecretary.Limiting.ContinuousWeightedBandExtraction

/-!
# Domination of the final residual by every finite-prefix residual

The final intensity is obtained by subtracting all retained weighted laws.
Its domination is proved from the actual prefix identities and the countable
measure sum, before applying the positive unweighting map.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical BigOperators Topology

namespace ProphetSecretary.Limiting

lemma extractedContinuousWeightedResidual_le_prefix (w : ℝ →ᵇ ℝ)
    (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) (N : ℕ) :
    (extractedContinuousWeightedResidual w Q ρ : Measure ℝ) ≤ (ρ N : Measure ℝ) := by
  apply Measure.sub_le_of_le_add
  have hp := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ))
    (continuousWeighted_residual_prefix_identity w Q ρ hρ N)
  rw [FiniteMeasure.toMeasure_add,FiniteMeasure.toMeasure_sum] at hp
  rw [hp,add_comm]
  apply add_le_add le_rfl
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.finsetSum_apply,retainedContinuousWeightedMeasure,Measure.sum_apply _ hs]
  exact ENNReal.sum_le_tsum (Finset.range N)

lemma reserveMarkIntensityAbove_mono (η ξ : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ)
    (a b : ℝ) (hw : Monotone w) (hb : a < b) (hwb : 0 < w b)
    (hOrder : (η : Measure ℝ) ≤ (ξ : Measure ℝ)) :
    (reserveMarkIntensityAbove η w a b hw hb hwb : Measure ℝ) ≤
      (reserveMarkIntensityAbove ξ w a b hw hb hwb : Measure ℝ) := by
  apply Measure.restrict_mono subset_rfl
  apply Measure.le_iff.mpr
  intro s hs
  change ((η : Measure ℝ).withDensity (reserveReciprocalWeight w a)) s ≤
    ((ξ : Measure ℝ).withDensity (reserveReciprocalWeight w a)) s
  rw [withDensity_apply _ hs,withDensity_apply _ hs]
  exact lintegral_mono' (Measure.restrict_mono subset_rfl hOrder) le_rfl

lemma reserveMarkIntensityAbove_extracted_le_prefix (w : ℝ →ᵇ ℝ)
    (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1))
    (a b : ℝ) (hw : Monotone w) (hb : a < b) (hwb : 0 < w b) (N : ℕ) :
    (reserveMarkIntensityAbove (extractedContinuousWeightedResidual w Q ρ) w a b hw hb hwb : Measure ℝ) ≤
      (reserveMarkIntensityAbove (ρ N) w a b hw hb hwb : Measure ℝ) :=
  reserveMarkIntensityAbove_mono _ _ w a b hw hb hwb
    (extractedContinuousWeightedResidual_le_prefix w Q ρ hρ N)

end ProphetSecretary.Limiting
