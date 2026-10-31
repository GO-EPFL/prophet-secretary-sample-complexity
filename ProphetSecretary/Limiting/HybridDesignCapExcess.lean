import ProphetSecretary.Limiting.HybridCapExcess
import ProphetSecretary.Limiting.BernoulliCapping

/-!
# Exact aggregate excess in the hybrid Bernoulli approximation

The virtual multiplicity and Bernoulli probability preserve the anonymous
intensity mass exactly. Thus the finite design's entire excess equals the
hybrid aggregate excess at every fixed cap, before any limit is taken.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.FiniteIntensityHybridInstance
variable {n k : ℕ}

lemma finiteDesign_tailSum_eq_totalCapExcess (B : FiniteIntensityHybridInstance n) (hμ : B.intensity≠0)
    (p : unitInterval) (hRate : (B.intensity : Measure ℝ).real univ=(k:ℝ)*(p:ℝ)) (K : ℝ≥0) :
    (finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) p k).tailSum K=
      B.totalCapExcess K := by
  rw [finitePoissonDesign_tailSum _ _ _ p k K (B.normalizedMark_integrable hμ)]
  have hIntegral := integral_finiteIntensity_test_eq_mass_normalized B.intensity (Model.tailValue K)
  have hMass : (B.intensity.mass:ℝ)=(k:ℝ)*(p:ℝ) := hRate
  change B.individuals.tailSum K+(k:ℝ)*(p:ℝ)*(∫ x, Model.tailValue K x ∂(B.intensity.normalize : Measure ℝ))=
    B.individuals.tailSum K+B.poissonCapExcess K
  rw [←hMass,←hIntegral]
  rfl

lemma bernoulliApproximation_tailSum (B : FiniteIntensityHybridInstance n) (hμ : B.intensity≠0)
    (m : ℕ) (K : ℝ≥0) : (B.bernoulliApproximation hμ m).tailSum K=B.totalCapExcess K :=
  B.finiteDesign_tailSum_eq_totalCapExcess hμ _ (bernoulliProbability_total _ measureReal_nonneg m).symm K

end ProphetSecretary.Limiting.FiniteIntensityHybridInstance
