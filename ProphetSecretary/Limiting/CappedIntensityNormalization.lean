import ProphetSecretary.Limiting.HybridCapping
import ProphetSecretary.Limiting.BernoulliCapping

/-!
# Mass and normalized law of the capped anonymous intensity

A measurable cap preserves the complete finite mass. Normalization therefore
commutes with capping, including atoms at the cap. The nonzero premise concerns
only normalization; actual zero intensity is treated separately.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Limiting

lemma finiteMeasure_cap_mass (μ : FiniteMeasure ℝ) (K : ℝ≥0) :
    (μ.map (Model.capValue K)).mass=μ.mass := by
  change (μ.map (Model.capValue K)) univ=μ univ
  rw [FiniteMeasure.map_apply μ (Model.measurable_capValue K) MeasurableSet.univ]
  rfl

lemma finiteMeasure_cap_nonzero (μ : FiniteMeasure ℝ) (hμ : μ≠0) (K : ℝ≥0) :
    μ.map (Model.capValue K)≠0 := by
  rw [←FiniteMeasure.mass_nonzero_iff,finiteMeasure_cap_mass]
  exact μ.mass_nonzero_iff.mpr hμ

lemma finiteMeasure_cap_normalize (μ : FiniteMeasure ℝ) (hμ : μ≠0) (K : ℝ≥0) :
    (μ.map (Model.capValue K)).normalize=cappedMarkLaw μ.normalize K := by
  have hMapped := finiteMeasure_cap_nonzero μ hμ K
  apply Subtype.ext
  change ((μ.map (Model.capValue K)).normalize : Measure ℝ)=(μ.normalize : Measure ℝ).map (Model.capValue K)
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hMapped,
    FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hμ,Measure.map_smul,finiteMeasure_cap_mass]
  rfl

end ProphetSecretary.Limiting
