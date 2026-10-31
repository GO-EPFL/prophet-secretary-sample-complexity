import ProphetSecretary.Limiting.CountableBandScore

/-!
# Finite decomposition of a complete positive-window score

Above a fixed positive distance from the reserve, only finitely many actual
construction bands contribute. Both the complete count and its intensity
decompose over exactly those bands, so their centered score does as well.
-/
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def constructionWindowScore (B : CountableInstance) (k : ℕ) (S : Set Point)
    (v : CompleteWorld Seed) : ℝ :=
  (pointCount S (v.1 k) : ℝ)-(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).real S

lemma integrable_constructionWindowScore (B : CountableInstance) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (k : ℕ) {S : Set Point} (hS : MeasurableSet S) :
    Integrable (B.constructionWindowScore k S) (B.completeWorldLaw ν) := by
  have hMP := (B.bandConfiguration_measurePreserving k).comp
    (measurePreserving_fst : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
      (B.completeWorldLaw ν) B.bandConfigurationsLaw)
  exact (hMP.integrable_comp_of_integrable (pointCount_integrable (B.bandIntensity k) hS)).sub (integrable_const _)

theorem poissonRegionScore_eq_finite_sum (B : CountableInstance) (ν : Measure Seed)
    [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal : ℝ)<b)
    {S : Set Point} (hS : MeasurableSet S) (hSub : S ⊆ univ ×ˢ Ioi b) :
    ∃ K : ℕ, (∀ k, K<k → ∀ x ∈ B.markBand k, x≤b) ∧
      ∀ᵐ v : CompleteWorld Seed ∂B.completeWorldLaw ν,
        (bandPointCount S v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real S=
          ∑ k ∈ Finset.range (K+1), B.constructionWindowScore k S v := by
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  have hMass : (Model.Instance.uniformClock.prod B.intensity).real S=
      ∑ k ∈ Finset.range (K+1), (ProphetSecretary.Limiting.intensity (B.bandIntensity k)).real S := by
    have h := congrArg ENNReal.toReal (B.poisson_intensity_region_eq_sum hS hSub hK)
    simpa only [measureReal_def,ENNReal.toReal_sum (fun k _ => measure_ne_top _ _)] using h
  have hCount := (Measure.quasiMeasurePreserving_fst (μ := B.bandConfigurationsLaw)
    (ν := B.individualWorldLaw ν)).ae (B.bandPointCount_region_eq_sum hS hSub hK)
  refine ⟨K,hK,?_⟩
  filter_upwards [hCount] with v hv
  rw [hv,Nat.cast_sum,hMass]
  simp only [constructionWindowScore,Finset.sum_sub_distrib]

end ProphetSecretary.Limiting.CountableInstance
