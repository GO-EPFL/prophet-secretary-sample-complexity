import ProphetSecretary.Limiting.ThresholdedOfferLaw
import ProphetSecretary.Limiting.RareOfferPoissonCoupling

/-!
# Independent ordinary offers and their thresholded point measure

Independence identifies the full thresholded point measure with the rare
configuration law. This is an equality of analytical observations before any
choice of stopping policy.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
variable {ι : Type*} [Fintype ι]

noncomputable def finiteMeasureSum (m : ι → Measure Point) : Measure Point := ∑ i, m i
lemma measurable_finiteMeasureSum : Measurable (finiteMeasureSum (ι := ι)) :=
  Finset.measurable_fun_sum _ (fun i _ => measurable_pi_apply i)

lemma rareCountingMeasureLaw_eq_sum (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval) :
    rareCountingMeasureLaw μ p =
      (Measure.pi (fun i => (bernoulliConfigurationLaw (μ i) (p i)).map countingMeasure)).map finiteMeasureSum := by
  haveI (i : ι) : IsProbabilityMeasure ((bernoulliConfigurationLaw (μ i) (p i)).map countingMeasure) :=
    Measure.isProbabilityMeasure_map measurable_countingMeasure.aemeasurable
  have hJoint := measurePreserving_pi (fun i => bernoulliConfigurationLaw (μ i) (p i))
    (fun i => (bernoulliConfigurationLaw (μ i) (p i)).map countingMeasure)
    (fun _ => (⟨measurable_countingMeasure,rfl⟩ : MeasurePreserving countingMeasure _ _))
  have he := Measure.map_map (μ := Measure.pi (fun i => bernoulliConfigurationLaw (μ i) (p i)))
    measurable_finiteMeasureSum hJoint.measurable
  rw [hJoint.map_eq] at he
  exact he.symm

noncomputable def thresholdedOfferCountingMeasure (b : ℝ) (q : ι → Point) : Measure Point :=
  ∑ i, observedSingleton (univ ×ˢ Ioi b) (q i)

lemma thresholdedOfferCountingMeasure_measurePreserving
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (b : ℝ) :
    MeasurePreserving (thresholdedOfferCountingMeasure b)
      (Measure.pi (fun i => Model.Instance.uniformClock.prod (ν i)))
      (rareCountingMeasureLaw (fun i => thresholdMarkIntensity (ν i) b)
        (fun i => thresholdOccurrenceProbability (ν i) b)) := by
  let γ := fun i => (bernoulliConfigurationLaw (thresholdMarkIntensity (ν i) b)
    (thresholdOccurrenceProbability (ν i) b)).map countingMeasure
  haveI (i : ι) : IsProbabilityMeasure (γ i) :=
    Measure.isProbabilityMeasure_map measurable_countingMeasure.aemeasurable
  have hSingle (i : ι) : MeasurePreserving (observedSingleton (univ ×ˢ Ioi b))
      (Model.Instance.uniformClock.prod (ν i)) (γ i) :=
    ⟨measurable_observedSingleton (MeasurableSet.univ.prod measurableSet_Ioi),
      thresholded_offer_countingMeasure_law (ν i) b⟩
  have hJoint := measurePreserving_pi (fun i => Model.Instance.uniformClock.prod (ν i)) γ hSingle
  have hSum : MeasurePreserving finiteMeasureSum (Measure.pi γ) ((Measure.pi γ).map finiteMeasureSum) :=
    ⟨measurable_finiteMeasureSum,rfl⟩
  have h := hSum.comp hJoint
  have hfun : finiteMeasureSum ∘ (fun q : ι → Point => fun i => observedSingleton (univ ×ˢ Ioi b) (q i)) =
      thresholdedOfferCountingMeasure b := by
    funext q
    rfl
  rw [hfun] at h
  rw [rareCountingMeasureLaw_eq_sum]
  exact h
end ProphetSecretary.Limiting
