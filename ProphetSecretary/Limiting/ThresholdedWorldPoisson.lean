import ProphetSecretary.Limiting.ThresholdedOfferFamily
import ProphetSecretary.Limiting.FiniteArrayEvaluation
import ProphetSecretary.Model.FirstMomentTailCount

/-!
# Marked Poisson comparison on an actual independent instance

The original values, independent uniform clocks, and arbitrary independent
seed are transported without altering their joint law. The cutoff projection
is analytical and does not remove zero-valued observations from a policy.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

lemma thresholdOccurrenceProbability_eq_real (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ) :
    (thresholdOccurrenceProbability ν b : ℝ) = ν.real (Ioi b) := by
  change ((ν.restrict (Ioi b)) univ).toReal = (ν (Ioi b)).toReal
  rw [Measure.restrict_apply_univ]

/-- A dimension-independent quantitative Poisson comparison for every bounded
measurable function of the cutoff point measure and independent seed. -/
theorem thresholdedWorld_poisson_observable_error (P : Model.Instance n) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (b : ℝ) (f : (Measure Point) × Aux → ℝ) (hf : Measurable f)
    {D : ℝ} (hD : 0≤D) (hb : ∀ q, |f q|≤D) :
    |(∫ ω : Model.World n Aux, f (thresholdedOfferCountingMeasure b
        (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂P.worldLaw ν)-
      ∫ q, f (countingMeasure q.1,q.2)
        ∂(configurationLaw (∑ i, thresholdMarkIntensity (P.law i) b)).prod ν| ≤
      2*D*∑ i, ((P.law i).real (Ioi b))^2 := by
  let μ := fun i => thresholdMarkIntensity (P.law i) b
  let p := fun i => thresholdOccurrenceProbability (P.law i) b
  have hRaw := (thresholdedOfferCountingMeasure_measurePreserving P.law b).prod (MeasurePreserving.id ν)
  have hWorld := hRaw.comp (retainedPairs_measurePreserving P ν)
  have hPoisson : MeasurePreserving
      (fun q : Configuration × Aux => (countingMeasure q.1,q.2))
      ((configurationLaw (∑ i, μ i)).prod ν)
      (((configurationLaw (∑ i, μ i)).map countingMeasure).prod ν) :=
    (⟨measurable_countingMeasure,rfl⟩ : MeasurePreserving countingMeasure _ _).prod (MeasurePreserving.id ν)
  have he := rareCountingMeasure_observable_error ν μ p
    (fun i => thresholdMarkIntensity_rate (P.law i) b) f hf hD hb
  rw [← hWorld.hasLaw.integral_comp hf.aestronglyMeasurable,
    ← hPoisson.hasLaw.integral_comp hf.aestronglyMeasurable] at he
  simpa only [Function.comp_def,Prod.map_apply,id_eq,μ,p,thresholdOccurrenceProbability_eq_real] using he

/-- The first-moment bound controls the aggregate error even when the number
of independent offers varies. -/
theorem thresholdedWorld_poisson_error_le_firstMoment (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (ν : Measure Aux)
    [IsProbabilityMeasure ν] {b δ D : ℝ} (hb : 0<b) (hδ : 0≤δ) (hD : 0≤D)
    (hRare : ∀ i, (P.law i).real (Ioi b)≤δ)
    (f : (Measure Point) × Aux → ℝ) (hf : Measurable f) (hfBound : ∀ q, |f q|≤D) :
    |(∫ ω : Model.World n Aux, f (thresholdedOfferCountingMeasure b
        (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂P.worldLaw ν)-
      ∫ q, f (countingMeasure q.1,q.2)
        ∂(configurationLaw (∑ i, thresholdMarkIntensity (P.law i) b)).prod ν| ≤
      2*D*δ*P.totalFirstMoment/b := by
  apply (thresholdedWorld_poisson_observable_error P ν b f hf hD hfBound).trans
  have hsum : (∑ i, ((P.law i).real (Ioi b))^2) ≤ δ*P.tailCount b := by
    rw [Model.Instance.tailCount,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change ((P.law i).real (Ioi b))^2 ≤ δ*(P.law i).real (Ioi b)
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hRare i) measureReal_nonneg
  have htail := P.tailCount_le_totalFirstMoment_div hP hb
  calc
    _ ≤ 2*D*(δ*P.tailCount b) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2*D*(δ*(P.totalFirstMoment/b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hδ) (by positivity)
    _ = _ := by ring
end ProphetSecretary.Limiting
