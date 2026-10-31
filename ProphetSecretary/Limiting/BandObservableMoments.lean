import ProphetSecretary.Limiting.ThresholdedBandCount
import ProphetSecretary.Probability.PoissonCenteredScore

/-!
# Actual second moments of complete observable band scores

The finite score is a count in the original independent offer vector. Its
Poisson counterpart uses the entire constructed configuration. Both moment
bounds are transported through proved observable laws, not assumed as an
independence interface.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

noncomputable def pointMeasureBandScore (a : ℝ) (B : Set ℝ) (q : (Measure Point) × Aux) : ℝ :=
  q.1.real (univ ×ˢ B)-a

lemma measurable_pointMeasureBandScore (a : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (pointMeasureBandScore (Aux := Aux) a B) :=
  (((Measure.measurable_coe (MeasurableSet.univ.prod hB)).ennreal_toReal).comp measurable_fst).sub_const a

lemma thresholdedPointWorld_measurePreserving (P : Model.Instance n) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (d : ℝ) :
    MeasurePreserving (fun ω : Model.World n Aux =>
      (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)) (P.worldLaw ν)
      ((rareCountingMeasureLaw (fun i => thresholdMarkIntensity (P.law i) d)
        (fun i => thresholdOccurrenceProbability (P.law i) d)).prod ν) :=
  ((thresholdedOfferCountingMeasure_measurePreserving P.law d).prod (MeasurePreserving.id ν)).comp
    (retainedPairs_measurePreserving P ν)

lemma rareBandScore_memLp_and_secondMoment (P : Model.Instance n) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (d : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hAbove : B⊆Ioi d) :
    let a := ∑ i, (P.law i).real B
    let ρ := (rareCountingMeasureLaw (fun i => thresholdMarkIntensity (P.law i) d)
      (fun i => thresholdOccurrenceProbability (P.law i) d)).prod ν
    MemLp (pointMeasureBandScore a B) 2 ρ ∧
      (∫ q, (pointMeasureBandScore (Aux := Aux) a B q)^2 ∂ρ)≤a := by
  let a := ∑ i, (P.law i).real B
  let ρ := (rareCountingMeasureLaw (fun i => thresholdMarkIntensity (P.law i) d)
    (fun i => thresholdOccurrenceProbability (P.law i) d)).prod ν
  let X := fun ω : Model.World n Aux =>
    (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)
  have hX : MeasurePreserving X (P.worldLaw ν) ρ := thresholdedPointWorld_measurePreserving P ν d
  have hPull : pointMeasureBandScore a B ∘ X =
      (fun ω : Model.World n Aux => centeredIndependentBandCount P.law B ω.1) := by
    funext ω
    change (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i))).real (univ ×ˢ B)-a = _
    rw [thresholdedOfferCountingMeasure_band_real d hB hAbove]
    rfl
  have hCM : Measurable (centeredIndependentBandCount P.law B) := by
    rw [centeredIndependentBandCount_eq_completeScore]
    exact measurable_completeScore (fun _ => centeredIndicator_measurable hB _)
  have hValues : MeasurePreserving (Prod.fst : Model.World n Aux → (Fin n → ℝ))
      (P.worldLaw ν) P.valuesLaw := measurePreserving_fst
  have hSource : MemLp (pointMeasureBandScore a B ∘ X) 2 (P.worldLaw ν) := by
    rw [hPull]
    exact (centeredIndependentBandCount_moments P.law hB).1.comp_measurePreserving hValues
  have hSourceMoment : (∫ ω, ((pointMeasureBandScore a B ∘ X) ω)^2 ∂P.worldLaw ν)≤a := by
    rw [hPull]
    exact (hValues.hasLaw.integral_comp (hCM.pow_const 2).aestronglyMeasurable).trans_le
      (centeredIndependentBandCount_secondMoment_le P.law hB)
  have hScoreMeas := measurable_pointMeasureBandScore (Aux := Aux) a hB
  change MemLp (pointMeasureBandScore (Aux := Aux) a B) 2 ρ ∧
    (∫ q, (pointMeasureBandScore (Aux := Aux) a B q)^2 ∂ρ)≤a
  constructor
  · rw [← hX.map_eq]
    exact (memLp_map_measure_iff hScoreMeas.aestronglyMeasurable hX.measurable.aemeasurable).mpr hSource
  · have he := hX.hasLaw.integral_comp (hScoreMeas.pow_const 2).aestronglyMeasurable
    exact he.symm.trans_le hSourceMoment

lemma poissonBandScore_memLp_and_secondMoment (μ : FiniteMeasure ℝ) (ν : Measure Aux)
    [IsProbabilityMeasure ν] {B : Set ℝ} (hB : MeasurableSet B) :
    let a := (μ:Measure ℝ).real B
    let ρ := ((configurationLaw μ).map countingMeasure).prod ν
    MemLp (pointMeasureBandScore a B) 2 ρ ∧
      (∫ q, (pointMeasureBandScore (Aux := Aux) a B q)^2 ∂ρ)=a := by
  let a := (μ:Measure ℝ).real B
  let ρ := ((configurationLaw μ).map countingMeasure).prod ν
  let S : Set Point := univ ×ˢ B
  have hS : MeasurableSet S := MeasurableSet.univ.prod hB
  let r := countRate μ S
  let X := fun q : Configuration × Aux => (countingMeasure q.1,q.2)
  have hX : MeasurePreserving X (worldLaw μ ν) ρ :=
    (⟨measurable_countingMeasure,rfl⟩ : MeasurePreserving countingMeasure _ _).prod (MeasurePreserving.id ν)
  have hRate : (r:ℝ)=a := by
    rw [countRate_coe_eq_intensity]
    simp only [a,S,intensity,Measure.real,Measure.prod_prod,measure_univ,one_mul]
  have hCount : MeasurePreserving (fun q : Configuration × Aux => pointCount S q.1)
      (worldLaw μ ν) (ProbabilityTheory.poissonMeasure r) :=
    (pointCount_measurePreserving μ hS).comp (measurePreserving_fst (μ := configurationLaw μ) (ν := ν))
  have hPull : pointMeasureBandScore a B ∘ X =
      poissonCenteredScore r ∘ (fun q : Configuration × Aux => pointCount S q.1) := by
    funext q
    change (countingMeasure q.1 S).toReal-a = _
    rw [countingMeasure_eq_pointCount hS,ENNReal.toReal_natCast]
    simp only [Function.comp_def,poissonCenteredScore,hRate]
  have hSource : MemLp (pointMeasureBandScore a B ∘ X) 2 (worldLaw μ ν) := by
    rw [hPull]
    exact (poissonCenteredScore_memLp_two r).comp_measurePreserving hCount
  have hSourceMoment : (∫ q, ((pointMeasureBandScore a B ∘ X) q)^2 ∂worldLaw μ ν)=a := by
    rw [hPull]
    have he := hCount.hasLaw.integral_comp ((measurable_poissonCenteredScore r).pow_const 2).aestronglyMeasurable
    exact he.trans ((integral_poissonCenteredScore_sq r).trans hRate)
  have hScoreMeas := measurable_pointMeasureBandScore (Aux := Aux) a hB
  change MemLp (pointMeasureBandScore (Aux := Aux) a B) 2 ρ ∧
    (∫ q, (pointMeasureBandScore (Aux := Aux) a B q)^2 ∂ρ)=a
  constructor
  · rw [← hX.map_eq]
    exact (memLp_map_measure_iff hScoreMeas.aestronglyMeasurable hX.measurable.aemeasurable).mpr hSource
  · have he := hX.hasLaw.integral_comp (hScoreMeas.pow_const 2).aestronglyMeasurable
    exact he.symm.trans hSourceMoment
end ProphetSecretary.Limiting
