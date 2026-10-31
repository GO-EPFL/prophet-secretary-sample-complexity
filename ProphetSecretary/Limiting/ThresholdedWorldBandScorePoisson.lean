import ProphetSecretary.Limiting.BandObservableMoments
import ProphetSecretary.Limiting.RareOfferL2Error
import ProphetSecretary.Probability.BoundedScorePayoffMoment

/-!
# Quantitative complete band-score Poisson comparison

Both second-moment inputs are discharged from actual independent-offer and
Poisson count laws. The payoff may depend on the entire cutoff configuration
and arbitrary independent auxiliary randomness; it is not supplied as future
information to any stopping callback.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

theorem thresholdedWorld_bandScore_poisson_error (P : Model.Instance n) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (d : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hAbove : B⊆Ioi d)
    (g : (Measure Point) × Aux → ℝ) (hg : Measurable g) {D : ℝ} (hD : 0≤D)
    (hb : ∀ q, |g q|≤D) :
    let a := ∑ i, (P.law i).real B
    let μ := ∑ i, thresholdMarkIntensity (P.law i) d
    |(∫ ω : Model.World n Aux, centeredIndependentBandCount P.law B ω.1*
        g (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂P.worldLaw ν)-
      ∫ q : Configuration × Aux, ((pointCount (univ ×ˢ B) q.1:ℝ)-a)*g (countingMeasure q.1,q.2)
        ∂(configurationLaw μ).prod ν| ≤
      Real.sqrt (4*D^2*a*(∑ i, ((P.law i).real (Ioi d))^2)) := by
  let a := ∑ i, (P.law i).real B
  let μs := fun i => thresholdMarkIntensity (P.law i) d
  let μ := ∑ i, μs i
  let p := fun i => thresholdOccurrenceProbability (P.law i) d
  let L := (rareCountingMeasureLaw μs p).prod ν
  let R := ((configurationLaw μ).map countingMeasure).prod ν
  let s := pointMeasureBandScore (Aux := Aux) a B
  let F : (Measure Point) × Aux → ℝ := fun q => s q*g q
  have hs : Measurable s := measurable_pointMeasureBandScore a hB
  have hF : Measurable F := hs.mul hg
  have hLeft := rareBandScore_memLp_and_secondMoment P ν d hB hAbove
  have hLMom := bounded_score_payoff_memLp_and_secondMoment L s g hLeft.1 hg.aestronglyMeasurable
    hLeft.2 hD (Eventually.of_forall hb)
  have hMass : (μ:Measure ℝ).real B=a := thresholdMarkIntensity_sum_band_real P.law d hB hAbove
  have hRight : MemLp s 2 R ∧ (∫ q, (s q)^2 ∂R)=a := by
    have h := poissonBandScore_memLp_and_secondMoment μ ν hB
    change MemLp (pointMeasureBandScore (Aux := Aux) ((μ:Measure ℝ).real B) B) 2 R ∧
      (∫ q, (pointMeasureBandScore (Aux := Aux) ((μ:Measure ℝ).real B) B q)^2 ∂R)=(μ:Measure ℝ).real B at h
    rw [hMass] at h
    exact h
  have hRMom := bounded_score_payoff_memLp_and_secondMoment R s g hRight.1 hg.aestronglyMeasurable
    hRight.2.le hD (Eventually.of_forall hb)
  have h := rareCountingMeasure_l2_observable_error ν μs p (fun i => thresholdMarkIntensity_rate (P.law i) d)
    F hF hLMom.1 hRMom.1 hLMom.2 hRMom.2
  have hX := thresholdedPointWorld_measurePreserving P ν d
  have hY : MeasurePreserving (fun q : Configuration × Aux => (countingMeasure q.1,q.2))
      ((configurationLaw μ).prod ν) R :=
    (⟨measurable_countingMeasure,rfl⟩ : MeasurePreserving countingMeasure _ _).prod (MeasurePreserving.id ν)
  rw [← hX.hasLaw.integral_comp hF.aestronglyMeasurable,← hY.hasLaw.integral_comp hF.aestronglyMeasurable] at h
  have hLeftFun : F ∘ (fun ω : Model.World n Aux =>
      (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)) =
      (fun ω : Model.World n Aux => centeredIndependentBandCount P.law B ω.1*
        g (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)) := by
    funext ω
    change ((thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i))).real (univ ×ˢ B)-a)*_ = _
    rw [thresholdedOfferCountingMeasure_band_real d hB hAbove]
    rfl
  have hRightFun : F ∘ (fun q : Configuration × Aux => (countingMeasure q.1,q.2)) =
      (fun q : Configuration × Aux => ((pointCount (univ ×ˢ B) q.1:ℝ)-a)*g (countingMeasure q.1,q.2)) := by
    funext q
    change ((countingMeasure q.1 (univ ×ˢ B)).toReal-a)*_ = _
    rw [countingMeasure_eq_pointCount (MeasurableSet.univ.prod hB),ENNReal.toReal_natCast]
  rw [hLeftFun,hRightFun] at h
  have hNum : 2*(D^2*a+D^2*a)*(∑ i, (p i:ℝ)^2)=4*D^2*a*(∑ i, (p i:ℝ)^2) := by ring
  rw [hNum] at h
  simpa only [p,thresholdOccurrenceProbability_eq_real] using h
end ProphetSecretary.Limiting
