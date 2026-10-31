import ProphetSecretary.Limiting.ThresholdedWorldBandScorePoisson
import ProphetSecretary.Probability.CompensatedCloudPayoff

/-!
# Original full-complement likelihood scores and Poisson scores

The compensated score of each original marginal is compared with its complete
centered band count, then with the actual Poisson count. The payoff may be an
analytical function of the full cutoff point measure, including future points;
this comparison supplies no additional policy observations.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

theorem thresholdedWorld_compensatedScore_poisson_error (P : Model.Instance n) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (d : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hAbove : B⊆Ioi d)
    (hHalf : ∀ i, (P.law i).real B≤1/2) (g : (Measure Point) × Aux → ℝ) (hg : Measurable g)
    {D : ℝ} (hD : 0≤D) (hb : ∀ q, |g q|≤D) :
    let a := ∑ i, (P.law i).real B
    let μ := ∑ i, thresholdMarkIntensity (P.law i) d
    |(∫ ω : Model.World n Aux, completeScore (fun i => compensatedBandScore (P.law i) B) ω.1*
        g (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂P.worldLaw ν)-
      ∫ q : Configuration × Aux, ((pointCount (univ ×ˢ B) q.1:ℝ)-a)*g (countingMeasure q.1,q.2)
        ∂(configurationLaw μ).prod ν| ≤
      Real.sqrt (D^2*(∑ i, ((P.law i).real B)^2))+
        Real.sqrt (4*D^2*a*(∑ i, ((P.law i).real (Ioi d))^2)) := by
  let G : Model.World n Aux → ℝ := fun ω =>
    g (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)
  have hG : Measurable G := hg.comp (thresholdedPointWorld_measurePreserving P ν d).measurable
  have hComp := compensatedCloudScore_payoff_error P.law ((Model.Instance.clocksLaw n).prod ν)
    hB hHalf G hG hD (fun ω => hb _)
  have hPoisson := thresholdedWorld_bandScore_poisson_error P ν d hB hAbove g hg hD hb
  apply (abs_sub_le _ (∫ ω : Model.World n Aux, centeredIndependentBandCount P.law B ω.1*G ω ∂P.worldLaw ν) _).trans
  exact add_le_add hComp hPoisson
end ProphetSecretary.Limiting
