import ProphetSecretary.Limiting.ThresholdedWorldPoisson
import ProphetSecretary.Probability.IndependentBandCount

/-!
# Complete upper-band counts under the analytical cutoff projection

Every band contained strictly above the cutoff has the same count before
and after projection, including arrivals after selection. Its Poisson
comparison intensity has exactly the original aggregate band mass.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

lemma thresholdedOfferCountingMeasure_band_real (d : ℝ) {B : Set ℝ} (hB : MeasurableSet B)
    (hAbove : B⊆Ioi d) (x u : Fin n → ℝ) :
    (thresholdedOfferCountingMeasure d (fun i => (u i,x i))).real (univ ×ˢ B)=countIn B x := by
  simp only [thresholdedOfferCountingMeasure,Measure.real,Measure.coe_finsetSum,Finset.sum_apply]
  rw [ENNReal.toReal_sum (fun i _ => by
    unfold observedSingleton
    split_ifs <;> finiteness)]
  unfold countIn
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : d<x i
  · rw [observedSingleton,if_pos (show (u i,x i)∈univ ×ˢ Ioi d from ⟨mem_univ _,hx⟩),
      Measure.dirac_apply' _ (MeasurableSet.univ.prod hB)]
    by_cases hi : x i∈B <;> simp [Set.indicator,hi]
  · have hi : x i∉B := fun h => hx (hAbove h)
    rw [observedSingleton,if_neg (by simpa only [mem_prod,mem_univ,true_and,mem_Ioi] using hx)]
    simp [Set.indicator,hi]

lemma thresholdMarkIntensity_sum_band_real (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (d : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hAbove : B⊆Ioi d) :
    ((∑ i, thresholdMarkIntensity (ν i) d : FiniteMeasure ℝ):Measure ℝ).real B=∑ i, (ν i).real B := by
  have hMass : ((∑ i, thresholdMarkIntensity (ν i) d : FiniteMeasure ℝ):Measure ℝ) B=∑ i, ν i B := by
    rw [FiniteMeasure.toMeasure_sum]
    simp only [Measure.coe_finsetSum,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (ν i).restrict (Ioi d) B=ν i B
    rw [Measure.restrict_apply hB,inter_eq_left.mpr hAbove]
  change (((∑ i, thresholdMarkIntensity (ν i) d : FiniteMeasure ℝ):Measure ℝ) B).toReal= _
  rw [hMass,ENNReal.toReal_sum (fun i _ => measure_ne_top (ν i) B)]
  rfl
end ProphetSecretary.Limiting
