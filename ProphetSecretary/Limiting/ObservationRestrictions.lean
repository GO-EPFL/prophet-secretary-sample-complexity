import ProphetSecretary.Limiting.CountableObservations
import ProphetSecretary.Limiting.CountablePoissonCounts

/-!
# Observable pasts as restrictions of the actual counting measure

Restricting by time and then by a mark cutoff commutes. These identities keep
all anonymous observations available in the intended truncated observer while
preventing generation labels or future configuration counts from entering it.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

lemma measurable_measureRestriction {S : Set Point} (hS : MeasurableSet S) :
    Measurable (fun μ : Measure Point => μ.restrict S) := by
  apply Measure.measurable_of_measurable_coe
  intro T hT
  have he : (fun μ : Measure Point => μ.restrict S T) = fun μ => μ (T ∩ S) := by
    funext μ
    exact Measure.restrict_apply hT
  rw [he]
  exact Measure.measurable_coe (hT.inter hS)

lemma observedHistory_eq_countingRestriction (ω : Configuration) (t : ℝ) :
    observedHistory ω t = (countingMeasure ω).restrict (Iio t ×ˢ univ) := by
  ext S hS
  rw [Measure.restrict_apply hS]
  simp only [observedHistory,countingMeasure,Measure.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases ht : (ω.2 j).1 < t
  · simp only [if_pos ht,Measure.dirac_apply' _ hS,Measure.dirac_apply' _
      (hS.inter (measurableSet_Iio.prod MeasurableSet.univ))]
    by_cases hjS : ω.2 j ∈ S <;> simp [Set.indicator,hjS,ht]
  · simp [ht,Measure.dirac_apply' _ (hS.inter (measurableSet_Iio.prod MeasurableSet.univ))]

lemma CountableInstance.anonymousHistory_eq_countingRestriction
    (ω : CountableInstance.BandConfigurations) (t : ℝ) :
    CountableInstance.anonymousHistory ω t = (bandCountingMeasure ω).restrict (Iio t ×ˢ univ) := by
  rw [bandCountingMeasure,Measure.restrict_sum (fun k => countingMeasure (ω k))
    (measurableSet_Iio.prod MeasurableSet.univ)]
  apply congrArg Measure.sum
  funext k
  exact observedHistory_eq_countingRestriction (ω k) t

lemma CountableInstance.anonymousHistory_markRestriction
    (ω : CountableInstance.BandConfigurations) (t b : ℝ) :
    (CountableInstance.anonymousHistory ω t).restrict (univ ×ˢ Ioi b) =
      ((bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)).restrict (Iio t ×ˢ univ) := by
  rw [CountableInstance.anonymousHistory_eq_countingRestriction,
    Measure.restrict_restrict (MeasurableSet.univ.prod measurableSet_Ioi),
    Measure.restrict_restrict (measurableSet_Iio.prod MeasurableSet.univ)]
  congr 1
  exact inter_comm _ _

end ProphetSecretary.Limiting
