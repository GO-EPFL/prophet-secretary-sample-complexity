import ProphetSecretary.Limiting.CountableReserveTranslation

/-!
# Exact labeled finite laws under reserve translation

Padded zero coordinates remain zero. Every positive tail is the original
shifted tail, and restriction commutes with the actual excess pushforward.
These identities preserve the chosen finite labels and all zero observations.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
open Model
variable {n : ℕ}

lemma labeledPaddedLaw_excessOffers (P : Model.Instance n) (a : ℝ≥0) (j : ℕ) :
    labeledPaddedLaw (P.excessOffers a) j=
      (labeledPaddedLaw P j).map (measurable_excessValueMap a).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  by_cases hj : j<n
  · rw [labeledPaddedLaw_of_lt _ hj,labeledPaddedLaw_of_lt P hj]
    rfl
  · rw [labeledPaddedLaw_of_ge _ (not_lt.mp hj),ProbabilityMeasure.toMeasure_map,
      labeledPaddedLaw_of_ge P (not_lt.mp hj),Measure.map_dirac' (measurable_excessValueMap a) 0]
    exact congrArg Measure.dirac (Model.excessValueMap_zero (a := (a : ℝ)) a.property).symm

lemma labeledPaddedLaw_excess_positiveTail (P : Model.Instance n) (a : ℝ≥0) (j : ℕ)
    (b : ℝ) (hb : 0≤b) :
    (labeledPaddedLaw (P.excessOffers a) j : Measure ℝ) (Ioi b)=
      (labeledPaddedLaw P j : Measure ℝ) (Ioi ((a : ℝ)+b)) := by
  rw [labeledPaddedLaw_excessOffers,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_excessValueMap a) measurableSet_Ioi,
    excessValueMap_preimage_Ioi (a := (a : ℝ)) (b := b) a.property hb]

lemma extendedTailCount_excessOffers (P : Model.Instance n) (a : ℝ≥0) (b : ℝ) (hb : 0≤b) :
    extendedTailCount (P.excessOffers a) b=extendedTailCount P ((a : ℝ)+b) := by
  unfold extendedTailCount
  apply Finset.sum_congr rfl
  intro i _
  exact excessLaw_positiveTail (P.law i) a.property hb

lemma tailCount_excessOffers (P : Model.Instance n) (a : ℝ≥0) (b : ℝ) (hb : 0≤b) :
    (P.excessOffers a).tailCount b=P.tailCount ((a : ℝ)+b) := by
  have h := congrArg ENNReal.toReal (extendedTailCount_excessOffers P a b hb)
  simpa only [extendedTailCount_toReal] using h

lemma labeledBandResidual_excessOffers (P : Model.Instance n) (N : ℕ) (a : ℝ≥0)
    (b : ℝ) (hb : 0≤b) :
    labeledBandResidual (P.excessOffers a) N b=
      (labeledBandResidual P N ((a : ℝ)+b)).map (excessValueMap a) := by
  symm
  change (FiniteMeasure.mapHom (measurable_excessValueMap a))
    (∑ i∈Finset.univ.filter (fun i : Fin n => N≤ i.val),
      (P.marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi ((a : ℝ)+b)))=_
  rw [map_sum]
  unfold labeledBandResidual
  apply Finset.sum_congr rfl
  intro i _
  apply FiniteMeasure.toMeasure_injective
  change ((P.law i).restrict (Ioi ((a : ℝ)+b))).map (excessValueMap a)=
    ((P.law i).map (excessValueMap a)).restrict (Ioi b)
  rw [Measure.restrict_map (measurable_excessValueMap a) measurableSet_Ioi,
    excessValueMap_preimage_Ioi (a := (a : ℝ)) (b := b) a.property hb]

end ProphetSecretary.Limiting
