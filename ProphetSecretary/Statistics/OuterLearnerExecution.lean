import ProphetSecretary.Statistics.OuterLearner

/-!
# Pathwise decisions of the outer sampling program

Training outcomes are arbitrary in these identities. The zero-pilot branch is
first positive retention; the positive-pilot branch passes only displayed values
and the original inner seed to the bounded learner. History presence is unchanged.
-/

open MeasureTheory
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

lemma outerLearner_decide (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (outerLearner m hm L).policy.decide p t i x H=(outerPolicy m hm L).decide p t i x H :=
  Learner.ofSamplePolicy_decide _ _ _ _ p.1 p.2 t i x H

lemma outerLearner_decide_zero_pilot (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (hB : outerPilotAt m hm L p=0)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (outerLearner m hm L).policy.decide p t i x H=
      if 0<outerRetainedObservation m hm L p i x then true else false := by
  rw [outerLearner_decide]
  simp only [outerPolicy,hB,if_pos,outerPositivePolicy,Policy.pullbackValuesBy,firstPositiveRule]

lemma outerLearner_decide_positive_pilot (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (hB : outerPilotAt m hm L p≠0)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (outerLearner m hm L).policy.decide p t i x H=
      L.policy.decide (outerInnerTraining m hm L p,outerInnerPolicySeed m L p) t i
        (outerDisplayedObservation m hm L p i x) (mapHistoryValuesBy (outerDisplayedObservation m hm L p) H) := by
  rw [outerLearner_decide]
  simp only [outerPolicy,hB,if_false,outerBoundedPolicy,Policy.pullbackValuesBy]

lemma outerDisplayedObservation_zero (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (i : Fin n) : outerDisplayedObservation m hm L p i 0=0 := by
  have hRet : outerRetainedObservation m hm L p i 0=0 := by
    unfold outerRetainedObservation retainAboveTag
    split <;> rfl
  simp only [outerDisplayedObservation,hRet,outerMeshDisplay_zero]

lemma outerLearner_rejects_zero (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (hZero : ∀ (y : Reservoir n (4*m)) (r : L.Seed) (t : ℝ) (i : Fin n) (H : History n),
      L.policy.decide (y,r) t i 0 H=false)
    (p : OuterLearnerInput m L) (t : ℝ) (i : Fin n) (H : History n) :
    (outerLearner m hm L).policy.decide p t i 0 H=false := by
  by_cases hB : outerPilotAt m hm L p=0
  · rw [outerLearner_decide_zero_pilot m hm L p hB]
    unfold outerRetainedObservation retainAboveTag
    split <;> norm_num
  · rw [outerLearner_decide_positive_pilot m hm L p hB,outerDisplayedObservation_zero]
    exact hZero _ _ _ _ _

lemma outerDisplayedHistory_none_iff (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (H : History n) (i : Fin n) :
    mapHistoryValuesBy (outerDisplayedObservation m hm L p) H i=none ↔ H i=none := by
  cases h : H i <;> simp only [mapHistoryValuesBy,mapObservationValues,h,reduceCtorEq,iff_self]

lemma outerDisplayedHistory_zero (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (H : History n) (i : Fin n) (t : ℝ) (h : H i=some (t,0)) :
    mapHistoryValuesBy (outerDisplayedObservation m hm L p) H i=some (t,0) := by
  simp only [mapHistoryValuesBy,mapObservationValues,h,outerDisplayedObservation_zero]

end ProphetSecretary.Statistics
