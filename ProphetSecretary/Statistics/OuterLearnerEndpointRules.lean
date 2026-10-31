import ProphetSecretary.Statistics.OuterLearnerExecution

/-!
# Endpoint rules on every outer training outcome

The bounded learner's pointwise endpoint rules transfer to every actual outer
observation, including zero displays caused by cutoff or downward rounding.
These identities do not discard null or impossible training outcomes.
-/

open MeasureTheory
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

lemma outerLearner_positive_rejects_zero_display (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (hZero : ∀ (y : Reservoir n (4*m)) (r : L.Seed) (t : ℝ) (i : Fin n) (H : History n),
      L.policy.decide (y,r) t i 0 H=false)
    (p : OuterLearnerInput m L) (hB : outerPilotAt m hm L p≠0)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) (hDisplay : outerDisplayedObservation m hm L p i x=0) :
    (outerLearner m hm L).policy.decide p t i x H=false := by
  rw [outerLearner_decide_positive_pilot m hm L p hB,hDisplay]
  exact hZero _ _ _ _ _

lemma outerLearner_positive_accepts_cap_display (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (hOne : ∀ (y : Reservoir n (4*m)) (r : L.Seed) (t : ℝ) (i : Fin n) (H : History n),
      L.policy.decide (y,r) t i 1 H=true)
    (p : OuterLearnerInput m L) (hB : outerPilotAt m hm L p≠0)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) (hDisplay : outerDisplayedObservation m hm L p i x=1) :
    (outerLearner m hm L).policy.decide p t i x H=true := by
  rw [outerLearner_decide_positive_pilot m hm L p hB,hDisplay]
  exact hOne _ _ _ _ _

lemma outerLearner_zero_pilot_rejects_zero_retained (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (p : OuterLearnerInput m L) (hB : outerPilotAt m hm L p=0)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) (hRetained : outerRetainedObservation m hm L p i x=0) :
    (outerLearner m hm L).policy.decide p t i x H=false := by
  rw [outerLearner_decide_zero_pilot m hm L p hB,hRetained]
  norm_num

end ProphetSecretary.Statistics
