import ProphetSecretary.Statistics.CalibratedOuter.ConditionalBranch

/-!
# Retained and conditional reward means on the observed-data space

The fresh pilot block does not change the cutoff's retained prophet mean.
Nonnegative online rewards remain nonnegative after conditioning on outer data.
-/

open MeasureTheory Set
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model
variable {n : ℕ}

lemma outerConditionalReward_nonnegative (P : Instance n) (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (a : OuterObservedData n m) : 0≤outerConditionalReward P m hm L a := by
  apply integral_nonneg
  intro r
  exact ((outerLearner m hm L).frozenRandomizedPolicy (outerReassemble m L (a,r)).1 (outerReassemble m L (a,r)).2).expectedReward_nonnegative P

lemma integrable_outerObservedRetainedMaximum (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) :
    Integrable (fun a : OuterObservedData n m => (P.retainedAtTag (outerObservedCutoff m hm a)).expectedMaximum) (outerObservedDataLaw P m) :=
  (outerCutoff_retainedMaximum_integrable P hP m hm).comp_fst (outerPilotInputsLaw P m)

lemma integral_outerObservedRetainedMaximum (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) :
    (∫ a : OuterObservedData n m, (P.retainedAtTag (outerObservedCutoff m hm a)).expectedMaximum ∂outerObservedDataLaw P m)=
      ∫ p, (P.retainedAtTag (outerCutoff m hm p)).expectedMaximum ∂outerCutoffDataLaw P m := by
  have hInt := integrable_outerObservedRetainedMaximum P hP m hm
  have h := integral_prod (fun a : OuterObservedData n m => (P.retainedAtTag (outerObservedCutoff m hm a)).expectedMaximum) hInt
  simpa only [outerObservedCutoff,outerObservedDataLaw,integral_const,probReal_univ,one_smul] using h

lemma outerObservedRetainedMaximum_mean (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) :
    ((m:ℝ)/((m:ℝ)+1))*P.expectedMaximum≤
      ∫ a : OuterObservedData n m, (P.retainedAtTag (outerObservedCutoff m hm a)).expectedMaximum ∂outerObservedDataLaw P m := by
  rw [integral_outerObservedRetainedMaximum P hP m hm]
  exact outerCutoff_retainedMaximum_mean P hP m hm

end ProphetSecretary.Statistics.Calibration
