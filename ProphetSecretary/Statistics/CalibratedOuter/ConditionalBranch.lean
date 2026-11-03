import ProphetSecretary.Statistics.CalibratedOuter.LearnerRewardConditioning
import ProphetSecretary.Statistics.CalibratedOuter.FixedSimulation
import ProphetSecretary.Statistics.CalibratedOuter.LearnerExecution
import ProphetSecretary.Model.PolicyRewardConditioning

/-!
# Identifying the actual conditional outer branches

The actual observed cutoff and pilot determine a scale before the fresh inner
factor is used. With those data fixed, the positive-pilot conditional reward is
exactly the reward of the fixed raw response experiment.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def outerObservedCutoff (m : ℕ) (hm : 1≤m) (a : OuterObservedData n m) : ℝ × ℝ := outerCutoff m hm a.1

noncomputable def outerObservedPilot (m : ℕ) (hm : 1≤m) (a : OuterObservedData n m) : ℝ :=
  outerPilotValue m hm (outerObservedCutoff m hm a) a.2

lemma outerObservedPilot_nonnegative (m : ℕ) (hm : 1≤m) (a : OuterObservedData n m) :
    0≤outerObservedPilot m hm a := outerPilotValue_nonnegative m hm _ _

noncomputable def outerObservedCap (m : ℕ) (hm : 1≤m) (a : OuterObservedData n m) : ℝ≥0 :=
  Instance.outerPilotCap ⟨outerObservedPilot m hm a,outerObservedPilot_nonnegative m hm a⟩

lemma outerCutoffInput_reassemble (m : ℕ) (L : Learner n (2*m)) (a : OuterObservedData n m) (r : OuterFreshInput m L) :
    outerCutoffInput m L (outerReassemble m L (a,r))=a.1 := by
  simp only [outerCutoffInput,outerReassemble,MeasurableEquiv.apply_symm_apply]

lemma outerPilotInput_reassemble (m : ℕ) (L : Learner n (2*m)) (a : OuterObservedData n m) (r : OuterFreshInput m L) :
    outerPilotInput m L (outerReassemble m L (a,r))=a.2 := by
  simp only [outerPilotInput,outerReassemble,MeasurableEquiv.apply_symm_apply]

lemma outerInnerInput_reassemble (m : ℕ) (L : Learner n (2*m)) (a : OuterObservedData n m) (r : OuterFreshInput m L) :
    outerInnerInput m L (outerReassemble m L (a,r))=r.1 := by
  simp only [outerInnerInput,outerReassemble,MeasurableEquiv.apply_symm_apply]

lemma outerCutoffAt_reassemble (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) (a : OuterObservedData n m) (r : OuterFreshInput m L) :
    outerCutoffAt m hm L (outerReassemble m L (a,r))=outerObservedCutoff m hm a := by
  rw [outerCutoffAt,outerCutoffInput_reassemble]
  rfl

lemma outerPilotAt_reassemble (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) (a : OuterObservedData n m) (r : OuterFreshInput m L) :
    outerPilotAt m hm L (outerReassemble m L (a,r))=outerObservedPilot m hm a := by
  rw [outerPilotAt,outerCutoffAt_reassemble,outerPilotInput_reassemble]
  rfl

lemma outerInnerTraining_reassemble (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) (a : OuterObservedData n m) (r : OuterFreshInput m L) :
    outerInnerTraining m hm L (outerReassemble m L (a,r))=
      outerTransformedReservoir m (outerObservedCutoff m hm a) (outerObservedCap m hm a) r.1 := by
  rw [outerInnerTraining,outerCutoffAt_reassemble,outerPilotAt_reassemble,outerInnerInput_reassemble]
  rfl

lemma outerInnerPolicySeed_reassemble (m : ℕ) (L : Learner n (2*m)) (a : OuterObservedData n m) (r : OuterFreshInput m L) :
    outerInnerPolicySeed m L (outerReassemble m L (a,r))=r.2.2 := rfl

lemma outerDisplayedObservation_reassemble (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) (a : OuterObservedData n m) (r : OuterFreshInput m L) :
    outerDisplayedObservation m hm L (outerReassemble m L (a,r))=
      (fun i x => outerMeshDisplay m (outerObservedCap m hm a) (retainAboveTag (outerObservedCutoff m hm a) (x,r.2.1 i))) := by
  funext i x
  unfold outerDisplayedObservation outerRetainedObservation
  rw [outerPilotAt_reassemble,outerCutoffAt_reassemble]
  rfl

lemma outerFrozenReward_positive_pilot (P : Instance n) (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (a : OuterObservedData n m) (hB : 0<outerObservedPilot m hm a) (r : OuterFreshInput m L) :
    outerFrozenReward P m hm L (outerReassemble m L (a,r))=
      ∫ ω : World n Unit, (outerFixedRawResponse P m (outerObservedCutoff m hm a) (outerObservedCap m hm a) L).rule.reward
        r Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()) := by
  have hB' : outerPilotAt m hm L (outerReassemble m L (a,r))≠0 := by
    rw [outerPilotAt_reassemble]
    exact ne_of_gt hB
  have hRule : (outerLearner m hm L).frozenRule (outerReassemble m L (a,r)).1 (outerReassemble m L (a,r)).2=
      (outerFixedRawResponse P m (outerObservedCutoff m hm a) (outerObservedCap m hm a) L).rule.pullbackSeed (fun _ : Unit => r) := by
    apply congrArg Policy.mk
    funext s t i x H
    change (outerLearner m hm L).policy.decide (outerReassemble m L (a,r)) t i x H=
      L.policy.decide (outerTransformedReservoir m (outerObservedCutoff m hm a) (outerObservedCap m hm a) r.1,r.2.2) t i
        (outerMeshDisplay m (outerObservedCap m hm a) (retainAboveTag (outerObservedCutoff m hm a) (x,r.2.1 i)))
        (mapHistoryValuesBy (fun j v => outerMeshDisplay m (outerObservedCap m hm a) (retainAboveTag (outerObservedCutoff m hm a) (v,r.2.1 j))) H)
    rw [outerLearner_decide_positive_pilot m hm L _ hB',outerInnerTraining_reassemble,
      outerInnerPolicySeed_reassemble,outerDisplayedObservation_reassemble]
  change (∫ ω : World n Unit, ((outerLearner m hm L).frozenRule (outerReassemble m L (a,r)).1 (outerReassemble m L (a,r)).2).reward
    ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()))=_
  rw [hRule]
  rfl

/-- The positive-pilot section of the actual learner's conditional expectation. -/
theorem outerConditionalReward_positive_pilot (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) (a : OuterObservedData n m) (hB : 0<outerObservedPilot m hm a) :
    outerConditionalReward P m hm L a=
      (outerFixedRawResponse P m (outerObservedCutoff m hm a) (outerObservedCap m hm a) L).expectedReward P := by
  unfold outerConditionalReward
  simp_rw [outerFrozenReward_positive_pilot P m hm L a hB]
  exact (outerFixedRawResponse P m (outerObservedCutoff m hm a) (outerObservedCap m hm a) L).integral_seedFirstReward P hP

end ProphetSecretary.Statistics.Calibration
