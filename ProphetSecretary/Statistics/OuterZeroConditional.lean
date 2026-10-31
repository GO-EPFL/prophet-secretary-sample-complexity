import ProphetSecretary.Statistics.OuterConditionalBranch
import ProphetSecretary.Statistics.OuterZeroResponse

/-!
# The actual zero-pilot conditional reward

When the observed pilot is zero, all unused fresh inner data are integrated out
and the online branch is precisely first positive tagged retention.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

lemma outerFrozenReward_zero_pilot (P : Instance n) (m : ℕ) (hm : 1≤m) (L : Learner n (4*m))
    (a : OuterObservedData n m) (hB : outerObservedPilot m hm a=0) (r : OuterFreshInput m L) :
    outerFrozenReward P m hm L (outerReassemble m L (a,r))=
      ∫ ω : World n Unit, (outerFixedZeroResponse P m (outerObservedCutoff m hm a) L).rule.reward
        r Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()) := by
  have hB' : outerPilotAt m hm L (outerReassemble m L (a,r))=0 := by
    rw [outerPilotAt_reassemble]
    exact hB
  have hRule : (outerLearner m hm L).frozenRule (outerReassemble m L (a,r)).1 (outerReassemble m L (a,r)).2=
      (outerFixedZeroResponse P m (outerObservedCutoff m hm a) L).rule.pullbackSeed (fun _ : Unit => r) := by
    apply congrArg Policy.mk
    funext s t i x H
    change (outerLearner m hm L).policy.decide (outerReassemble m L (a,r)) t i x H=
      (outerFixedZeroResponse P m (outerObservedCutoff m hm a) L).rule.decide r t i x H
    rw [outerLearner_decide_zero_pilot m hm L _ hB',outerFixedZeroResponse_decide]
    unfold outerRetainedObservation
    rw [outerCutoffAt_reassemble]
    rfl
  change (∫ ω : World n Unit, ((outerLearner m hm L).frozenRule (outerReassemble m L (a,r)).1 (outerReassemble m L (a,r)).2).reward
    ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()))=_
  rw [hRule]
  rfl

theorem outerConditionalReward_zero_pilot (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) (a : OuterObservedData n m) (hB : outerObservedPilot m hm a=0) :
    outerConditionalReward P m hm L a=
      (outerFixedZeroResponse P m (outerObservedCutoff m hm a) L).expectedReward P := by
  unfold outerConditionalReward
  simp_rw [outerFrozenReward_zero_pilot P m hm L a hB]
  exact (outerFixedZeroResponse P m (outerObservedCutoff m hm a) L).integral_seedFirstReward P hP

theorem outerConditionalReward_zero_pilot_ge (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (L : Learner n (4*m)) (a : OuterObservedData n m) (hB : outerObservedPilot m hm a=0)
    (hStrict : (P.retainedAtTag (outerObservedCutoff m hm a)).valuesLaw.real {x | 0<Instance.maximum x}≤3/1000) :
    (997/1000:ℝ)*(P.retainedAtTag (outerObservedCutoff m hm a)).expectedMaximum≤outerConditionalReward P m hm L a := by
  rw [outerConditionalReward_zero_pilot P hP m hm L a hB]
  exact outerFixedZeroResponse_reward_ge P hP m (outerObservedCutoff m hm a) L hStrict

end ProphetSecretary.Statistics
