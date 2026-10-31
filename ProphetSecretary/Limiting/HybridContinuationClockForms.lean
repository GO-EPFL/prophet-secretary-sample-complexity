import ProphetSecretary.Limiting.HybridBellmanLossMeasurability
import ProphetSecretary.Limiting.VirtualUnseenState
import ProphetSecretary.Limiting.BernoulliClockState

/-!
# Clock forms of actual and finite-design continuation values

The actual retained state is determined by strict-past original clocks. Zero
values still create history records. Anonymous labels do not enter that
retained state. These identities expose the remaining-horizon value without
supplying the analytical clock vectors to an executed policy.
-/
open MeasureTheory Set
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n N q : ℕ}

lemma retainedUnseen_appendClock_history (u : Fin n → ℝ) (v : Fin N → ℝ) (t : ℝ) :
    retainedUnseen (Model.unseen (Model.history Finset.univ (fun _ => 0)
      (Model.ZeroSimulation.appendClocks u v) t)) =
      Model.unseen (Model.history Finset.univ (fun _ => 0) u t) := by
  change Model.retainedSet N (Model.unseen (Model.history Finset.univ (fun _ => 0)
    (Model.ZeroSimulation.appendClocks u v) t)) = _
  rw [retainedSet_unseen_history]
  simp only [Model.ZeroSimulation.appendClocks,Fin.addCases_left]

lemma FiniteIntensityHybridInstance.finiteContinuation_retained_clockForm
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c : ℝ)
    (u : Fin n → ℝ) (v : Fin N → ℝ) (i : Fin n) :
    B.finiteContinuationAtArrival w c (fun _ => 0) (Model.ZeroSimulation.appendClocks u v) (i.castAdd N) =
      ((B.restrictIndividuals (retainedClockState u (u i) (some i))).remainingHorizon (remainingTime (u i))).optimalScalarValue w (c*(remainingTime (u i) : ℝ)) := by
  have hTime : Model.ZeroSimulation.appendClocks u v (i.castAdd N) = u i := by
    simp only [Model.ZeroSimulation.appendClocks,Fin.addCases_left]
  unfold FiniteIntensityHybridInstance.finiteContinuationAtArrival
  rw [hTime]
  simp only [finiteHybridThreshold,Fin.addCases_left]
  rw [retainedUnseen_appendClock_history,B.valueHybridThreshold_mul_eq hw c]
  rfl

lemma FiniteIntensityHybridInstance.finiteContinuation_anonymous_clockForm
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c : ℝ)
    (u : Fin n → ℝ) (v : Fin N → ℝ) (j : Fin N) :
    B.finiteContinuationAtArrival w c (fun _ => 0) (Model.ZeroSimulation.appendClocks u v) (j.natAdd n) =
      ((B.restrictIndividuals (retainedClockState u (v j) none)).remainingHorizon (remainingTime (v j))).optimalScalarValue w (c*(remainingTime (v j) : ℝ)) := by
  have hTime : Model.ZeroSimulation.appendClocks u v (j.natAdd n) = v j := by
    simp only [Model.ZeroSimulation.appendClocks,Fin.addCases_right]
  unfold FiniteIntensityHybridInstance.finiteContinuationAtArrival
  rw [hTime]
  simp only [finiteHybridThreshold,Fin.addCases_right]
  rw [retainedUnseen_appendClock_history,B.valueHybridThreshold_mul_eq hw c]
  rfl

end ProphetSecretary.Limiting
