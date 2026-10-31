import ProphetSecretary.Limiting.OmissionExecutionCoupling
import ProphetSecretary.Limiting.FullAcceptedMeasure
import ProphetSecretary.Limiting.HybridAcceptedMeasure

/-!
# The simulator feeds the original callbacks exactly their allowed past

The histories agree on the analytical coupling. The simulator additionally
rejects values at most the reserve; it preserves all retained identities and
virtual omitted observations, including zero-valued arrivals.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

variable {Seed : Type*}

lemma omission_individualHistory_agrees (N : ℕ) (q : OmissionExecutionWorld Seed) (t : ℝ) :
    augmentIndividualHistory N
      (Model.history Finset.univ (newExecutionWorld N q).2.1 (newExecutionWorld N q).2.2.1 t)
      (newExecutionWorld N q).2.2.2.2.1 (newExecutionWorld N q).2.2.2.2.2 t =
        individualHistory (oldExecutionWorld q).2.1 (oldExecutionWorld q).2.2.1 t := by
  rw [augmentIndividualHistory_actual]
  change individualHistory
    (splicePrefix (splitCoordinates N q.2.1).1 (splitCoordinates N q.2.1).2)
    (splicePrefix (splitCoordinates N q.2.2.1).1 (splitCoordinates N q.2.2.1).2) t = _
  rw [splice_splitCoordinates,splice_splitCoordinates]
  rfl

lemma omission_anonymousHistory_agrees (B : CountableInstance) (q : OmissionExecutionWorld Seed)
    (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b : ℝ} (hlow : LowCloudRegular B b q.1.1.2) (t : ℝ) :
    anonymousHistory q.1.2 t = observedHistory q.1.1.1 t + omittedCloudPast B q.1.1.2 t := by
  rw [anonymousHistory_eq_countingRestriction,hcount,joinedCloud,Measure.restrict_add,
    ← observedHistory_eq_countingRestriction,hlow.past_eq t]

lemma simulated_individualAction_agrees (B : CountableInstance) (π : CountableRule Seed) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b : ℝ} (hlow : LowCloudRegular B b q.1.1.2) (i : Fin N) :
    (simulateOmittedRule B π N).individualMeasureAction (hybridObserverWorld (newExecutionWorld N q)) i =
      if (B.terminal : ℝ) < (oldExecutionWorld q).2.1 i.val then
        π.candidateAction (oldExecutionWorld q) (Sum.inl i.val) else false := by
  change (if (B.terminal : ℝ) < (oldExecutionWorld q).2.1 i.val then
    π.individual (oldExecutionWorld q).2.2.2 ((oldExecutionWorld q).2.2.1 i.val) i.val
      ((oldExecutionWorld q).2.1 i.val)
      (augmentIndividualHistory N
        (Model.history Finset.univ (newExecutionWorld N q).2.1 (newExecutionWorld N q).2.2.1
          ((oldExecutionWorld q).2.2.1 i.val))
        (newExecutionWorld N q).2.2.2.2.1 (newExecutionWorld N q).2.2.2.2.2 ((oldExecutionWorld q).2.2.1 i.val))
      (finitePast (configurationFiniteMeasure q.1.1.1) ((oldExecutionWorld q).2.2.1 i.val) +
        omittedCloudPast B q.1.1.2 ((oldExecutionWorld q).2.2.1 i.val)) else false) = _
  rw [configurationFinitePast,omission_individualHistory_agrees,
    ← omission_anonymousHistory_agrees B q hcount hlow]
  rfl

lemma simulated_anonymousAction_agrees (B : CountableInstance) (π : CountableRule Seed) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b : ℝ} (hlow : LowCloudRegular B b q.1.1.2) (p : Point) :
    (simulateOmittedRule B π N).anonymousMeasureAction (hybridObserverWorld (newExecutionWorld N q)) p =
      if (B.terminal : ℝ) < p.2 then π.poisson (oldExecutionWorld q).2.2.2 p.1 p.2
        (individualHistory (oldExecutionWorld q).2.1 (oldExecutionWorld q).2.2.1 p.1)
        (anonymousHistory (oldExecutionWorld q).1 p.1) else false := by
  change (if (B.terminal : ℝ) < p.2 then π.poisson (oldExecutionWorld q).2.2.2 p.1 p.2
    (augmentIndividualHistory N (Model.history Finset.univ (newExecutionWorld N q).2.1
      (newExecutionWorld N q).2.2.1 p.1) (newExecutionWorld N q).2.2.2.2.1 (newExecutionWorld N q).2.2.2.2.2 p.1)
    (finitePast (configurationFiniteMeasure q.1.1.1) p.1 + omittedCloudPast B q.1.1.2 p.1) else false) = _
  rw [configurationFinitePast,omission_individualHistory_agrees,
    ← omission_anonymousHistory_agrees B q hcount hlow]
  rfl

lemma simulated_individualAccepted_iff (B : CountableInstance) (π : CountableRule Seed) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b : ℝ} (hlow : LowCloudRegular B b q.1.1.2) (i : Fin N) :
    (simulateOmittedRule B π N).individualMeasureAccepted (hybridObserverWorld (newExecutionWorld N q)) i ↔
      (B.terminal : ℝ) < (oldExecutionWorld q).2.1 i.val ∧ π.individualActionAccepted (oldExecutionWorld q) i.val := by
  unfold HybridRule.individualMeasureAccepted
  rw [simulated_individualAction_agrees B π N q hcount hlow i]
  by_cases hg : (B.terminal : ℝ) < (oldExecutionWorld q).2.1 i.val
  · change (B.terminal : ℝ) < q.2.1 i.val at hg
    simp [hg,CountableRule.individualActionAccepted,CountableRule.candidateAction,candidatePoint,
      hybridObserverWorld,newExecutionWorld,omissionNewWorld,splitIndividualsWorld,splitCoordinates,oldExecutionWorld]
  · simp [hg]

lemma simulated_anonymousAccepted_iff (B : CountableInstance) (π : CountableRule Seed) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b : ℝ} (hlow : LowCloudRegular B b q.1.1.2) (p : Point) :
    (simulateOmittedRule B π N).anonymousMeasureAccepted (hybridObserverWorld (newExecutionWorld N q)) p ↔
      (B.terminal : ℝ) < p.2 ∧ π.anonymousActionAccepted (oldExecutionWorld q) p := by
  unfold HybridRule.anonymousMeasureAccepted
  rw [simulated_anonymousAction_agrees B π N q hcount hlow p]
  by_cases hg : (B.terminal : ℝ) < p.2
  · simp [hg,CountableRule.anonymousActionAccepted]
  · simp [hg]

end ProphetSecretary.Limiting
