import ProphetSecretary.Limiting.OmissionActionAgreement
import ProphetSecretary.Limiting.FilteredAcceptedAtoms

/-!
# The simulator deletes only low accepted occurrences

Its accepted-point measure is below the original one. Above any level d at
least the reserve, the two measures agree when omitted individual values and
low-cloud marks are at most d. This includes analytical acceptances after the
old stopping point, and permits infinite total accepted mass.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace ProphetSecretary.Limiting
open CountableInstance

variable {Seed : Type*}

noncomputable def omissionOldAccepted (π : CountableRule Seed) (q : OmissionExecutionWorld Seed) : Measure Point :=
  FirstAcceptance.pointMeasure π.codeAccepted codeTime codeValue (oldExecutionWorld q)

noncomputable def omissionNewAccepted (B : CountableInstance) (π : CountableRule Seed) (N : ℕ)
    (q : OmissionExecutionWorld Seed) : Measure Point :=
  ((simulateOmittedRule B π N).acceptedPointMeasure (hybridObserverWorld (newExecutionWorld N q)) : Measure Point)

lemma omissionNewAccepted_normalized (B : CountableInstance) (π : CountableRule Seed) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b : ℝ} (hlow : LowCloudRegular B b q.1.1.2) :
    omissionNewAccepted B π N q =
      (∑ i : Fin N, if (B.terminal : ℝ) < (oldExecutionWorld q).2.1 i.val ∧
        π.individualActionAccepted (oldExecutionWorld q) i.val then
          Measure.dirac ((oldExecutionWorld q).2.2.1 i.val,(oldExecutionWorld q).2.1 i.val) else 0) +
      (countingMeasure q.1.1.1).restrict ({p : Point | (B.terminal : ℝ) < p.2} ∩
        {p | π.anonymousActionAccepted (oldExecutionWorld q) p}) := by
  have hSet : {p | (simulateOmittedRule B π N).anonymousMeasureAccepted
      (hybridObserverWorld (newExecutionWorld N q)) p} =
      {p : Point | (B.terminal : ℝ) < p.2} ∩ {p | π.anonymousActionAccepted (oldExecutionWorld q) p} := by
    ext p
    exact simulated_anonymousAccepted_iff B π N q hcount hlow p
  change (∑ i : Fin N, if (simulateOmittedRule B π N).individualMeasureAccepted
      (hybridObserverWorld (newExecutionWorld N q)) i then
        Measure.dirac ((newExecutionWorld N q).2.2.1 i,(newExecutionWorld N q).2.1 i) else 0) +
      (configurationFiniteMeasure q.1.1.1 : Measure Point).restrict
        {p | (simulateOmittedRule B π N).anonymousMeasureAccepted (hybridObserverWorld (newExecutionWorld N q)) p} = _
  rw [configurationFiniteMeasure_coe,hSet]
  apply congrArg (fun M : Measure Point => M + (countingMeasure q.1.1.1).restrict
    ({p : Point | (B.terminal : ℝ) < p.2} ∩ {p | π.anonymousActionAccepted (oldExecutionWorld q) p}))
  apply Finset.sum_congr rfl
  intro i _
  change (if (simulateOmittedRule B π N).individualMeasureAccepted (hybridObserverWorld (newExecutionWorld N q)) i then
    Measure.dirac ((oldExecutionWorld q).2.2.1 i.val,(oldExecutionWorld q).2.1 i.val) else 0) = _
  simp only [simulated_individualAccepted_iff B π N q hcount hlow i]

variable [MeasurableSpace Seed]

lemma omissionOldAccepted_normalized (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1) :
    omissionOldAccepted π q =
      Measure.sum (fun i => if π.individualActionAccepted (oldExecutionWorld q) i then
        Measure.dirac ((oldExecutionWorld q).2.2.1 i,(oldExecutionWorld q).2.1 i) else 0) +
      (countingMeasure q.1.1.1+q.1.1.2).restrict {p | π.anonymousActionAccepted (oldExecutionWorld q) p} := by
  rw [omissionOldAccepted,π.pointMeasure_eq_individuals_add_cloud hπ (oldExecutionWorld q)]
  exact congrArg (fun M : Measure Point =>
    Measure.sum (fun i => if π.individualActionAccepted (oldExecutionWorld q) i then
      Measure.dirac ((oldExecutionWorld q).2.2.1 i,(oldExecutionWorld q).2.1 i) else 0) +
      M.restrict {p | π.anonymousActionAccepted (oldExecutionWorld q) p}) hcount

lemma omissionNewAccepted_le (B : CountableInstance) (π : CountableRule Seed) (hπ : π.IsMeasurable) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b : ℝ} (hlow : LowCloudRegular B b q.1.1.2) : omissionNewAccepted B π N q ≤ omissionOldAccepted π q := by
  rw [omissionNewAccepted_normalized B π N q hcount hlow,omissionOldAccepted_normalized π hπ q hcount]
  apply add_le_add
  · apply finitePrefix_measure_le
    intro i
    exact acceptedAtom_gate_le ((oldExecutionWorld q).2.2.1 i.val,(oldExecutionWorld q).2.1 i.val)
      (π.individualActionAccepted (oldExecutionWorld q) i.val) B.terminal
  · exact gatedCloud_le _ _ _ _

lemma omissionNewAccepted_high_eq (B : CountableInstance) (π : CountableRule Seed) (hπ : π.IsMeasurable) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b d : ℝ} (hlow : LowCloudRegular B b q.1.1.2) (had : (B.terminal : ℝ) ≤ d) (hbd : b ≤ d)
    (hTail : ∀ j, N ≤ j → (oldExecutionWorld q).2.1 j ≤ d) :
    (omissionNewAccepted B π N q).restrict {p : Point | d < p.2} =
      (omissionOldAccepted π q).restrict {p : Point | d < p.2} := by
  rw [omissionNewAccepted_normalized B π N q hcount hlow,omissionOldAccepted_normalized π hπ q hcount,
    Measure.restrict_add,Measure.restrict_add]
  apply congrArg₂ (fun α β : Measure Point => α + β)
  · apply finitePrefix_restrict_eq N _ _ (measurableSet_lt measurable_const measurable_snd)
    · intro i
      exact acceptedAtom_gate_high_eq ((oldExecutionWorld q).2.2.1 i.val,(oldExecutionWorld q).2.1 i.val)
        (π.individualActionAccepted (oldExecutionWorld q) i.val) had
    · intro j hj
      exact acceptedAtom_high_zero ((oldExecutionWorld q).2.2.1 j,(oldExecutionWorld q).2.1 j)
        (π.individualActionAccepted (oldExecutionWorld q) j) (hTail j hj)
  · have hLow0 : q.1.1.2.restrict {p : Point | d < p.2} = 0 := by
      apply Measure.restrict_eq_zero.mpr
      apply measure_eq_zero_iff_ae_notMem.mpr
      exact hlow.marks_le.mono (fun p hp => not_lt_of_ge (hp.trans hbd))
    exact gatedCloud_high_eq _ _ _ had hLow0

end ProphetSecretary.Limiting
