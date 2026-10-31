import ProphetSecretary.Limiting.CountablePendingDuration
import ProphetSecretary.Limiting.CountablePendingPrefix
import ProphetSecretary.Limiting.CountableScalarObjectives

/-!
# Selection of an individual in the actual countable execution

Selection is the earliest accepted code, using the existing null-tie convention.
The indicator is measurable and bounded. Whenever an individual is selected,
both the analytical accepted-time infimum and the executed duration equal its
arrival clock; no admissibility assumption on an auxiliary clock slice is used.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def CountableRule.SelectsIndividual (π : CountableRule Seed) (v : CompleteWorld Seed) (i : ℕ) : Prop :=
  FirstAcceptance.Earliest π.codeAccepted codeTime v (candidateEnumeration (Sum.inl i))

noncomputable def CountableRule.individualSelectionIndicator (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed) : ℝ := if π.SelectsIndividual v i then 1 else 0

lemma CountableRule.individualSelectionIndicator_mem_unit (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed) : π.individualSelectionIndicator i v ∈ Icc (0 : ℝ) 1 := by
  unfold CountableRule.individualSelectionIndicator
  split_ifs <;> norm_num

lemma CountableRule.infimumDuration_eq_clock_of_selectsIndividual (π : CountableRule Seed)
    (i : ℕ) (v : CompleteWorld Seed) (hSel : π.SelectsIndividual v i) :
    π.infimumDuration v=v.2.2.1 i :=
  (FirstAcceptance.infimumTime_of_earliest (fun _ h => h.2.1) hSel).trans (codeTime_individual i v)

lemma CountableRule.duration_eq_clock_of_selectsIndividual (π : CountableRule Seed)
    (i : ℕ) (v : CompleteWorld Seed) (hSel : π.SelectsIndividual v i) :
    π.realizedDuration v=v.2.2.1 i :=
  (FirstAcceptance.stoppingTime_of_earliest hSel).trans (codeTime_individual i v)

variable [MeasurableSpace Seed]

lemma CountableRule.measurableSet_selectsIndividual (π : CountableRule Seed) (hπ : π.IsMeasurable) (i : ℕ) :
    MeasurableSet {v | π.SelectsIndividual v i} :=
  FirstAcceptance.measurableSet_earliest (π.measurableSet_codeAccepted hπ) measurable_codeTime _

lemma CountableRule.measurable_individualSelectionIndicator (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (i : ℕ) : Measurable (π.individualSelectionIndicator i) :=
  Measurable.ite (π.measurableSet_selectsIndividual hπ i) measurable_const measurable_const

noncomputable def CountableRule.individualSelectionProbability (π : CountableRule Seed)
    (B : CountableInstance) (ν : Measure Seed) (i : ℕ) : ℝ :=
  (B.completeWorldLaw ν).real {v | π.SelectsIndividual v i}

lemma CountableRule.integrable_individualSelectionIndicator (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    Integrable (π.individualSelectionIndicator i) (B.completeWorldLaw ν) :=
  ProphetSecretary.Reach.integrable_of_ae_unit _ (π.measurable_individualSelectionIndicator hπ i).aestronglyMeasurable
    (Eventually.of_forall (π.individualSelectionIndicator_mem_unit i))

lemma CountableRule.integral_individualSelectionIndicator (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) (i : ℕ) :
    (∫ v, π.individualSelectionIndicator i v ∂B.completeWorldLaw ν)=π.individualSelectionProbability B ν i := by
  simpa only [CountableRule.individualSelectionIndicator,CountableRule.individualSelectionProbability,
    Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply] using
    (integral_indicator_one (μ := B.completeWorldLaw ν) (π.measurableSet_selectsIndividual hπ i))

end ProphetSecretary.Limiting.CountableInstance

namespace ProphetSecretary.Limiting.RandomizedCountablePolicy
open CountableInstance
variable {B : CountableInstance}

noncomputable def individualSelectionProbability (π : RandomizedCountablePolicy B) (i : ℕ) : ℝ :=
  π.rule.individualSelectionProbability B π.seedLaw i

end ProphetSecretary.Limiting.RandomizedCountablePolicy
