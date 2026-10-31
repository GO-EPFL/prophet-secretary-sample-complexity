import ProphetSecretary.Limiting.CountablePendingPrefix
import ProphetSecretary.Limiting.CountableClockReplacement
import ProphetSecretary.Limiting.CountableScalarObjectives

/-!
# General individual reach-duration comparison in the full countable model

The pending infimum is constructed from the same callbacks and is independent
of the candidate's value and clock. Exact prefix agreement and actual policy
admissibility identify reach with the pending event and compare actual duration
with the earlier of that infimum and the uniform candidate clock. This is the
full-countable general-policy part of `lem:monotone-reach` = `lem:strict-reach`.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def CountableRule.individualReachProbability (π : CountableRule Seed)
    (B : CountableInstance) (ν : Measure Seed) (i : ℕ) : ℝ :=
  (B.completeWorldLaw ν).real {v | v.2.2.1 i ≤ π.realizedDuration v}

lemma CountableRule.measurableSet_reachesIndividual (π : CountableRule Seed) (hπ : π.IsMeasurable) (i : ℕ) :
    MeasurableSet {v : CompleteWorld Seed | v.2.2.1 i ≤ π.realizedDuration v} :=
  measurableSet_le ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    (π.measurable_realizedDuration hπ)

lemma CountableRule.individualReachProbability_eq_mean_pending (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hAdm : π.Admissible B ν) (i : ℕ) :
    π.individualReachProbability B ν i=∫ v, π.pendingIndividualTime i v ∂B.completeWorldLaw ν := by
  have hClock := individualClock_completeWorld_measurePreserving B ν i
  have hUnit : ∀ᵐ v ∂B.completeWorldLaw ν, v.2.2.1 i ∈ Icc (0 : ℝ) 1 :=
    hClock.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)
  have hEq : {v : CompleteWorld Seed | v.2.2.1 i ≤ π.realizedDuration v} =ᵐ[B.completeWorldLaw ν]
      {v | v.2.2.1 i ≤ π.pendingIndividualTime i v} := by
    filter_upwards [hUnit,π.infimumDuration_eq_actual B ν hAdm] with v hv hRaw
    apply propext
    change v.2.2.1 i ≤ π.realizedDuration v ↔ v.2.2.1 i ≤ π.pendingIndividualTime i v
    rw [← hRaw]
    exact (π.le_pending_iff_le_infimum_before i v le_rfl hv.2).symm
  unfold CountableRule.individualReachProbability
  rw [measureReal_congr hEq]
  exact ProphetSecretary.Reach.reach_probability_eq_mean_pending (B.completeWorldLaw ν)
    (π.measurable_pendingIndividualTime hπ i) hClock.measurable hClock.map_eq
    (π.pendingIndividualTime_clock_independent hπ B ν i)
    (Eventually.of_forall (π.pendingIndividualTime_bounds i))

/-- Every admissible observable policy is covered, including policies accepting
zero offers and policies using arbitrary independent auxiliary randomness. -/
theorem CountableRule.individualReachProbability_le_twice_meanDuration (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hAdm : π.Admissible B ν) (i : ℕ) :
    π.individualReachProbability B ν i ≤ 2*∫ v, π.realizedDuration v ∂B.completeWorldLaw ν := by
  rw [π.individualReachProbability_eq_mean_pending hπ B ν hAdm i]
  have hClock := individualClock_completeWorld_measurePreserving B ν i
  apply ProphetSecretary.Reach.mean_pending_le_twice_duration (B.completeWorldLaw ν)
    (π.measurable_pendingIndividualTime hπ i) hClock.measurable
    (π.measurable_realizedDuration hπ).aestronglyMeasurable hClock.map_eq
    (π.pendingIndividualTime_clock_independent hπ B ν i)
    (Eventually.of_forall (π.pendingIndividualTime_bounds i)) (Eventually.of_forall π.duration_bounds)
  have hUnit : ∀ᵐ v ∂B.completeWorldLaw ν, v.2.2.1 i ∈ Icc (0 : ℝ) 1 :=
    hClock.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hUnit,π.infimumDuration_eq_actual B ν hAdm] with v hv hRaw
  rw [← hRaw]
  exact π.min_clock_pending_le_infimumDuration i v hv.2

end ProphetSecretary.Limiting.CountableInstance

namespace ProphetSecretary.Limiting.RandomizedCountablePolicy
open CountableInstance
variable {B : CountableInstance}

noncomputable def individualReachProbability (π : RandomizedCountablePolicy B) (i : ℕ) : ℝ :=
  π.rule.individualReachProbability B π.seedLaw i

theorem individualReachProbability_le_twice_expectedDuration (π : RandomizedCountablePolicy B) (i : ℕ) :
    π.individualReachProbability i ≤ 2*π.expectedDuration :=
  π.rule.individualReachProbability_le_twice_meanDuration π.measurable_rule B π.seedLaw π.admissible i

end ProphetSecretary.Limiting.RandomizedCountablePolicy
