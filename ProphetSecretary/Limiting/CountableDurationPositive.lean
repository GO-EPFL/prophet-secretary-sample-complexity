import ProphetSecretary.Limiting.CountableCanonicalReach
import ProphetSecretary.Limiting.CountableClockNullSets

/-!
# Positive duration and canonical individual reach

Every present clock is strictly positive almost surely. An attained first
acceptance therefore has positive duration; no first acceptance has duration
one. Positivity includes empty positive clouds and zero-maximum auxiliary
instances. The canonical strict-reach comparison then gives positive reach
for every retained individual identity.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

lemma CountableRule.duration_positive (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, 0 < π.realizedDuration v := by
  filter_upwards [B.present_candidate_times_mem_Ioo ν] with v hv
  by_cases h : ∃ j, FirstAcceptance.Earliest π.codeAccepted codeTime v j
  · obtain ⟨j,hj⟩ := h
    change 0 < FirstAcceptance.stoppingTime π.codeAccepted codeTime v
    rw [FirstAcceptance.stoppingTime_of_earliest hj]
    exact (hv (candidateEnumeration.symm j) hj.1.1).1
  · rw [CountableRule.realizedDuration,FirstAcceptance.stoppingTime_of_no_first h]
    exact zero_lt_one

theorem CountableRule.meanDuration_positive (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    0 < ∫ v, π.realizedDuration v ∂B.completeWorldLaw ν := by
  have hp := π.duration_positive B ν
  have hSupport : Function.support π.realizedDuration =ᵐ[B.completeWorldLaw ν] (Set.univ : Set (CompleteWorld Seed)) := by
    filter_upwards [hp] with v hv
    apply propext
    exact ⟨fun _ => Set.mem_univ v,fun _ => ne_of_gt hv⟩
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le) (π.integrable_duration B ν hπ)).mpr
  rw [measure_congr hSupport,measure_univ]
  norm_num

end ProphetSecretary.Limiting.CountableInstance

namespace ProphetSecretary.Limiting.RandomizedCountablePolicy
open CountableInstance
variable {B : CountableInstance}

theorem expectedDuration_positive (π : RandomizedCountablePolicy B) : 0 < π.expectedDuration :=
  π.rule.meanDuration_positive π.measurable_rule B π.seedLaw

end ProphetSecretary.Limiting.RandomizedCountablePolicy

namespace ProphetSecretary.Limiting.CountableInstance

theorem valuePolicy_individualReachProbability_positive (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ) :
    0 < (B.valuePolicy hw hc).individualReachProbability i :=
  (B.valuePolicy hw hc).expectedDuration_positive.trans_le
    (B.valuePolicy_expectedDuration_le_individualReach hZero hw hc i)

end ProphetSecretary.Limiting.CountableInstance
