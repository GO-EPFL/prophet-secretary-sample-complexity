import ProphetSecretary.Limiting.FirstAcceptanceInfimum
import ProphetSecretary.Limiting.CountablePendingWorld
import ProphetSecretary.Reach.IndependentReachBounds

/-!
# The constructed countable pending duration

The analytical infimum agrees almost surely with an admissible policy's actual
duration. In the auxiliary vector one individual remains pending until time
one. Its infimum is measurable, unit bounded, and jointly independent of that
individual's value and clock by actual product erasure. No admissibility is
postulated on the exceptional terminal-clock slice.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

noncomputable def CountableRule.infimumDuration (π : CountableRule Seed) : CompleteWorld Seed → ℝ :=
  FirstAcceptance.infimumTime π.codeAccepted codeTime

noncomputable def CountableRule.pendingIndividualTime (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed) : ℝ := π.infimumDuration (keepIndividualPending i v)

lemma CountableRule.infimumDuration_bounds (π : CountableRule Seed) (v : CompleteWorld Seed) :
    π.infimumDuration v ∈ Icc (0 : ℝ) 1 :=
  FirstAcceptance.infimumTime_bounds (fun _ h => h.2.1)

lemma CountableRule.pendingIndividualTime_bounds (π : CountableRule Seed) (i : ℕ) (v : CompleteWorld Seed) :
    π.pendingIndividualTime i v ∈ Icc (0 : ℝ) 1 := π.infimumDuration_bounds _

lemma CountableRule.le_infimumDuration_iff (π : CountableRule Seed) (v : CompleteWorld Seed) (t : ℝ) :
    t ≤ π.infimumDuration v ↔ t ≤ 1 ∧ ∀ j, π.codeAccepted v j → t ≤ codeTime v j :=
  FirstAcceptance.le_infimumTime_iff (fun _ h => h.2.1) t

variable [MeasurableSpace Seed]

lemma CountableRule.measurable_infimumDuration (π : CountableRule Seed) (hπ : π.IsMeasurable) :
    Measurable π.infimumDuration :=
  FirstAcceptance.measurable_infimumTime (π.measurableSet_codeAccepted hπ) measurable_codeTime

lemma CountableRule.measurable_pendingIndividualTime (π : CountableRule Seed) (hπ : π.IsMeasurable) (i : ℕ) :
    Measurable (π.pendingIndividualTime i) :=
  (π.measurable_infimumDuration hπ).comp (measurable_keepIndividualPending i)

lemma CountableRule.infimumDuration_eq_actual (π : CountableRule Seed)
    (B : CountableInstance) (ν : Measure Seed) (hπ : π.Admissible B ν) :
    π.infimumDuration =ᵐ[B.completeWorldLaw ν] π.realizedDuration := by
  filter_upwards [hπ] with v hv
  exact FirstAcceptance.infimumTime_eq_stoppingTime (fun _ h => h.2.1) hv

lemma CountableRule.pendingIndividualTime_candidate_independent (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    IndepFun (π.pendingIndividualTime i) (fun v : CompleteWorld Seed => (v.2.1 i,v.2.2.1 i))
      (B.completeWorldLaw ν) :=
  (keepIndividualPending_candidate_independent B ν i).comp (π.measurable_infimumDuration hπ) measurable_id

lemma CountableRule.pendingIndividualTime_clock_independent (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    IndepFun (π.pendingIndividualTime i) (fun v : CompleteWorld Seed => v.2.2.1 i) (B.completeWorldLaw ν) :=
  (π.pendingIndividualTime_candidate_independent hπ B ν i).comp measurable_id measurable_snd

lemma CountableRule.integrable_pendingIndividualTime (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    Integrable (π.pendingIndividualTime i) (B.completeWorldLaw ν) :=
  ProphetSecretary.Reach.integrable_of_ae_unit _ (π.measurable_pendingIndividualTime hπ i).aestronglyMeasurable
    (Eventually.of_forall (π.pendingIndividualTime_bounds i))

lemma CountableRule.integrable_infimumDuration (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    Integrable π.infimumDuration (B.completeWorldLaw ν) :=
  ProphetSecretary.Reach.integrable_of_ae_unit _ (π.measurable_infimumDuration hπ).aestronglyMeasurable
    (Eventually.of_forall π.infimumDuration_bounds)

end ProphetSecretary.Limiting.CountableInstance
