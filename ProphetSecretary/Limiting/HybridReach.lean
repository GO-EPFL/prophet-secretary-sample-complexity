import ProphetSecretary.Limiting.HybridRetainedPending
import ProphetSecretary.Limiting.HybridScalarObjectives

/-!
# General retained-variable reach bound in a finite-intensity hybrid instance

This extends the universal qᵢ≤2Eτ comparison to each retained identity while
anonymous Poisson arrivals are observed by one common count-hidden hybrid rule.
The auxiliary execution and joint value-clock independence are constructed in
`HybridRetainedPending`; no analytical count is supplied to a policy callback.
Infinite-intensity and countably retained limits remain separate obligations.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma individualClock_measurePreserving (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    MeasurePreserving (fun v : HybridWorld n Seed => v.2.2.1 i) (hybridWorldLaw P μ ν) Model.Instance.uniformClock :=
  (P.world_clock_measurePreserving ν i).comp measurePreserving_snd

omit [MeasurableSpace Seed] in
lemma HybridRule.reachesIndividual_iff_le_duration (π : HybridRule n Seed) (i : Fin n)
    (v : HybridWorld n Seed) :
    π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i ↔ v.2.2.1 i ≤ π.realizedDuration v := by
  simp only [HybridRule.ReachesIndividual,Model.Policy.Reaches,HybridRule.realizedDuration,
    HybridRule.stoppingTime,combinedClocks,Fin.addCases_left]

omit [MeasurableSpace Seed] in
lemma HybridRule.reachesIndividual_iff_le_pending (π : HybridRule n Seed) (i : Fin n)
    (v : HybridWorld n Seed) (hu : v.2.2.1 i ≤ 1) :
    π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i ↔ v.2.2.1 i ≤ π.pendingIndividualTime i v := by
  have hi : combinedClocks v.2.2.1 v.1.2 (i.castAdd v.1.1) ≤ 1 := by
    simpa only [combinedClocks,Fin.addCases_left] using hu
  have h := (π.asFinitePolicy v.1.1).reaches_iff_le_pendingTime v.2.2.2
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) (i.castAdd v.1.1) hi
  simpa only [HybridRule.ReachesIndividual,HybridRule.pendingIndividualTime,combinedClocks,Fin.addCases_left] using h

lemma HybridRule.measurableSet_reachesIndividual (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n) :
    MeasurableSet {v : HybridWorld n Seed | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i} := by
  have hu : Measurable (fun v : HybridWorld n Seed => v.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have heq : {v : HybridWorld n Seed | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i} =
      {v | v.2.2.1 i ≤ π.realizedDuration v} := by
    ext v
    exact π.reachesIndividual_iff_le_duration i v
  rw [heq]
  exact measurableSet_le hu (π.measurable_realizedDuration hπ)

noncomputable def HybridRule.individualReachProbability (π : HybridRule n Seed) (P : Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) (i : Fin n) : ℝ :=
  (hybridWorldLaw P μ ν).real {v : HybridWorld n Seed | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i}

lemma HybridRule.integrable_retainedReachIndicator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Integrable (fun v : HybridWorld n Seed => if π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i then (1 : ℝ) else 0)
      (hybridWorldLaw P μ ν) := by
  apply Integrable.of_bound (Measurable.ite (π.measurableSet_reachesIndividual hπ i) measurable_const measurable_const).aestronglyMeasurable 1
  exact Eventually.of_forall fun v => by
    change ‖if _ then (1 : ℝ) else 0‖ ≤ 1
    split_ifs <;> norm_num

lemma HybridRule.individualReachProbability_mem_unit (π : HybridRule n Seed)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    π.individualReachProbability P μ ν i ∈ Icc (0 : ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩

lemma HybridRule.integral_retainedReachIndicator_eq_probability (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (∫ v : HybridWorld n Seed, if π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i then (1 : ℝ) else 0
      ∂hybridWorldLaw P μ ν) = π.individualReachProbability P μ ν i := by
  simpa only [HybridRule.individualReachProbability,Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply] using
    (integral_indicator_one (μ := hybridWorldLaw P μ ν) (π.measurableSet_reachesIndividual hπ i))

/-- Actual retained reach equals the mean of the constructed pending time. -/
theorem HybridRule.individualReachProbability_eq_mean_pending (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    π.individualReachProbability P μ ν i = ∫ v, π.pendingIndividualTime i v ∂hybridWorldLaw P μ ν := by
  have hclock := (Measure.quasiMeasurePreserving_snd (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (P.world_clocks_mem_unitInterval ν)
  have heq : {v : HybridWorld n Seed | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i} =ᵐ[hybridWorldLaw P μ ν]
      {v | v.2.2.1 i ≤ π.pendingIndividualTime i v} := by
    filter_upwards [hclock] with v hv
    exact propext (π.reachesIndividual_iff_le_pending i v (hv i).2)
  unfold individualReachProbability
  rw [measureReal_congr heq]
  exact ProphetSecretary.Reach.reach_probability_eq_mean_pending (hybridWorldLaw P μ ν)
    (π.measurable_pendingIndividualTime hπ i) (individualClock_measurePreserving P μ ν i).measurable
    (individualClock_measurePreserving P μ ν i).map_eq
    (π.pendingIndividualTime_clock_independent hπ P μ ν i) (π.pendingIndividualTime_mem_unit P μ ν i)

/-- Finite-intensity hybrid extension of the general-policy part of
`lem:monotone-reach` = `lem:strict-reach`. No threshold monotonicity is assumed. -/
theorem HybridRule.individualReachProbability_le_twice_meanDuration (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    π.individualReachProbability P μ ν i ≤ 2 * π.meanDuration P μ ν := by
  rw [π.individualReachProbability_eq_mean_pending hπ P μ ν i]
  apply ProphetSecretary.Reach.mean_pending_le_twice_duration (hybridWorldLaw P μ ν)
    (π.measurable_pendingIndividualTime hπ i) (individualClock_measurePreserving P μ ν i).measurable
    (π.measurable_realizedDuration hπ).aestronglyMeasurable
    (individualClock_measurePreserving P μ ν i).map_eq
    (π.pendingIndividualTime_clock_independent hπ P μ ν i)
    (π.pendingIndividualTime_mem_unit P μ ν i) (π.realizedDuration_mem_unitInterval P μ ν)
  have hclock := (Measure.quasiMeasurePreserving_snd (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (P.world_clocks_mem_unitInterval ν)
  filter_upwards [hclock] with v hv
  have hi : combinedClocks v.2.2.1 v.1.2 (i.castAdd v.1.1) ≤ 1 := by
    simpa only [combinedClocks,Fin.addCases_left] using (hv i).2
  have h := (π.asFinitePolicy v.1.1).min_le_stoppingTime v.2.2.2 (combinedValues v.2.1 v.1.2)
    (combinedClocks v.2.2.1 v.1.2) (i.castAdd v.1.1) hi
  simpa only [HybridRule.pendingIndividualTime,HybridRule.realizedDuration,HybridRule.stoppingTime,
    combinedClocks,Fin.addCases_left] using h

namespace RandomizedHybridPolicy
noncomputable def individualReachProbability (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (i : Fin n) : ℝ :=
  π.rule.individualReachProbability B.individuals B.intensity π.seedLaw i

/-- Independent policy randomization is included in the actual hybrid law. -/
theorem individualReachProbability_le_twice_expectedDuration (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (i : Fin n) :
    π.individualReachProbability B i ≤ 2 * π.expectedDuration B :=
  π.rule.individualReachProbability_le_twice_meanDuration π.measurable_rule B.individuals B.intensity π.seedLaw i
end RandomizedHybridPolicy
end ProphetSecretary.Limiting
