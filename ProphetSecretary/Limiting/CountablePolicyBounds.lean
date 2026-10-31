import ProphetSecretary.Limiting.CountablePolicy
import ProphetSecretary.Limiting.CountableBenchmark

/-!
# Integrable rewards for the full countable policy class

Admissibility only requires existence of the executed first acceptance. Bounds
and the comparison with the actual prophet maximum are derived from the
constructed world, not stored as assumptions on competing policies.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]

lemma value_projection_measurePreserving :
    MeasurePreserving (fun v : CompleteWorld Seed => (v.1,v.2.1)) (B.completeWorldLaw ν) B.valueLaw :=
  (MeasurePreserving.id B.bandConfigurationsLaw).prod (measurePreserving_fst :
    MeasurePreserving (fun v : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => v.1)
      (B.individualWorldLaw ν) B.individualValuesLaw)

omit [IsProbabilityMeasure ν] in
lemma candidate_value_bounded :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ i, candidatePresent v i →
      (candidatePoint v i).2 ∈ Icc (0 : ℝ) B.cap := by
  have hx0 : ∀ᵐ q ∂B.individualWorldLaw ν, ∀ i, q.1 i ∈ Icc (0 : ℝ) B.cap :=
    (Measure.quasiMeasurePreserving_fst (μ := B.individualValuesLaw)
      (ν := individualClocksLaw.prod ν)).ae B.individual_values_supported
  have hx := (Measure.quasiMeasurePreserving_snd (μ := B.bandConfigurationsLaw)
    (ν := B.individualWorldLaw ν)).ae hx0
  have hp := (Measure.quasiMeasurePreserving_fst (μ := B.bandConfigurationsLaw)
    (ν := B.individualWorldLaw ν)).ae B.bandConfigurations_supported
  filter_upwards [hx,hp] with v hv hc
  intro i hi
  cases i with
  | inl i => exact hv i
  | inr kj =>
    change kj.2 < (v.1 kj.1).1 at hi
    change (configurationPoint kj.2 (v.1 kj.1)).2 ∈ _
    rw [configurationPoint,dif_pos hi]
    exact ⟨(hc kj.1 ⟨kj.2,hi⟩).2.1.le,(hc kj.1 ⟨kj.2,hi⟩).2.2⟩

omit [IsProbabilityMeasure ν] in
lemma codeValue_bounded :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ i, codePresent v i → codeValue v i ∈ Icc (0 : ℝ) B.cap :=
  (B.candidate_value_bounded ν).mono (fun _ hv i => hv (candidateEnumeration.symm i))

lemma candidate_value_le_maximum :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ i, candidatePresent v i →
      (candidatePoint v i).2 ≤ B.maximum (v.1,v.2.1) := by
  have hx := (B.value_projection_measurePreserving ν).quasiMeasurePreserving.ae B.individual_le_maximum
  have hp := (B.value_projection_measurePreserving ν).quasiMeasurePreserving.ae B.mark_le_maximum
  filter_upwards [hx,hp] with v hv hc
  intro i hi
  cases i with
  | inl i => exact hv i
  | inr kj =>
    change kj.2 < (v.1 kj.1).1 at hi
    change (configurationPoint kj.2 (v.1 kj.1)).2 ≤ _
    rw [configurationPoint,dif_pos hi]
    exact hc kj.1 ⟨kj.2,hi⟩

omit [IsProbabilityMeasure ν] in
lemma CountableRule.reward_bounded (π : CountableRule Seed) :
    ∀ᵐ v ∂B.completeWorldLaw ν, π.realizedReward B.terminal v ∈ Icc (0 : ℝ) B.cap := by
  filter_upwards [B.codeValue_bounded ν] with v hv
  exact FirstAcceptance.reward_bounded ⟨B.terminal.property,by exact_mod_cast B.terminal_le_cap⟩
    (fun i hi => hv i hi.1)

lemma CountableRule.reward_le_maximum (π : CountableRule Seed) :
    ∀ᵐ v ∂B.completeWorldLaw ν, π.realizedReward B.terminal v ≤ B.maximum (v.1,v.2.1) := by
  have hb := (B.value_projection_measurePreserving ν).quasiMeasurePreserving.ae B.maximum_bounded
  filter_upwards [B.candidate_value_le_maximum ν,hb] with v hv hm
  by_cases he : ∃ i, FirstAcceptance.Earliest π.codeAccepted codeTime v i
  · obtain ⟨i,hi⟩ := he
    rw [CountableRule.realizedReward,FirstAcceptance.reward_of_earliest B.terminal hi]
    exact hv (candidateEnumeration.symm i) hi.1.1
  · rw [π.no_first_reward _ _ he]
    exact hm.1

lemma CountableRule.integrable_reward (π : CountableRule Seed) (hπ : π.IsMeasurable) :
    Integrable (π.realizedReward B.terminal) (B.completeWorldLaw ν) := by
  apply Integrable.of_bound (π.measurable_realizedReward hπ B.terminal).aestronglyMeasurable B.cap
  filter_upwards [π.reward_bounded B ν] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg hv.1]
  exact hv.2

lemma CountableRule.integrable_duration (π : CountableRule Seed) (hπ : π.IsMeasurable) :
    Integrable π.realizedDuration (B.completeWorldLaw ν) := by
  apply Integrable.of_bound (π.measurable_realizedDuration hπ).aestronglyMeasurable 1
  apply ae_of_all
  intro v
  rw [Real.norm_eq_abs,abs_of_nonneg (π.duration_bounds v).1]
  exact (π.duration_bounds v).2

end ProphetSecretary.Limiting.CountableInstance
