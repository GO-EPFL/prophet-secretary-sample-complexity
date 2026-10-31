import ProphetSecretary.Limiting.OmissionPerformanceFacts

/-!
# Causal upper comparison with a genuine truncated instance

Every full admissible policy has a constructed truncated competitor. Averaging
on the actual coupling gives reward error at most the omitted individual excess
maximum plus b minus reserve, and duration increases. The constants are uniform
in the instance size, the policy, and every nonnegative duration weight.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.omission_expected_comparison {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    let σ := π.simulateOmissions N b
    π.expectedDuration ≤ σ.expectedDuration (B.truncation N b hb) ∧
      π.expectedReward ≤ σ.expectedReward (B.truncation N b hb) +
        (B.expectedIndividualTailExcessMaximum N + (b-(B.terminal : ℝ))) := by
  let σ := π.simulateOmissions N b
  let C := B.truncation N b hb
  obtain ⟨Γ,hΓ,hNew,hOld,hPerf⟩ := π.exists_omission_performance_coupling N hb
  letI : IsProbabilityMeasure Γ := hΓ
  have hOldTI : Integrable (fun q : OmissionExecutionWorld π.Seed => π.rule.realizedDuration (oldExecutionWorld q)) Γ := hOld.integrable_comp_of_integrable π.integrable_duration
  have hNewTI : Integrable (fun q : OmissionExecutionWorld π.Seed => σ.rule.realizedDuration (newExecutionWorld N q)) Γ := hNew.integrable_comp_of_integrable (σ.integrable_duration C)
  have hOldRI : Integrable (fun q : OmissionExecutionWorld π.Seed => π.rule.realizedReward B.terminal (oldExecutionWorld q)) Γ := hOld.integrable_comp_of_integrable π.integrable_reward
  have hNewRI : Integrable (fun q : OmissionExecutionWorld π.Seed => σ.rule.realizedReward B.terminal (newExecutionWorld N q)) Γ := hNew.integrable_comp_of_integrable (σ.integrable_reward C)
  have hOldT := hOld.hasLaw.integral_comp (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable
  have hNewT := hNew.hasLaw.integral_comp (σ.rule.measurable_realizedDuration σ.measurable_rule).aestronglyMeasurable
  have hOldR := hOld.hasLaw.integral_comp (π.rule.measurable_realizedReward π.measurable_rule B.terminal).aestronglyMeasurable
  have hNewR := hNew.hasLaw.integral_comp (σ.rule.measurable_realizedReward σ.measurable_rule B.terminal).aestronglyMeasurable
  change (∫ q, π.rule.realizedDuration (oldExecutionWorld q) ∂Γ) = π.expectedDuration at hOldT
  change (∫ q, σ.rule.realizedDuration (newExecutionWorld N q) ∂Γ) = σ.expectedDuration C at hNewT
  change (∫ q, π.rule.realizedReward B.terminal (oldExecutionWorld q) ∂Γ) = π.expectedReward at hOldR
  change (∫ q, σ.rule.realizedReward B.terminal (newExecutionWorld N q) ∂Γ) = σ.expectedReward C at hNewR
  have hV : MeasurePreserving (fun v : CompleteWorld π.Seed => v.2.1) (B.completeWorldLaw π.seedLaw)
      B.individualValuesLaw := measurePreserving_fst.comp measurePreserving_snd
  have hValues := hV.comp hOld
  have hEI : Integrable (fun q : OmissionExecutionWorld π.Seed => B.individualTailExcessMaximum N (oldExecutionWorld q).2.1) Γ := hValues.integrable_comp_of_integrable (B.integrable_individualTailExcessMaximum N)
  have hE := hValues.hasLaw.integral_comp (B.measurable_individualTailExcessMaximum N).aestronglyMeasurable
  change (∫ q, B.individualTailExcessMaximum N (oldExecutionWorld q).2.1 ∂Γ) =
    B.expectedIndividualTailExcessMaximum N at hE
  constructor
  · have h := integral_mono_ae hOldTI hNewTI (hPerf.mono (fun _ h => h.1))
    rw [hOldT,hNewT] at h
    exact h
  · have hpoint : ∀ᵐ q ∂Γ, π.rule.realizedReward B.terminal (oldExecutionWorld q) ≤
        (σ.rule.realizedReward B.terminal (newExecutionWorld N q) +
          B.individualTailExcessMaximum N (oldExecutionWorld q).2.1) + (b-(B.terminal : ℝ)) :=
      hPerf.mono (fun _ h => h.2.trans_eq (add_assoc _ _ _).symm)
    have hPairI : Integrable (fun q : OmissionExecutionWorld π.Seed =>
        σ.rule.realizedReward B.terminal (newExecutionWorld N q) + B.individualTailExcessMaximum N (oldExecutionWorld q).2.1) Γ := hNewRI.add hEI
    have hI : Integrable (fun q : OmissionExecutionWorld π.Seed =>
        (σ.rule.realizedReward B.terminal (newExecutionWorld N q) + B.individualTailExcessMaximum N (oldExecutionWorld q).2.1) +
          (b-(B.terminal : ℝ))) Γ := hPairI.add (integrable_const (b-(B.terminal : ℝ)))
    have h := integral_mono_ae hOldRI hI hpoint
    rw [integral_add hPairI (integrable_const (b-(B.terminal : ℝ))),
      integral_add hNewRI hEI,integral_const,hOldR,hNewR,hE] at h
    simp only [probReal_univ,one_smul] at h
    exact h.trans_eq (add_assoc _ _ _)

lemma RandomizedCountablePolicy.scalarObjective_le_simulateOmissions {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.scalarObjective w c ≤ (π.simulateOmissions N b).scalarObjective (B.truncation N b hb) w c +
      w * (B.expectedIndividualTailExcessMaximum N + (b-(B.terminal : ℝ))) := by
  have h := π.omission_expected_comparison N hb
  rw [RandomizedCountablePolicy.scalarObjective,(π.simulateOmissions N b).scalarObjective_eq]
  calc
    _ ≤ w * ((π.simulateOmissions N b).expectedReward (B.truncation N b hb) +
        (B.expectedIndividualTailExcessMaximum N + (b-(B.terminal : ℝ)))) +
        c * (π.simulateOmissions N b).expectedDuration (B.truncation N b hb) :=
      add_le_add (mul_le_mul_of_nonneg_left h.2 hw) (mul_le_mul_of_nonneg_left h.1 hc)
    _ = _ := by ring

lemma CountableInstance.value_le_truncation_add (B : CountableInstance) (N : ℕ) {b : ℝ}
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c ≤ (B.truncation N b hb).optimalScalarValue w c +
      w * (B.expectedIndividualTailExcessMaximum N + (b-(B.terminal : ℝ))) := by
  apply csSup_le (B.scalarPayoffs_nonempty w c)
  rintro _ ⟨π,rfl⟩
  change π.scalarObjective w c ≤ _
  exact (π.scalarObjective_le_simulateOmissions N hb hw hc).trans
    (add_le_add ((B.truncation N b hb).scalarObjective_le_value (π.simulateOmissions N b) w c) le_rfl)

end ProphetSecretary.Limiting
