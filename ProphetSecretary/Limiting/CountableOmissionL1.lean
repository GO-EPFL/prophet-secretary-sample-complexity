import ProphetSecretary.Limiting.CountableOmissionRegret

/-!
# Coupled outcome control under causal omission

For fixed scalar weights, near optimality controls the absolute duration and
reward changes on the constructed omission coupling. The omitted maximum is
integrated under its actual independent product marginal.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.omission_coupled_l1_bounds {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b)
    {w c r : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hNear : B.optimalScalarValue w c-π.scalarObjective w c ≤ r)
    (Γ : Measure (OmissionExecutionWorld π.Seed)) [IsProbabilityMeasure Γ]
    (hNew : MeasurePreserving (newExecutionWorld N) Γ
      ((B.truncation N b hb).law (π.simulateOmissions N b).seedLaw))
    (hOld : MeasurePreserving oldExecutionWorld Γ (B.completeWorldLaw π.seedLaw))
    (hPerf : ∀ᵐ q ∂Γ,
      π.rule.realizedDuration (oldExecutionWorld q) ≤
        (π.simulateOmissions N b).rule.realizedDuration (newExecutionWorld N q) ∧
      π.rule.realizedReward B.terminal (oldExecutionWorld q) ≤
        (π.simulateOmissions N b).rule.realizedReward B.terminal (newExecutionWorld N q) +
          (B.individualTailExcessMaximum N (oldExecutionWorld q).2.1 + (b-(B.terminal : ℝ)))) :
    let σ := π.simulateOmissions N b
    (c*(∫ q, |σ.rule.realizedDuration (newExecutionWorld N q)-
      π.rule.realizedDuration (oldExecutionWorld q)| ∂Γ) ≤ r+w*B.omissionError N b) ∧
    (w*(∫ q, |σ.rule.realizedReward B.terminal (newExecutionWorld N q)-
      π.rule.realizedReward B.terminal (oldExecutionWorld q)| ∂Γ) ≤ r+2*w*B.omissionError N b) := by
  let σ := π.simulateOmissions N b
  let C := B.truncation N b hb
  let R₀ := fun q : OmissionExecutionWorld π.Seed => π.rule.realizedReward B.terminal (oldExecutionWorld q)
  let R₁ := fun q : OmissionExecutionWorld π.Seed => σ.rule.realizedReward B.terminal (newExecutionWorld N q)
  let T₀ := fun q : OmissionExecutionWorld π.Seed => π.rule.realizedDuration (oldExecutionWorld q)
  let T₁ := fun q : OmissionExecutionWorld π.Seed => σ.rule.realizedDuration (newExecutionWorld N q)
  let E := fun q : OmissionExecutionWorld π.Seed =>
    B.individualTailExcessMaximum N (oldExecutionWorld q).2.1+(b-(B.terminal : ℝ))
  have hR₀I : Integrable R₀ Γ := hOld.integrable_comp_of_integrable π.integrable_reward
  have hR₁I : Integrable R₁ Γ := hNew.integrable_comp_of_integrable (σ.integrable_reward C)
  have hT₀I : Integrable T₀ Γ := hOld.integrable_comp_of_integrable π.integrable_duration
  have hT₁I : Integrable T₁ Γ := hNew.integrable_comp_of_integrable (σ.integrable_duration C)
  have hR₀ := hOld.hasLaw.integral_comp (π.rule.measurable_realizedReward π.measurable_rule B.terminal).aestronglyMeasurable
  have hR₁ := hNew.hasLaw.integral_comp (σ.rule.measurable_realizedReward σ.measurable_rule B.terminal).aestronglyMeasurable
  have hT₀ := hOld.hasLaw.integral_comp (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable
  have hT₁ := hNew.hasLaw.integral_comp (σ.rule.measurable_realizedDuration σ.measurable_rule).aestronglyMeasurable
  change (∫ q, R₀ q ∂Γ) = π.expectedReward at hR₀
  change (∫ q, R₁ q ∂Γ) = σ.expectedReward C at hR₁
  change (∫ q, T₀ q ∂Γ) = π.expectedDuration at hT₀
  change (∫ q, T₁ q ∂Γ) = σ.expectedDuration C at hT₁
  have hV : MeasurePreserving (fun v : CompleteWorld π.Seed => v.2.1)
      (B.completeWorldLaw π.seedLaw) B.individualValuesLaw := measurePreserving_fst.comp measurePreserving_snd
  have hValues := hV.comp hOld
  have hTailI : Integrable (fun q : OmissionExecutionWorld π.Seed =>
      B.individualTailExcessMaximum N (oldExecutionWorld q).2.1) Γ :=
    hValues.integrable_comp_of_integrable (B.integrable_individualTailExcessMaximum N)
  have hEI : Integrable E Γ := hTailI.add (integrable_const _)
  have hTail := hValues.hasLaw.integral_comp (B.measurable_individualTailExcessMaximum N).aestronglyMeasurable
  change (∫ q, B.individualTailExcessMaximum N (oldExecutionWorld q).2.1 ∂Γ) =
    B.expectedIndividualTailExcessMaximum N at hTail
  have hE : (∫ q, E q ∂Γ) = B.omissionError N b := by
    rw [show E = fun q => B.individualTailExcessMaximum N (oldExecutionWorld q).2.1+
      (b-(B.terminal : ℝ)) from rfl,integral_add hTailI (integrable_const _),integral_const,hTail]
    simp only [probReal_univ,one_smul,CountableInstance.omissionError]
  have hE0 : ∀ᵐ q ∂Γ, 0 ≤ E q := by
    filter_upwards [hValues.quasiMeasurePreserving.ae (B.individualTailExcessMaximum_bounded N)] with q hq
    exact add_nonneg hq.1 (sub_nonneg.mpr hb.le)
  have hMeans := π.omission_regret_mean_bounds N hb hw hc hNear
  have hTime : (∫ q, |T₁ q-T₀ q| ∂Γ) = σ.expectedDuration C-π.expectedDuration := by
    calc
      _ = ∫ q, T₁ q-T₀ q ∂Γ := integral_congr_ae
        (hPerf.mono (fun q hq => abs_of_nonneg (sub_nonneg.mpr hq.1)))
      _ = _ := by rw [integral_sub hT₁I hT₀I,hT₁,hT₀]
  have hPoint : ∀ᵐ q ∂Γ, |R₁ q-R₀ q| ≤ (R₁ q-R₀ q)+E q+E q := by
    filter_upwards [hPerf,hE0] with q hq he
    apply abs_le.mpr
    have hqR : R₀ q ≤ R₁ q+E q := hq.2
    constructor <;> linarith only [hqR,he]
  have hReward := integral_mono_ae (hR₁I.sub hR₀I).abs
    (((hR₁I.sub hR₀I).add hEI).add hEI) hPoint
  change (∫ q, |R₁ q-R₀ q| ∂Γ) ≤ ∫ q, (R₁ q-R₀ q)+E q+E q ∂Γ at hReward
  rw [integral_add (f := fun q => (R₁ q-R₀ q)+E q) (g := E) ((hR₁I.sub hR₀I).add hEI) hEI,
    integral_add (f := fun q => R₁ q-R₀ q) (g := E) (hR₁I.sub hR₀I) hEI,
    integral_sub hR₁I hR₀I,hR₁,hR₀,hE] at hReward
  constructor
  · change c*(∫ q, |T₁ q-T₀ q| ∂Γ) ≤ _
    rw [hTime]
    exact hMeans.2.2.1
  · have hWeighted := mul_le_mul_of_nonneg_left hReward hw
    have hMean := hMeans.2.2.2
    change w*(∫ q, |R₁ q-R₀ q| ∂Γ) ≤ _
    nlinarith only [hWeighted,hMean]

end ProphetSecretary.Limiting
