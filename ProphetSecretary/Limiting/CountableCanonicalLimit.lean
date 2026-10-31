import ProphetSecretary.Limiting.CountableOutcomeStability
import ProphetSecretary.Limiting.CountableCanonicalOptimizer
import ProphetSecretary.Limiting.FirstAcceptanceTimeUniqueness

/-!
# Canonical optimization and uniqueness in the limiting model

This completes `lem:canonical-limit`. The actual value rule is a measurable
Markov threshold optimizer; its strict positive-level time profiles exclude
acceptance ties. The same-input modulus controls every admissible competitor,
and at zero regret it identifies both outcomes and the selected occurrence.
-/

open MeasureTheory Set Filter
open scoped Topology Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma CountableInstance.outcome_stability (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∃ Ω : ℝ → ℝ, (∀ r, 0 ≤ Ω r ∧ Ω r ≤ (B.cap : ℝ)+1) ∧ Monotone Ω ∧ Ω 0=0 ∧
      Tendsto Ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ π : RandomizedCountablePolicy B,
        π.expectedValueOutcomeError w c ≤ Ω (B.optimalScalarValue w c-π.scalarObjective w c) := by
  obtain ⟨Ω,hΩ,hMono,hΩZero,hLimit,hError⟩ := countable_outcome_stability_fixed_weights
    (fun _ : Unit => B) B.cap.property hw hc (fun _ => hZero) (fun _ => le_rfl)
    (fun d => (B.totalTailMass d).toReal) (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ _ => le_rfl)
  exact ⟨Ω,hΩ,hMono,hΩZero,hLimit,fun π => hError () π⟩

lemma RandomizedCountablePolicy.outcomes_eq_canonical_ae_of_optimal {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hOptimal : π.scalarObjective w c=B.optimalScalarValue w c) :
    ∀ᵐ v ∂B.completeWorldLaw π.seedLaw,
      π.rule.realizedReward B.terminal v=(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v) ∧
      π.rule.realizedDuration v=(B.valueRule w c).realizedDuration (eraseCompleteSeed v) := by
  obtain ⟨Ω,_,_,hΩZero,_,hError⟩ := B.outcome_stability hZero hw hc
  have hE : π.expectedValueOutcomeError w c=0 := le_antisymm
    (by simpa only [hOptimal,sub_self,hΩZero] using hError π)
    (π.expectedValueOutcomeError_nonnegative w c)
  have hAE := (integral_eq_zero_iff_of_nonneg (π.rule.coupledValueOutcomeError_nonnegative B w c)
    (π.rule.integrable_coupledValueOutcomeError π.measurable_rule B π.seedLaw hw.le hc.le)).1 hE
  filter_upwards [hAE] with v hv
  change |π.rule.realizedReward B.terminal v-(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)|+
    |π.rule.realizedDuration v-(B.valueRule w c).realizedDuration (eraseCompleteSeed v)|=0 at hv
  have hR : |π.rule.realizedReward B.terminal v-(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)|=0 := by
    nlinarith only [hv,abs_nonneg (π.rule.realizedReward B.terminal v-(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)),
      abs_nonneg (π.rule.realizedDuration v-(B.valueRule w c).realizedDuration (eraseCompleteSeed v))]
  have hT : |π.rule.realizedDuration v-(B.valueRule w c).realizedDuration (eraseCompleteSeed v)|=0 := by
    linarith only [hv,hR]
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp hR),sub_eq_zero.mp (abs_eq_zero.mp hT)⟩

lemma RandomizedCountablePolicy.selectedOccurrence_eq_canonical_ae_of_optimal {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hOptimal : π.scalarObjective w c=B.optimalScalarValue w c) :
    ∀ᵐ v ∂B.completeWorldLaw π.seedLaw,
      FirstAcceptance.selectedCode π.rule.codeAccepted codeTime v =
        FirstAcceptance.selectedCode (B.valueRule w c).codeAccepted codeTime (eraseCompleteSeed v) := by
  filter_upwards [π.outcomes_eq_canonical_ae_of_optimal hZero hw hc hOptimal,
    B.present_candidate_times_injective π.seedLaw,B.present_candidate_times_mem_Ioo π.seedLaw]
      with v hOutcome hInjective hTime
  apply FirstAcceptance.selectedCode_eq_of_stoppingTime_eq π.rule.codeAccepted
    (fun v i => (B.valueRule w c).codeAccepted (eraseCompleteSeed v) i) codeTime v (codePresent v)
    (fun _ hi => hi.1) (fun _ hi => hi.1)
  · intro i hi
    exact (hTime (candidateEnumeration.symm i) hi).2
  · intro i hi j hj he
    exact candidateEnumeration.symm.injective (hInjective hi hj he)
  · exact hOutcome.2

end ProphetSecretary.Limiting
