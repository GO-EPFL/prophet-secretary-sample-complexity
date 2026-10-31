import ProphetSecretary.Limiting.CountableConditionalIndividualReward
import ProphetSecretary.Probability.ConditionalPayloadSampler

/-!
# Simulating original individual observations from a displayed value

Conditional sampling supplies a causal policy on the displayed-value instance.
The original value is reconstructed at its occurrence; no inverse or injectivity
of the display map is required. The independent policy seed is arbitrary.
-/

open MeasureTheory Set
open scoped Classical unitInterval

namespace ProphetSecretary.Limiting
open CountableInstance

/-- Every original policy has an observable displayed-value simulation with
the same duration and the corresponding selected-value reward change. -/
theorem RandomizedCountablePolicy.exists_displayedIndividualPolicy {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x∈Icc (0 : ℝ) B.cap) :
    ∃ policy : RandomizedCountablePolicy (B.mapIndividual i g hg hSupport),
      policy.expectedDuration=π.expectedDuration ∧
      policy.expectedReward=∫ v, π.rule.realizedReward B.terminal v+
        π.rule.individualSelectionIndicator i v*(g (v.2.1 i)-v.2.1 i) ∂B.completeWorldLaw π.seedLaw := by
  obtain ⟨F,_,_,hMarg,hGraph⟩ := ProphetSecretary.Probability.exists_conditional_payload_sampler
    (B.individuals i : Measure ℝ) g hg
  let q := (B.individuals i).map hg.aemeasurable
  have hq : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap :=
    (ae_map_iff hg.aemeasurable measurableSet_Icc).mpr hSupport
  have hMP : MeasurePreserving (Function.uncurry F) ((q : Measure ℝ).prod (volume : Measure unitInterval))
      (B.individuals i : Measure ℝ) := hMarg
  let policy := π.reconstructIndividualPolicy i q hq (volume : Measure unitInterval) (Function.uncurry F) hMP
  refine ⟨policy,π.reconstructIndividualPolicy_expectedDuration i q hq _ _ hMP,?_⟩
  exact π.reconstructIndividualPolicy_expectedReward_of_graph i q hq _ _ hMP g hg hGraph

end ProphetSecretary.Limiting
