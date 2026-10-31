import ProphetSecretary.Limiting.CountableIndividualTaggedReward
import ProphetSecretary.Limiting.CountableIndividualPayloadMap
import ProphetSecretary.Probability.ConditionalPayloadSampler

/-!
# Causal conditional simulation of original individual payloads

The displayed value alone and one fresh independent uniform reconstruct the
original value and occurrence tag jointly. The tag is used only at its own
arrival or through its already present history entry.
-/

open MeasureTheory Set
open scoped Classical unitInterval

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedIndividualTaggedPolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T] [StandardBorelSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

theorem exists_displayedPayloadPolicy (π : RandomizedIndividualTaggedPolicy B i κ)
    (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap) :
    ∃ policy : RandomizedCountablePolicy (B.mapIndividualPayload i κ g hg hSupport),
      policy.expectedDuration=π.toBasePolicy.expectedDuration ∧
      policy.expectedReward=∫ v : CompleteWorld (π.Seed × T), π.rule.realizedReward B.terminal v+
        π.rule.individualSelectionIndicator i v*(g (v.2.1 i,v.2.2.2.2)-v.2.1 i)
          ∂B.completeWorldLaw (π.seedLaw.prod κ) := by
  obtain ⟨F,_,_,hMarg,hGraph⟩ := ProphetSecretary.Probability.exists_conditional_payload_sampler
    ((B.individuals i : Measure ℝ).prod κ) g hg
  let q := B.individualPayloadLaw i κ g hg
  have hq : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap :=
    (ae_map_iff hg.aemeasurable measurableSet_Icc).mpr hSupport
  have hMP : MeasurePreserving (Function.uncurry F) ((q : Measure ℝ).prod (volume : Measure unitInterval))
      ((B.individuals i : Measure ℝ).prod κ) := hMarg
  let t0 : T := Classical.choice (nonempty_of_isProbabilityMeasure κ)
  let policy := π.reconstructPolicy q hq (volume : Measure unitInterval) (Function.uncurry F) hMP t0
  refine ⟨policy,π.reconstructPolicy_expectedDuration q hq _ _ hMP t0,?_⟩
  exact π.reconstructPolicy_expectedReward_of_graph q hq _ _ hMP t0 g hg hGraph

end RandomizedIndividualTaggedPolicy
end ProphetSecretary.Limiting
