import ProphetSecretary.Limiting.CountableDisplayedIndividualPayloadPolicy
import ProphetSecretary.Limiting.CountableIndividualPayloadPullback

/-!
# The common full policy supremum for a displayed individual payload

The two causal simulations give the same scalar displacement on the selected
occurrence. Consequently the actual displayed-instance optimum is a common
supremum over policies observing the latent tag only at its occurrence.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedIndividualTaggedPolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

noncomputable def payloadDisplacementMean (π : RandomizedIndividualTaggedPolicy B i κ) (g : ℝ × T → ℝ) : ℝ :=
  ∫ v : CompleteWorld (π.Seed × T), π.rule.individualSelectionIndicator i v*(g (v.2.1 i,v.2.2.2.2)-v.2.1 i)
    ∂B.completeWorldLaw (π.seedLaw.prod κ)

lemma integrable_payloadDisplacement (π : RandomizedIndividualTaggedPolicy B i κ)
    (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap) :
    Integrable (fun v : CompleteWorld (π.Seed × T) =>
      π.rule.individualSelectionIndicator i v*(g (v.2.1 i,v.2.2.2.2)-v.2.1 i)) (B.completeWorldLaw (π.seedLaw.prod κ)) := by
  have hPair := B.individual_seedAuxiliary_measurePreserving i π.seedLaw κ
  have hXi : Measurable (fun v : CompleteWorld (π.Seed × T) => v.2.1 i) := by fun_prop
  have hm : Measurable (fun v : CompleteWorld (π.Seed × T) => g (v.2.1 i,v.2.2.2.2)-v.2.1 i) :=
    (hg.comp hPair.measurable).sub hXi
  apply (π.rule.integrable_individualSelectionIndicator π.measurable_rule B (π.seedLaw.prod κ) i).mul_bdd hm.aestronglyMeasurable
  have hX : MeasurePreserving (fun v : CompleteWorld (π.Seed × T) => v.2.1 i)
      (B.completeWorldLaw (π.seedLaw.prod κ)) (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
  filter_upwards [hPair.quasiMeasurePreserving.ae hSupport,hX.quasiMeasurePreserving.ae (B.individual_supported i)] with v hv hx
  change ‖g (v.2.1 i,v.2.2.2.2)-v.2.1 i‖≤(B.cap : ℝ)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith only [hv.1,hx.2],by linarith only [hv.2,hx.1]⟩

lemma exists_displayedPayloadPolicy_scalarObjective [StandardBorelSpace T]
    (π : RandomizedIndividualTaggedPolicy B i κ) (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap) (w c : ℝ) :
    ∃ policy : RandomizedCountablePolicy (B.mapIndividualPayload i κ g hg hSupport),
      policy.scalarObjective w c=π.toBasePolicy.scalarObjective w c+w*π.payloadDisplacementMean g := by
  obtain ⟨policy,hT,hR⟩ := π.exists_displayedPayloadPolicy g hg hSupport
  refine ⟨policy,?_⟩
  have hRewardI : Integrable (π.rule.realizedReward B.terminal) (B.completeWorldLaw (π.seedLaw.prod κ)) :=
    π.toBasePolicy.integrable_reward
  rw [integral_add hRewardI (π.integrable_payloadDisplacement g hg hSupport)] at hR
  change w*policy.expectedReward+c*policy.expectedDuration=_
  rw [hR,hT]
  change w*(π.toBasePolicy.expectedReward+π.payloadDisplacementMean g)+c*π.toBasePolicy.expectedDuration=
    π.toBasePolicy.scalarObjective w c+w*π.payloadDisplacementMean g
  unfold RandomizedCountablePolicy.scalarObjective
  ring

end RandomizedIndividualTaggedPolicy

namespace RandomizedCountablePolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

lemma individualPayloadPullback_expectedReward (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap)
    (policy : RandomizedCountablePolicy (B.mapIndividualPayload i κ g hg hSupport)) :
    policy.expectedReward=(policy.individualPayloadPullback g hg hSupport).toBasePolicy.expectedReward+
      (policy.individualPayloadPullback g hg hSupport).payloadDisplacementMean g := by
  let π := policy.individualPayloadPullback g hg hSupport
  have hMP := B.displayedIndividualWorld_measurePreserving i κ g hg hSupport policy.seedLaw
  have hMean := hMP.hasLaw.integral_comp (policy.rule.measurable_realizedReward policy.measurable_rule B.terminal).aestronglyMeasurable
  change (∫ v, policy.rule.realizedReward B.terminal (recoverIndividualWorld i g v)
    ∂B.completeWorldLaw (policy.seedLaw.prod κ))=policy.expectedReward at hMean
  rw [← hMean]
  change _=(∫ v, π.rule.realizedReward B.terminal v ∂B.completeWorldLaw (π.seedLaw.prod κ))+
    ∫ v, π.rule.individualSelectionIndicator i v*(g (v.2.1 i,v.2.2.2.2)-v.2.1 i) ∂B.completeWorldLaw (π.seedLaw.prod κ)
  have hRewardI : Integrable (π.rule.realizedReward B.terminal) (B.completeWorldLaw (π.seedLaw.prod κ)) :=
    π.toBasePolicy.integrable_reward
  rw [← integral_add hRewardI (π.integrable_payloadDisplacement g hg hSupport)]
  exact integral_congr_ae (Eventually.of_forall (policy.individualPayloadPullback_reward g hg hSupport))

lemma individualPayloadPullback_scalarObjective (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap)
    (policy : RandomizedCountablePolicy (B.mapIndividualPayload i κ g hg hSupport)) (w c : ℝ) :
    policy.scalarObjective w c=(policy.individualPayloadPullback g hg hSupport).toBasePolicy.scalarObjective w c+
      w*(policy.individualPayloadPullback g hg hSupport).payloadDisplacementMean g := by
  have hR := policy.individualPayloadPullback_expectedReward g hg hSupport
  have hT := policy.individualPayloadPullback_expectedDuration g hg hSupport
  unfold scalarObjective
  rw [hR,← hT]
  ring

end RandomizedCountablePolicy

lemma CountableInstance.optimalScalarValue_mapIndividualPayload_eq_sSup
    (B : CountableInstance) (i : ℕ) {T : Type} [MeasurableSpace T] [StandardBorelSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap) (w c : ℝ) :
    (B.mapIndividualPayload i κ g hg hSupport).optimalScalarValue w c=
      sSup (Set.range (fun π : RandomizedIndividualTaggedPolicy B i κ =>
        π.toBasePolicy.scalarObjective w c+w*π.payloadDisplacementMean g)) := by
  let D := B.mapIndividualPayload i κ g hg hSupport
  let J := fun π : RandomizedIndividualTaggedPolicy B i κ => π.toBasePolicy.scalarObjective w c+w*π.payloadDisplacementMean g
  have hUpper (π : RandomizedIndividualTaggedPolicy B i κ) : J π≤D.optimalScalarValue w c := by
    obtain ⟨policy,hJ⟩ := π.exists_displayedPayloadPolicy_scalarObjective g hg hSupport w c
    exact hJ.symm.trans_le (D.scalarObjective_le_value policy w c)
  have hBound : BddAbove (Set.range J) := ⟨D.optimalScalarValue w c,by rintro _ ⟨π,rfl⟩; exact hUpper π⟩
  apply le_antisymm
  · apply csSup_le (D.scalarPayoffs_nonempty w c)
    rintro _ ⟨policy,rfl⟩
    exact (policy.individualPayloadPullback_scalarObjective g hg hSupport w c).trans_le (le_csSup hBound (Set.mem_range_self _))
  · exact csSup_le ⟨_,⟨RandomizedIndividualTaggedPolicy.ignoreTag (RandomizedCountablePolicy.waiting B) i κ,rfl⟩⟩
      (by rintro _ ⟨π,rfl⟩; exact hUpper π)

end ProphetSecretary.Limiting
