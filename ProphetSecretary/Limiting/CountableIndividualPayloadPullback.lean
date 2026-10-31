import ProphetSecretary.Limiting.CountableIndividualTaggedPolicies
import ProphetSecretary.Limiting.CountableIndividualPayloadMap

/-!
# Observable forward simulation of a displayed individual payload

A displayed-value policy can evaluate the display map at the current tagged
arrival and at its already observed history entry. Before that arrival, the
resulting callbacks are independent of the latent tag.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedCountablePolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

noncomputable def individualPayloadPullback (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap)
    (policy : RandomizedCountablePolicy (B.mapIndividualPayload i κ g hg hSupport)) :
    RandomizedIndividualTaggedPolicy B i κ where
  Seed := policy.Seed
  seedLaw := policy.seedLaw
  rule := (policy.rule.comapSeed Prod.fst).pullbackSeededIndividual i (fun r x => g (x,r.2))
  measurable_rule := (policy.rule.comapSeed Prod.fst).pullbackSeededIndividual_isMeasurable
    (policy.rule.comapSeed_isMeasurable policy.measurable_rule measurable_fst) i
    (hg.comp (measurable_snd.prodMk measurable_fst.snd))
  blind_before := policy.rule.pullbackSeededIndividual_tagBlindBefore i _
  admissible := by
    have hMP := B.displayedIndividualWorld_measurePreserving i κ g hg hSupport policy.seedLaw
    filter_upwards [hMP.quasiMeasurePreserving.ae policy.admissible] with v hv
    apply ((policy.rule.comapSeed Prod.fst).pullbackSeededIndividual_hasFirst i (fun r x => g (x,r.2)) v).mpr
    exact hv

lemma individualPayloadPullback_expectedDuration (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap)
    (policy : RandomizedCountablePolicy (B.mapIndividualPayload i κ g hg hSupport)) :
    (policy.individualPayloadPullback g hg hSupport).toBasePolicy.expectedDuration=policy.expectedDuration := by
  have hMP := B.displayedIndividualWorld_measurePreserving i κ g hg hSupport policy.seedLaw
  have hMean := hMP.hasLaw.integral_comp (policy.rule.measurable_realizedDuration policy.measurable_rule).aestronglyMeasurable
  change (∫ v : CompleteWorld (policy.Seed × T),
    ((policy.rule.comapSeed Prod.fst).pullbackSeededIndividual i (fun r x => g (x,r.2))).realizedDuration v
      ∂B.completeWorldLaw (policy.seedLaw.prod κ))=∫ v, policy.rule.realizedDuration v
        ∂(B.mapIndividualPayload i κ g hg hSupport).completeWorldLaw policy.seedLaw
  rw [← hMean]
  apply integral_congr_ae
  exact Eventually.of_forall ((policy.rule.comapSeed Prod.fst).pullbackSeededIndividual_duration i (fun r x => g (x,r.2)))

lemma individualPayloadPullback_reward (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap)
    (policy : RandomizedCountablePolicy (B.mapIndividualPayload i κ g hg hSupport)) (v : CompleteWorld (policy.Seed × T)) :
    policy.rule.realizedReward B.terminal (recoverIndividualWorld i g v)=
      (policy.individualPayloadPullback g hg hSupport).rule.realizedReward B.terminal v+
        (policy.individualPayloadPullback g hg hSupport).rule.individualSelectionIndicator i v*(g (v.2.1 i,v.2.2.2.2)-v.2.1 i) :=
  (policy.rule.comapSeed Prod.fst).pullbackSeededIndividual_reward i (fun r x => g (x,r.2)) B.terminal v

end RandomizedCountablePolicy
end ProphetSecretary.Limiting
