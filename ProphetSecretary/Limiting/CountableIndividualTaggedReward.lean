import ProphetSecretary.Limiting.CountableIndividualTaggedReconstruction

/-!
# The selected reward of a conditionally reconstructed tagged individual

The payload/display graph identifies the displayed value on the selected
occurrence. This identity preserves the joint old value and independent tag,
rather than only the displayed marginal.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedIndividualTaggedPolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

lemma reconstructPolicy_expectedReward_of_graph (π : RandomizedIndividualTaggedPolicy B i κ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ × T) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) ((B.individuals i : Measure ℝ).prod κ))
    (t0 : T) (g : ℝ × T → ℝ) (hg : Measurable g)
    (hGraph : ∀ᵐ z ∂(q : Measure ℝ).prod ρ, g (F z)=z.1) :
    (π.reconstructPolicy q hSupport ρ F hF t0).expectedReward=
      ∫ v : CompleteWorld (π.Seed × T), π.rule.realizedReward B.terminal v+
        π.rule.individualSelectionIndicator i v*(g (v.2.1 i,v.2.2.2.2)-v.2.1 i)
          ∂B.completeWorldLaw (π.seedLaw.prod κ) := by
  let D := B.updateIndividual i q hSupport
  let obs := fun v : CompleteWorld (π.Seed × T) => π.rule.realizedReward B.terminal v+
    π.rule.individualSelectionIndicator i v*(g (v.2.1 i,v.2.2.2.2)-v.2.1 i)
  have hXi : Measurable (fun v : CompleteWorld (π.Seed × T) => v.2.1 i) := by fun_prop
  have hTag : Measurable (fun v : CompleteWorld (π.Seed × T) => v.2.2.2.2) := by fun_prop
  have hObs : Measurable obs := (π.rule.measurable_realizedReward π.measurable_rule B.terminal).add
    ((π.rule.measurable_individualSelectionIndicator π.measurable_rule i).mul ((hg.comp (hXi.prodMk hTag)).sub hXi))
  have hMP := B.recoverIndividualPayloadWorld_measurePreserving i q hSupport π.seedLaw ρ κ hF
  have hMean := hMP.hasLaw.integral_comp hObs.aestronglyMeasurable
  have hPair : MeasurePreserving (fun v : CompleteWorld (π.Seed × U) => (v.2.1 i,v.2.2.2.2))
      (D.completeWorldLaw (π.seedLaw.prod ρ)) ((q : Measure ℝ).prod ρ) := by
    simpa only [D,updateIndividual,Function.update_self] using D.individual_seedAuxiliary_measurePreserving i π.seedLaw ρ
  have hG := hPair.quasiMeasurePreserving.ae hGraph
  change (∫ v : CompleteWorld (π.Seed × U), (π.rule.pullbackIndividualPayload i F t0).realizedReward B.terminal v
    ∂D.completeWorldLaw (π.seedLaw.prod ρ))=∫ v, obs v ∂B.completeWorldLaw (π.seedLaw.prod κ)
  rw [← hMean]
  apply integral_congr_ae
  filter_upwards [hG] with v hv
  have hR := π.rule.pullbackIndividualPayload_reward i F t0 π.blind_before B.terminal v
  have hI := π.reconstructPolicy_selection q hSupport ρ F hF t0 v
  change _=obs (recoverIndividualPayloadWorld i F v)
  dsimp only [obs]
  rw [← hI]
  have hValue : (recoverIndividualPayloadWorld i F v).2.1 i=(F (v.2.1 i,v.2.2.2.2)).1 := Function.update_self i _ _
  have hDisplay : g ((recoverIndividualPayloadWorld i F v).2.1 i,(recoverIndividualPayloadWorld i F v).2.2.2.2)=v.2.1 i := by
    rw [hValue]
    exact hv
  rw [hDisplay,hValue]
  change (π.rule.pullbackIndividualPayload i F t0).realizedReward B.terminal v=
    π.rule.realizedReward B.terminal (recoverIndividualPayloadWorld i F v)+
      (π.rule.pullbackIndividualPayload i F t0).individualSelectionIndicator i v*(v.2.1 i-(F (v.2.1 i,v.2.2.2.2)).1)
  linarith only [hR]

end RandomizedIndividualTaggedPolicy
end ProphetSecretary.Limiting
