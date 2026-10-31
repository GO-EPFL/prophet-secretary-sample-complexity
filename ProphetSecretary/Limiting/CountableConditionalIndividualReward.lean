import ProphetSecretary.Limiting.CountableConditionalIndividualPolicy

/-!
# Selected reward under conditional individual reconstruction

The joint graph assertion identifies the displayed value with the specified
map of the reconstructed old value. The identity concerns the selected
occurrence and preserves the no-selection convention.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedCountablePolicy
variable {B : CountableInstance}

lemma reconstructIndividualPolicy_reward (π : RandomizedCountablePolicy B) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) (B.individuals i : Measure ℝ))
    (v : CompleteWorld (π.Seed × U)) :
    π.rule.realizedReward B.terminal (recoverIndividualWorld i F v)=
      (π.reconstructIndividualPolicy i q hSupport ρ F hF).rule.realizedReward B.terminal v+
        (π.reconstructIndividualPolicy i q hSupport ρ F hF).rule.individualSelectionIndicator i v*
          (F (v.2.1 i,v.2.2.2.2)-v.2.1 i) := by
  exact (π.rule.comapSeed Prod.fst).pullbackSeededIndividual_reward i (fun r y => F (y,r.2)) B.terminal v

lemma reconstructIndividualPolicy_expectedReward_of_graph (π : RandomizedCountablePolicy B) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (F : ℝ × U → ℝ) (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) (B.individuals i : Measure ℝ))
    (g : ℝ → ℝ) (hg : Measurable g)
    (hGraph : ∀ᵐ z ∂(q : Measure ℝ).prod ρ, g (F z)=z.1) :
    (π.reconstructIndividualPolicy i q hSupport ρ F hF).expectedReward=
      ∫ v, π.rule.realizedReward B.terminal v+
        π.rule.individualSelectionIndicator i v*(g (v.2.1 i)-v.2.1 i) ∂B.completeWorldLaw π.seedLaw := by
  let D := B.updateIndividual i q hSupport
  let obs := fun v : CompleteWorld π.Seed => π.rule.realizedReward B.terminal v+
    π.rule.individualSelectionIndicator i v*(g (v.2.1 i)-v.2.1 i)
  have hXi : Measurable (fun v : CompleteWorld π.Seed => v.2.1 i) := by fun_prop
  have hObs : Measurable obs := (π.rule.measurable_realizedReward π.measurable_rule B.terminal).add
    ((π.rule.measurable_individualSelectionIndicator π.measurable_rule i).mul ((hg.comp hXi).sub hXi))
  have hMP := B.recoverIndividualWorld_measurePreserving i q hSupport π.seedLaw ρ hF
  have hMean := hMP.hasLaw.integral_comp hObs.aestronglyMeasurable
  have hPair : MeasurePreserving (fun v : CompleteWorld (π.Seed × U) => (v.2.1 i,v.2.2.2.2))
      (D.completeWorldLaw (π.seedLaw.prod ρ)) ((q : Measure ℝ).prod ρ) := by
    simpa only [D,updateIndividual,Function.update_self] using D.individual_seedAuxiliary_measurePreserving i π.seedLaw ρ
  have hG := hPair.quasiMeasurePreserving.ae hGraph
  change (∫ v : CompleteWorld (π.Seed × U),
    (π.reconstructIndividualPolicy i q hSupport ρ F hF).rule.realizedReward B.terminal v
      ∂D.completeWorldLaw (π.seedLaw.prod ρ))=∫ v, obs v ∂B.completeWorldLaw π.seedLaw
  rw [← hMean]
  apply integral_congr_ae
  filter_upwards [hG] with v hv
  have hR := π.reconstructIndividualPolicy_reward i q hSupport ρ F hF v
  have hI := π.reconstructIndividualPolicy_selection i q hSupport ρ F hF v
  change _=obs (recoverIndividualWorld i F v)
  dsimp only [obs]
  rw [← hI,show (recoverIndividualWorld i F v).2.1 i=F (v.2.1 i,v.2.2.2.2) from Function.update_self i _ _,hv]
  linarith only [hR]

end RandomizedCountablePolicy
end ProphetSecretary.Limiting
