import ProphetSecretary.Limiting.CountableIndividualTagObservations
import ProphetSecretary.Limiting.CountableCanonicalLimit

/-!
# Policies observing an individual tag at its occurrence

The tag law is independent of the offers and the policy's own auxiliary seed.
The explicit tag-blindness condition is nonanticipation of that latent tag.
It permits the tag at its own current arrival and after a present history
entry, including a zero-valued observation.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

structure RandomizedIndividualTaggedPolicy (B : CountableInstance) (i : ℕ)
    {T : Type} [MeasurableSpace T] (κ : Measure T) [IsProbabilityMeasure κ] where
  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  rule : CountableRule (Seed × T)
  measurable_rule : rule.IsMeasurable
  blind_before : rule.TagBlindBefore i
  admissible : rule.Admissible B (seedLaw.prod κ)

attribute [instance] RandomizedIndividualTaggedPolicy.seedSpace RandomizedIndividualTaggedPolicy.probability

namespace RandomizedIndividualTaggedPolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

/-- The independent tag is an analytical part of the base-world seed;
`blind_before` enforces when the executed callbacks may use it. -/
noncomputable def toBasePolicy (π : RandomizedIndividualTaggedPolicy B i κ) : RandomizedCountablePolicy B where
  Seed := π.Seed × T
  seedLaw := π.seedLaw.prod κ
  rule := π.rule
  measurable_rule := π.measurable_rule
  admissible := π.admissible

noncomputable def ignoreTag (π : RandomizedCountablePolicy B) (i : ℕ) (κ : Measure T)
    [IsProbabilityMeasure κ] : RandomizedIndividualTaggedPolicy B i κ where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.comapSeed Prod.fst
  measurable_rule := π.rule.comapSeed_isMeasurable π.measurable_rule measurable_fst
  blind_before := π.rule.comapSeed_tagBlindBefore i
  admissible := (B.mapCompleteSeed_measurePreserving (measurePreserving_fst :
    MeasurePreserving (Prod.fst : π.Seed × T → π.Seed) (π.seedLaw.prod κ) π.seedLaw)).quasiMeasurePreserving.ae π.admissible

lemma ignoreTag_scalarObjective (π : RandomizedCountablePolicy B) (i : ℕ) (κ : Measure T)
    [IsProbabilityMeasure κ] (w c : ℝ) :
    ((ignoreTag π i κ).toBasePolicy).scalarObjective w c=π.scalarObjective w c :=
  π.comapSeed_scalarObjective (π.seedLaw.prod κ) Prod.fst measurePreserving_fst w c

end RandomizedIndividualTaggedPolicy
end ProphetSecretary.Limiting
