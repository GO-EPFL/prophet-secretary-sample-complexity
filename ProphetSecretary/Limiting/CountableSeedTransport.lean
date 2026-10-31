import ProphetSecretary.Limiting.CountableCanonicalL1

/-!
# Transport and extension of independent auxiliary randomness

A measurable measure-preserving change of seed leaves the online observations,
selected reward and stopping time unchanged. In particular an arbitrary
independent auxiliary space can be adjoined for occurrence tags or analysis.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def mapCompleteSeed {Seed Seed' : Type*} (f : Seed' → Seed)
    (v : CompleteWorld Seed') : CompleteWorld Seed :=
  (v.1,(v.2.1,(v.2.2.1,f v.2.2.2)))

lemma CountableInstance.mapCompleteSeed_measurePreserving (B : CountableInstance)
    {Seed Seed' : Type*} [MeasurableSpace Seed] [MeasurableSpace Seed']
    {ν : Measure Seed} {ν' : Measure Seed'} [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {f : Seed' → Seed} (hf : MeasurePreserving f ν' ν) :
    MeasurePreserving (mapCompleteSeed f) (B.completeWorldLaw ν') (B.completeWorldLaw ν) :=
  (MeasurePreserving.id B.bandConfigurationsLaw).prod
    ((MeasurePreserving.id B.individualValuesLaw).prod
      ((MeasurePreserving.id individualClocksLaw).prod hf))

namespace CountableInstance

noncomputable def CountableRule.comapSeed {Seed Seed' : Type*} (π : CountableRule Seed)
    (f : Seed' → Seed) : CountableRule Seed' where
  individual r := π.individual (f r)
  poisson r := π.poisson (f r)

lemma CountableRule.comapSeed_isMeasurable {Seed Seed' : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Seed'] (π : CountableRule Seed) (hπ : π.IsMeasurable)
    {f : Seed' → Seed} (hf : Measurable f) : (π.comapSeed f).IsMeasurable := by
  constructor
  · exact hπ.1.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  · exact hπ.2.comp ((hf.comp measurable_fst).prodMk measurable_snd)

lemma CountableRule.comapSeed_realizedReward {Seed Seed' : Type*} (π : CountableRule Seed)
    (f : Seed' → Seed) (a : ℝ) (v : CompleteWorld Seed') :
    (π.comapSeed f).realizedReward a v=π.realizedReward a (mapCompleteSeed f v) := rfl

lemma CountableRule.comapSeed_realizedDuration {Seed Seed' : Type*} (π : CountableRule Seed)
    (f : Seed' → Seed) (v : CompleteWorld Seed') :
    (π.comapSeed f).realizedDuration v=π.realizedDuration (mapCompleteSeed f v) := rfl

end CountableInstance

noncomputable def RandomizedCountablePolicy.comapSeed {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {Seed' : Type} [MeasurableSpace Seed']
    (ν' : Measure Seed') [IsProbabilityMeasure ν'] (f : Seed' → π.Seed)
    (hf : MeasurePreserving f ν' π.seedLaw) : RandomizedCountablePolicy B where
  Seed := Seed'
  seedLaw := ν'
  rule := π.rule.comapSeed f
  measurable_rule := π.rule.comapSeed_isMeasurable π.measurable_rule hf.measurable
  admissible := (B.mapCompleteSeed_measurePreserving hf).quasiMeasurePreserving.ae π.admissible

lemma RandomizedCountablePolicy.comapSeed_expectedReward {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {Seed' : Type} [MeasurableSpace Seed']
    (ν' : Measure Seed') [IsProbabilityMeasure ν'] (f : Seed' → π.Seed)
    (hf : MeasurePreserving f ν' π.seedLaw) :
    (π.comapSeed ν' f hf).expectedReward=π.expectedReward :=
  (B.mapCompleteSeed_measurePreserving hf).hasLaw.integral_comp
    (π.rule.measurable_realizedReward π.measurable_rule B.terminal).aestronglyMeasurable

lemma RandomizedCountablePolicy.comapSeed_expectedDuration {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {Seed' : Type} [MeasurableSpace Seed']
    (ν' : Measure Seed') [IsProbabilityMeasure ν'] (f : Seed' → π.Seed)
    (hf : MeasurePreserving f ν' π.seedLaw) :
    (π.comapSeed ν' f hf).expectedDuration=π.expectedDuration :=
  (B.mapCompleteSeed_measurePreserving hf).hasLaw.integral_comp
    (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable

lemma RandomizedCountablePolicy.comapSeed_scalarObjective {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {Seed' : Type} [MeasurableSpace Seed']
    (ν' : Measure Seed') [IsProbabilityMeasure ν'] (f : Seed' → π.Seed)
    (hf : MeasurePreserving f ν' π.seedLaw) (w c : ℝ) :
    (π.comapSeed ν' f hf).scalarObjective w c=π.scalarObjective w c := by
  rw [RandomizedCountablePolicy.scalarObjective,π.comapSeed_expectedReward ν' f hf,
    π.comapSeed_expectedDuration ν' f hf]
  rfl

noncomputable def RandomizedCountablePolicy.adjoinAuxiliary {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {Aux : Type} [MeasurableSpace Aux]
    (ξ : Measure Aux) [IsProbabilityMeasure ξ] : RandomizedCountablePolicy B :=
  π.comapSeed (π.seedLaw.prod ξ) Prod.fst measurePreserving_fst

end ProphetSecretary.Limiting
