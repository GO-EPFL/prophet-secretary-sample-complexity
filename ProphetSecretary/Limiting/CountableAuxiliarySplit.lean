import ProphetSecretary.Limiting.CountableSeedTransport

/-!
# Separating one independent auxiliary factor of the complete world

The exact product rearrangement permits Fubini with arbitrary policy seed
spaces. It adds no information to a callback.
-/

open MeasureTheory Set

namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def splitCompleteAuxiliary {Seed T : Type*} (v : CompleteWorld (Seed × T)) : CompleteWorld Seed × T :=
  (mapCompleteSeed Prod.fst v,v.2.2.2.2)

lemma CountableInstance.splitCompleteAuxiliary_measurePreserving (B : CountableInstance)
    {Seed T : Type*} [MeasurableSpace Seed] [MeasurableSpace T]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (κ : Measure T) [IsProbabilityMeasure κ] :
    MeasurePreserving splitCompleteAuxiliary (B.completeWorldLaw (ν.prod κ)) ((B.completeWorldLaw ν).prod κ) := by
  have h₁ := (MeasurePreserving.id B.bandConfigurationsLaw).prod
    ((MeasurePreserving.id B.individualValuesLaw).prod
      ((measurePreserving_prodAssoc individualClocksLaw ν κ).symm MeasurableEquiv.prodAssoc))
  have h₂ := (MeasurePreserving.id B.bandConfigurationsLaw).prod
    ((measurePreserving_prodAssoc B.individualValuesLaw (individualClocksLaw.prod ν) κ).symm MeasurableEquiv.prodAssoc)
  have h₃ := (measurePreserving_prodAssoc B.bandConfigurationsLaw (B.individualValuesLaw.prod (individualClocksLaw.prod ν)) κ).symm MeasurableEquiv.prodAssoc
  exact h₃.comp (h₂.comp h₁)

end ProphetSecretary.Limiting
