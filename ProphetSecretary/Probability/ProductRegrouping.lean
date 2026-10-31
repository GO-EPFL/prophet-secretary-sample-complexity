import Mathlib.MeasureTheory.Measure.Prod

/-!
# Regrouping independent product factors

The four-factor shuffle pairs each raw-data block with its own independent tag
block. Its product law follows from measurable product associativity and swap.
-/

open MeasureTheory
namespace ProphetSecretary.Probability

lemma productPairShuffle_measurePreserving
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μB] [IsProbabilityMeasure μC] [IsProbabilityMeasure μD] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h0 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h1 := (MeasurePreserving.id μA).prod
    ((measurePreserving_prodAssoc μB μC μD).symm (MeasurableEquiv.prodAssoc : ((B × C) × D) ≃ᵐ (B × (C × D))))
  have h2 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ:=μB) (ν:=μC)).prod (MeasurePreserving.id μD))
  have h3 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h4 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm (MeasurableEquiv.prodAssoc : ((A × C) × (B × D)) ≃ᵐ (A × (C × (B × D))))
  exact h4.comp (h3.comp (h2.comp (h1.comp h0)))

end ProphetSecretary.Probability
