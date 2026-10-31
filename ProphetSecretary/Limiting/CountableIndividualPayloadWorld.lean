import ProphetSecretary.Limiting.CountableConditionalIndividualWorld
import ProphetSecretary.Probability.InfiniteCoordinatePayload

/-!
# Actual full-world law of a reconstructed individual payload

The displayed coordinate and fresh auxiliary sample reconstruct the old value
and its independent occurrence tag jointly. The untouched identities, clocks,
anonymous process and arbitrary policy seed retain their complete product law.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed U T : Type*} [MeasurableSpace Seed] [MeasurableSpace U] [MeasurableSpace T]

noncomputable def recoverIndividualPayloadWorld (i : ℕ) (F : ℝ × U → ℝ × T)
    (v : CompleteWorld (Seed × U)) : CompleteWorld (Seed × T) :=
  (v.1,(Function.update v.2.1 i (F (v.2.1 i,v.2.2.2.2)).1,
    (v.2.2.1,(v.2.2.2.1,(F (v.2.1 i,v.2.2.2.2)).2))))

lemma recoverIndividualPayloadWorld_measurePreserving (B : CountableInstance) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hSupport : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (κ : Measure T) [IsProbabilityMeasure κ] {F : ℝ × U → ℝ × T}
    (hF : MeasurePreserving F ((q : Measure ℝ).prod ρ) ((B.individuals i : Measure ℝ).prod κ)) :
    MeasurePreserving (recoverIndividualPayloadWorld i F)
      ((B.updateIndividual i q hSupport).completeWorldLaw (ν.prod ρ)) (B.completeWorldLaw (ν.prod κ)) := by
  let D := B.updateIndividual i q hSupport
  have hFD : MeasurePreserving F ((D.individuals i : Measure ℝ).prod ρ) ((B.individuals i : Measure ℝ).prod κ) := by
    simpa only [D,updateIndividual,Function.update_self] using hF
  have hCoordinate : MeasurePreserving (fun z : (ℕ → ℝ) × U =>
      (Function.update z.1 i (F (z.1 i,z.2)).1,(F (z.1 i,z.2)).2))
      (D.individualValuesLaw.prod ρ) (B.individualValuesLaw.prod κ) := by
    have h := ProphetSecretary.Probability.infinite_randomCoordinate_payload_measurePreserving
      (fun j => (D.individuals j : Measure ℝ)) i (0 : ℝ) ρ (B.individuals i : Measure ℝ) κ hFD
    have hFamily : Function.update (fun j => (D.individuals j : Measure ℝ)) i (B.individuals i : Measure ℝ)=
        (fun j => (B.individuals j : Measure ℝ)) := by
      funext j
      by_cases hj : j=i
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hj,D,updateIndividual]
    rw [hFamily] at h
    exact h
  have hMap := (MeasurePreserving.id B.bandConfigurationsLaw).prod
    (hCoordinate.prod (MeasurePreserving.id (individualClocksLaw.prod ν)))
  have hSwap := Model.measurePreserving_swap_last B.individualValuesLaw κ (individualClocksLaw.prod ν)
  have hAssoc := measurePreserving_prodAssoc B.individualValuesLaw (individualClocksLaw.prod ν) κ
  have hInner := (MeasurePreserving.id B.individualValuesLaw).prod (measurePreserving_prodAssoc individualClocksLaw ν κ)
  have hMerge := (MeasurePreserving.id B.bandConfigurationsLaw).prod (hInner.comp (hAssoc.comp hSwap))
  exact hMerge.comp (hMap.comp (D.separateIndividualAuxiliary_measurePreserving ν ρ))

end ProphetSecretary.Limiting.CountableInstance
