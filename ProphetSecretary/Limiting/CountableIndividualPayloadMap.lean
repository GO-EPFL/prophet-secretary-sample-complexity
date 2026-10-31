import ProphetSecretary.Limiting.CountableConditionalIndividualWorld

/-!
# Displaying a measurable individual payload

The payload consists of its original value and an independent occurrence tag.
Its displayed-value marginal replaces exactly one individual law. The actual
forward world map preserves the full displayed instance law and drops the
latent tag from the independent policy seed.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance
variable {T : Type} [MeasurableSpace T]

noncomputable def individualPayloadLaw (B : CountableInstance) (i : ℕ)
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g) : ProbabilityMeasure ℝ :=
  ⟨((B.individuals i : Measure ℝ).prod κ).map g,
    ((B.individuals i : Measure ℝ).prod κ).isProbabilityMeasure_map hg.aemeasurable⟩

noncomputable def mapIndividualPayload (B : CountableInstance) (i : ℕ)
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap) : CountableInstance :=
  B.updateIndividual i (B.individualPayloadLaw i κ g hg) ((ae_map_iff hg.aemeasurable measurableSet_Icc).mpr hSupport)

lemma mapIndividualPayload_restore (B : CountableInstance) (i : ℕ)
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap) :
    (B.mapIndividualPayload i κ g hg hSupport).updateIndividual i (B.individuals i) (B.individual_supported i)=B := by
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · funext j
    change Function.update (Function.update B.individuals i (B.individualPayloadLaw i κ g hg)) i (B.individuals i) j=B.individuals j
    rw [Function.update_idem,Function.update_eq_self]
  · rfl

lemma displayedIndividualWorld_measurePreserving (B : CountableInstance) (i : ℕ)
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, g z∈Icc (0 : ℝ) B.cap)
    {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (recoverIndividualWorld i g) (B.completeWorldLaw (ν.prod κ))
      ((B.mapIndividualPayload i κ g hg hSupport).completeWorldLaw ν) := by
  let D := B.mapIndividualPayload i κ g hg hSupport
  have hG : MeasurePreserving g ((B.individuals i : Measure ℝ).prod κ) (D.individuals i : Measure ℝ) := by
    refine ⟨hg,?_⟩
    change ((B.individuals i : Measure ℝ).prod κ).map g=
      ((Function.update B.individuals i (B.individualPayloadLaw i κ g hg)) i : Measure ℝ)
    rw [Function.update_self]
    rfl
  have h := D.recoverIndividualWorld_measurePreserving i (B.individuals i) (B.individual_supported i) ν κ hG
  rw [B.mapIndividualPayload_restore i κ g hg hSupport] at h
  exact h

end ProphetSecretary.Limiting.CountableInstance
