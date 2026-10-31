import ProphetSecretary.Limiting.PoissonPayloadIntensity
import ProphetSecretary.Limiting.HybridScalarObjectives
import ProphetSecretary.Probability.ConditionalPayloadSampler
import ProphetSecretary.Model.ClockReplacement

/-!
# Conditional sampling for an actual displayed Poisson intensity

The sampler is constructed from the normalized old mark and independent tag
law. The exact displayed intensity and complete Poisson-mixture law then
prove its full joint pushforward. Policy seeds remain arbitrary independent
measurable spaces and are not part of the disintegration.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal unitInterval

namespace ProphetSecretary.Limiting

noncomputable def conditionalTaggedHybridWorld {n : ℕ} {Seed U T : Type*}
    (F : ℝ × U → ℝ × T) (v : HybridWorld n (Seed × (ℕ → U))) :
    PayloadConfiguration T × Model.World n Seed :=
  (chronologicalPayloadConfiguration F (v.1,v.2.2.2.2),(v.2.1,(v.2.2.1,v.2.2.2.1)))

theorem exists_poisson_conditional_payload_sampler (μ : FiniteMeasure ℝ)
    {T : Type*} [MeasurableSpace T] [StandardBorelSpace T] (κ : Measure T) [IsProbabilityMeasure κ]
    (g : ℝ × T → ℝ) (hg : Measurable g) :
    ∃ F : ℝ × unitInterval → ℝ × T, Measurable F ∧
      (∀ᵐ z ∂(displayedPayloadMarkLaw μ κ g hg : Measure ℝ).prod (volume : Measure unitInterval), g (F z)=z.1) ∧
      ∀ (n : ℕ) (P : Model.Instance n) {Seed : Type*} [MeasurableSpace Seed]
        (ν : Measure Seed) [IsProbabilityMeasure ν],
        MeasurePreserving (conditionalTaggedHybridWorld F)
          (hybridWorldLaw P (displayedPayloadIntensity μ κ g hg)
            (ν.prod (Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval)))))
          ((payloadConfigurationLaw μ.mass (μ.normalize : Measure ℝ) κ).prod (P.worldLaw ν)) := by
  obtain ⟨F,hF,_,hMarg,hGraph⟩ := ProphetSecretary.Probability.exists_conditional_payload_sampler
    ((μ.normalize : Measure ℝ).prod κ) g hg
  have hKernel : MeasurePreserving (Function.uncurry F)
      ((displayedPayloadMarkLaw μ κ g hg : Measure ℝ).prod (volume : Measure unitInterval))
      ((μ.normalize : Measure ℝ).prod κ) := hMarg
  refine ⟨Function.uncurry F,hF,hGraph,?_⟩
  intro n P Seed _ ν _
  let K := Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))
  let C := rateConfigurationLaw μ.mass (displayedPayloadMarkLaw μ κ g hg : Measure ℝ)
  have hOne := (MeasurePreserving.id P.valuesLaw).prod
    ((measurePreserving_prodAssoc (Model.Instance.clocksLaw n) ν K).symm MeasurableEquiv.prodAssoc)
  have hTwo := (measurePreserving_prodAssoc P.valuesLaw ((Model.Instance.clocksLaw n).prod ν) K).symm MeasurableEquiv.prodAssoc
  have hOuter := (MeasurePreserving.id C).prod (hTwo.comp hOne)
  have hAssoc := (measurePreserving_prodAssoc C (P.worldLaw ν) K).symm MeasurableEquiv.prodAssoc
  have hSwap := Model.measurePreserving_swap_last C (P.worldLaw ν) K
  have hPayload := chronologicalPayloadConfiguration_measurePreserving μ.mass
    (displayedPayloadMarkLaw μ κ g hg : Measure ℝ) (μ.normalize : Measure ℝ)
    (volume : Measure unitInterval) κ hKernel
  have hAll := (hPayload.prod (MeasurePreserving.id (P.worldLaw ν))).comp (hSwap.comp (hAssoc.comp hOuter))
  unfold hybridWorldLaw worldLaw
  rw [configurationLaw_displayedPayloadIntensity]
  exact hAll

end ProphetSecretary.Limiting
