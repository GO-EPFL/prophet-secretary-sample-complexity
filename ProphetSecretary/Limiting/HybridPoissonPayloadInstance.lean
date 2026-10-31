import ProphetSecretary.Limiting.PoissonPayloadIntensity
import ProphetSecretary.Limiting.HybridScalarObjectives

/-!
# A hybrid instance with a displayed anonymous payload

Only the anonymous mark intensity is replaced by the actual payload image.
Retained identities and laws, independent arrival clocks and terminal reward
are unchanged. An explicit larger cap certifies every displayed offer.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting
variable {n : ℕ} {T : Type*} [MeasurableSpace T]

noncomputable def FiniteIntensityHybridInstance.displayPoissonPayload
    (B : FiniteIntensityHybridInstance n) (H : ℝ≥0) (hH : B.cap≤H)
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g)
    (hImage : ∀ᵐ z ∂(B.intensity : Measure ℝ).prod κ, g z∈Ioc (0 : ℝ) H) : FiniteIntensityHybridInstance n where
  cap := H
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap.trans hH
  individuals := B.individuals
  individual_bounded i := (B.individual_bounded i).mono (fun _ hx => hx.trans hH)
  intensity := displayedPayloadIntensity B.intensity κ g hg
  intensity_supported := by
    rw [displayedPayloadIntensity_toMeasure]
    exact (ae_map_iff hg.aemeasurable measurableSet_Ioc).mpr hImage

lemma FiniteIntensityHybridInstance.displayPoissonPayload_law
    (B : FiniteIntensityHybridInstance n) (H : ℝ≥0) (hH : B.cap≤H)
    (κ : Measure T) [IsProbabilityMeasure κ] (g : ℝ × T → ℝ) (hg : Measurable g)
    (hImage : ∀ᵐ z ∂(B.intensity : Measure ℝ).prod κ, g z∈Ioc (0 : ℝ) H)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) :
    (B.displayPoissonPayload H hH κ g hg hImage).law ν=
      hybridWorldLaw B.individuals (displayedPayloadIntensity B.intensity κ g hg) ν := rfl

end ProphetSecretary.Limiting
