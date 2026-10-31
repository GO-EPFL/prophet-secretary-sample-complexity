import ProphetSecretary.Limiting.CountableInstance
import ProphetSecretary.Model.WeakValueContinuity

/-!
# Finite retained-prefix states with explicit intensity and terminal reward

This auxiliary state keeps every first-N individual law, including zeros.
It is used to separate the original-sequence limit from the retained-prefix
and cutoff limits in compact extraction.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Limiting

noncomputable def CountableInstance.prefixIntensityState (B : CountableInstance) (N : ℕ)
    (b : ℝ≥0) (hbH : b ≤ B.cap) (μ : FiniteMeasure ℝ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap) : FiniteIntensityHybridInstance N where
  cap := B.cap
  terminal := b
  terminal_le_cap := hbH
  individuals := B.individualPrefix N
  individual_bounded i := (B.individual_supported i.val).mono (fun _ hx => hx.2)
  intensity := μ
  intensity_supported := hμ

lemma CountableInstance.individualPrefix_marginalProbabilityLaw (B : CountableInstance) (N : ℕ) (i : Fin N) :
    (B.individualPrefix N).marginalProbabilityLaw i = B.individuals i.val := by
  apply Subtype.ext
  rfl

end ProphetSecretary.Limiting
