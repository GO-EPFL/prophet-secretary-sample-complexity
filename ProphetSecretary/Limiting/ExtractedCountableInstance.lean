import ProphetSecretary.Limiting.CountableInstance
import ProphetSecretary.Limiting.ReserveResidualOrder

/-!
# The actual countable instance supplied by weighted measure extraction

Every support and local-finiteness obligation is discharged from the positive
weighted residual and the extracted prefix identities. No scalar-value or
policy convergence is stored in the instance data.
-/

open MeasureTheory Set BoundedContinuousFunction
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

noncomputable def extractedCountableInstance (H : ℝ≥0) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) H)
    (w : ℝ →ᵇ ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw : Monotone w) (hpos : ∀ b, a < b → 0 < w b)
    (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w+ρ (N+1))
    (hQ : ∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0)
    (hρCap : (ρ 0 : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) : CountableInstance where
  cap := H
  terminal := ⟨a,ha.1⟩
  terminal_le_cap := by exact_mod_cast ha.2
  individuals := Q
  individual_supported i := ae_iff.mpr (hQ i)
  intensity := reserveMarkIntensity (extractedContinuousWeightedResidual w Q ρ) w a
  intensity_supported := ae_iff.mpr (reserveMarkIntensity_supported_interval _ w a
    (extractedContinuousWeightedResidual_supported_interval w Q ρ hρCap))
  individual_tail_finite b hb :=
    (reserve_extracted_individual_tail_sum_le w hw0 a hw Q ρ hρ hb (hpos b hb)).trans_lt ENNReal.ofReal_lt_top
  intensity_tail_finite b hb :=
    (reserveMarkIntensity_tail_le _ w a hw hb (hpos b hb)).trans_lt ENNReal.ofReal_lt_top

end ProphetSecretary.Limiting
