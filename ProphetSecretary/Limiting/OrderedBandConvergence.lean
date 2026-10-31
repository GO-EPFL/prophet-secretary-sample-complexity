import ProphetSecretary.Limiting.WeightedBandPoissonState
import ProphetSecretary.Limiting.ExtendedTailLevels
import ProphetSecretary.Limiting.CountableInstance

/-!
# Ordered convergence of individual laws and nonnegative offer bands

The ordering weight chooses actual finite permutations of the offer identities.
Padded laws are zero beyond the finite size. Below-reserve divergence is stated
for nonnegative levels, the domain relevant to nonnegative offer thresholds.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology

namespace ProphetSecretary.Limiting

/-- Structural convergence of actual finite marginals and residual bands.
The fixed-prefix original-sequence limit precedes the residual-prefix limit. -/
structure OrderedBandConvergence (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (wgt : ℝ →ᵇ ℝ) (B : CountableInstance) : Prop where
  individual_weak : ∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P m) wgt i) atTop (𝓝 (B.individuals i))
  residual_bands : ∀ (b : ℝ) (hb : (B.terminal : ℝ) < b),
    (∀ i, (B.individuals i : Measure ℝ) {b} = 0) → B.intensity {b} = 0 →
    ∃ μs : ℕ → FiniteMeasure ℝ,
      (∀ N, Tendsto (fun m => weightOrderedBandResidual (P m) wgt N b) atTop (𝓝 (μs N))) ∧
      Tendsto μs atTop (𝓝 (B.intensityAbove b hb))
  uniformly_rare : ∀ b : ℝ, (B.terminal : ℝ) < b → ∀ ε > (0 : ℝ),
    ∃ N : ℕ, ∀ m j, N ≤ j → (weightOrderedPaddedLaw (P m) wgt j : Measure ℝ).real (Ioi b) < ε
  below_reserve : ∀ x : ℝ, 0 ≤ x → x < (B.terminal : ℝ) →
    Tendsto (fun m => extendedTailCount (P m) x) atTop (𝓝 ⊤)
  above_reserve : ∀ b : ℝ, (B.terminal : ℝ) < b →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m, (P m).tailCount b ≤ K

end ProphetSecretary.Limiting
