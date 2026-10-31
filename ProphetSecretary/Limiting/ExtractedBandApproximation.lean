import ProphetSecretary.Limiting.FixedBandTwoLimits
import ProphetSecretary.Limiting.ExtractedCountableInstance

/-!
# The two actual approximation limits for extracted measure data

Residual domination, supports and weak laws are derived from the weighted
extraction identities. This instantiates the fixed-band comparison, rather
than postulating a limiting value or a policy-convergence interface.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators

namespace ProphetSecretary.Limiting

section Extracted

variable (H : ℝ≥0) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) H)
    (wgt : ℝ →ᵇ ℝ) (hwgt0 : ∀ x, 0 ≤ wgt x) (hwgtZero : wgt 0 = 0)
    (hwgt : Monotone wgt) (hpos : ∀ b, a < b → 0 < wgt b)
    (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) wgt+ρ (N+1))
    (hQ : ∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0)
    (hρcap : ∀ N, (ρ N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) (hρmass : (ρ 0).mass ≤ 1)
    (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ))
    (hWeight : ∀ m, (∑ i, ∫ x, wgt x ∂(P m).law i) ≤ 1)
    (hQweak : ∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P m) wgt i) atTop (𝓝 (Q i)))
    (hρweak : ∀ N, Tendsto (fun m => weightOrderedResidual (P m) wgt N) atTop (𝓝 (ρ N)))

local notation "B" => extractedCountableInstance H a ha wgt hwgt0 hwgt hpos Q ρ hρ hQ (hρcap 0)

include hwgtZero hρmass hcap hWeight hQweak hρweak

/-- The actual fixed-cutoff approximation preserves the order of limits:
original finite sequence first, retained prefix second. -/
theorem extracted_fixed_band_approximation (b W : ℝ≥0) (hb : a < b) (hbH : b ≤ H)
    (hQatom : ∀ i, (Q i : Measure ℝ) {(b : ℝ)} = 0) (hμatom : (B).intensity {(b : ℝ)} = 0) :
    (∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop, ∀ w c : ℝ,
      0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
      |Model.optimalTerminalScalarValue (P m) b w c-
        ((B).prefixIntensityState N b hbH ((B).intensityAbove b hb)
          ((B).truncation N b hb).intensity_supported).optimalScalarValue w c| < ε) ∧
    (∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop,
      |(P m).expectedTerminalMaximum b-
        ((B).prefixIntensityState N b hbH ((B).intensityAbove b hb)
          ((B).truncation N b hb).intensity_supported).expectedMaximum| < ε) := by
  let η := extractedContinuousWeightedResidual wgt Q ρ
  let μs : ℕ → FiniteMeasure ℝ := fun N => reserveMarkIntensityAbove (ρ N) wgt a b hwgt hb (hpos b hb)
  have hμs (N : ℕ) : ∀ᵐ x ∂(μs N : Measure ℝ), x ∈ Ioc (0 : ℝ) (B).cap := by
    have hBase : ∀ᵐ x ∂reserveMarkIntensity (ρ N) wgt a, x ∈ Ioc a H :=
      ae_iff.mpr (reserveMarkIntensity_supported_interval (ρ N) wgt a (hρcap N))
    have hRestrict : ∀ᵐ x ∂(μs N : Measure ℝ), x ∈ Ioc a H := ae_restrict_of_ae hBase
    exact hRestrict.mono (fun _ hx => ⟨ha.1.trans_lt hx.1,hx.2⟩)
  have hOrder (N : ℕ) : ((B).intensityAbove b hb : Measure ℝ) ≤ (μs N : Measure ℝ) := by
    change (reserveMarkIntensityAbove η wgt a b hwgt hb (hpos b hb) : Measure ℝ) ≤ _
    exact reserveMarkIntensityAbove_extracted_le_prefix wgt Q ρ hρ a b hwgt hb (hpos b hb) N
  have hBand := (continuousWeighted_positive_band_limits H 1 a wgt hwgt0 hwgt hpos Q ρ hρ
    (hρcap 0) hρmass sizes P hρweak).2.2.2 b hb hQatom hμatom
  have hWeak : Tendsto μs atTop (𝓝 ((B).intensityAbove b hb)) := hBand.2
  exact ⟨fixed_band_scalar_two_limits sizes P B wgt b W hb hbH hcap hwgt0 hwgtZero hwgt hWeight
      (hpos b hb) μs hμs hOrder hWeak hQweak hBand.1,
    fixed_band_benchmark_two_limits sizes P B wgt b hb hbH hcap hwgt0 hwgtZero hwgt hWeight
      (hpos b hb) μs hμs hOrder hWeak hQweak hBand.1⟩

end Extracted

end ProphetSecretary.Limiting
