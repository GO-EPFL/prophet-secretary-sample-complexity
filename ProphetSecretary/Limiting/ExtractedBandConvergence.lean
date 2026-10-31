import ProphetSecretary.Limiting.OrderedBandConvergence
import ProphetSecretary.Limiting.ExtractedBandApproximation
import ProphetSecretary.Limiting.WeightedTailCount

/-!
# Structural nonnegative-band convergence from actual extracted data

Every structural field is proved from the retained/residual measure identities,
weak extraction, ordering and actual finite tail-count bounds.
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
    (hBelow : ∀ ℓ, 0 ≤ ℓ → ℓ < a → Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤))

local notation "B" => extractedCountableInstance H a ha wgt hwgt0 hwgt hpos Q ρ hρ hQ (hρcap 0)

include hwgtZero hρmass hWeight hQweak hρweak hBelow

theorem extracted_data_ordered_band_convergence : OrderedBandConvergence sizes P wgt B := by
  refine ⟨hQweak,?_,?_,hBelow,?_⟩
  · intro b hb hQatom hμatom
    have hBand := (continuousWeighted_positive_band_limits H 1 a wgt hwgt0 hwgt hpos Q ρ hρ
      (hρcap 0) hρmass sizes P hρweak).2.2.2 b hb hQatom hμatom
    exact ⟨fun N => reserveMarkIntensityAbove (ρ N) wgt a b hwgt hb (hpos b hb),hBand.1,hBand.2⟩
  · intro b hb ε hε
    exact weightOrdered_residual_uniformly_rare sizes P wgt hwgt0 hwgtZero hWeight
      (hpos b hb) (fun y hby => hwgt hby.le) hε
  · intro b hb
    exact ⟨1/wgt b,one_div_nonneg.mpr (hwgt0 b),fun m =>
      tailCount_le_inverse_weight (P m) wgt hwgt0 hwgt (hWeight m) (hpos b hb)⟩

end Extracted

end ProphetSecretary.Limiting
