import ProphetSecretary.Limiting.ExtractedDataConvergence
import ProphetSecretary.Limiting.ExtractedBandConvergence
import ProphetSecretary.Limiting.ReserveMeasureExtraction

/-!
# Compact extraction at nonnegative offer levels

A single subsequence has actual individual and residual-band convergence,
nonnegative below-reserve divergence, maximum convergence and scalar values
uniform on bounded nonnegative weight rectangles.

The limiting scalar value is the supremum over actual admissible randomized
countable-history policies; it is not defined by the approximating values.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators

namespace ProphetSecretary.Limiting

/-- Nonnegative-level structural extraction with the actual scalar and
benchmark conclusions of `lem:compact-extract`, on the same subsequence. -/
theorem exists_cap_bounded_ordered_band_subsequence (H : ℝ≥0) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (B : CountableInstance) (wgt : ℝ →ᵇ ℝ), B.cap = H ∧
      OrderedBandConvergence (fun m => sizes (φ m)) (fun m => P (φ m)) wgt B ∧
      Tendsto (fun m => (P (φ m)).expectedMaximum) atTop (𝓝 B.expectedMaximum) ∧
      ∀ W C : ℝ≥0, ∀ ε > (0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ,
        0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c → c ≤ (C : ℝ) →
        |Model.optimalScalarValue (P (φ m)) w c-B.optimalScalarValue w c| < ε := by
  obtain ⟨a,wgt,Q,ρ,φ,hφ,ha,hwgt0,hwgt,hzero,hpos,hWeight,hQ,hρmass,hρcap,
      hQweak,hρweak,hρ,hBelow,_hRare⟩ := exists_cap_bounded_reserve_measure_data H sizes P hcap
  let B := extractedCountableInstance H a ha wgt hwgt0 hwgt hpos Q ρ hρ hQ (hρcap 0)
  have hConv (W C : ℝ≥0) : ∀ ε > (0 : ℝ), ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c → c ≤ (C : ℝ) →
        |Model.optimalScalarValue (P (φ m)) w c-B.optimalScalarValue w c| < ε) ∧
      |(P (φ m)).expectedMaximum-B.expectedMaximum| < ε :=
    extracted_data_convergence H a ha wgt hwgt0 (hzero 0 ha.1) hwgt hpos Q ρ hρ hQ hρcap (hρmass 0)
      (fun m => sizes (φ m)) (fun m => P (φ m)) (fun m => hcap (φ m)) hWeight hQweak hρweak hBelow W C
  have hBand : OrderedBandConvergence (fun m => sizes (φ m)) (fun m => P (φ m)) wgt B :=
    extracted_data_ordered_band_convergence H a ha wgt hwgt0 (hzero 0 ha.1) hwgt hpos Q ρ hρ hQ hρcap (hρmass 0)
      (fun m => sizes (φ m)) (fun m => P (φ m)) hWeight hQweak hρweak hBelow
  refine ⟨φ,hφ,B,wgt,rfl,hBand,?_,?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hConv 0 0 ε hε] with m hm
    simpa only [Real.dist_eq] using hm.2
  · intro W C ε hε
    filter_upwards [hConv W C ε hε] with m hm
    exact hm.1

end ProphetSecretary.Limiting
