import ProphetSecretary.Limiting.CompactBandExtraction

/-!
# Compact extraction of scalar values and prophet benchmarks

This is the scalar-value and benchmark conclusion of `lem:compact-extract`.
A single subsequence and actual countable
individual/Poisson instance work for the prophet benchmark and every scalar
weight. The scalar convergence is uniform on bounded nonnegative rectangles,
which in particular gives the manuscript's compact positive weight sets.

The limiting scalar value is the supremum over actual admissible randomized
countable-history policies; it is not defined by the approximating values.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators

namespace ProphetSecretary.Limiting

/-- Scalar-value and benchmark part of `lem:compact-extract`: arbitrary finite dimensions, a common cap, one
subsequence, actual maximum convergence and uniform full-policy scalar values. -/
theorem exists_cap_bounded_value_convergent_subsequence (H : ℝ≥0) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ B : CountableInstance, B.cap = H ∧
      Tendsto (fun m => (P (φ m)).expectedMaximum) atTop (𝓝 B.expectedMaximum) ∧
      ∀ W C : ℝ≥0, ∀ ε > (0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ,
        0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c → c ≤ (C : ℝ) →
        |Model.optimalScalarValue (P (φ m)) w c-B.optimalScalarValue w c| < ε := by
  obtain ⟨φ,hφ,B,_wgt,hCap,_hBands,hM,hV⟩ := exists_cap_bounded_ordered_band_subsequence H sizes P hcap
  exact ⟨φ,hφ,B,hCap,hM,hV⟩

end ProphetSecretary.Limiting
