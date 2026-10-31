import ProphetSecretary.Limiting.WeightedPaddedBenchmark
import ProphetSecretary.Limiting.WeightedBandPoissonState
import ProphetSecretary.Limiting.PoissonBandBenchmark

/-!
# Actual benchmark errors for ordered finite Poisson states

The finite maximum includes the same terminal reward before the Poisson
comparison. Its error is explicitly dimension-free under the ordering weight.
-/

open MeasureTheory Set BoundedContinuousFunction
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

theorem weightOrderedBandState_benchmark_comparison (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    (H b : ℝ≥0) (hbH : b ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    0 ≤ P.expectedTerminalMaximum b-(weightOrderedBandState P wgt N H b hbH hcap).expectedMaximum ∧
      P.expectedTerminalMaximum b-(weightOrderedBandState P wgt N H b hbH hcap).expectedMaximum ≤
        (H : ℝ)*(∑ i : Fin n, ((weightOrderedRemainder P wgt N).law i).real (Ioi (b : ℝ))^2) := by
  let S := (weightOrderedPrefix P wgt N).appendIndependent (weightOrderedRemainder P wgt N)
  have hM : S.expectedTerminalMaximum b = P.expectedTerminalMaximum b := by
    exact (congrArg (fun T : Model.Instance (N+n) => T.expectedTerminalMaximum b)
      (weightOrderedPrefix_append_remainder P wgt N)).trans
        (weightOrderedPrefix_full_terminal_benchmark P wgt N (P.integrable_maximum_of_bounded hcap) b.property)
  have h := finite_poisson_band_benchmark_comparison (weightOrderedPrefix P wgt N) (weightOrderedRemainder P wgt N)
    H b hbH (weightOrderedPrefix_bounded P wgt N H.property hcap)
    (weightOrderedRemainder_bounded P wgt N H.property hcap)
  change 0 ≤ S.expectedTerminalMaximum b-(weightOrderedBandState P wgt N H b hbH hcap).expectedMaximum ∧
    S.expectedTerminalMaximum b-(weightOrderedBandState P wgt N H b hbH hcap).expectedMaximum ≤ _ at h
  rw [hM] at h
  exact h

theorem weightOrderedBandState_benchmark_error_le (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    (H b : ℝ≥0) (hbH : b ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hwgt0 : ∀ x, 0 ≤ wgt x) (hwgtZero : wgt 0 = 0)
    (hWeight : (∑ i, ∫ x, wgt x ∂P.law i) ≤ 1)
    (hbPos : 0 < wgt b) (hbMono : ∀ x, (b : ℝ) < x → wgt b ≤ wgt x) :
    |P.expectedTerminalMaximum b-(weightOrderedBandState P wgt N H b hbH hcap).expectedMaximum| ≤
      (H : ℝ)*(1/((wgt b)^2*(N+1 : ℕ))) := by
  have h := weightOrderedBandState_benchmark_comparison P wgt N H b hbH hcap
  rw [abs_of_nonneg h.1]
  have hs := weightOrderedPaddedLaw_residual_tail_square_sum_le P wgt hwgt0 hwgtZero hWeight hbPos hbMono N
  have he := weightOrderedRemainder_tail_square_sum P wgt N b.property
  have hs' : (∑ i : Fin n, ((weightOrderedRemainder P wgt N).law i).real (Ioi (b : ℝ))^2) ≤
      1/((wgt b)^2*(N+1 : ℕ)) := he.le.trans hs
  exact h.2.trans (mul_le_mul_of_nonneg_left hs' H.property)

end ProphetSecretary.Limiting
