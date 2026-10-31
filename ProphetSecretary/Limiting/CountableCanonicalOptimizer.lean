import ProphetSecretary.Limiting.CountableValueMeanLimit
import ProphetSecretary.Limiting.CountableValueLimit

/-!
# Actual canonical optimization on the countable instance

This proves the optimizer assertion in `lem:canonical-limit`. The canonical
finite truncations have their actual optimal objectives. Their outcomes were
proved to converge on the common full world before transferring expectations.
Uniqueness and the general near-optimal outcome modulus are separate results.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

theorem valuePolicy_optimal (B : CountableInstance) (hZero : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    (B.valuePolicy hw hc).scalarObjective w c = B.optimalScalarValue w c := by
  have hMeans := B.valuePolicy_truncation_means_tendsto hZero hw hc
  have hObjective : Tendsto (fun N =>
      (B.truncatedValuePolicy N (B.markCutoff N) (B.terminal_lt_markCutoff N) hw.le hc.le).scalarObjective w c)
      atTop (𝓝 ((B.valuePolicy hw hc).scalarObjective w c)) :=
    (hMeans.1.const_mul w).add (hMeans.2.const_mul c)
  have hValues := B.truncation_value_tendsto (fun N : ℕ => N) B.markCutoff B.terminal_lt_markCutoff
    tendsto_id B.markCutoff_tendsto hw.le hc.le
  have hEqual : (fun N => (B.truncation N (B.markCutoff N) (B.terminal_lt_markCutoff N)).optimalScalarValue w c) =ᶠ[atTop]
      (fun N => (B.truncatedValuePolicy N (B.markCutoff N) (B.terminal_lt_markCutoff N) hw.le hc.le).scalarObjective w c) :=
    Eventually.of_forall (fun N => (B.truncatedValuePolicy_scalarObjective hZero N (B.markCutoff N)
      (B.terminal_lt_markCutoff N) hw hc.le).symm)
  have hOptimalLimit := Tendsto.congr' hEqual hValues
  exact tendsto_nhds_unique hObjective hOptimalLimit

end ProphetSecretary.Limiting.CountableInstance
