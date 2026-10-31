import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A local exponential bound retaining the second moment

The installed exponential-series remainder gives a variance-sensitive local
moment-generating-function bound, rather than a dimension-dependent range proxy.
-/

namespace ProphetSecretary.Analysis

lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) : Real.exp x ≤ 1+x+x^2 := by
  have h := Real.exp_bound (n := 2) hx (by decide : 0 < 2)
  norm_num [Finset.sum_range_succ,sq_abs] at h
  have hu := (abs_le.mp h).2
  nlinarith only [hu,sq_nonneg x]

end ProphetSecretary.Analysis
