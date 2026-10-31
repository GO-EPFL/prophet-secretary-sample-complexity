import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Absorbing the logarithmic first-moment inequality

The final numerical bound in `upmom:theorem` follows from its explicit scalar
inequality. This analytic lemma does not assume the paper's integrated estimate
has been proved; that estimate must be supplied by the instance-level argument.
-/
namespace ProphetSecretary.Analysis

lemma log_one_add_le_quarter_add_log_four {S : ℝ} (hS : 0 ≤ S) :
    Real.log (1 + S) ≤ S / 4 + Real.log 4 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (1 + S) / 4)
  rw [Real.log_div (by positivity : (1 + S) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)] at h
  linarith only [h]

/-- The explicit bound B=17/2+2 log(4K₀) from the final paragraph of the
first-moment proof, with every required hypothesis exposed. -/
theorem firstMoment_logarithmic_absorption {S K₀ : ℝ} (hS : 0 ≤ S) (hK : 0 < K₀)
    (hscalar : S ≤ (1 + S) / 4 + Real.log (K₀ * (1 + S)) + 4) :
    S ≤ 17 / 2 + 2 * Real.log (4 * K₀) := by
  have hlog := log_one_add_le_quarter_add_log_four hS
  rw [Real.log_mul hK.ne' (by positivity : (1 + S) ≠ 0)] at hscalar
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hK.ne']
  linarith only [hscalar,hlog]

end ProphetSecretary.Analysis
