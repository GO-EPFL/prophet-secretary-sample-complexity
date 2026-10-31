import ProphetSecretary.Model.NumericalRewardBounds
import ProphetSecretary.Model.CompetitiveBasic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # A self-contained strict numerical bound on the global constant
The explicit thirty-iid-plus-standby instance has unrestricted stopping value
at most `1.434` and expected maximum at least `1.967`. This supplies the strict
inequality needed by the nondegeneracy argument without a numerical axiom.
-/
namespace ProphetSecretary.Model
open NumericalCompetitiveBound

theorem optimalCompetitiveRatio_le_seventyThreeHundredths : optimalCompetitiveRatio ≤ (73 : ℝ) / 100 := by
  have hM : 0 < witnessInstance.expectedMaximum :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1967 / 1000) instance_expectedMaximum_lower
  have hC := optimalCompetitiveRatio_le_instance witnessInstance ⟨instance_integrable, hM⟩
  have hCM := (le_div_iff₀ hM).mp hC
  have hLower := mul_le_mul_of_nonneg_left instance_expectedMaximum_lower optimalCompetitiveRatio_nonnegative
  have hV := instance_optimalReward_upper
  nlinarith

/-- The exact strict relation used for finite and limiting nondegeneracy. -/
theorem optimalCompetitiveRatio_lt_sqrt_three_sub_one :
    optimalCompetitiveRatio < Real.sqrt 3 - 1 := by
  apply optimalCompetitiveRatio_le_seventyThreeHundredths.trans_lt
  have hSquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hPositive := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem optimalCompetitiveRatio_quadratic_strict :
    optimalCompetitiveRatio ^ 2 + 2 * optimalCompetitiveRatio < 2 := by
  have hC := optimalCompetitiveRatio_le_seventyThreeHundredths
  have hSq := mul_le_mul hC hC optimalCompetitiveRatio_nonnegative (by norm_num : (0 : ℝ) ≤ 73 / 100)
  nlinarith

end ProphetSecretary.Model
