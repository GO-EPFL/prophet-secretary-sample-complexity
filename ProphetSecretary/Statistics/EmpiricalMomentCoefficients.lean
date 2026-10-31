import ProphetSecretary.Statistics.WeightedCriticalMoments

/-!
# Explicit coefficients in the empirical entrance moment profiles

The second and sixth moment constants depend only on the fixed scalar
interval. Factoring them out makes the expected regional loss constants
independent of the state, number of variables, and sample budget.
-/

namespace ProphetSecretary.Model

noncomputable def empiricalSecondMomentConstant (lo hi : ℝ) : ℝ :=
  16 * (18 * (128 + 4 * (hi - lo) ^ 2 / hi))

noncomputable def empiricalSixthMomentConstant (lo hi : ℝ) : ℝ :=
  832 * (23328 * (2 * (6672000000000 ^ 2 + 13348000000000) +
    (106000000000 ^ 2 + 212000000000) * (hi - lo) ^ 6 / hi ^ 3))

lemma empiricalSecondMomentConstant_nonnegative {lo hi : ℝ} (hhi : 0 < hi) :
    0 ≤ empiricalSecondMomentConstant lo hi := by unfold empiricalSecondMomentConstant; positivity

lemma empiricalSixthMomentConstant_nonnegative {lo hi : ℝ} (hhi : 0 < hi) :
    0 ≤ empiricalSixthMomentConstant lo hi := by unfold empiricalSixthMomentConstant; positivity

lemma empiricalRestartMomentBound_two (k : ℕ) (lo hi a : ℝ) :
    empiricalRestartMomentBound k lo hi a 2 =
      empiricalSecondMomentConstant lo hi * (a / (k : ℝ) + 1 / (k : ℝ) ^ 2) := by
  simp only [empiricalRestartMomentBound, ↓reduceIte, empiricalSecondMomentConstant]

lemma empiricalRestartMomentBound_six (k : ℕ) (lo hi a : ℝ) :
    empiricalRestartMomentBound k lo hi a 6 =
      empiricalSixthMomentConstant lo hi * (a ^ 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6) := by
  simp only [empiricalRestartMomentBound, show ¬(6 : ℕ) = 2 by decide, ↓reduceIte, empiricalSixthMomentConstant]

end ProphetSecretary.Model
