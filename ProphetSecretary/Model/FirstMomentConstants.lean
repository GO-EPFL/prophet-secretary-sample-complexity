import ProphetSecretary.Model.FirstMomentError

/-!
# Uniform constants in the first-moment argument

These abbreviate the paper's ρ, γ and κ. They depend only on the global
competitive ratio and δ. Positivity uses the already proved finite-instance
upper bound on the global ratio.
-/

namespace ProphetSecretary.Model

noncomputable def firstMomentSurvivalConstant : ℝ := (1 - optimalCompetitiveRatio) / 2
noncomputable def firstMomentWindowConstant (δ : ℝ) : ℝ := min (firstMomentSurvivalConstant / 4) (δ / 2)
noncomputable def firstMomentSelectionConstant (δ : ℝ) : ℝ :=
  firstMomentWindowConstant δ * firstMomentSurvivalConstant / 2

lemma firstMomentSurvivalConstant_positive : 0 < firstMomentSurvivalConstant := by
  unfold firstMomentSurvivalConstant
  linarith [optimalCompetitiveRatio_le_threeQuarters]

lemma firstMomentSelectionConstant_positive {δ : ℝ} (hδ : 0 < δ) :
    0 < firstMomentSelectionConstant δ := by
  have hρ := firstMomentSurvivalConstant_positive
  unfold firstMomentSelectionConstant firstMomentWindowConstant
  exact div_pos (mul_pos (lt_min (by positivity) (by positivity)) hρ) (by norm_num)

end ProphetSecretary.Model
