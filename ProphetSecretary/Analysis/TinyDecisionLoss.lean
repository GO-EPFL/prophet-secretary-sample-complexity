import ProphetSecretary.Analysis.PairedDecisionLoss

/-!
# Elementary local-loss bounds for tiny offers

A nonnegative candidate and continuation bound either decision loss by their
sum. If both true and estimated continuations exceed the candidate, both
threshold decisions reject and both Bellman losses vanish.
-/

namespace ProphetSecretary.Analysis

lemma gapLoss_le_value_sum (accept : Bool) {x v : ℝ} (hx : 0 ≤ x) (hv : 0 ≤ v) :
    gapLoss accept (x - v) ≤ x + v := by
  cases accept
  · change max (x - v) 0 ≤ x + v
    apply max_le <;> linarith
  · change max (-(x - v)) 0 ≤ x + v
    apply max_le <;> linarith

lemma paired_gapLoss_zero_of_both_below {x v vhat : ℝ} (hv : x < v) (hhat : x < vhat) :
    gapLoss (decide (0 ≤ x - vhat)) (x - v) = 0 ∧
      gapLoss (decide (0 ≤ x - v)) (x - vhat) = 0 := by
  have hnv : ¬0 ≤ x - v := not_le.mpr (sub_neg.mpr hv)
  have hnhat : ¬0 ≤ x - vhat := not_le.mpr (sub_neg.mpr hhat)
  simp only [hnv, hnhat, decide_false, gapLoss, Bool.false_eq_true, if_false,
    max_eq_right (sub_neg.mpr hv).le, max_eq_right (sub_neg.mpr hhat).le, and_self]

end ProphetSecretary.Analysis
