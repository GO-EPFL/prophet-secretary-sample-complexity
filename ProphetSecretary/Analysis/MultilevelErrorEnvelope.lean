import ProphetSecretary.Analysis.MultilevelError
import Mathlib.Algebra.BigOperators.Fin

/-! # An explicit uniform squared-error envelope -/

open scoped BigOperators

namespace ProphetSecretary.Analysis

/-- The deterministic mean-square envelope in `alg:mlmc-mse`. -/
noncomputable def multilevelErrorEnvelope : ℕ → ℝ
  | 0 => 25
  | r + 1 => (1 / 16 : ℝ) *
      (multilevelErrorEnvelope r + (1 / 4 : ℝ) ^ (r + 1) +
        2 * ∑ l : Fin r, (1 / 4 : ℝ) ^ (r - l.val) *
          (multilevelErrorEnvelope (l.val + 1) + multilevelErrorEnvelope l.val))
termination_by r => r
decreasing_by all_goals omega

lemma multilevelErrorEnvelope_nonnegative (r : ℕ) : 0 ≤ multilevelErrorEnvelope r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => norm_num [multilevelErrorEnvelope]
    | succ n =>
      rw [multilevelErrorEnvelope]
      apply mul_nonneg (by norm_num)
      apply add_nonneg
      · exact add_nonneg (ih n (by omega)) (by positivity)
      · apply mul_nonneg (by norm_num)
        apply Finset.sum_nonneg
        intro l _
        exact mul_nonneg (by positivity)
          (add_nonneg (ih (l.val + 1) (by have := l.isLt; omega))
            (ih l.val (by have := l.isLt; omega)))

lemma multilevelErrorEnvelope_decay (r : ℕ) :
    multilevelErrorEnvelope r ≤ 25 * (1 / 2 : ℝ) ^ r := by
  apply multilevel_error_decay multilevelErrorEnvelope (by simp [multilevelErrorEnvelope]) _ r
  intro n
  rw [multilevelErrorEnvelope]
  simp only [geometricConvolution, Finset.sum_range]
  exact le_rfl

end ProphetSecretary.Analysis
