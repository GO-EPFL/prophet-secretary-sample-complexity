import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bellman loss caused by a threshold error

`a` is acceptance payoff, `b` the true continuation payoff, and `old` the
continuation payoff used to choose the action. The resulting loss is at most
the continuation error and can be positive only near the true boundary.
-/

namespace ProphetSecretary.Analysis

lemma max_action_loss_le_shift (a old b : ℝ) :
    max a b - (if old ≤ a then a else b) ≤ |old - b| := by
  by_cases h : old ≤ a
  · rw [if_pos h]
    have hm : max a b ≤ a + |old - b| :=
      max_le (by linarith [abs_nonneg (old - b)]) (by linarith [neg_le_abs (old - b)])
    linarith
  · rw [if_neg h]
    have hm : max a b ≤ b + |old - b| :=
      max_le (by linarith [le_abs_self (old - b)]) (by linarith [abs_nonneg (old - b)])
    linarith

lemma max_action_loss_zero_or_abs (a old b : ℝ) :
    max a b - (if old ≤ a then a else b) = 0 ∨
      max a b - (if old ≤ a then a else b) = |a - b| := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    by_cases ha : old ≤ a
    · rw [if_pos ha]
      right
      ring
    · rw [if_neg ha, sub_self]
      exact Or.inl rfl
  · rw [max_eq_left (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
    by_cases ha : old ≤ a
    · rw [if_pos ha, sub_self]
      exact Or.inl rfl
    · rw [if_neg ha]
      exact Or.inr rfl

lemma max_action_loss_le_band {a old b δ : ℝ} (hshift : |old - b| ≤ δ) :
    max a b - (if old ≤ a then a else b) ≤ if |a - b| ≤ δ then δ else 0 := by
  have h := (max_action_loss_le_shift a old b).trans hshift
  by_cases hb : |a - b| ≤ δ
  · rw [if_pos hb]
    exact h
  · rw [if_neg hb]
    rcases max_action_loss_zero_or_abs a old b with hz | hg
    · rw [hz]
    · exact False.elim (hb (hg ▸ h))

end ProphetSecretary.Analysis
