import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Loss of a stopping decision

The gap is acceptance payoff minus continuation payoff. A fixed decision's loss
is one-Lipschitz in this gap. A perturbed optimal decision incurs loss only in
the corresponding boundary band, as used in `upmom:transport`.
-/

namespace ProphetSecretary.Analysis

def gapLoss (accept : Bool) (gap : ℝ) : ℝ := if accept then max (-gap) 0 else max gap 0

lemma gapLoss_nonnegative (accept : Bool) (gap : ℝ) : 0 ≤ gapLoss accept gap := by
  cases accept <;> exact le_max_right _ _

lemma gapLoss_eq_decisionLoss (accept : Bool) (a v : ℝ) :
    gapLoss accept (a - v) = max a v - (if accept then a else v) := by
  cases accept with
  | false => simpa only [gapLoss, Bool.false_eq_true, if_false, sub_self] using max_sub_sub_right a v v
  | true =>
    have h := max_sub_sub_right a v a
    simpa only [gapLoss, if_true, sub_self, neg_sub, max_comm] using h

lemma gapLoss_lipschitz (accept : Bool) (g g' : ℝ) :
    |gapLoss accept g' - gapLoss accept g| ≤ |g' - g| := by
  cases accept with
  | false => exact abs_max_sub_max_le_abs g' g 0
  | true =>
    simpa only [gapLoss, if_true, neg_sub_neg, abs_sub_comm] using
      abs_max_sub_max_le_abs (-g') (-g) 0

lemma gapLoss_perturbation_bound {accept : Bool} {g g' e : ℝ}
    (hzero : gapLoss accept g = 0) (hpert : |g' - g| ≤ e) : gapLoss accept g' ≤ e := by
  have h := (gapLoss_lipschitz accept g g').trans hpert
  rwa [hzero, sub_zero, abs_of_nonneg (gapLoss_nonnegative accept g')] at h

lemma gapLoss_vanishes_outside_band {accept : Bool} {g g' e : ℝ}
    (hzero : gapLoss accept g = 0) (hpert : |g' - g| ≤ e) (hout : e < |g|) :
    gapLoss accept g' = 0 := by
  have hp := abs_le.mp hpert
  cases accept with
  | false =>
    have hg : g ≤ 0 := (le_max_left g 0).trans hzero.le
    have hg' : g' ≤ 0 := by
      rw [abs_of_nonpos hg] at hout
      linarith only [hp.2, hout]
    exact max_eq_right hg'
  | true =>
    have hg : 0 ≤ g := by have h := (le_max_left (-g) 0).trans hzero.le; linarith only [h]
    have hg' : 0 ≤ g' := by
      rw [abs_of_nonneg hg] at hout
      linarith only [hp.1, hout]
    exact max_eq_right (neg_nonpos.mpr hg')

end ProphetSecretary.Analysis
