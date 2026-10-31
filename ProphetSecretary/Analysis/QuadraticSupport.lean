import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Calculus from quadratic affine support

An actual quadratic remainder gives a derivative. Two-sided quadratic affine
support then makes those derivatives Lipschitz. These are analytic implications;
applications must separately prove their remainder bounds.
-/

open Filter Asymptotics
open scoped Topology

namespace ProphetSecretary.Analysis

lemma hasDerivAt_of_quadratic_remainder {f : ℝ → ℝ} {x d K : ℝ}
    (h : ∀ᶠ y in 𝓝 x, |f y - f x - (y - x) * d| ≤ K * (y - x) ^ 2) :
    HasDerivAt f d x := by
  apply HasDerivAt.of_isLittleO
  change (fun y : ℝ ↦ f y - f x - (y - x) * d) =o[𝓝 x] (fun y ↦ y - x)
  have hO : (fun y : ℝ ↦ f y - f x - (y - x) * d) =O[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2) := by
    apply IsBigO.of_bound K
    filter_upwards [h] with y hy
    simpa only [Real.norm_eq_abs, sq_abs, abs_of_nonneg (sq_nonneg (y - x))] using hy
  exact hO.trans_isLittleO (isLittleO_pow_sub_sub x (m := 2) (by norm_num))

lemma abs_sub_slopes_le_of_quadratic {S : Set ℝ} {f g : ℝ → ℝ} {K : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S,
      0 ≤ f y - f x - (y - x) * g x ∧ f y - f x - (y - x) * g x ≤ K * (y - x) ^ 2)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : |g y - g x| ≤ 2 * K * |y - x| := by
  have hOrder (a b : ℝ) (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
      0 ≤ g b - g a ∧ g b - g a ≤ 2 * K * (b - a) := by
    have h1 := h a ha b hb
    have h2 := h b hb a ha
    have hP0 : 0 ≤ (b - a) * (g b - g a) := by nlinarith [h1.1, h2.1]
    have hP1 : (b - a) * (g b - g a) ≤ 2 * K * (b - a) ^ 2 := by nlinarith [h1.2, h2.2]
    have hd : 0 < b - a := sub_pos.mpr hab
    constructor
    · by_contra hn
      have hneg := mul_neg_of_pos_of_neg hd (lt_of_not_ge hn)
      exact not_lt_of_ge hP0 hneg
    · apply (mul_le_mul_iff_right₀ hd).mp
      nlinarith [hP1]
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have ht := hOrder x y hx hy hxy
    simpa only [abs_of_nonneg ht.1, abs_of_pos (sub_pos.mpr hxy)] using ht.2
  · simp
  · have ht := hOrder y x hy hx hyx
    rw [abs_sub_comm (g y) (g x), abs_sub_comm y x]
    simpa only [abs_of_nonneg ht.1, abs_of_pos (sub_pos.mpr hyx)] using ht.2

end ProphetSecretary.Analysis
