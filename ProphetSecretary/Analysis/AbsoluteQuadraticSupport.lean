import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lipschitz slopes from absolute quadratic support

Convexity is not required. Summing the two affine remainders bounds the slope
difference, which is useful when varying product laws rather than scalar weights.
-/

namespace ProphetSecretary.Analysis

lemma abs_sub_slopes_le_of_absolute_quadratic {S : Set ℝ} {f g : ℝ → ℝ} {K : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, |f y - f x - (y - x) * g x| ≤ K * (y - x) ^ 2)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : |g y - g x| ≤ 2 * K * |y - x| := by
  by_cases heq : y = x
  · simp only [heq, sub_self, abs_zero, mul_zero, le_refl]
  · have hpos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr heq)
    have hProd : |y - x| * |g y - g x| ≤ 2 * K * (y - x) ^ 2 := by
      rw [← abs_mul]
      have he : (y - x) * (g y - g x) =
          (f y - f x - (y - x) * g x) + (f x - f y - (x - y) * g y) := by ring
      rw [he]
      calc
        _ ≤ |f y - f x - (y - x) * g x| + |f x - f y - (x - y) * g y| := abs_add_le _ _
        _ ≤ K * (y - x) ^ 2 + K * (x - y) ^ 2 := add_le_add (h x hx y hy) (h y hy x hx)
        _ = _ := by ring
    rw [← sq_abs (y - x)] at hProd
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith

end ProphetSecretary.Analysis
