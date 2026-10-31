import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit scalar rate estimates for empirical local losses

For x≥1/k, both inverse-power far-loss terms are at most x/k. These algebraic
bounds are uniform in instance size and apply after the actual sixth-moment
and entrance-size estimates have supplied their explicit constants.
-/

namespace ProphetSecretary.Analysis

lemma empirical_far_terms_le {k x : ℝ} (hk : 0 < k) (hxk : 1 / k ≤ x) :
    1 / (x * k ^ 3) + 1 / (x ^ 4 * k ^ 6) ≤ 2 * x / k := by
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have hxk1 : 1 ≤ x * k := (div_le_iff₀ hk).mp hxk
  have hd : 0 < x * k := mul_pos hx hk
  have hr0 : 0 ≤ 1 / (x * k) := le_of_lt (one_div_pos.mpr hd)
  have hr1 : 1 / (x * k) ≤ 1 := (div_le_one hd).mpr hxk1
  have hp2 : (1 / (x * k)) ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  have hp5 : (1 / (x * k)) ^ 5 ≤ 1 := pow_le_one₀ hr0 hr1
  have hm2 := mul_le_mul_of_nonneg_left hp2 (div_nonneg hx.le hk.le)
  have hm5 := mul_le_mul_of_nonneg_left hp5 (div_nonneg hx.le hk.le)
  have he2 : 1 / (x * k ^ 3) = (x / k) * (1 / (x * k)) ^ 2 := by field_simp
  have he5 : 1 / (x ^ 4 * k ^ 6) = (x / k) * (1 / (x * k)) ^ 5 := by field_simp
  rw [he2, he5]
  exact (add_le_add hm2 hm5).trans_eq (by ring)

lemma empirical_inverse_square_le {k x : ℝ} (hk : 0 < k) (hxk : 1 / k ≤ x) :
    1 / k ^ 2 ≤ x / k := by
  have h := div_le_div_of_nonneg_right hxk hk.le
  simpa only [div_div, one_mul, pow_two] using h

/-- The near-loss moment expression at the entrance a=Ax. -/
lemma empirical_near_rate_le {k x A : ℝ} (hk : 0 < k) (hxk : 1 / k ≤ x) (hA : 0 ≤ A) :
    (A * x / k + 1 / k ^ 2) * A ≤ A * (A + 1) * x / k := by
  have hsmall := empirical_inverse_square_le hk hxk
  calc
    _ ≤ (A * x / k + x / k) * A :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hsmall) hA
    _ = _ := by ring

end ProphetSecretary.Analysis
