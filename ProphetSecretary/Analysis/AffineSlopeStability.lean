import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Slope stability from local quadratic support

A bounded slope difference can be tested at a displacement proportional to that
difference. The resulting square bound includes all regret sizes and yields an
explicit square-root modulus without choosing a perturbed optimizer.
-/

namespace ProphetSecretary.Analysis

lemma slope_difference_le_sqrt {b r K B d : ℝ} (_hr : 0 ≤ r) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hd : 0 < d) (hb : |b| ≤ B)
    (hpay : ∀ h : ℝ, |h| ≤ d → h * b ≤ r + K * h ^ 2 / 2) :
    |b| ≤ Real.sqrt (2 * (K + 2 * B / d + 1)) * Real.sqrt r := by
  let A := K + 2 * B / d + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hKA : K ≤ A := by
    have hp : 0 ≤ 2 * B / d := div_nonneg (mul_nonneg (by norm_num) hB) hd.le
    dsimp [A]
    linarith
  have hBd : B ≤ A * d := by
    have he : A * d = K * d + 2 * B + d := by dsimp [A]; field_simp [hd.ne']
    rw [he]
    nlinarith [mul_nonneg hK hd.le]
  have hstep : |b / A| ≤ d := by
    rw [abs_div, abs_of_pos hA]
    exact (div_le_iff₀ hA).mpr (hb.trans (by simpa only [mul_comm] using hBd))
  have hp := mul_le_mul_of_nonneg_left (hpay (b / A) hstep) (by positivity : 0 ≤ 2 * A ^ 2)
  have hleft : (2 * A ^ 2) * ((b / A) * b) = 2 * A * b ^ 2 := by field_simp
  have hright : (2 * A ^ 2) * (r + K * (b / A) ^ 2 / 2) = 2 * A ^ 2 * r + K * b ^ 2 := by field_simp
  rw [hleft, hright] at hp
  have hsq : b ^ 2 ≤ 2 * A * r := by
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith [mul_nonneg (sub_nonneg.mpr hKA) (sq_nonneg b)]
  calc
    |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
    _ ≤ Real.sqrt (2 * A * r) := Real.sqrt_le_sqrt hsq
    _ = _ := by rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * A)]

end ProphetSecretary.Analysis
