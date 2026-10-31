import ProphetSecretary.Model.WeightedSaturatedValue
import ProphetSecretary.Model.LawRoots
import ProphetSecretary.Analysis.MovingThreshold

/-!
# Canonical acceptance expressed through the duration root

Before terminal time, a level below the reward-only continuation is always
rejected. At a larger level the constructed duration root gives exactly the
elapsed-time threshold, with the original positive reward coefficient retained.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.durationRoot_acceptance_iff (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c x t : ℝ}
    (hw : 0 < w) (hc : 0 < c) (ht : t < 1) :
    optimalScalarValue P w (c * (1 - t)) ≤ w * x ↔
      1 - (w * P.durationRoot hP x) / c ≤ t := by
  have hu : 0 < c * (1 - t) := mul_pos hc (sub_pos.mpr ht)
  by_cases hx : optimalScalarValue P 1 0 < x
  · have hd : 0 ≤ w * P.durationRoot hP x := mul_nonneg hw.le (P.durationRoot_nonnegative hP x)
    have hLevel := fun s ↦ P.weightedSaturatedValue_level_iff hP hw hd s
    have h := ProphetSecretary.Analysis.moving_level_iff hLevel hc t
    simp only [Instance.weightedSaturatedValue, max_eq_right hu.le, max_eq_right hd] at h
    rw [P.weightedDurationRoot_value hP hw hx] at h
    exact h
  · have hxle : x ≤ optimalScalarValue P 1 0 := le_of_not_gt hx
    rw [P.durationRoot_eq_zero_of_le hP hxle, mul_zero, zero_div, sub_zero]
    have hHom := optimalScalarValue_smul P hP (a := w) (w := 1) (c := 0) hw.le zero_le_one le_rfl
    simp only [mul_one, mul_zero] at hHom
    have hBase : w * x ≤ optimalScalarValue P w 0 := by
      rw [hHom]
      exact mul_le_mul_of_nonneg_left hxle hw.le
    have hg := P.remainingHorizon_growth hP (w := w) (c := 1) hw zero_le_one (le_rfl : (0 : ℝ) ≤ 0) hu.le
    simp only [one_mul, sub_zero] at hg
    have hPos : 0 < (1 / (4 * (1 + (n : ℝ)))) * (c * (1 - t)) := mul_pos (by positivity) hu
    have hStrict : w * x < optimalScalarValue P w (c * (1 - t)) := by linarith
    exact iff_of_false (not_le.mpr hStrict) (not_le.mpr ht)

end ProphetSecretary.Model
