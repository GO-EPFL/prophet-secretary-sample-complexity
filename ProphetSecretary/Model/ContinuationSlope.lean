import ProphetSecretary.Model.ContinuationODE
import ProphetSecretary.Model.RewardDuration
import ProphetSecretary.Model.DurationLower

/-!
# Quantitative continuation slopes

Paper correspondence: `upstat:duration`, `upstat:slope`, and the preliminary
finite-dimensional slope bounds in the scalar-curvature proof. Derivatives here
refer to the remaining horizon; elapsed-time derivatives have the opposite sign.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.totalFirstMoment_nonnegative (P : Instance n) : 0 ≤ P.totalFirstMoment := by
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg_of_ae (P.nonnegative i)

/-- The state's scalar value is bounded by normalized duration times its first-moment scale. -/
lemma remainingScalarValue_le_duration_firstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 ≤ u) :
    remainingScalarValue P w c u ≤
      (P.valuePolicy hP hw.le (mul_nonneg hc hu)).expectedDuration P *
        (2 * w * P.totalFirstMoment + c * u) :=
  P.valuePolicy_value_le_duration hP hw (mul_nonneg hc hu)

/-- The dimension-free reciprocal-slope control used for empirical threshold errors. -/
lemma remainingScalarValue_deriv_ge_firstMoment_ratio (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hu : 0 < u) :
    c * remainingScalarValue P w c u / (2 * w * P.totalFirstMoment + c * u) ≤
      deriv (remainingScalarValue P w c) u := by
  have hden : 0 < 2 * w * P.totalFirstMoment + c * u :=
    add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg (by norm_num) hw.le) P.totalFirstMoment_nonnegative)
      (mul_pos hc hu)
  rw [remainingScalarValue_deriv_eq_canonicalDuration P hP hw hc.le hu]
  apply (div_le_iff₀ hden).mpr
  have h := mul_le_mul_of_nonneg_left (remainingScalarValue_le_duration_firstMoment P hP hw hc.le hu.le) hc.le
  nlinarith

/-- A finite-dimensional slope floor, with its cardinality dependence explicit. -/
lemma remainingScalarValue_deriv_ge_card_bound (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    c / (4 * (1 + (n : ℝ))) ≤ deriv (remainingScalarValue P w c) u := by
  rw [remainingScalarValue_deriv_eq_canonicalDuration P hP hw hc hu]
  have h := mul_le_mul_of_nonneg_left
    ((P.valuePolicy hP hw.le (mul_nonneg hc hu.le)).expectedDuration_ge_card_bound P) hc
  simpa only [mul_one_div] using h

/-- Zero rejection replaces the cardinality by the expected number of positive offers. -/
lemma remainingScalarValue_deriv_ge_positiveCount_bound (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hu : 0 < u) :
    c / (4 * (1 + P.positiveCount)) ≤ deriv (remainingScalarValue P w c) u := by
  rw [remainingScalarValue_deriv_eq_canonicalDuration P hP hw hc.le hu]
  have hT := P.valuePolicy_duration_ge_positiveCount hP hw (mul_pos hc hu) P
  have h := mul_le_mul_of_nonneg_left hT hc.le
  simpa only [mul_one_div] using h

end ProphetSecretary.Model
