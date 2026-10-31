import ProphetSecretary.Model.ClockFarLoss
import ProphetSecretary.Analysis.TinyDecisionLoss

/-!
# Actual local loss bounds for tiny offers

Waiting lower-bounds both true and empirical continuations. Thus both
threshold rules reject before the final x/lo horizon window. Within that
window, a local loss is bounded by the candidate plus the target state's
first moment and duration value, as used in `upstat:tiny`.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

open ProphetSecretary.Probability ProphetSecretary.Analysis

variable {n : ℕ}

lemma Instance.clockContinuation_ge_waiting (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z t : ℝ} (hz : 0 ≤ z) (ht : t ≤ 1)
    (u : Fin n → ℝ) : z * (1 - t) ≤ P.clockContinuation z u t := by
  rw [P.clockContinuation_eq z u ht]
  exact P.durationWeight_le_continuationValue hP _ (sub_nonneg.mpr ht) zero_le_one hz

lemma Instance.clockContinuation_le_pendingMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z hi t : ℝ} (hz : 0 ≤ z) (hzhi : z ≤ hi) (ht : t ≤ 1)
    (u : Fin n → ℝ) :
    P.clockContinuation z u t ≤ (P.restrictTo (pendingClockSet t u)).totalFirstMoment + hi * (1 - t) := by
  let Q := P.restrictTo (pendingClockSet t u)
  have hQ := P.restrictTo_integrable_maximum (pendingClockSet t u) hP
  have h := optimalScalarValue_le_benchmark Q hQ zero_le_one (mul_nonneg hz (sub_nonneg.mpr ht))
  simp only [one_mul] at h
  have hM := Q.expectedMaximum_le_totalFirstMoment hQ
  have hc := mul_le_mul_of_nonneg_right hzhi (sub_nonneg.mpr ht)
  rw [P.clockContinuation_eq z u ht]
  change optimalScalarValue Q 1 (z * (1 - t)) ≤ _
  exact h.trans (add_le_add hM hc)

lemma Instance.clock_gapLoss_le_pendingMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x z hi t : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hzhi : z ≤ hi) (ht : t ≤ 1) (u : Fin n → ℝ) (accept : Bool) :
    gapLoss accept (x - P.clockContinuation z u t) ≤
      x + (P.restrictTo (pendingClockSet t u)).totalFirstMoment + hi * (1 - t) := by
  have hv0 : 0 ≤ P.clockContinuation z u t := by
    rw [P.clockContinuation_eq z u ht]
    exact P.continuationValue_nonnegative hP _ (sub_nonneg.mpr ht) zero_le_one hz
  have h := gapLoss_le_value_sum accept hx hv0
  have hv := P.clockContinuation_le_pendingMean hP hz hzhi ht u
  linarith only [h, hv]

/-- This rejects before the terminal window for both actual canonical
threshold comparisons; the design and evaluation laws may differ. -/
theorem clock_paired_gapLoss_zero_before_window (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {lo z x t : ℝ} (hlo : 0 < lo) (hloz : lo ≤ z) (ht : t ≤ 1)
    (hwindow : x / lo < 1 - t) (u : Fin n → ℝ) :
    gapLoss (decide (0 ≤ x - Q.clockContinuation z u t)) (x - P.clockContinuation z u t) = 0 ∧
      gapLoss (decide (0 ≤ x - P.clockContinuation z u t)) (x - Q.clockContinuation z u t) = 0 := by
  have hz : 0 ≤ z := (hlo.trans_le hloz).le
  have hmul := (div_lt_iff₀ hlo).mp hwindow
  have hc := mul_le_mul_of_nonneg_right hloz (sub_nonneg.mpr ht)
  have hwP := P.clockContinuation_ge_waiting hP hz ht u
  have hwQ := Q.clockContinuation_ge_waiting hQ hz ht u
  apply paired_gapLoss_zero_of_both_below
  · nlinarith only [hmul, hc, hwP]
  · nlinarith only [hmul, hc, hwQ]

end ProphetSecretary.Model
