import ProphetSecretary.Model.ClockContinuationOrder
import ProphetSecretary.Model.ContinuationValueFloorSlope
import ProphetSecretary.Statistics.RemainingSize

/-!
# Actual reciprocal slope along the remaining-clock path

Fixing the smaller end state absorbs all intervening deletions. The actual
continuation derivative is then integrated on that state. The reciprocal
constant is 2(2+hi)/lo, and the size is the true remaining mean plus horizon
at the entrance. The proof covers zero entrance size and terminal horizons.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.clockContinuation_reciprocalSlope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z x σ t s : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (hx : 0 < x)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc σ 1) (hs : s ∈ Icc σ 1) (hts : t ≤ s)
    (u : Fin n → ℝ)
    (hfloor : x / 2 ≤ P.continuationValue (pendingClockSet s u) (1 - s) 1 z) :
    x * (s - t) ≤ (2 * (2 + hi) / lo) * P.remainingSize σ u *
      (P.continuationValue (pendingClockSet t u) (1 - t) 1 z -
        P.continuationValue (pendingClockSet s u) (1 - s) 1 z) := by
  let B := P.remainingSize σ u
  let Q := P.restrictTo (pendingClockSet s u)
  have hz : 0 < z := hlo.trans_le hloz
  have hhi : 0 < hi := hz.trans_le hzhi
  have hS0 := (P.restrictTo (pendingClockSet σ u)).totalFirstMoment_nonnegative
  have hB0 : 0 ≤ B := add_nonneg hS0 (sub_nonneg.mpr hσ.2)
  by_cases hB : 0 < B
  · have hmean0 := P.totalFirstMoment_restrictTo_mono (pendingClockSet_antitone u hs.1)
    have hmean : Q.totalFirstMoment ≤ B := by
      dsimp [Q, B, Instance.remainingSize]
      linarith only [hmean0, hσ.2]
    have htime : 1 - t ≤ B := by
      dsimp [B, Instance.remainingSize]
      linarith only [ht.1, hS0]
    have hQ := P.restrictTo_integrable_maximum (pendingClockSet s u) hP
    have hfixed := Q.remainingScalarValue_increment_ge_floor hQ hlo hloz hzhi hB hx hmean
      (sub_nonneg.mpr hs.2) (by linarith only [hts]) htime hfloor
    have hdrop := P.clockContinuation_drop_ge_endState hP hz.le ht.2 hts u
    have hcoef : 0 ≤ (2 * (2 + hi) / lo) * B := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hdrop hcoef
    change (2 * (2 + hi) / lo) * B *
      (remainingScalarValue Q 1 z (1 - t) - remainingScalarValue Q 1 z (1 - s)) ≤ _ at hscaled
    have hleft : x * ((1 - t) - (1 - s)) = x * (s - t) := by ring
    rw [hleft] at hfixed
    exact hfixed.trans hscaled
  · have hBzero : B = 0 := le_antisymm (not_lt.mp hB) hB0
    have hzero : (P.restrictTo (pendingClockSet σ u)).totalFirstMoment + (1 - σ) = 0 := hBzero
    have hσone : σ = 1 := by linarith only [hzero, hS0, hσ.2]
    have htone : t = 1 := by linarith only [hσone, ht.1, ht.2]
    have hsone : s = 1 := by linarith only [hσone, hs.1, hs.2]
    rw [htone, hsone]
    simp only [sub_self, mul_zero, le_refl]

end ProphetSecretary.Model
