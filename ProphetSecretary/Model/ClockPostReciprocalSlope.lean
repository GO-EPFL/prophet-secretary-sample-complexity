import ProphetSecretary.Model.ClockReciprocalSlope
import ProphetSecretary.Statistics.GridStateStabilization

/-!
# Reciprocal slope after a post-arrival entrance

For times strictly after σ, the smaller end state is contained in the strict
unseen set {i : σ<Uᵢ}. Thus the slope uses the actual POST-entrance size, even
when an arrival causes a downward jump at σ. The single time σ is excluded.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.clockContinuation_post_reciprocalSlope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z x σ t s : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (hx : 0 < x)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (ht : t ∈ Ioc σ 1) (hs : s ∈ Ioc σ 1) (hts : t ≤ s)
    (u : Fin n → ℝ)
    (hfloor : x / 2 ≤ P.continuationValue (pendingClockSet s u) (1 - s) 1 z) :
    x * (s - t) ≤ (2 * (2 + hi) / lo) * P.postRemainingSize σ u *
      (P.continuationValue (pendingClockSet t u) (1 - t) 1 z -
        P.continuationValue (pendingClockSet s u) (1 - s) 1 z) := by
  let B := P.postRemainingSize σ u
  let Q := P.restrictTo (pendingClockSet s u)
  have hz : 0 < z := hlo.trans_le hloz
  have hhi : 0 < hi := hz.trans_le hzhi
  have hS0 := (P.restrictTo (strictPendingClockSet σ u)).totalFirstMoment_nonnegative
  have hσ1 : σ < 1 := ht.1.trans_le ht.2
  have hB : 0 < B := add_pos_of_nonneg_of_pos hS0 (sub_pos.mpr hσ1)
  have hsub : pendingClockSet s u ⊆ strictPendingClockSet σ u := by
    intro i hi
    exact (mem_strictPendingClockSet σ u i).mpr (hs.1.trans_le ((mem_pendingClockSet s u i).mp hi))
  have hmean0 := P.totalFirstMoment_restrictTo_mono hsub
  have hmean : Q.totalFirstMoment ≤ B := by
    dsimp [Q, B, Instance.postRemainingSize]
    linarith only [hmean0, hσ.2]
  have htime : 1 - t ≤ B := by
    dsimp [B, Instance.postRemainingSize]
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

end ProphetSecretary.Model
