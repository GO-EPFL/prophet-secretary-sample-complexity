import ProphetSecretary.Statistics.EmpiricalClockGapLoss
import ProphetSecretary.Statistics.EntranceFutureError

/-!
# Actual paired clock losses after a true entrance

The constructed entrance envelope supplies the continuation perturbation bound
on one common event for every later time and scalar. The actual paired-gap
loss theorem then supplies both support-band bounds, uniformly in the fixed
candidate value. No centering or additional conditional-law hypothesis occurs.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.paired_clockGapLoss_after_entrance (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ} (hlo : 0≤lo) (hlohi : lo≤hi) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t∈Ioc (P.trueCriticalEntrance hi a q.2) 1, ∀ z∈Icc lo hi, ∀ x : ℝ,
      empiricalClockGapLoss P (reservoirCoordinates.symm q.1) z q.2 x t ≤
          (if |x-P.clockContinuation z q.2 t|≤P.entranceFutureError k lo hi a q then P.entranceFutureError k lo hi a q else 0) ∧
        trueClockGapLossEmpiricalEval P (reservoirCoordinates.symm q.1) z q.2 x t ≤
          (if |x-P.clockContinuation z q.2 t|≤P.entranceFutureError k lo hi a q then P.entranceFutureError k lo hi a q else 0) := by
  filter_upwards [P.entranceFutureError_dominates_later (k:=k) hbound hlo hlohi] with q hq
  intro t ht z hz x
  have hError := hq t ht z hz
  have hClock : |P.clockContinuation z q.2 t-
      (totalEmpiricalInstance (reservoirCoordinates.symm q.1)).clockContinuation z q.2 t| ≤ P.entranceFutureError k lo hi a q := by
    rw [P.clockContinuation_eq z q.2 ht.2,
      (totalEmpiricalInstance (reservoirCoordinates.symm q.1)).clockContinuation_eq z q.2 ht.2,abs_sub_comm]
    exact hError
  exact paired_clockGapLoss_bound P (reservoirCoordinates.symm q.1) z q.2 x t _ hClock

end ProphetSecretary.Model
