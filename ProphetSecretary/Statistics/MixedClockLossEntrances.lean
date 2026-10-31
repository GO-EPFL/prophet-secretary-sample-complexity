import ProphetSecretary.Statistics.MixedClockGapLoss
import ProphetSecretary.Statistics.MixedEntranceFutureError

/-!
# Actual paired mixed clock losses after a true entrance

The constructed mixed entrance envelope supplies a continuation perturbation
bound for every later time and scalar on one event. Both actual comparison
losses therefore satisfy the same TRUE-gap support bound, uniformly in the
candidate value, with no selected-weight centering or independence premise.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.paired_mixedClockGapLoss_after_entrance (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ} (hlo : 0≤lo) (hlohi : lo≤hi) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t∈Ioc (P.trueCriticalEntrance hi a q.2) 1, ∀ z∈Icc lo hi, ∀ x : ℝ,
      mixedClockGapLoss P known (reservoirCoordinates.symm q.1) z q.2 x t ≤
          (if |x-P.clockContinuation z q.2 t|≤P.mixedEntranceFutureError known k lo hi a q then P.mixedEntranceFutureError known k lo hi a q else 0) ∧
        trueClockGapLossMixedEval P known (reservoirCoordinates.symm q.1) z q.2 x t ≤
          (if |x-P.clockContinuation z q.2 t|≤P.mixedEntranceFutureError known k lo hi a q then P.mixedEntranceFutureError known k lo hi a q else 0) := by
  filter_upwards [P.mixedEntranceFutureError_dominates_later (k:=k) known hbound hlo hlohi] with q hq
  intro t ht z hz x
  have hError := hq t ht z hz
  have hClock : |P.clockContinuation z q.2 t-
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).clockContinuation z q.2 t| ≤ P.mixedEntranceFutureError known k lo hi a q := by
    rw [P.clockContinuation_eq z q.2 ht.2,
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).clockContinuation_eq z q.2 ht.2,abs_sub_comm]
    exact hError
  exact paired_mixedClockGapLoss_bound P known (reservoirCoordinates.symm q.1) z q.2 x t _ hClock

end ProphetSecretary.Model
