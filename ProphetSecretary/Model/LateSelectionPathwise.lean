import ProphetSecretary.Model.PendingContinuation
import ProphetSecretary.Model.MarginalPremium
import ProphetSecretary.Probability.CandidateTimeValue

/-!
# Selection after a late reached arrival

The candidate remains pending during the auxiliary execution. If the unseen
other first moment and waiting value are each at most half its reward, the
canonical policy selects it. Candidate replacement is used analytically, with
its effect on pending execution and continuation justified explicitly.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.pendingFirstMoment_update_clock (P : Instance n) (i : Fin n)
    (t v : ℝ) (u : Fin n → ℝ) :
    P.pendingFirstMoment i t (Function.update u i v) = P.pendingFirstMoment i t u := by
  unfold pendingFirstMoment
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- A deterministic implication used before integrating the candidate clock.
Distinct clocks are stated here; the probabilistic specialization must remove
the clock-tie null set using the independent continuous clocks. -/
theorem Instance.canonical_selects_of_pending_smallMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c a t : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (ht : t ≤ 1)
    (x u : Fin n → ℝ) (i : Fin n)
    (hu : Function.Injective (Function.update u i t))
    (hr : t ≤ (P.valuePolicy hP hw.le hc).rule.pendingTime () x u i)
    (hmean : P.pendingFirstMoment i t u ≤ a / 2)
    (hwait : c * (1 - t) ≤ w * a / 2) :
    (P.valuePolicy hP hw.le hc).rule.ActualSelects () Finset.univ
      (Function.update x i a) (Function.update u i t) i := by
  let π := (P.valuePolicy hP hw.le hc).rule
  have htime : (Function.update u i t) i ≤ 1 := by simpa only [Function.update_self] using ht
  have hreach : π.Reaches () (Function.update x i a) (Function.update u i t) i := by
    apply (π.reaches_iff_le_pendingTime () _ _ i htime).mpr
    rw [Function.update_self, π.pendingTime_update]
    exact hr
  have hv := P.continuationAtArrival_le_pendingFirstMoment hP hw.le hc
    (Function.update x i a) (Function.update u i t) i htime
  rw [Function.update_self, P.pendingFirstMoment_update_clock] at hv
  have hm := mul_le_mul_of_nonneg_left hmean hw.le
  have hgap : P.continuationAtArrival w c (Function.update x i a) (Function.update u i t) i ≤
      w * (Function.update x i a) i := by
    rw [Function.update_self]
    linarith only [hv, hm, hwait]
  exact (π.actualSelects_iff_selects () Finset.univ _ _ hu i).mpr
    (P.canonical_selects_of_reaches_of_gap hP hw hc _ _ i hreach hgap)

end ProphetSecretary.Model
