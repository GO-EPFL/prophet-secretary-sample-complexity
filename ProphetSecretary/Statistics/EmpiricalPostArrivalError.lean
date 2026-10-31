import ProphetSecretary.Statistics.EmpiricalFutureError
import ProphetSecretary.Probability.PendingStateRightLimit

/-!
# The same uniform error controls post-arrival states

Entrances into a value sublevel can occur at downward jumps when an identity
arrives. The strict pending state immediately after that observation is a right
limit of the already controlled strict-prefix states. No sample-dependent
entrance is introduced here.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.empiricalFutureError_postArrival_dominates (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t ∈ Ico (0 : ℝ) 1, ∀ z ∈ Icc lo hi,
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.strictPendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.strictPendingClockSet t q.2) (1-t) 1 z| ≤
      P.empiricalFutureError k lo hi q := by
  have hb := P.empiricalFutureError_dominates (k := k) hbound hlo hlohi
  have hP := P.integrable_maximum_of_bounded hbound
  filter_upwards [hb] with q hq
  intro t ht z hz
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm q.1)
  have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm q.1)
  have hz0 : 0 ≤ z := hlo.trans hz.1
  have hlim := continuous_abs.continuousAt.tendsto.comp
    ((ProphetSecretary.Probability.pendingContinuationValue_tendsto_right Q hQ hz0 q.2 t).sub
      (ProphetSecretary.Probability.pendingContinuationValue_tendsto_right P hP hz0 q.2 t))
  have hwindow : ∀ᶠ s in 𝓝[>] t, s ∈ Icc (0 : ℝ) 1 := by
    have hs1 : ∀ᶠ s in 𝓝 t, s < 1 := isOpen_Iio.mem_nhds ht.2
    filter_upwards [self_mem_nhdsWithin (a := t) (s := Ioi t), hs1.filter_mono nhdsWithin_le_nhds] with s hs hs1
    exact ⟨ht.1.trans hs.le,hs1.le⟩
  have hmean := le_of_tendsto hlim (hwindow.mono (fun s hs => by
    change |Q.continuationValue _ (max 0 (1-s)) 1 z - P.continuationValue _ (max 0 (1-s)) 1 z| ≤ _
    rw [max_eq_right (sub_nonneg.mpr hs.2)]
    exact hq s hs z hz))
  change |Q.continuationValue _ (1-t) 1 z - P.continuationValue _ (1-t) 1 z| ≤ _
  simpa only [max_eq_right (sub_nonneg.mpr ht.2.le)] using hmean

end ProphetSecretary.Model
