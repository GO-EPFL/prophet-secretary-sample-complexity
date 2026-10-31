import ProphetSecretary.Statistics.DataSelectedLossRegions
import ProphetSecretary.Statistics.EntranceFutureMoments

/-!
# Actual regional time bounds for both selected-weight comparison losses

The envelope and post-entrance size are constructed from the actual training
and clocks. Their joint moment bounds are applied separately; no independence
between these two quantities is asserted.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.dataSelectedClockLossDirection_after_entrance (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hZ : ∀ y, Z y ∈ Icc lo hi)
    (reverse : Bool) (x : ℝ) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t ∈ Ioc (P.trueCriticalEntrance hi a q.2) 1,
      dataSelectedClockLossDirection P Z reverse x q t ≤
        if |x-P.clockContinuation (Z q.1) q.2 t| ≤ P.entranceFutureError k lo hi a q
        then P.entranceFutureError k lo hi a q else 0 := by
  filter_upwards [P.paired_clockGapLoss_after_entrance (k := k) (a := a) hbound hlo hlohi] with q hq
  intro t ht
  have h := hq t ht (Z q.1) (hZ q.1) x
  cases reverse
  · exact h.1
  · exact h.2

theorem Instance.dataSelectedClockLoss_near_time_bound (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi a x : ℝ}
    (hlo : 0 < lo) (hZrange : ∀ y, Z y ∈ Icc lo hi)
    (hlohi : lo ≤ hi) (hx : 0 < x) (reverse : Bool) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      clockRegionLoss P Z hi a (x/2) true
        (fun qt => dataSelectedClockLossDirection P Z reverse x qt.1 qt.2) q ≤
      ((4*(2+hi)/lo)/x) * (P.entranceRemainingSize hi a q.2 *
        P.entranceFutureError k lo hi a q ^ 2) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hZ0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  filter_upwards [P.dataSelectedClockLossDirection_after_entrance hbound hlo.le hlohi hZrange reverse x]
    with q hq
  have htime := measurable_dataSelectedClockLossDirection_time P hP Z hZ0 reverse x q
  have hS := measurableSet_clockLossRegion P hP hZ0 hi a (x/2) true q
  have hdom := clock_lossGapBound_restrict P (z := Z q.1) (x := x)
    (E := P.entranceFutureError k lo hi a q) (σ := P.trueCriticalEntrance hi a q.2)
    (S := clockLossRegion P Z hi a (x/2) true q)
    (loss := fun t => dataSelectedClockLossDirection P Z reverse x q t) q.2 hS (fun _ ht => ht.1) hq
  have h := P.clock_post_near_loss_integral_le hP hlo (hZrange q.1).1 (hZrange q.1).2 hx
    (P.trueCriticalEntrance_mem hi a q.2) (P.entranceFutureError_nonnegative lo hi a q) q.2
    (fun t => dataSelectedClockLossDirection P Z reverse x q t)
    htime.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (dataSelectedClockLossDirection_nonnegative P Z reverse x q)) hdom
  exact h.trans_eq (by unfold Instance.entranceRemainingSize; ring)

theorem Instance.dataSelectedClockLoss_far_time_bound (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi a x : ℝ}
    (hlo : 0 < lo) (hZrange : ∀ y, Z y ∈ Icc lo hi)
    (hlohi : lo ≤ hi) (hx : 0 < x) (reverse : Bool) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      clockRegionLoss P Z hi a (x/2) false
        (fun qt => dataSelectedClockLossDirection P Z reverse x qt.1 qt.2) q ≤
      ((1/(2*lo))*x) * (if x/2 ≤ P.entranceFutureError k lo hi a q
        then P.entranceFutureError k lo hi a q else 0) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hZ0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  filter_upwards [P.dataSelectedClockLossDirection_after_entrance hbound hlo.le hlohi hZrange reverse x]
    with q hq
  have htime := measurable_dataSelectedClockLossDirection_time P hP Z hZ0 reverse x q
  have hS := measurableSet_clockLossRegion P hP hZ0 hi a (x/2) false q
  have hdom := clock_lossGapBound_restrict P (z := Z q.1) (x := x)
    (E := P.entranceFutureError k lo hi a q) (σ := P.trueCriticalEntrance hi a q.2)
    (S := clockLossRegion P Z hi a (x/2) false q)
    (loss := fun t => dataSelectedClockLossDirection P Z reverse x q t) q.2 hS (fun _ ht => ht.1) hq
  have h := P.clock_post_far_loss_integral_le hP hlo (hZrange q.1).1 hx
    (P.trueCriticalEntrance_mem hi a q.2) (P.entranceFutureError_nonnegative lo hi a q) q.2
    (fun t => dataSelectedClockLossDirection P Z reverse x q t)
    htime.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (dataSelectedClockLossDirection_nonnegative P Z reverse x q)) hdom
  exact h.trans_eq (by ring)

theorem Instance.dataSelectedClockLoss_early_time_bound (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi a x : ℝ}
    (hlo : 0 < lo) (hZrange : ∀ y, Z y ∈ Icc lo hi)
    (hlohi : lo ≤ hi) (ha : 0 < a) (hx : x ≤ a/(4*(hi/lo))) (reverse : Bool) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      clockRegionLoss P (fun _ => hi) hi (2*a) a true
        (fun qt => dataSelectedClockLossDirection P Z reverse x qt.1 qt.2) q ≤
      (((32*(2+hi)/lo)*(hi/lo)^5)/a^5) * (P.entranceRemainingSize hi (2*a) q.2 *
        P.entranceFutureError k lo hi (2*a) q ^ 6) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hZ0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  have hhi : 0 ≤ hi := (hlo.trans_le hlohi).le
  filter_upwards [P.dataSelectedClockLossDirection_after_entrance (a := 2*a) hbound hlo.le hlohi hZrange reverse x]
    with q hq
  have htime := measurable_dataSelectedClockLossDirection_time P hP Z hZ0 reverse x q
  have hS := measurableSet_clockLossRegion P hP (fun _ => hhi) hi (2*a) a true q
  have hdom := clock_lossGapBound_restrict P (z := Z q.1) (x := x)
    (E := P.entranceFutureError k lo hi (2*a) q) (σ := P.trueCriticalEntrance hi (2*a) q.2)
    (S := clockLossRegion P (fun _ => hi) hi (2*a) a true q)
    (loss := fun t => dataSelectedClockLossDirection P Z reverse x q t) q.2 hS (fun _ ht => ht.1) hq
  have h := P.clock_post_early_loss_integral_sixth_le hP hlo (hZrange q.1).1 (hZrange q.1).2 ha hx
    (P.trueCriticalEntrance_mem hi (2*a) q.2) (P.entranceFutureError_nonnegative lo hi (2*a) q) q.2
    (fun t => dataSelectedClockLossDirection P Z reverse x q t)
    htime.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (dataSelectedClockLossDirection_nonnegative P Z reverse x q)) hdom
  exact h.trans_eq (by unfold Instance.entranceRemainingSize; ring)

end ProphetSecretary.Model
