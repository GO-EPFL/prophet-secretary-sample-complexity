import ProphetSecretary.Statistics.MixedDataSelectedLossRegions
import ProphetSecretary.Statistics.MixedEntranceFutureMoments
import ProphetSecretary.Statistics.MixedClockLossEntrances

/-!
# Actual mixed regional time-loss bounds

Both directions use the constructed mixed entrance envelope and true post-size.
The scalar is fixed during time integration. Generic true continuation slopes
and measurable true time regions give near, far and early estimates without
assuming any error/size independence or selected-weight centering.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.mixedDataSelectedClockLossDirection_after_entrance (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hZ : ∀ y, Z y ∈ Icc lo hi)
    (reverse : Bool) (x : ℝ) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t ∈ Ioc (P.trueCriticalEntrance hi a q.2) 1,
      mixedDataSelectedClockLossDirection P known Z reverse x q t ≤
        if |x-P.clockContinuation (Z q.1) q.2 t| ≤ P.mixedEntranceFutureError known k lo hi a q
        then P.mixedEntranceFutureError known k lo hi a q else 0 := by
  filter_upwards [P.paired_mixedClockGapLoss_after_entrance (k := k) (a := a) known hbound hlo hlohi] with q hq
  intro t ht
  have h := hq t ht (Z q.1) (hZ q.1) x
  cases reverse
  · exact h.1
  · exact h.2

theorem Instance.mixedDataSelectedClockLoss_near_time_bound (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi a x : ℝ}
    (hlo : 0 < lo) (hZrange : ∀ y, Z y ∈ Icc lo hi)
    (hlohi : lo ≤ hi) (hx : 0 < x) (reverse : Bool) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      clockRegionLoss P Z hi a (x/2) true
        (fun qt => mixedDataSelectedClockLossDirection P known Z reverse x qt.1 qt.2) q ≤
      ((4*(2+hi)/lo)/x) * (P.entranceRemainingSize hi a q.2 *
        P.mixedEntranceFutureError known k lo hi a q ^ 2) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hZ0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  filter_upwards [P.mixedDataSelectedClockLossDirection_after_entrance known hbound hlo.le hlohi hZrange reverse x]
    with q hq
  have htime := measurable_mixedDataSelectedClockLossDirection_time P known hP Z hZ0 reverse x q
  have hS := measurableSet_clockLossRegion P hP hZ0 hi a (x/2) true q
  have hdom := clock_lossGapBound_restrict P (z := Z q.1) (x := x)
    (E := P.mixedEntranceFutureError known k lo hi a q) (σ := P.trueCriticalEntrance hi a q.2)
    (S := clockLossRegion P Z hi a (x/2) true q)
    (loss := fun t => mixedDataSelectedClockLossDirection P known Z reverse x q t) q.2 hS (fun _ ht => ht.1) hq
  have h := P.clock_post_near_loss_integral_le hP hlo (hZrange q.1).1 (hZrange q.1).2 hx
    (P.trueCriticalEntrance_mem hi a q.2) (P.mixedEntranceFutureError_nonnegative known lo hi a q) q.2
    (fun t => mixedDataSelectedClockLossDirection P known Z reverse x q t)
    htime.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (mixedDataSelectedClockLossDirection_nonnegative P known Z reverse x q)) hdom
  exact h.trans_eq (by unfold Instance.entranceRemainingSize; ring)

theorem Instance.mixedDataSelectedClockLoss_far_time_bound (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi a x : ℝ}
    (hlo : 0 < lo) (hZrange : ∀ y, Z y ∈ Icc lo hi)
    (hlohi : lo ≤ hi) (hx : 0 < x) (reverse : Bool) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      clockRegionLoss P Z hi a (x/2) false
        (fun qt => mixedDataSelectedClockLossDirection P known Z reverse x qt.1 qt.2) q ≤
      ((1/(2*lo))*x) * (if x/2 ≤ P.mixedEntranceFutureError known k lo hi a q
        then P.mixedEntranceFutureError known k lo hi a q else 0) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hZ0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  filter_upwards [P.mixedDataSelectedClockLossDirection_after_entrance known hbound hlo.le hlohi hZrange reverse x]
    with q hq
  have htime := measurable_mixedDataSelectedClockLossDirection_time P known hP Z hZ0 reverse x q
  have hS := measurableSet_clockLossRegion P hP hZ0 hi a (x/2) false q
  have hdom := clock_lossGapBound_restrict P (z := Z q.1) (x := x)
    (E := P.mixedEntranceFutureError known k lo hi a q) (σ := P.trueCriticalEntrance hi a q.2)
    (S := clockLossRegion P Z hi a (x/2) false q)
    (loss := fun t => mixedDataSelectedClockLossDirection P known Z reverse x q t) q.2 hS (fun _ ht => ht.1) hq
  have h := P.clock_post_far_loss_integral_le hP hlo (hZrange q.1).1 hx
    (P.trueCriticalEntrance_mem hi a q.2) (P.mixedEntranceFutureError_nonnegative known lo hi a q) q.2
    (fun t => mixedDataSelectedClockLossDirection P known Z reverse x q t)
    htime.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (mixedDataSelectedClockLossDirection_nonnegative P known Z reverse x q)) hdom
  exact h.trans_eq (by ring)

theorem Instance.mixedDataSelectedClockLoss_early_time_bound (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi a x : ℝ}
    (hlo : 0 < lo) (hZrange : ∀ y, Z y ∈ Icc lo hi)
    (hlohi : lo ≤ hi) (ha : 0 < a) (hx : x ≤ a/(4*(hi/lo))) (reverse : Bool) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      clockRegionLoss P (fun _ => hi) hi (2*a) a true
        (fun qt => mixedDataSelectedClockLossDirection P known Z reverse x qt.1 qt.2) q ≤
      (((32*(2+hi)/lo)*(hi/lo)^5)/a^5) * (P.entranceRemainingSize hi (2*a) q.2 *
        P.mixedEntranceFutureError known k lo hi (2*a) q ^ 6) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hZ0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  have hhi : 0 ≤ hi := (hlo.trans_le hlohi).le
  filter_upwards [P.mixedDataSelectedClockLossDirection_after_entrance (a := 2*a) known hbound hlo.le hlohi hZrange reverse x]
    with q hq
  have htime := measurable_mixedDataSelectedClockLossDirection_time P known hP Z hZ0 reverse x q
  have hS := measurableSet_clockLossRegion P hP (fun _ => hhi) hi (2*a) a true q
  have hdom := clock_lossGapBound_restrict P (z := Z q.1) (x := x)
    (E := P.mixedEntranceFutureError known k lo hi (2*a) q) (σ := P.trueCriticalEntrance hi (2*a) q.2)
    (S := clockLossRegion P (fun _ => hi) hi (2*a) a true q)
    (loss := fun t => mixedDataSelectedClockLossDirection P known Z reverse x q t) q.2 hS (fun _ ht => ht.1) hq
  have h := P.clock_post_early_loss_integral_sixth_le hP hlo (hZrange q.1).1 (hZrange q.1).2 ha hx
    (P.trueCriticalEntrance_mem hi (2*a) q.2) (P.mixedEntranceFutureError_nonnegative known lo hi (2*a) q) q.2
    (fun t => mixedDataSelectedClockLossDirection P known Z reverse x q t)
    htime.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (mixedDataSelectedClockLossDirection_nonnegative P known Z reverse x q)) hdom
  exact h.trans_eq (by unfold Instance.entranceRemainingSize; ring)

end ProphetSecretary.Model
