import ProphetSecretary.Statistics.MixedTinyExpectation
import ProphetSecretary.Statistics.MixedDataSelectedClockLossIntegrability
import ProphetSecretary.Model.ClockTinyLoss

/-!
# Actual mixed tiny-offer losses for selected scalars

Both canonical rules reject before the final waiting window. Within it, their
actual target pending means have the proved independent-sample/clock expectation.
The same explicit quadratic and inverse-linear tiny bounds hold for both loss
directions, even with the scalar selected using all training samples.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.mixedDataSelectedClockLoss_pair_tiny_dom (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hlo : 0 < lo) (hZ : ∀ a, Z a ∈ Icc lo hi) (hx : 0 ≤ x)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    mixedDataSelectedClockLoss P known Z x q t ≤ (Icc (1-x/lo) 1).indicator
      (fun s => x+P.mixedTinyTargetPendingMean (k := k) known false q s+hi*(1-s)) t ∧
    mixedDataSelectedClockLossReverse P known Z x q t ≤ (Icc (1-x/lo) 1).indicator
      (fun s => x+P.mixedTinyTargetPendingMean (k := k) known true q s+hi*(1-s)) t := by
  have hz0 : 0 ≤ Z q.1 := (hlo.trans_le (hZ q.1).1).le
  by_cases hw : t ∈ Icc (1-x/lo) 1
  · rw [indicator_of_mem hw, indicator_of_mem hw]
    constructor
    · exact P.clock_gapLoss_le_pendingMean hP hx hz0 (hZ q.1).2 ht.2 q.2 _
    · exact (mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).clock_gapLoss_le_pendingMean
        (mixedEmpiricalInstance_integrable P hP known _) hx hz0 (hZ q.1).2 ht.2 q.2 _
  · rw [indicator_of_notMem hw, indicator_of_notMem hw]
    have hwindow : x/lo < 1-t := by
      have hlt : t < 1-x/lo := lt_of_not_ge (fun h => hw ⟨h,ht.2⟩)
      linarith only [hlt]
    have hzero := clock_paired_gapLoss_zero_before_window P
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)) hP
      (mixedEmpiricalInstance_integrable P hP known _) hlo (hZ q.1).1 ht.2 hwindow q.2
    exact ⟨hzero.1.le, hzero.2.le⟩

/-- Both actual losses at any measurable training-selected scalar have the
quadratic tiny-offer bound, with no fixed-weight centering assumption. -/
theorem Instance.mixedDataSelectedClockLoss_pair_tiny_expectation (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ a, Z a ∈ Icc lo hi) (hx : 0 ≤ x) :
    (∫ q, ∫ t, mixedDataSelectedClockLoss P known Z x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x^2 ∧
    (∫ q, ∫ t, mixedDataSelectedClockLossReverse P known Z x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x^2 := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hhi : 0 ≤ hi := (hlo.trans_le hlohi).le
  have hI := P.integrable_mixedDataSelectedClockLoss_pair known hbound hZ
    (fun a => ⟨(hlo.trans_le (hZrange a).1).le,(hZrange a).2⟩) x
  constructor
  · exact P.mixed_tiny_expectation_from_dom known hP false hlo hhi hx hI.1
      (mixedDataSelectedClockLoss_nonnegative P known Z x)
      (fun t ht => Filter.Eventually.of_forall fun q =>
        (P.mixedDataSelectedClockLoss_pair_tiny_dom known hP hlo hZrange hx q ht).1)
  · exact P.mixed_tiny_expectation_from_dom known hP true hlo hhi hx hI.2
      (mixedDataSelectedClockLossReverse_nonnegative P known Z x)
      (fun t ht => Filter.Eventually.of_forall fun q =>
        (P.mixedDataSelectedClockLoss_pair_tiny_dom known hP hlo hZrange hx q ht).2)

/-- The `x ≤ 1/k` branch of the per-candidate inverse-linear estimate. -/
theorem Instance.mixedDataSelectedClockLoss_pair_tiny_rate (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ a, Z a ∈ Icc lo hi) (hx : 0 ≤ x) (hxk : x ≤ 1/(k : ℝ)) :
    (∫ q, ∫ t, mixedDataSelectedClockLoss P known Z x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) ∧
    (∫ q, ∫ t, mixedDataSelectedClockLossReverse P known Z x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) := by
  have h := P.mixedDataSelectedClockLoss_pair_tiny_expectation known hbound hZ hlo hlohi hZrange hx
  have hx2 : x^2 ≤ x/(k : ℝ) := by
    simpa only [pow_two,mul_one_div] using mul_le_mul_of_nonneg_left hxk hx
  have hC : 0 ≤ empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment) := by
    have hhi : 0 < hi := hlo.trans_le hlohi
    have hS := P.totalFirstMoment_nonnegative
    unfold empiricalTinyRegretConstant
    positivity
  have hR : empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x^2 ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) :=
    (mul_le_mul_of_nonneg_left hx2 hC).trans_eq (by ring)
  exact ⟨h.1.trans hR,h.2.trans hR⟩

end ProphetSecretary.Model
