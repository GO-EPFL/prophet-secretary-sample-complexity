import ProphetSecretary.Statistics.EmpiricalTinyExpectation
import ProphetSecretary.Statistics.DataSelectedClockLossIntegrability
import ProphetSecretary.Model.ClockTinyLoss

/-!
# Tiny-offer losses at a training-selected scalar (`upstat:tiny`)

The scalar may depend on all training coordinates, but is fixed during the
candidate-time integration. Both actual comparison losses vanish before the
terminal window. Their target pending means have expectations (1-t)S under
the actual independent training and clock law.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.dataSelectedClockLoss_pair_tiny_dom (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hlo : 0 < lo) (hZ : ∀ a, Z a ∈ Icc lo hi) (hx : 0 ≤ x)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dataSelectedClockLoss P Z x q t ≤ (Icc (1-x/lo) 1).indicator
      (fun s => x+P.tinyTargetPendingMean (k := k) false q s+hi*(1-s)) t ∧
    dataSelectedClockLossReverse P Z x q t ≤ (Icc (1-x/lo) 1).indicator
      (fun s => x+P.tinyTargetPendingMean (k := k) true q s+hi*(1-s)) t := by
  have hz0 : 0 ≤ Z q.1 := (hlo.trans_le (hZ q.1).1).le
  by_cases hw : t ∈ Icc (1-x/lo) 1
  · rw [indicator_of_mem hw, indicator_of_mem hw]
    constructor
    · exact P.clock_gapLoss_le_pendingMean hP hx hz0 (hZ q.1).2 ht.2 q.2 _
    · exact (totalEmpiricalInstance (reservoirCoordinates.symm q.1)).clock_gapLoss_le_pendingMean
        (totalEmpiricalInstance_integrable _) hx hz0 (hZ q.1).2 ht.2 q.2 _
  · rw [indicator_of_notMem hw, indicator_of_notMem hw]
    have hwindow : x/lo < 1-t := by
      have hlt : t < 1-x/lo := lt_of_not_ge (fun h => hw ⟨h,ht.2⟩)
      linarith only [hlt]
    have hzero := clock_paired_gapLoss_zero_before_window P
      (totalEmpiricalInstance (reservoirCoordinates.symm q.1)) hP
      (totalEmpiricalInstance_integrable _) hlo (hZ q.1).1 ht.2 hwindow q.2
    exact ⟨hzero.1.le, hzero.2.le⟩

/-- Both actual losses at any measurable training-selected scalar have the
quadratic tiny-offer bound, with no fixed-weight centering assumption. -/
theorem Instance.dataSelectedClockLoss_pair_tiny_expectation (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ a, Z a ∈ Icc lo hi) (hx : 0 ≤ x) :
    (∫ q, ∫ t, dataSelectedClockLoss P Z x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x^2 ∧
    (∫ q, ∫ t, dataSelectedClockLossReverse P Z x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x^2 := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hhi : 0 ≤ hi := (hlo.trans_le hlohi).le
  have hI := P.integrable_dataSelectedClockLoss_pair hbound hZ
    (fun a => ⟨(hlo.trans_le (hZrange a).1).le,(hZrange a).2⟩) x
  constructor
  · exact P.empirical_tiny_expectation_from_dom hP false hlo hhi hx hI.1
      (dataSelectedClockLoss_nonnegative P Z x)
      (fun t ht => Filter.Eventually.of_forall fun q =>
        (P.dataSelectedClockLoss_pair_tiny_dom hP hlo hZrange hx q ht).1)
  · exact P.empirical_tiny_expectation_from_dom hP true hlo hhi hx hI.2
      (dataSelectedClockLossReverse_nonnegative P Z x)
      (fun t ht => Filter.Eventually.of_forall fun q =>
        (P.dataSelectedClockLoss_pair_tiny_dom hP hlo hZrange hx q ht).2)

/-- The `x ≤ 1/k` branch of the per-candidate inverse-linear estimate. -/
theorem Instance.dataSelectedClockLoss_pair_tiny_rate (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ a, Z a ∈ Icc lo hi) (hx : 0 ≤ x) (hxk : x ≤ 1/(k : ℝ)) :
    (∫ q, ∫ t, dataSelectedClockLoss P Z x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) ∧
    (∫ q, ∫ t, dataSelectedClockLossReverse P Z x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) := by
  have h := P.dataSelectedClockLoss_pair_tiny_expectation hbound hZ hlo hlohi hZrange hx
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
