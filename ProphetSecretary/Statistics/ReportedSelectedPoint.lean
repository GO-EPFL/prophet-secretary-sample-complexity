import ProphetSecretary.Statistics.ReportedDurationComparison
import ProphetSecretary.Statistics.CalibratedSelectorRegret

/-!
# The reward inequality with reported validation times

The scalar regret is measured under the actual online stopping time. Its
comparison to the reported validation surrogate incurs at most a quarter
of the clock mesh.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace PSeed] [NeZero m]

theorem reported_calibration_reward_master (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP]
    (hP : P.HasPositiveFiniteMaximum) (report : ℝ → ℝ) (hReport : Measurable report)
    {δ : ℝ} (hδ : 0≤δ)
    (hr : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) t ∧ t-report t≤δ)
    (hMono : MonotoneOn report (Icc (0 : ℝ) 1)) {mu zlo b : ℝ}
    (hb : b∈Icc (0 : ℝ) 1) (h0 : 0≤zlo) (hz : zlo≤1/4)
    (hMu : mu≤1/40) (hMean : mu≤P.expectedMaximum) (hM : P.expectedMaximum≤1)
    (hClamp : ∀ (π : RandomizedPolicy n) (x : ℝ), π.normalizedRegret P b≤x →
      normalizedScalarGap P 1/40-5*x≤π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (d : OfflineData n m J TSeed PSeed) :
    let A := reportedOfflinePrepare report mu zlo (1/4) targetEstimate policyEstimate
    let π := selectorConditionalPolicy νP zlo (1/4) policyEstimate A hC d
    let Z := selectorCoefficient zlo A d
    let g := reportedOfflineError P νP report mu zlo (1/4) targetEstimate policyEstimate d
    let ρ := offlineTarget mu targetEstimate d
    let r := selectorRegret P νP zlo policyEstimate A hC b d
    mu*normalizedScalarGap P (normalizedCoefficient Z)-5*r-Z*g-
      (1/4)*max 0 (ρ-P.optimalScalarRatio)-δ/4≤π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum := by
  let A := reportedOfflinePrepare (J := J) report mu zlo (1/4) targetEstimate policyEstimate
  let π := selectorConditionalPolicy νP zlo (1/4) policyEstimate A hC d
  let Z := selectorCoefficient zlo A d
  let g := reportedOfflineError P νP report mu zlo (1/4) targetEstimate policyEstimate d
  let ρ := offlineTarget mu targetEstimate d
  let r := selectorRegret P νP zlo policyEstimate A hC b d
  have hBounds := reportedOfflinePrepare_bounds (J := J) report mu zlo (1/4) targetEstimate policyEstimate
  have hR0 : 0≤r := selectorRegret_nonnegative P νP zlo policyEstimate A hBounds hC hP.1 h0 hz hb d
  have hZ : Z∈Icc (0 : ℝ) (1/4) := selectorCoefficient_range zlo A hBounds h0 hz d
  change mu*normalizedScalarGap P (normalizedCoefficient Z)-5*r-Z*g-
    (1/4)*max 0 (ρ-P.optimalScalarRatio)-δ/4≤π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum
  by_cases hl : (A d).2.1=1
  · have hZ0 : Z=0 := selectorCoefficient_left zlo A d hl
    have hReg : π.normalizedRegret P b≤r := by
      change π.normalizedRegret P b≤ (if (A d).2.1=1 then π.normalizedRegret P b
        else optimalScalarValue P 1 Z-π.scalarObjective P 1 Z)
      rw [if_pos hl]
    have h := calibration_reward_master_left P π hP hMu (hClamp _ _ hReg)
    rw [hZ0,zero_mul,sub_zero]
    linarith only [h,hδ,mul_nonneg (by norm_num : (0 : ℝ)≤1/4) (le_max_left (0 : ℝ) (ρ-P.optimalScalarRatio))]
  · have hReg : optimalScalarValue P 1 Z-π.scalarObjective P 1 Z≤r := by
      change optimalScalarValue P 1 Z-π.scalarObjective P 1 Z≤ (if (A d).2.1=1 then π.normalizedRegret P b
        else optimalScalarValue P 1 Z-π.scalarObjective P 1 Z)
      rw [if_neg hl]
    have hTime : π.expectedDuration P≤ρ+g+δ :=
      (reportedOffline_duration_comparison P νP report hReport hδ hr hMono mu hz targetEstimate policyEstimate hC d).1 hl
    have h := calibration_reward_master_nonleft_reported P π hP hMean hM hZ hδ hReg hTime
    linarith only [h,hR0]

end ProphetSecretary.Statistics.Calibration
