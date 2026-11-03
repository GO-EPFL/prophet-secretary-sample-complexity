import ProphetSecretary.Statistics.CalibratedClockRounding
import ProphetSecretary.Statistics.CalibratedPolicyCoupling

/-!
# Planner confidence after clock rounding

The planner is queried at the rounded remaining horizon with half of the
policy tolerance. Choosing the clock mesh so that the horizon error uses
the other half preserves the same single-call confidence contract.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {PSeed : Type} [MeasurableSpace PSeed] [NeZero m]

theorem clockRoundedEstimate_confidence (ν : Measure PSeed) [IsProbabilityMeasure ν]
    (f : ℝ → ℝ) {δ zlo : ℝ} (hδ : 0≤δ) (hzlo : 0<zlo)
    (hf : ∀ t∈Icc (0 : ℝ) 1, f t∈Icc (0 : ℝ) t ∧ t-f t≤δ)
    (hMesh : 4*δ≤policyAccuracy m zlo/2)
    (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (A : Finset (Fin n)) {u z : ℝ}
    (hu : u∈Icc (0 : ℝ) 1) (hz : z∈Icc (0 : ℝ) 4)
    (hConf : ∀ v∈Icc (0 : ℝ) 1, ν.real {r | policyAccuracy m zlo/2 <
      |estimate q A v z r-(totalEmpiricalInstance q).continuationValue A v 1 z|}≤policyFailureBound n m J) :
    ν.real {r | policyAccuracy m zlo <
      |clockRoundedEstimate f estimate q A u z r-(totalEmpiricalInstance q).continuationValue A u 1 z|}
        ≤ policyFailureBound n m J := by
  let t := 1-u
  let v := unitRemaining (f t)
  let Q := totalEmpiricalInstance q
  have ht : t∈Icc (0 : ℝ) 1 := ⟨by dsimp [t]; linarith [hu.2],by dsimp [t]; linarith [hu.1]⟩
  have hft : f t∈Icc (0 : ℝ) 1 := ⟨(hf t ht).1.1,(hf t ht).1.2.trans ht.2⟩
  have hv := unitRemaining_range (f t)
  have hDiff : v-u=t-f t := by dsimp [v]; rw [unitRemaining_eq hft]; dsimp [t]; ring
  have hDiff0 : 0≤v-u := hDiff ▸ sub_nonneg.mpr (hf t ht).1.2
  have hDiff1 : v-u≤δ := hDiff ▸ (hf t ht).2
  have hQ := totalEmpiricalInstance_integrable q
  have hV := optimalScalarValue_horizon_lipschitz (Q.restrictTo A) (Q.restrictTo_integrable_maximum A hQ)
    (w := 1) zero_le_one hz.1 hv.1 hu.1
  rw [abs_of_nonneg hDiff0] at hV
  have hTime : |Q.continuationValue A v 1 z-Q.continuationValue A u 1 z|≤z*δ :=
    hV.trans (mul_le_mul_of_nonneg_left hDiff1 hz.1)
  have hFloor := Q.durationWeight_le_continuationValue hQ A hu.1 (show (0 : ℝ)≤1 by norm_num) hz.1
  have hAcc : 0≤policyAccuracy m zlo/2 := by unfold policyAccuracy; positivity
  have hInc : {r | policyAccuracy m zlo <
      |clockRoundedEstimate f estimate q A u z r-Q.continuationValue A u 1 z|} ⊆
      {r | policyAccuracy m zlo/2 < |estimate q A v z r-Q.continuationValue A v 1 z|} := by
    intro r hr
    change policyAccuracy m zlo/2 < |estimate q A v z r-Q.continuationValue A v 1 z|
    apply lt_of_not_ge
    intro hb
    have h := clockRoundedEstimate_error hz.1 hAcc hDiff1 hFloor hTime hb
    have hDrift : z*δ≤policyAccuracy m zlo/2 := (mul_le_mul_of_nonneg_right hz.2 hδ).trans hMesh
    have hBound : |clockRoundedEstimate f estimate q A u z r-Q.continuationValue A u 1 z|≤policyAccuracy m zlo := by
      change |max (z*v) (estimate q A v z r)-Q.continuationValue A u 1 z|≤policyAccuracy m zlo
      linarith only [h,hDrift]
    exact (not_lt_of_ge hBound) hr
  exact (measureReal_mono hInc).trans (hConf v hv)

end ProphetSecretary.Statistics.Calibration
