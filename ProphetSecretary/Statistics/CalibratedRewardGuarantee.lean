import ProphetSecretary.Statistics.CalibratedSelectedPoint
import ProphetSecretary.Statistics.CalibrationMasterExpectation
import ProphetSecretary.Limiting.ScalarDiameter
import ProphetSecretary.Model.LargeFirstMomentGapFloor
import ProphetSecretary.Model.FirstMomentLayercake
import ProphetSecretary.Model.FrozenSelectedGapIntegrability

/-!
# Reward guarantee for the calibrated learner

The quantitative regret bound remains the policy-quality input. The
target bounds, calibration covariance, endpoint clamp, and large-moment
gap floor are applied to the same actual two-block learner.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

/-- Conditional on the selected-policy regret bound, the actual calibrated
learner has uniform reward loss of order (1/m). -/
theorem exists_calibrated_reward_of_expected_regret (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
    ∃ b : ℚ, (b : ℝ)∈Ioo (4/5 : ℝ) 1 ∧ ∀ KR : ℝ, 0≤KR →
      ∃ K : ℝ, 0<K ∧ ∀ (n m J : ℕ) [NeZero m] (P : Instance n)
        (_hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (_hMean : mu≤P.expectedMaximum)
        (_hM : P.expectedMaximum≤1/80) (_hL : P.positiveCount≤2*Real.log (m : ℝ))
        (TSeed PSeed : Type) [MeasurableSpace TSeed] [MeasurableSpace PSeed]
        (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
        (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
        (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
        (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
          policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)),
        let zlo := (1-(b : ℝ))/(b : ℝ)
        (∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
          νT.real {r | 1/(m : ℝ) < |targetEstimate (reservoirCoordinates.symm a) (targetGrid j) r-
            optimalScalarValue (trainingInstance a) 1 (targetGrid j)|}≤1/((m : ℝ)^2*(4*(m : ℝ)+1))) →
        (∫ d, offlineSelectedRegret (J := J) P νP mu zlo targetEstimate policyEstimate hC (b : ℝ) d
          ∂offlineDataLaw P νT νP)≤KR*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ) →
        optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤
          (learnerCore (J := J) mu zlo (1/4) νT νP targetEstimate policyEstimate hT hC).expectedReward P := by
  obtain ⟨b,hb,hClamp⟩ := exists_rational_calibration_endpoint mu hmu
  obtain ⟨S0,κ,hS0,hκ,hFloor⟩ := bounded_largeFirstMoment_gap_floor mu hmu
  have hSpos : 0<S0 := zero_lt_one.trans_le hS0
  obtain ⟨KD,hKD,hDiam⟩ := ProphetSecretary.Limiting.bounded_scalarGap_quadratic_diameter
    1 S0 mu hSpos hmu
  obtain ⟨KT,hKT,hTarget⟩ := exists_numericalTarget_sharp_bound mu hmu hmuHi S0 hSpos.le
  refine ⟨b,hb,?_⟩
  intro KR hKR
  let KC := 20/mu+2
  have hKC : 0≤KC := by dsimp [KC]; positivity
  obtain ⟨m0,_hm0,hHighThreshold⟩ := exists_calibration_highMoment_threshold hmu hκ hKR hKC
  let B := ((Real.sqrt (32*KD)+KT/(4*Real.sqrt mu))^2/(4*mu)+
    (5*(KR*(1+S0*(1+S0)))+1/4+KT/4))
  let K := max B (m0 : ℝ)+1
  have hK : 0<K := by dsimp [K]; linarith [le_max_right B (m0 : ℝ),Nat.cast_nonneg (α := ℝ) m0]
  refine ⟨K,hK,?_⟩
  intro n m J hm P hcap hMean hM hL TSeed PSeed hTS hPS νT νP hνT hνP
    targetEstimate policyEstimate hT hC
  dsimp only
  intro hConf hReg
  let zlo := (1-(b : ℝ))/(b : ℝ)
  have hz := calibrationEndpoint_coefficient_bounds hb
  have hbI : (b : ℝ)∈Icc 0 1 := ⟨(by norm_num : (0 : ℝ)≤4/5).trans hb.1.le,hb.2.le⟩
  have hP : P.HasPositiveFiniteMaximum := ⟨P.integrable_maximum_of_bounded hcap,hmu.trans_le hMean⟩
  have hmR : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
  have hM1 : P.expectedMaximum≤1 := hM.trans (by norm_num)
  let L := learnerCore (J := J) mu zlo (1/4) νT νP targetEstimate policyEstimate hT hC
  change optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P
  by_cases hm0 : m0≤m
  · let O := offlineDataLaw (m := m) (J := J) P νT νP
    let D := OfflineData n m J TSeed PSeed
    let Z := offlineSelectedCoefficient (J := J) mu zlo targetEstimate policyEstimate
    let g := offlineCalibrationError (J := J) P νP mu zlo (1/4) targetEstimate policyEstimate
    let r := offlineSelectedRegret (J := J) P νP mu zlo targetEstimate policyEstimate hC (b : ℝ)
    let ρ := offlineTarget (J := J) (PSeed := PSeed) mu targetEstimate
    let e := fun d : D => max 0 (ρ d-P.optimalScalarRatio)
    let R := fun d : D => (conditionalCalibrationPolicy νP mu zlo (1/4) targetEstimate policyEstimate hC d).expectedReward P
    let F := fun d : D => normalizedScalarGap P (normalizedCoefficient (Z d))
    let G := ∫ d,F d ∂O
    let Δ := P.optimalScalarRatio-optimalCompetitiveRatio
    have hZ := measurable_offlineSelectedCoefficient (J := J) mu zlo targetEstimate policyEstimate hT hC
    have hZR := offlineSelectedCoefficient_range (J := J) mu zlo targetEstimate policyEstimate hz.1.le hz.2.le
    have hg := measurable_offlineCalibrationError (J := J) P νP mu targetEstimate policyEstimate hT hC
      (zlo := zlo) (zhi := (1/4))
    have hgR := offlineCalibrationError_abs_le_one (J := J) P νP mu targetEstimate policyEstimate hC hz.2.le
    have hMom := offlineCalibrationError_moments (J := J) P νT νP mu targetEstimate policyEstimate hT hC hz.2.le
    have hR := integrable_conditionalCalibrationReward (J := J) P νT νP mu zlo (1/4)
      targetEstimate policyEstimate hT hC hP.1
    have hr := integrable_offlineSelectedRegret (J := J) P νT νP mu zlo targetEstimate policyEstimate hT hC
      hP.1 hz.1.le hz.2.le hbI
    have hgI : Integrable g O := Integrable.of_bound hg.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun d => by simpa only [Real.norm_eq_abs] using hgR d)
    have hzg : Integrable (fun d => Z d*g d) O := hgI.bdd_mul hZ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun d => by
        change ‖Z d‖≤1/4
        rw [Real.norm_eq_abs,abs_of_nonneg (hZR d).1]
        exact (hZR d).2)
    have hρ := measurable_offlineTarget (J := J) (PSeed := PSeed) mu targetEstimate hT
    have he : Integrable e O := Integrable.of_bound
      (measurable_const.max (hρ.sub_const _)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun d => by
        have h := computedTarget_range mu targetEstimate d.1.1 d.1.2
        have hRatio0 : 0≤P.optimalScalarRatio := optimalCompetitiveRatio_nonnegative.trans (P.optimalScalarRatio_bounds hP).1
        change ‖max 0 (computedTarget mu targetEstimate d.1.1 d.1.2-P.optimalScalarRatio)‖≤1
        rw [Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
        exact max_le zero_le_one (by linarith [h.2]))
    have hl : ∀ d : D, normalizedCoefficient (Z d)∈Icc (0 : ℝ) 1 := fun d =>
      let h := normalizedCoefficient_mem (hZR d)
      ⟨(by norm_num : (0 : ℝ)≤4/5).trans h.1,h.2⟩
    have hlm : Measurable (fun d : D => normalizedCoefficient (Z d)) :=
      measurable_const.div (measurable_const.add hZ)
    have hF := P.integrable_normalizedGap_of_weight hcap O hlm hl
    have hG : 0≤G := integral_nonneg (fun d => normalizedScalarGap_nonnegative P hP.1 (hl d))
    have hΔG : mu*Δ≤G := expected_gap_ge_ratio_slack P hP O (by linarith) hMean hl hF
    have hMaster := integral_calibration_reward_master O hF hr hzg he hR mu
      (optimalCompetitiveRatio*P.expectedMaximum) (Filter.Eventually.of_forall fun d =>
        offline_calibration_reward_master P νP mu zlo targetEstimate policyEstimate hC hP hbI hz.1.le hz.2.le
          (by linarith) hMean hM1 (hClamp n P hcap hMean) d)
    have hConf' := targetTable_conditional_confidence P νT mu targetEstimate hT hConf
    have hEq := offlineTarget_integral (J := J) P νT νP mu targetEstimate hT
      (fun x => max 0 (x-P.optimalScalarRatio)) (measurable_const.max (measurable_id.sub_const _))
    simp only [firstInformationLaw] at hEq
    change (∫ d,e d ∂O)=_ at hEq
    rw [learnerCore_expectedReward_eq_integral (J := J) P νT νP mu zlo (1/4)
      targetEstimate policyEstimate hT hC hP.1]
    change optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤∫ d,R d ∂O
    by_cases hS : P.totalFirstMoment≤S0
    · have hT' := hTarget n m P hcap hMean hM hL hS _ (targetQueryArrayLaw νT) _
        (measurable_targetTable mu targetEstimate hT) hConf'
      rw [← hEq] at hT'
      have hCov := calibration_covariance_sharp P hcap O hZ hg hZR hgR hMom.1 hMom.2
        hKD.le (hDiam n P hcap hS hMean)
      have hS0' : 0≤P.totalFirstMoment := Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae (P.nonnegative i))
      have hReg' : (∫ d,r d ∂O)≤KR*(1+S0*(1+S0))/(m : ℝ) := by
        refine hReg.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hKR) hmR.le)
        have h : P.totalFirstMoment*(1+P.totalFirstMoment)≤S0*(1+S0) :=
          mul_le_mul hS (add_le_add le_rfl hS) (by linarith) hSpos.le
        exact add_le_add le_rfl h
      have hRate := calibration_lowMoment_reward_rate hmu hmR hG hΔG hKT.le hReg' hCov hT' hMaster
      have hBK : B≤K := (le_max_left _ _).trans (by dsimp [K]; linarith)
      have hD := div_le_div_of_nonneg_right hBK hmR.le
      change -B/(m : ℝ)≤(∫ d,R d ∂O)-optimalCompetitiveRatio*P.expectedMaximum at hRate
      calc
        _ ≤ optimalCompetitiveRatio*P.expectedMaximum-B/(m : ℝ) := sub_le_sub_left hD _
        _ = -B/(m : ℝ)+optimalCompetitiveRatio*P.expectedMaximum := by ring
        _ ≤ ((∫ d,R d ∂O)-optimalCompetitiveRatio*P.expectedMaximum)+optimalCompetitiveRatio*P.expectedMaximum :=
          add_le_add hRate le_rfl
        _ = _ := sub_add_cancel _ _
    · have hS' : S0≤P.totalFirstMoment := le_of_lt (lt_of_not_ge hS)
      have hFloor' := hFloor n P hcap hMean hS'
      have hL0 := P.tailCount_nonnegative 0
      have hLLog : 0≤2*Real.log (m : ℝ) := hL0.trans hL
      have hDen : 0<(1+P.positiveCount)^4 := by positivity
      have hPow : (1+P.positiveCount)^4≤(1+2*Real.log (m : ℝ))^4 :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have hGap : κ/(1+2*Real.log (m : ℝ))^4≤G := by
        have hPoint (d : D) : κ/(1+2*Real.log (m : ℝ))^4≤F d :=
          ((div_le_div_of_nonneg_left hκ.le hDen hPow).trans hFloor').trans
            (intervalNormalizedScalarGapMinimum_le P hP.1 le_rfl le_rfl (hl d))
        have h := integral_mono (integrable_const _) hF hPoint
        simpa only [integral_const,probReal_univ,one_smul] using h
      have hCoarse := numericalTarget_expected_coarse P hP hcap (targetQueryArrayLaw νT) mu hmu hMean hL
        _ (measurable_targetTable mu targetEstimate hT) hConf'
      rw [← hEq] at hCoarse
      have hCov := calibration_covariance_coarse O hZ hg hZR hgR hMom.2
      have hSlog := (P.totalFirstMoment_le_positiveCount hcap).trans hL
      have hReg' : (∫ d,r d ∂O)≤KR*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ) := by
        refine hReg.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hKR) hmR.le)
        have hS0' : 0≤P.totalFirstMoment := Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae (P.nonnegative i))
        have h : P.totalFirstMoment*(1+P.totalFirstMoment)≤(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)) :=
          mul_le_mul hSlog (add_le_add le_rfl hSlog) (by linarith) hLLog
        exact add_le_add le_rfl h
      have hHigh := hHighThreshold m hm0
      have hGain := mul_le_mul_of_nonneg_left hGap hmu.le
      have hCost := (le_abs_self (∫ d,Z d*g d ∂O)).trans hCov
      have hD := div_nonneg hK.le hmR.le
      change (∫ d,e d ∂O)≤KC/Real.sqrt (m : ℝ) at hCoarse
      have hFactor : (1/2+KC/4)/Real.sqrt (m : ℝ) =
          1/(2*Real.sqrt (m : ℝ))+(1/4)*(KC/Real.sqrt (m : ℝ)) := by ring
      rw [hFactor] at hHigh
      have hRe : 5*KR*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ)=
          5*(KR*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ)) := by ring
      rw [hRe] at hHigh
      have hGb : mu*κ/(1+2*Real.log (m : ℝ))^4 =
          mu*(κ/(1+2*Real.log (m : ℝ))^4) := by ring
      rw [hGb] at hHigh
      linarith only [hMaster,hHigh,hGain,hCost,hCoarse,hReg',hD]
  · have hcm : optimalCompetitiveRatio*P.expectedMaximum≤1 :=
      (mul_le_mul_of_nonneg_right (optimalCompetitiveRatio_le_threeQuarters.trans (by norm_num : (3/4 : ℝ)≤1))
        P.expectedMaximum_nonnegative).trans (by simpa only [one_mul] using hM1)
    have hMK : (m : ℝ)≤K := by
      have h := (Nat.cast_le.mpr (le_of_lt (lt_of_not_ge hm0)) : (m : ℝ)≤(m0 : ℝ))
      exact h.trans ((le_max_right B _).trans (by dsimp [K]; linarith))
    have hK1 : (1 : ℝ)≤K/(m : ℝ) := (le_div_iff₀ hmR).mpr (by simpa only [one_mul] using hMK)
    exact (by linarith only [hcm,hK1] : optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤0).trans
      ((L.randomizedPolicy P).expectedReward_nonnegative P)

end ProphetSecretary.Statistics.Calibration
