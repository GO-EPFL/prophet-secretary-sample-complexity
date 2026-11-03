import ProphetSecretary.Statistics.CalibratedSelectedRegretBound
import ProphetSecretary.Statistics.CalibratedRewardGuarantee
import ProphetSecretary.Statistics.CalibratedReachGuarantee

/-!
# The bounded calibrated learner from its numerical estimates

This separates the statistical argument from the accuracy and coupling
proofs for the numerical continuation routine. The only remaining inputs
are its target-call confidence and its endpoint payoff and reach estimates.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

theorem exists_calibrated_bounded_of_endpoint_estimates (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
    ∃ b : ℚ, (b : ℝ)∈Ioo (4/5 : ℝ) 1 ∧ ∃ K : ℝ, 0<K ∧
      ∀ (n m : ℕ) [NeZero m] (P : Instance n)
        (_hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (_hMean : mu≤P.expectedMaximum)
        (_hM : P.expectedMaximum≤1/80) (_hL : P.positiveCount≤2*Real.log (m : ℝ)),
        let zlo := (1-(b : ℝ))/(b : ℝ)
        let J := familyGridSize m zlo (1/4)
        ∀ (TSeed PSeed : Type) [MeasurableSpace TSeed] [MeasurableSpace PSeed]
          (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
          (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
          (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
          (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
            policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)),
          (∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
            νT.real {r | 1/(m : ℝ) < |targetEstimate (reservoirCoordinates.symm a) (targetGrid j) r-
              optimalScalarValue (trainingInstance a) 1 (targetGrid j)|}≤1/((m : ℝ)^2*(4*(m : ℝ)+1))) →
          (∀ᵐ d ∂offlineDataLaw (m := m) (J := J) P νT νP,
            empiricalPositiveCount d.1.1≤targetCountCutoff m → ∀ j : Fin (J+1),
              let z := familyCoefficient zlo (1/4) J j.val
              let q := offlineEmpiricalBlock d
              (exactCalibrationEndpoint q z).scalarObjective P 1 z-
                (numericalCalibrationEndpoint νP zlo (1/4) policyEstimate hC q j).scalarObjective P 1 z≤4/(m : ℝ)) →
          (∀ i : Fin n, ∀ᵐ d ∂offlineDataLaw (m := m) (J := J) P νT νP, ∀ j : Fin (J+1),
            let π := numericalCalibrationEndpoint νP zlo (1/4) policyEstimate hC (offlineEmpiricalBlock d) j
            π.expectedDuration P-6/(m : ℝ)≤π.rule.reachProbability P π.seedLaw i) →
          let L := learnerCore (J := J) mu zlo (1/4) νT νP targetEstimate policyEstimate hT hC
          optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P ∧
            ∀ i : Fin n, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability P i := by
  obtain ⟨b,hb,hReward⟩ := exists_calibrated_reward_of_expected_regret mu hmu hmuHi
  let zlo := (1-(b : ℝ))/(b : ℝ)
  have hz := calibrationEndpoint_coefficient_bounds hb
  let KR := 2*empiricalCapRegretConstant zlo+7
  have hKR : 0≤KR := by dsimp [KR]; linarith [empiricalCapRegretConstant_positive hz.1 hz.2.le]
  obtain ⟨K,hK,hMain⟩ := hReward KR hKR
  refine ⟨b,hb,max K 31,hK.trans_le (le_max_left _ _),?_⟩
  intro n m hm P hcap hMean hM hL
  dsimp only
  let J := familyGridSize m zlo (1/4)
  intro TSeed PSeed hTS hPS νT νP hνT hνP targetEstimate policyEstimate hT hC hConf hPayoff hReach
  have hJ : 0<J := familyGridSize_pos (NeZero.pos m) hz.2
  have hSize : (m : ℝ)*(1/4-zlo)≤(J : ℝ) := Nat.le_ceil _
  have hP := P.integrable_maximum_of_bounded hcap
  have hmR : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
  have hReg := offline_selectedRegret_le_of_coupling (J := J) P νT νP hcap hM hL hb hJ hSize
    mu targetEstimate policyEstimate hT hC hPayoff
  have hR := hMain n m J P hcap hMean hM hL TSeed PSeed νT νP targetEstimate policyEstimate hT hC hConf hReg
  constructor
  · apply le_trans _ hR
    exact sub_le_sub_left (div_le_div_of_nonneg_right (le_max_left K 31) hmR.le) _
  · intro i
    have hR' : ∀ᵐ d ∂offlineDataLaw (m := m) (J := J) P νT νP,
        let π := conditionalCalibrationPolicy νP mu zlo (1/4) targetEstimate policyEstimate hC d
        π.expectedDuration P-6/(m : ℝ)≤π.rule.reachProbability P (onlineCalibrationSeedLaw νP) i := by
      filter_upwards [hReach i] with d hd
      let p := offlinePrepare (J := J) mu zlo (1/4) targetEstimate policyEstimate d
      let a := p.2.2
      let F (j : Fin (J+1)) := numericalCalibrationEndpoint νP zlo (1/4) policyEstimate hC (offlineEmpiricalBlock d) j
      let L := F (lowerPolicyIndex J p.2.1)
      let U := F (upperPolicyIndex J p.2.1)
      have hα := (offlinePrepare_bounds mu zlo (1/4) targetEstimate policyEstimate d).2.2
      have hα' : a∈Icc (0 : ℝ) 1 := ⟨hα.1.le,hα.2⟩
      have hRmix := preparedPolicy_reach_eq_mean (J := J) P νP zlo (1/4) policyEstimate hC p hα' i
      have hTmix := preparedPolicy_duration_eq_mean (J := J) P νP zlo (1/4) policyEstimate hC p hα'
      change (preparedPolicy zlo (1/4) policyEstimate p).reachProbability P (onlineCalibrationSeedLaw νP) i =
        (1-a)*L.rule.reachProbability P L.seedLaw i+a*U.rule.reachProbability P U.seedLaw i at hRmix
      change (preparedPolicy zlo (1/4) policyEstimate p).meanDuration P (onlineCalibrationSeedLaw νP) =
        (1-a)*L.expectedDuration P+a*U.expectedDuration P at hTmix
      change (preparedPolicy zlo (1/4) policyEstimate p).meanDuration P (onlineCalibrationSeedLaw νP)-6/(m : ℝ)≤
        (preparedPolicy zlo (1/4) policyEstimate p).reachProbability P (onlineCalibrationSeedLaw νP) i
      rw [hRmix,hTmix]
      have h1 := mul_le_mul_of_nonneg_left (hd (lowerPolicyIndex J p.2.1)) (sub_nonneg.mpr hα'.2)
      have h2 := mul_le_mul_of_nonneg_left (hd (upperPolicyIndex J p.2.1)) hα'.1
      change (1-a)*(L.expectedDuration P-6/(m : ℝ))≤(1-a)*L.rule.reachProbability P L.seedLaw i at h1
      change a*(U.expectedDuration P-6/(m : ℝ))≤a*U.rule.reachProbability P U.seedLaw i at h2
      nlinarith only [h1,h2]
    have hBound := learnerCore_reach_of_conditional_comparison (J := J) P νT νP hmu hz.1.le hz.2.le hJ
      hP hM targetEstimate policyEstimate hT hC hConf i hR'
    exact (sub_le_sub_left (div_le_div_of_nonneg_right (le_max_right K 31) hmR.le) _).trans hBound

end ProphetSecretary.Statistics.Calibration
