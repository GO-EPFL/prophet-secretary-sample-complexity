import ProphetSecretary.Statistics.ReportedRewardGuarantee
import ProphetSecretary.Statistics.ReportedReachGuarantee
import ProphetSecretary.Statistics.CalibratedPlannerGuarantee

/-!
# The bounded learner with reported validation times

This combines the actual two-block reported selector with the same scalar
planner confidence and coupling as the continuous-clock construction.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

theorem exists_reported_calibrated_bounded_of_planner_confidence (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
    ∃ b : ℚ, (b : ℝ)∈Ioo (4/5 : ℝ) 1 ∧ ∃ K : ℝ, 0<K ∧
      ∀ (n m : ℕ) [NeZero n] [NeZero m] (P : Instance n)
        (_hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (_hMean : mu≤P.expectedMaximum)
        (_hM : P.expectedMaximum≤1/80) (_hL : P.positiveCount≤2*Real.log (m : ℝ)),
        let zlo := (1-(b : ℝ))/(b : ℝ)
        let J := familyGridSize m zlo (1/4)
        ∀ (TSeed PSeed : Type) [MeasurableSpace TSeed] [MeasurableSpace PSeed]
          (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
          (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
          (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
          (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
            policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
          (report : ℝ → ℝ) (hReport : Measurable report) (δ : ℝ) (_hδ : 0≤δ)
          (_hδm : δ≤1/(m : ℝ)) (_hδSmall : δ≤1/20)
          (_hRep : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) t ∧ t-report t≤δ)
          (_hMono : MonotoneOn report (Icc (0 : ℝ) 1)),
          let A := reportedOfflinePrepare (J := J) report mu zlo (1/4) targetEstimate policyEstimate
          let hA := measurable_reportedOfflinePrepare (J := J) report hReport mu zlo (1/4)
            targetEstimate policyEstimate hT hC
          (∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
            νT.real {r | 1/(m : ℝ) < |targetEstimate (reservoirCoordinates.symm a) (targetGrid j) r-
              optimalScalarValue (trainingInstance a) 1 (targetGrid j)|}≤1/((m : ℝ)^2*(4*(m : ℝ)+1))) →
          (∀ (q : Reservoir n m), (∀ i l, q i l∈Icc (0 : ℝ) 1) →
            (totalEmpiricalInstance q).positiveCount≤targetCountCutoff m →
            ∀ (B : Finset (Fin n)) (u z : ℝ), u∈Icc (0 : ℝ) 1 → z∈Icc (0 : ℝ) 4 →
            νP.real {s | policyAccuracy m zlo < |policyEstimate q B u z s-
              (totalEmpiricalInstance q).continuationValue B u 1 z|}≤policyFailureBound n m J) →
          let L := selectorLearner νT νP zlo (1/4) policyEstimate A hA hC
          optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P ∧
            ∀ i : Fin n, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability P i := by
  obtain ⟨b,hb,hReward⟩ := exists_reported_calibrated_reward_of_expected_regret mu hmu hmuHi
  let zlo := (1-(b : ℝ))/(b : ℝ)
  have hz := calibrationEndpoint_coefficient_bounds hb
  let KR := 2*empiricalCapRegretConstant zlo+7
  have hKR : 0≤KR := by dsimp [KR]; linarith [empiricalCapRegretConstant_positive hz.1 hz.2.le]
  obtain ⟨K,hK,hMain⟩ := hReward KR hKR
  refine ⟨b,hb,max K 208,hK.trans_le (le_max_left _ _),?_⟩
  intro n m hn hm P hcap hMean hM hL
  dsimp only
  intro TSeed PSeed hTS hPS νT νP hνT hνP targetEstimate policyEstimate hT hC
    report hReport δ hδ hδm hδSmall hRep hMono hTConf hPConf
  let J := familyGridSize m zlo (1/4)
  let A := reportedOfflinePrepare (J := J) report mu zlo (1/4) targetEstimate policyEstimate
  let hA := measurable_reportedOfflinePrepare (J := J) report hReport mu zlo (1/4)
    targetEstimate policyEstimate hT hC
  have hBounds := reportedOfflinePrepare_bounds (J := J) report mu zlo (1/4) targetEstimate policyEstimate
  have hJ : 0<J := familyGridSize_pos (NeZero.pos m) hz.2
  have hSize : (m : ℝ)*(1/4-zlo)≤(J : ℝ) := Nat.le_ceil _
  have hP := P.integrable_maximum_of_bounded hcap
  have hmR : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
  have hZ (l : ℕ) : familyCoefficient zlo (1/4) J l∈Icc zlo (1/4 : ℝ) :=
    familyCoefficient_range hz.2.le J l
  have hLP : P.positiveCount≤targetCountCutoff m := by
    unfold targetCountCutoff
    have hlog := log_le_clog_two m (NeZero.pos m)
    have hClog : (0 : ℝ)≤Nat.clog 2 m := Nat.cast_nonneg _
    linarith only [hL,hlog,hClog]
  have hGood := offlineEmpiricalBlock_unit_ae (m := m) (J := J) P νT νP hcap
  have hReg := selectorRegret_le_of_coupling (J := J) P νT νP hcap hM hL hb hJ hSize
    policyEstimate A hA (fun _ => rfl) hBounds hC (by
      filter_upwards [hGood] with d hD hCut j
      let q := offlineEmpiricalBlock d
      have hQ : (totalEmpiricalInstance q).positiveCount≤targetCountCutoff m :=
        (empiricalPositiveCount_eq d.1.1).symm.trans_le hCut
      exact frozenFamilyPolicy_scalarObjective_loss_le P νP hz.1 hz.2.le hZ policyEstimate hC q
        (fun i l => (hD i l).1) hLP (hPConf q hD) j hcap hQ)
  have hR := hMain n m J P hcap hMean hM hL TSeed PSeed νT νP targetEstimate policyEstimate hT hC
    report hReport δ hδ hδm hRep hMono hTConf hReg
  constructor
  · exact (sub_le_sub_left (div_le_div_of_nonneg_right (le_max_left K 208) hmR.le) _).trans hR
  · intro i
    have hReach : ∀ᵐ d ∂offlineDataLaw (m := m) (J := J) P νT νP,
        let π := selectorConditionalPolicy νP zlo (1/4) policyEstimate A hC d
        π.expectedDuration P-6/(m : ℝ)≤π.rule.reachProbability P (onlineCalibrationSeedLaw νP) i := by
      filter_upwards [hGood] with d hd
      let p := A d
      let α := p.2.2
      let q := offlineEmpiricalBlock d
      let F (j : Fin (J+1)) := numericalCalibrationEndpoint νP zlo (1/4) policyEstimate hC q j
      let L := F (lowerPolicyIndex J p.2.1)
      let U := F (upperPolicyIndex J p.2.1)
      have hα : α∈Icc (0 : ℝ) 1 := ⟨(hBounds d).2.2.1.le,(hBounds d).2.2.2⟩
      have hEndpoint (j : Fin (J+1)) : (F j).expectedDuration P-6/(m : ℝ)≤
          (F j).rule.reachProbability P (F j).seedLaw i := by
        have h := frozenFamilyPolicy_duration_le_reach P νP hz.1 hz.2.le hZ policyEstimate hC q
          (fun j l => (hd j l).1) hLP (hPConf q hd) j i
        exact (sub_le_iff_le_add).mpr h
      have hRmix := preparedPolicy_reach_eq_mean (J := J) P νP zlo (1/4) policyEstimate hC p hα i
      have hTmix := preparedPolicy_duration_eq_mean (J := J) P νP zlo (1/4) policyEstimate hC p hα
      change (preparedPolicy zlo (1/4) policyEstimate p).reachProbability P (onlineCalibrationSeedLaw νP) i =
        (1-α)*L.rule.reachProbability P L.seedLaw i+α*U.rule.reachProbability P U.seedLaw i at hRmix
      change (preparedPolicy zlo (1/4) policyEstimate p).meanDuration P (onlineCalibrationSeedLaw νP) =
        (1-α)*L.expectedDuration P+α*U.expectedDuration P at hTmix
      change (preparedPolicy zlo (1/4) policyEstimate p).meanDuration P (onlineCalibrationSeedLaw νP)-6/(m : ℝ)≤
        (preparedPolicy zlo (1/4) policyEstimate p).reachProbability P (onlineCalibrationSeedLaw νP) i
      rw [hRmix,hTmix]
      have h1 := mul_le_mul_of_nonneg_left (hEndpoint (lowerPolicyIndex J p.2.1)) (sub_nonneg.mpr hα.2)
      have h2 := mul_le_mul_of_nonneg_left (hEndpoint (upperPolicyIndex J p.2.1)) hα.1
      change (1-α)*(L.expectedDuration P-6/(m : ℝ))≤(1-α)*L.rule.reachProbability P L.seedLaw i at h1
      change α*(U.expectedDuration P-6/(m : ℝ))≤α*U.rule.reachProbability P U.seedLaw i at h2
      nlinarith only [h1,h2]
    have h := reportedSelector_reach_of_conditional_comparison (J := J) P νT νP hmu hz.1.le hz.2.le hJ
      hP hM targetEstimate policyEstimate hT hC report hReport hδ hδSmall hRep hMono hTConf i hReach
    exact (sub_le_sub_left (div_le_div_of_nonneg_right (le_max_right K 208) hmR.le) _).trans h

end ProphetSecretary.Statistics.Calibration
