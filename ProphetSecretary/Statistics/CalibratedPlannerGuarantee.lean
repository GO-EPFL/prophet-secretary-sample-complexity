import ProphetSecretary.Statistics.CalibratedBoundedGuarantee
import ProphetSecretary.Statistics.CalibratedPolicyCoupling

/-!
# Connecting the bounded learner to scalar planner confidence

The statistical guarantee requires only the two specified single-call
confidence bounds. The actual empirical block satisfies the planner's
support restriction almost surely. All endpoint comparisons are consequences
of the same numerical action coupling.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

/-- The bounded construction under the two scalar planner confidence contracts. -/
theorem exists_calibrated_bounded_of_planner_confidence (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
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
            policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)),
          (∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
            νT.real {r | 1/(m : ℝ) < |targetEstimate (reservoirCoordinates.symm a) (targetGrid j) r-
              optimalScalarValue (trainingInstance a) 1 (targetGrid j)|}≤1/((m : ℝ)^2*(4*(m : ℝ)+1))) →
          (∀ (q : Reservoir n m), (∀ i l, q i l∈Icc (0 : ℝ) 1) →
            (totalEmpiricalInstance q).positiveCount≤targetCountCutoff m →
            ∀ (A : Finset (Fin n)) (u z : ℝ), u∈Icc (0 : ℝ) 1 → z∈Icc (0 : ℝ) 4 →
            νP.real {s | policyAccuracy m zlo < |policyEstimate q A u z s-
              (totalEmpiricalInstance q).continuationValue A u 1 z|}≤policyFailureBound n m J) →
          let L := learnerCore (J := J) mu zlo (1/4) νT νP targetEstimate policyEstimate hT hC
          optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P ∧
            ∀ i : Fin n, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability P i := by
  obtain ⟨b,hb,K,hK,hMain⟩ := exists_calibrated_bounded_of_endpoint_estimates mu hmu hmuHi
  refine ⟨b,hb,K,hK,?_⟩
  intro n m hn hm P hcap hMean hM hL
  dsimp only
  intro TSeed PSeed hTS hPS νT νP hνT hνP targetEstimate policyEstimate hT hC hTConf hPConf
  let zlo := (1-(b : ℝ))/(b : ℝ)
  let J := familyGridSize m zlo (1/4)
  have hz := calibrationEndpoint_coefficient_bounds hb
  have hZ (l : ℕ) : familyCoefficient zlo (1/4) J l∈Icc zlo (1/4 : ℝ) :=
    familyCoefficient_range hz.2.le J l
  have hLP : P.positiveCount≤targetCountCutoff m := by
    unfold targetCountCutoff
    have hlog := log_le_clog_two m (NeZero.pos m)
    have hClog : (0 : ℝ)≤Nat.clog 2 m := Nat.cast_nonneg _
    linarith only [hL,hlog,hClog]
  have hGood := offlineEmpiricalBlock_unit_ae (m := m) (J := J) P νT νP hcap
  apply hMain n m P hcap hMean hM hL TSeed PSeed νT νP targetEstimate policyEstimate hT hC hTConf
  · filter_upwards [hGood] with d hD hCut j
    let q := offlineEmpiricalBlock d
    have hQ : (totalEmpiricalInstance q).positiveCount≤targetCountCutoff m :=
      (empiricalPositiveCount_eq d.1.1).symm.trans_le hCut
    exact frozenFamilyPolicy_scalarObjective_loss_le P νP hz.1 hz.2.le hZ policyEstimate hC q
      (fun i l => (hD i l).1) hLP (hPConf q hD) j hcap hQ
  · intro i
    filter_upwards [hGood] with d hD j
    let q := offlineEmpiricalBlock d
    have h := frozenFamilyPolicy_duration_le_reach P νP hz.1 hz.2.le hZ policyEstimate hC q
      (fun i l => (hD i l).1) hLP (hPConf q hD) j i
    exact (sub_le_iff_le_add).mpr h

end ProphetSecretary.Statistics.Calibration
