import ProphetSecretary.Statistics.CalibrationClockScale
import ProphetSecretary.Statistics.ReportedBoundedGuarantee
import ProphetSecretary.Statistics.ReportedClockGrid
import ProphetSecretary.Statistics.RoundedClockConfidence

/-!
# Calibrating with fair-bit estimates and reported timestamps

This is the ideal rounded-clock comparison protocol. Its scalar queries
already use their actual finite-bit laws. Exact uniform permutations and
the continuous mixture coin are still used here for the statistical
comparison to the finite-key execution.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ}

/-- Public parameters used to choose the finite seed spaces. -/
structure FairCalibrationParameters (n m : ℕ) where
  zlo : ℝ
  clockInverse : ℕ
  nonempty : 0<n
  two_le : 2≤m
  coefficient_mem : zlo∈Ioo (0 : ℝ) (1/4)
  inverse_bound : 1/zlo≤(clockInverse : ℝ)

namespace FairCalibrationParameters

noncomputable def grid (a : FairCalibrationParameters n m) : ℕ :=
  familyGridSize m a.zlo (1/4)

def clockBits (a : FairCalibrationParameters n m) : ℕ :=
  calibrationClockBits n m a.clockInverse

noncomputable def clock (a : FairCalibrationParameters n m) : ℝ → ℝ :=
  uniformGridRound (2^a.clockBits) (by positivity)

lemma measurable_clock (a : FairCalibrationParameters n m) : Measurable a.clock :=
  measurable_uniformGridRound _ _

noncomputable def report (a : FairCalibrationParameters n m) : ℝ → ℝ :=
  terminalClockReport a.clock

lemma measurable_report (a : FairCalibrationParameters n m) : Measurable a.report :=
  measurable_terminalClockReport a.measurable_clock

noncomputable def clockError (a : FairCalibrationParameters n m) : ℝ :=
  1/((2^a.clockBits : ℕ) : ℝ)

lemma clockError_bounds (a : FairCalibrationParameters n m) :
    0≤a.clockError ∧ a.clockError≤1/(m : ℝ) ∧ a.clockError≤1/20 ∧
      4*a.clockError≤policyAccuracy m a.zlo/2 :=
  calibrationClockGrid_error a.two_le a.coefficient_mem a.inverse_bound

lemma clock_approx (a : FairCalibrationParameters n m) (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
    a.clock t∈Icc (0 : ℝ) t ∧ t-a.clock t≤a.clockError := by
  have h := uniformGridRound_bounds (2^a.clockBits) (by positivity) ht
  exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩

lemma report_approx (a : FairCalibrationParameters n m) (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
    a.report t∈Icc (0 : ℝ) t ∧ t-a.report t≤a.clockError :=
  uniformGridReport_approx _ _ ht

lemma report_mono (a : FairCalibrationParameters n m) : MonotoneOn a.report (Icc (0 : ℝ) 1) :=
  uniformGridReport_monotoneOn _ _

noncomputable def targetTolerance (_ : FairCalibrationParameters n m) : ℝ := 1/(m : ℝ)
noncomputable def targetFailure (_ : FairCalibrationParameters n m) : ℝ :=
  1/((m : ℝ)^2*(4*(m : ℝ)+1))
noncomputable def thresholdTolerance (a : FairCalibrationParameters n m) : ℝ := policyAccuracy m a.zlo/2
noncomputable def thresholdFailure (a : FairCalibrationParameters n m) : ℝ := policyFailureBound n m a.grid

lemma targetTolerance_mem (a : FairCalibrationParameters n m) : a.targetTolerance∈Ioo (0 : ℝ) 1 :=
  targetAccuracy_mem a.two_le

lemma targetFailure_range (a : FairCalibrationParameters n m) : a.targetFailure∈Ioo (0 : ℝ) 1 :=
  targetFailure_mem a.two_le

lemma thresholdTolerance_mem (a : FairCalibrationParameters n m) :
    a.thresholdTolerance∈Ioo (0 : ℝ) 1 := by
  have h := policyAccuracy_mem a.two_le a.coefficient_mem
  unfold thresholdTolerance
  exact ⟨by linarith [h.1],by linarith [h.2]⟩

lemma thresholdFailure_range (a : FairCalibrationParameters n m) : a.thresholdFailure∈Ioo (0 : ℝ) 1 :=
  policyFailure_mem a.nonempty a.two_le

noncomputable def targetBits (a : FairCalibrationParameters n m) : ℕ :=
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  calibrationFairPrecision n m a.targetTolerance a.targetTolerance_mem

noncomputable def thresholdBits (a : FairCalibrationParameters n m) : ℕ :=
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  calibrationFairPrecision n m a.thresholdTolerance a.thresholdTolerance_mem

abbrev TargetSeed (a : FairCalibrationParameters n m) :=
  CalibrationFairSeed n m a.targetBits a.targetTolerance a.targetFailure a.targetFailure_range

abbrev ThresholdSeed (a : FairCalibrationParameters n m) :=
  CalibrationFairSeed n m a.thresholdBits a.thresholdTolerance a.thresholdFailure a.thresholdFailure_range

noncomputable def targetLaw (a : FairCalibrationParameters n m) : Measure a.TargetSeed :=
  calibrationFairSeedLaw n m a.targetBits a.targetTolerance a.targetFailure a.targetFailure_range

noncomputable def thresholdLaw (a : FairCalibrationParameters n m) : Measure a.ThresholdSeed :=
  calibrationFairSeedLaw n m a.thresholdBits a.thresholdTolerance a.thresholdFailure a.thresholdFailure_range

instance (a : FairCalibrationParameters n m) : IsProbabilityMeasure a.targetLaw := by
  unfold targetLaw
  infer_instance

instance (a : FairCalibrationParameters n m) : IsProbabilityMeasure a.thresholdLaw := by
  unfold thresholdLaw
  infer_instance

noncomputable def target (a : FairCalibrationParameters n m) : TargetEstimator n m a.TargetSeed :=
  calibrationFairTarget a.targetBits a.targetTolerance a.targetFailure a.targetFailure_range

noncomputable def threshold (a : FairCalibrationParameters n m) : ContinuationEstimator n m a.ThresholdSeed :=
  calibrationFairCall a.thresholdBits a.thresholdTolerance a.thresholdFailure a.thresholdFailure_range

noncomputable def roundedThreshold (a : FairCalibrationParameters n m) :
    ContinuationEstimator n m a.ThresholdSeed :=
  clockRoundedEstimate a.clock a.threshold

lemma measurable_target (a : FairCalibrationParameters n m) :
    Measurable (fun p : Reservoir n m × (ℝ × a.TargetSeed) => a.target p.1 p.2.1 p.2.2) :=
  measurable_calibrationFairTarget _ _ _ _

lemma measurable_threshold (a : FairCalibrationParameters n m) :
    Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × a.ThresholdSeed))) =>
      a.threshold p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  measurable_calibrationFairCall _ _ _ _

lemma measurable_roundedThreshold (a : FairCalibrationParameters n m) :
    Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × a.ThresholdSeed))) =>
      a.roundedThreshold p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  measurable_clockRoundedEstimate a.measurable_clock a.threshold a.measurable_threshold

noncomputable def reportedLearner (a : FairCalibrationParameters n m) (mu : ℝ) : Learner n (2*m) :=
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  let A := reportedOfflinePrepare (J := a.grid) a.report mu a.zlo (1/4) a.target a.roundedThreshold
  let hA := measurable_reportedOfflinePrepare (J := a.grid) a.report a.measurable_report
    mu a.zlo (1/4) a.target a.roundedThreshold a.measurable_target a.measurable_roundedThreshold
  selectorLearner a.targetLaw a.thresholdLaw a.zlo (1/4) a.roundedThreshold A hA a.measurable_roundedThreshold

lemma target_confidence (a : FairCalibrationParameters n m) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (mu : ℝ) :
    letI : NeZero m := ⟨by have := a.two_le; omega⟩
    ∀ᵐ y ∂P.trainingCoordinateLaw m, targetEligible mu y → ∀ j : TargetGrid m,
      a.targetLaw.real {s | 1/(m : ℝ) < |a.target (reservoirCoordinates.symm y) (targetGrid j) s -
        optimalScalarValue (trainingInstance y) 1 (targetGrid j)|}≤a.targetFailure := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  exact calibrationFairTarget_correct_ae P hcap mu a.targetTolerance_mem a.targetFailure_range

lemma roundedThreshold_confidence (a : FairCalibrationParameters n m) (q : Reservoir n m)
    (hq : ∀ i l, q i l∈Icc (0 : ℝ) 1) :
    letI : NeZero m := ⟨by have := a.two_le; omega⟩
    (totalEmpiricalInstance q).positiveCount≤targetCountCutoff m →
    ∀ (A : Finset (Fin n)) (u z : ℝ), u∈Icc (0 : ℝ) 1 → z∈Icc (0 : ℝ) 4 →
    a.thresholdLaw.real {s | policyAccuracy m a.zlo <
      |a.roundedThreshold q A u z s-(totalEmpiricalInstance q).continuationValue A u 1 z|}≤a.thresholdFailure := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  intro hc A u z hu hz
  apply clockRoundedEstimate_confidence a.thresholdLaw a.clock a.clockError_bounds.1
    a.coefficient_mem.1 a.clock_approx a.clockError_bounds.2.2.2 a.threshold q A hu hz
  intro v hv
  exact calibrationFairCall_correct _ _ a.thresholdTolerance_mem a.thresholdFailure_range q hq hc A v z hv hz

end FairCalibrationParameters

/-- The ideal rounded-clock construction, with the actual fair scalar
queries, satisfies both bounded guarantees uniformly in dimension. -/
theorem exists_fair_reported_learner (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
      (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (K : ℝ), 0<K ∧
      ∀ (n m : ℕ) (hn : 0<n) (hm : 2≤m) (P : Instance n),
        (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum → P.expectedMaximum≤1/80 →
        P.positiveCount≤2*Real.log (m : ℝ) →
        let a : FairCalibrationParameters n m :=
          ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
        let L := a.reportedLearner mu
        optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P ∧
        ∀ i, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability P i := by
  obtain ⟨b,hb,K,hK,hMain⟩ := exists_reported_calibrated_bounded_of_planner_confidence mu hmu hmuHi
  obtain ⟨zInv,hInv⟩ := exists_nat_ge (1/((1-(b : ℝ))/(b : ℝ)))
  refine ⟨b,hb,zInv,hInv,K,hK,?_⟩
  intro n m hn hm P hcap hMean hM hL
  dsimp only
  let a : FairCalibrationParameters n m :=
    ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero m := ⟨by omega⟩
  exact hMain n m P hcap hMean hM hL a.TargetSeed a.ThresholdSeed
    a.targetLaw a.thresholdLaw a.target a.roundedThreshold a.measurable_target a.measurable_roundedThreshold
    a.report a.measurable_report a.clockError a.clockError_bounds.1 a.clockError_bounds.2.1
    a.clockError_bounds.2.2.1 a.report_approx a.report_mono (a.target_confidence P hcap mu)
    a.roundedThreshold_confidence

end ProphetSecretary.Statistics.Calibration
