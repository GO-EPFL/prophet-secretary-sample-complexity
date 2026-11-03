import ProphetSecretary.Statistics.CalibratedOuter.NativeRankExecution
import ProphetSecretary.Statistics.FairCalibratedNativeExecution
import ProphetSecretary.Statistics.FiniteBitLearner

/-!
# The native finite-bit learner

The native schedules compute the same public precisions as the measured
finite rank learner. Reindexing the fair query banks preserves their law
and leaves all clock, key, coin and outer mark bits unchanged.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ}

namespace FairCalibrationParameters

abbrev NativeBits (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) :=
  RankCalibrationBits n m a.grid a.clockBits a.coinBits (a.nativeTargetSchedule.Seed n)
    ((a.nativeThresholdSchedule zlo hz).Seed n)

lemma nativeFiniteDecision_eq_finiteLearner (a : FairCalibrationParameters n m)
    (mu zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) (data : Fin n → Fin (2*m) → ℚ)
    (bits : a.NativeBits zlo hz) (k i : Fin n) (x : ℚ) (H : Fin n → Option (Fin n × ℚ))
    (hRank : onlineQueryRank H i=k) :
    let P := a.nativeThresholdSchedule zlo hz
    let q := countedFiniteCalibrationPrepare a.nativeTargetSchedule P
      a.clockBits a.coinBits mu zlo (1/4) (nativeCalibrationCutoff m)
      (fun i j => data i (finiteTrainingIndex m j)) (fun j i => data i (finiteValidationIndex m j)) bits
    (countedFiniteCalibrationDecision P zlo (1/4) q i x H).1 =
      (a.finiteLearner (mu : ℝ)).policy.decide
        ((fun i j => (data i j : ℝ)),a.nativeCalibrationBitsToMeasured zlo hz bits)
        k i (x : ℝ) (calibrationRankHistoryCast H) := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  have h := a.nativeFiniteRankExecution_eq mu zlo hz a.clockBits a.coinBits data bits k i x H hRank
  dsimp only at h ⊢
  refine h.trans ?_
  let s := a.nativeCalibrationBitsToMeasured zlo hz bits
  let y : Reservoir n (2*m) := fun i j => (data i j : ℝ)
  let ν := rankCalibrationBitsLaw (n := n) (m := m) (J := a.grid)
    a.clockBits a.coinBits a.targetLaw a.thresholdLaw
  let π := finiteRankSamplePolicy (J := a.grid) a.clockBits a.coinBits (mu : ℝ) a.zlo (1/4) a.target a.threshold
  have hπ := finiteRankSamplePolicy_isMeasurable (J := a.grid) a.clockBits a.coinBits
    a.targetLaw a.thresholdLaw (mu : ℝ) a.zlo (1/4) a.target a.threshold a.measurable_target a.measurable_threshold
  exact (RankLearner.ofComputedSamplePolicy_decide _ ν π hπ y s k i (x : ℝ) (calibrationRankHistoryCast H)).symm

/-- Exact agreement between the native rational outer execution and the
actual finite rank learner on a legal observed prefix. -/
theorem nativeFiniteOuterDecision_eq (a : FairCalibrationParameters n m)
    (mu zlo : ℚ) (hz : (zlo : ℝ)=a.zlo)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ)
    (marks : OuterMarkArray n m (Fin (outerMarkBits n m) → Bool)) (bits : a.NativeBits zlo hz)
    (k i : Fin n) (x : ℚ) (H : Fin n → Option (Fin n × ℚ)) (hRank : onlineQueryRank H i=k) :
    let Y := outerRawBlocks y
    let T := a.nativeTargetSchedule
    let P := a.nativeThresholdSchedule zlo hz
    let q := countedFiniteOuterPrepare (by have := a.two_le; omega : 1≤m) T P
      a.clockBits a.coinBits (outerMarkBits n m) mu zlo (1/4) (nativeCalibrationCutoff m)
      (fun r i => Y.1 i r) (fun r i => Y.2.1 i r) (fun r i => Y.2.2 i r) marks bits
    (countedFiniteOuterDecision P zlo (1/4) q k i x H).1 =
      (outerFairRankLearner (by have := a.two_le; omega : 1≤m) (a.finiteLearner (mu : ℝ))
        (outerMarkBits n m)).policy.decide
        ((fun i j => (y i j : ℝ)),marks,a.nativeCalibrationBitsToMeasured zlo hz bits)
        k i (x : ℝ) (calibrationRankHistoryCast H) := by
  exact countedFiniteOuterDecision_eq_of_inner (by have := a.two_le; omega)
    a.nativeTargetSchedule (a.nativeThresholdSchedule zlo hz) a.clockBits a.coinBits (outerMarkBits n m)
    mu zlo (1/4) (nativeCalibrationCutoff m) (a.finiteLearner (mu : ℝ)) y marks bits
    (a.nativeCalibrationBitsToMeasured zlo hz bits)
    (fun d k i x H h => a.nativeFiniteDecision_eq_finiteLearner mu zlo hz d bits k i x H h) k i x H hRank

abbrev NativeOuterSeed (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) :=
  OuterMarkArray n m (Fin (outerMarkBits n m) → Bool) × a.NativeBits zlo hz

noncomputable def nativeOuterSeedLaw (a : FairCalibrationParameters n m) (zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) : Measure (a.NativeOuterSeed zlo hz) :=
  (Measure.pi fun _ : Fin (outerMarkSlotCount n m) => fairBitVectorLaw (outerMarkBits n m)).prod
    (rankCalibrationBitsLaw a.clockBits a.coinBits (nativeScheduleLaw n a.nativeTargetSchedule)
      (nativeScheduleLaw n (a.nativeThresholdSchedule zlo hz)))

theorem nativeOuterSeed_measurePreserving (a : FairCalibrationParameters n m) (mu zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) :
    let L := outerFairRankLearner (by have := a.two_le; omega : 1≤m) (a.finiteLearner (mu : ℝ)) (outerMarkBits n m)
    MeasurePreserving (fun s : a.NativeOuterSeed zlo hz =>
      (s.1,a.nativeCalibrationBitsToMeasured zlo hz s.2) : a.NativeOuterSeed zlo hz → L.Seed)
      (a.nativeOuterSeedLaw zlo hz) L.seedLaw := by
  dsimp only
  let μ := Measure.pi fun _ : Fin (outerMarkSlotCount n m) => fairBitVectorLaw (outerMarkBits n m)
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  exact (MeasurePreserving.id μ).prod
    (a.nativeCalibrationBitsToMeasured_measurePreserving zlo hz a.clockBits a.coinBits)

end FairCalibrationParameters

end ProphetSecretary.Statistics.Calibration
