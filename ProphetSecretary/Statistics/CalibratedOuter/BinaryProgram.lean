import ProphetSecretary.Statistics.CalibratedOuter.BinaryLearner
import ProphetSecretary.Statistics.BinaryLearnerStartup
import ProphetSecretary.Statistics.CalibratedOuter.NativeReward

/-!
# The binary program at the learner's public parameters

The public startup supplies the encoded tolerances and cached confidence
indices. The same finite rank seed then drives the encoded and measured
executions.
-/

open Set
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ}

namespace FairCalibrationParameters

structure BinaryPrepared (a : FairCalibrationParameters n m) (zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) where
  grid : ℕ
  schedule : FairCallSchedule
  state : BinaryOuterStage n m (BinaryBoundedState n m grid (schedule.Seed n))
  policyAccuracy : BinaryRational
  halfCopies : ℕ
  halfCopies_eq : halfCopies=(countedConfidenceLevel schedule.failure schedule.confidence).1
  work : ℕ

noncomputable def prepareBinaryProgram (a : FairCalibrationParameters n m) (mu zlo : BinaryRational)
    (hz : (zlo.value : ℝ)=a.zlo)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (seed : a.NativeOuterSeed zlo.value hz) : a.BinaryPrepared zlo.value hz :=
  let q := countedBinaryLearnerStartup n m a.grid zlo
  let H := countedBinaryLearnerStartup_value a zlo hz
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo.value hz
  let p := countedBinaryLearnerPrepare (by have := a.two_le; omega) T P
    q.target.halfCopies q.threshold.halfCopies H.2.2.2.2.1 H.2.2.2.2.2.2.2
    mu zlo (BinaryRational.ofRat (1/4)) (q.inputs 1) (q.inputs 3)
    a.clockBits a.coinBits (outerMarkBits n m) y seed.1 seed.2
  ⟨a.grid,P,p,q.inputs 3,q.threshold.halfCopies,H.2.2.2.2.2.2.2,q.work+p.work+3⟩

def decideBinaryProgram (a : FairCalibrationParameters n m) {zlo : ℚ} {hz : (zlo : ℝ)=a.zlo}
    (q : a.BinaryPrepared zlo hz) (k i : Fin n) (x : BinaryRational)
    (H : BinaryOuterHistory n (Fin n)) : Bool × ℕ :=
  countedBinaryLearnerDecision q.schedule
    q.halfCopies q.halfCopies_eq q.policyAccuracy q.state k i x H

theorem decideBinaryProgram_value (a : FairCalibrationParameters n m)
    (mu zlo : BinaryRational) (hz : (zlo.value : ℝ)=a.zlo)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (seed : a.NativeOuterSeed zlo.value hz) (k i : Fin n) (x : BinaryRational)
    (H : BinaryOuterHistory n (Fin n)) (hRank : onlineQueryRank (binaryOuterHistoryValue H) i=k) :
    let L := outerFairRankLearner (by have := a.two_le; omega : 1≤m)
      (a.finiteLearner (mu.value : ℝ)) (outerMarkBits n m)
    (a.decideBinaryProgram (a.prepareBinaryProgram mu zlo hz y seed) k i x H).1 =
      L.policy.decide ((fun i j => ((y i j).value : ℝ)),seed.1,a.nativeCalibrationBitsToMeasured zlo.value hz seed.2)
        k i (x.value : ℝ) (calibrationRankHistoryCast (binaryOuterHistoryValue H)) := by
  dsimp only
  let st := countedBinaryLearnerStartup n m a.grid zlo
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo.value hz
  let e := countedBinaryLearnerStartup_value a zlo hz
  have h := countedBinaryLearnerDecision_value (by have := a.two_le; omega : 1≤m) T P
    st.target.halfCopies st.threshold.halfCopies e.2.2.2.2.1 e.2.2.2.2.2.2.2
    mu zlo (BinaryRational.ofRat (1/4)) (st.inputs 1) (st.inputs 3) e.1 e.2.1
    a.clockBits a.coinBits (outerMarkBits n m) y seed.1 seed.2 k i x H
  dsimp only at h
  unfold decideBinaryProgram prepareBinaryProgram
  dsimp only
  refine h.trans ?_
  rw [BinaryRational.ofRat_value]
  exact a.nativeFiniteOuterDecision_eq mu.value zlo.value hz (fun i j => (y i j).value)
    seed.1 seed.2 k i x.value (binaryOuterHistoryValue H) hRank

theorem prepareBinaryProgram_work (a : FairCalibrationParameters n m)
    (mu zlo : BinaryRational) (hz : (zlo.value : ℝ)=a.zlo)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (seed : a.NativeOuterSeed zlo.value hz) (D B : ℕ)
    (hY : ∀ i j, RationalHeight (y i j).value B) (hMarks : outerMarkBits n m≤B)
    (hmu : RationalHeight mu.value D) (hZ : RationalHeight zlo.value D) (hD : 2≤D) :
    let A := binaryLearnerAccuracyWidth n m a.grid D
    let T := a.nativeTargetSchedule
    let P := a.nativeThresholdSchedule zlo.value hz
    (a.prepareBinaryProgram mu zlo hz y seed).work ≤
      binaryLearnerStartupBound n m a.grid D+
        binaryOuterStageWorkBound n m (outerMarkBits n m) m B
          (binaryBoundedRankPrepareWork T P n m a.grid a.clockBits a.coinBits (2*m) m D m A A+2)+3 := by
  dsimp only
  let st := countedBinaryLearnerStartup n m a.grid zlo
  let A := binaryLearnerAccuracyWidth n m a.grid D
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo.value hz
  let e := countedBinaryLearnerStartup_value a zlo hz
  have hs := countedBinaryLearnerStartup_bounds n m a.grid D zlo hZ
  dsimp only at hs
  have hM : m≤2^m := (Nat.lt_two_pow_self (n := m)).le
  have hJ : a.grid≤2^m := (familyGridSize_le (by linarith [a.coefficient_mem.1])).trans hM
  have hZhi : RationalHeight (BinaryRational.ofRat (1/4)).value D := by
    rw [BinaryRational.ofRat_value]
    exact (rationalHeight_one.div (rationalHeight_natCast 4 2 (by decide))).mono hD
  have h := countedBinaryLearnerPrepare_work (by have := a.two_le; omega : 1≤m) T P
    st.target.halfCopies st.threshold.halfCopies e.2.2.2.2.1 e.2.2.2.2.2.2.2
    mu zlo (BinaryRational.ofRat (1/4)) (st.inputs 1) (st.inputs 3)
    a.clockBits a.coinBits (outerMarkBits n m) y seed.1 seed.2 m B D m A A hM hJ
    hY hMarks hmu hZ hZhi (hs.1 1) (hs.1 3)
  exact Nat.add_le_add_right (Nat.add_le_add hs.2 h) 3

theorem decideBinaryProgram_work (a : FairCalibrationParameters n m)
    (mu zlo : BinaryRational) (hz : (zlo.value : ℝ)=a.zlo)
    (y : Fin n → Fin (outerSampleBudget m) → BinaryRational)
    (seed : a.NativeOuterSeed zlo.value hz) (D B : ℕ)
    (hY : ∀ i j, RationalHeight (y i j).value B) (hMarks : outerMarkBits n m≤B)
    (hZ : RationalHeight zlo.value D) (hD : 2≤D)
    (k i : Fin n) (x : BinaryRational) (H : BinaryOuterHistory n (Fin n))
    (hx : RationalHeight x.value B)
    (hH : ∀ j s v, H j=some (s,v) → RationalHeight v.value B) :
    (a.decideBinaryProgram (a.prepareBinaryProgram mu zlo hz y seed) k i x H).2 ≤
      binaryBoundedRankDecisionWork (a.nativeThresholdSchedule zlo.value hz) n m a.grid a.clockBits
        (2*m) m D m (binaryLearnerAccuracyWidth n m a.grid D)+binaryOuterOnlineOverhead n m m B := by
  let st := countedBinaryLearnerStartup n m a.grid zlo
  let A := binaryLearnerAccuracyWidth n m a.grid D
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo.value hz
  let e := countedBinaryLearnerStartup_value a zlo hz
  have hs := countedBinaryLearnerStartup_bounds n m a.grid D zlo hZ
  dsimp only at hs
  have hM : m≤2^m := (Nat.lt_two_pow_self (n := m)).le
  have hJ : a.grid≤2^m := (familyGridSize_le (by linarith [a.coefficient_mem.1])).trans hM
  have hZhi : RationalHeight (BinaryRational.ofRat (1/4)).value D := by
    rw [BinaryRational.ofRat_value]
    exact (rationalHeight_one.div (rationalHeight_natCast 4 2 (by decide))).mono hD
  exact countedBinaryLearnerDecision_work (by have := a.two_le; omega : 1≤m) T P
    st.target.halfCopies st.threshold.halfCopies e.2.2.2.2.1 e.2.2.2.2.2.2.2
    mu zlo (BinaryRational.ofRat (1/4)) (st.inputs 1) (st.inputs 3)
    a.clockBits a.coinBits (outerMarkBits n m) y seed.1 seed.2 m B D m A hM hJ
    hY hMarks hZ hZhi (hs.1 3) k i x H hx hH

end FairCalibrationParameters

end ProphetSecretary.Statistics.Calibration
