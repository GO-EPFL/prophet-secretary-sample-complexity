import ProphetSecretary.Statistics.FairCalibratedNativeCalls
import ProphetSecretary.Statistics.NativeFiniteCalibration

/-!
# Exact execution of the public native schedule

The actual rational planner schedule and the measured finite-bit rank
learner use the same empirical rows, validation profiles and mixture
choice. A reindexing of the fair banks supplies the measured callback
with exactly the bits used by its native rational evaluation.
-/

open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {T P T' P' : Type}

def mapRankCalibrationBanks (f : T → T') (g : P → P')
    (p : RankCalibratedSeed n m J T P) : RankCalibratedSeed n m J T' P' :=
  (fun i => f (p.1 i),
    fun i => ((p.2.1 i).1,(p.2.1 i).2.1,fun j => g ((p.2.1 i).2.2 j)),
    p.2.2.1,(fun j => g (p.2.2.2.1 j)),p.2.2.2.2)

lemma rankCalibratedSamplePolicy_mapBanks [NeZero m] (roundProb : ℝ → ℝ) (mu zlo zhi : ℝ)
    (target : TargetEstimator n m T') (estimate : ContinuationEstimator n m P')
    (f : T → T') (g : P → P') (y : Reservoir n (2*m)) (p : RankCalibratedSeed n m J T P)
    (k i : Fin n) (x : ℝ) (H : RankHistory n) :
    (rankCalibratedSamplePolicy roundProb mu zlo zhi
      (fun q z s => target q z (f s)) (fun q A u z s => estimate q A u z (g s))).decide (y,p) k i x H =
    (rankCalibratedSamplePolicy roundProb mu zlo zhi target estimate).decide (y,mapRankCalibrationBanks f g p) k i x H := rfl

namespace FairCalibrationParameters

def nativeCalibrationCutoff (m : ℕ) : ℚ := 4*(Nat.clog 2 m : ℚ)+2

lemma nativeCalibrationCutoff_cast (m : ℕ) :
    (nativeCalibrationCutoff m : ℝ)=targetCountCutoff m := by
  simp only [nativeCalibrationCutoff,targetCountCutoff,
    Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_add]

theorem nativeFiniteRankExecution_eq (a : FairCalibrationParameters n m)
    (mu zlo : ℚ) (hz : (zlo : ℝ)=a.zlo) (b c : ℕ)
    (data : Fin n → Fin (2*m) → ℚ)
    (bits : RankCalibrationBits n m a.grid b c (a.nativeTargetSchedule.Seed n)
      ((a.nativeThresholdSchedule zlo hz).Seed n))
    (k i : Fin n) (x : ℚ) (H : Fin n → Option (Fin n × ℚ))
    (hRank : onlineQueryRank H i=k) :
    letI : NeZero m := ⟨by have := a.two_le; omega⟩
    let q := countedFiniteCalibrationPrepare a.nativeTargetSchedule (a.nativeThresholdSchedule zlo hz)
      b c mu zlo (1/4) (nativeCalibrationCutoff m)
      (rationalCalibrationFirstBlock data) (rationalCalibrationValidationValues data) bits
    (countedFiniteCalibrationDecision (a.nativeThresholdSchedule zlo hz) zlo (1/4) q i x H).1 =
      (rankCalibratedSamplePolicy (J := a.grid) (uniformGridRound (2^c) (by positivity))
        (mu : ℝ) a.zlo (1/4) a.target a.threshold).decide
        ((fun i j => (data i j : ℝ)),
          interpretRankCalibrationBits b c (a.nativeCalibrationBitsToMeasured zlo hz bits))
        k i (x : ℝ) (calibrationRankHistoryCast H) := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  let f := a.nativeTargetSeed
  let g := a.nativeThresholdSeed zlo hz
  let target := fun (q : Reservoir n m) z s => a.target q z (f s)
  let threshold := fun (q : Reservoir n m) A u z s => a.threshold q A u z (g s)
  have h := countedFiniteCalibrationExecution_eq a.nativeTargetSchedule (a.nativeThresholdSchedule zlo hz)
    b c mu zlo (1/4) (nativeCalibrationCutoff m) (nativeCalibrationCutoff_cast m) data bits target threshold
    (fun z s => a.nativeTargetCall_value _ z s)
    (fun A u z s => a.nativeThresholdCall_value zlo hz _ A u z s)
    k i x H hRank
  refine h.trans ?_
  unfold target threshold
  rw [rankCalibratedSamplePolicy_mapBanks]
  have hBits : mapRankCalibrationBanks f g (interpretRankCalibrationBits b c bits)=
      interpretRankCalibrationBits b c (a.nativeCalibrationBitsToMeasured zlo hz bits) := rfl
  rw [hBits,hz]
  norm_num

end FairCalibrationParameters

end ProphetSecretary.Statistics.Calibration
