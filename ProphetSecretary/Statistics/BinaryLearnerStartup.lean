import ProphetSecretary.Statistics.BinaryFairStartup

/-!
# Public startup of the binary learner

The two encoded tolerances and confidence levels are prepared once.
Both sets of scalar query sizes are computed before the independent fair
tapes are allocated.
-/

open Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability
open FairCalibrationParameters

structure BinaryLearnerStartup where
  inputs : Fin 5 → BinaryRational
  target : BinaryPublicSearchResult
  threshold : BinaryPublicSearchResult
  work : ℕ

def countedBinaryLearnerStartup (n m J : ℕ) (zlo : BinaryRational) : BinaryLearnerStartup :=
  let x := countedBinaryCalibrationQueryInputs n m J zlo
  let t := countedBinaryFairStartup n (x.1 0) (x.1 1) (x.1 2)
  let p := countedBinaryFairStartup n (x.1 0) (x.1 3) (x.1 4)
  ⟨x.1,t,p,x.2+t.work+p.work+4⟩

private lemma nativePublicFairSchedule_congr (n m : ℕ) [NeZero m] {h p h' p' : ℚ}
    (hh : (h : ℝ)∈Ioo (0 : ℝ) 1) (hp : (p : ℝ)∈Ioo (0 : ℝ) 1)
    (hh' : (h' : ℝ)∈Ioo (0 : ℝ) 1) (hp' : (p' : ℝ)∈Ioo (0 : ℝ) 1)
    (eh : h=h') (ep : p=p') :
    nativePublicFairSchedule n m h p hh hp=nativePublicFairSchedule n m h' p' hh' hp' := by
  subst h' p'
  rfl

theorem countedBinaryLearnerStartup_value {n m : ℕ} (a : FairCalibrationParameters n m)
    (zlo : BinaryRational) (hz : (zlo.value : ℝ)=a.zlo) :
    let st := countedBinaryLearnerStartup n m a.grid zlo
    let T := a.nativeTargetSchedule
    let P := a.nativeThresholdSchedule zlo.value hz
    (st.inputs 1).value=T.accuracy ∧ (st.inputs 3).value=P.accuracy ∧
      st.target.level=T.level ∧ st.target.precision=T.bits ∧
      st.target.halfCopies=(countedConfidenceLevel T.failure T.confidence).1 ∧
      st.threshold.level=P.level ∧ st.threshold.precision=P.bits ∧
      st.threshold.halfCopies=(countedConfidenceLevel P.failure P.confidence).1 := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  let x := (countedBinaryCalibrationQueryInputs n m a.grid zlo).1
  obtain ⟨hB,hT,hTf,hP,hPf⟩ := countedBinaryCalibrationQueryInputs_value n m a.grid zlo
  have hT' : ((x 1).value : ℝ)∈Ioo (0 : ℝ) 1 := by
    rw [hT,a.rationalTargetTolerance_cast]
    exact a.targetTolerance_mem
  have hTf' : ((x 2).value : ℝ)∈Ioo (0 : ℝ) 1 := by
    rw [hTf,a.rationalTargetFailure_cast]
    exact a.targetFailure_range
  have hP' : ((x 3).value : ℝ)∈Ioo (0 : ℝ) 1 := by
    rw [hP,a.rationalThresholdTolerance_cast zlo.value hz]
    exact a.thresholdTolerance_mem
  have hPf' : ((x 4).value : ℝ)∈Ioo (0 : ℝ) 1 := by
    rw [hPf,← a.rationalGrid_eq zlo.value hz,a.rationalThresholdFailure_cast zlo.value hz]
    exact a.thresholdFailure_range
  have hTarget := countedBinaryFairStartup_value n m (x 0) (x 1) (x 2) hB hT' hTf'
  have hPolicy := countedBinaryFairStartup_value n m (x 0) (x 3) (x 4) hB hP' hPf'
  dsimp only at hTarget hPolicy ⊢
  have hTe : nativePublicFairSchedule n m (x 1).value (x 2).value hT' hTf'=a.nativeTargetSchedule := by
    unfold nativeTargetSchedule
    exact nativePublicFairSchedule_congr _ _ _ _ _ _ hT hTf
  have hPe : nativePublicFairSchedule n m (x 3).value (x 4).value hP' hPf'=
      a.nativeThresholdSchedule zlo.value hz := by
    unfold nativeThresholdSchedule
    exact nativePublicFairSchedule_congr _ _ _ _ _ _ hP
      (hPf.trans (congrArg (rationalThresholdFailure n m) (a.rationalGrid_eq zlo.value hz).symm))
  rw [hTe] at hTarget
  rw [hPe] at hPolicy
  exact ⟨hT,hP,hTarget.1,hTarget.2.1,hTarget.2.2,hPolicy.1,hPolicy.2.1,hPolicy.2.2⟩

def binaryLearnerInputWidth (n m J D : ℕ) : ℕ := D+n+m+J+20

def binaryLearnerAccuracyWidth (n m J D : ℕ) : ℕ := 150*(binaryLearnerInputWidth n m J D+1)

def binaryLearnerStartupBound (n m J D : ℕ) : ℕ :=
  binaryCalibrationQueryInputsWork m (binaryLearnerInputWidth n m J D)+
    2*binaryFairStartupWorkBound (binaryLearnerAccuracyWidth n m J D)+4

theorem countedBinaryLearnerStartup_bounds (n m J D : ℕ) (zlo : BinaryRational)
    (hz : RationalHeight zlo.value D) :
    let st := countedBinaryLearnerStartup n m J zlo
    (∀ i, RationalHeight (st.inputs i).value (binaryLearnerAccuracyWidth n m J D)) ∧
      st.work≤binaryLearnerStartupBound n m J D := by
  let B := binaryLearnerInputWidth n m J D
  let H := binaryLearnerAccuracyWidth n m J D
  have hB : 16≤B := by unfold B binaryLearnerInputWidth; omega
  have hP (k : ℕ) (hk : k≤B) : k≤2^B :=
    (Nat.lt_two_pow_self (n := k)).le.trans (Nat.pow_le_pow_right (by decide) hk)
  have hN := hP n (by unfold B binaryLearnerInputWidth; omega)
  have hM := hP m (by unfold B binaryLearnerInputWidth; omega)
  have hJ := hP J (by unfold B binaryLearnerInputWidth; omega)
  have hC : 4*(m-1).bits.length+2≤2^B := by
    rw [← calibrationClog_eq_width]
    have hc := clog_two_le_self m
    have hp := (Nat.lt_two_pow_self (n := m)).le
    have hpos : 0<(2:ℕ)^m := by positivity
    calc
      _ ≤ 8*2^m := by omega
      _ = 2^(m+3) := by rw [pow_add,show (2:ℕ)^3=8 by decide,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold B binaryLearnerInputWidth; omega)
  have h := countedBinaryCalibrationQueryInputs_bounds n m J zlo B hB hN hM hJ hC
    (hz.mono (by unfold B binaryLearnerInputWidth; omega))
  dsimp only at h ⊢
  let x := countedBinaryCalibrationQueryInputs n m J zlo
  have hH : 4≤H := by unfold H binaryLearnerAccuracyWidth; omega
  have hNH : n ≤ 2^H := (Nat.lt_two_pow_self (n := n)).le.trans
    (Nat.pow_le_pow_right (by decide) (by unfold H binaryLearnerAccuracyWidth binaryLearnerInputWidth; omega))
  have ht := countedBinaryFairStartup_work n (x.1 0) (x.1 1) (x.1 2) H hH hNH
    (h.1 0) (h.1 1) (h.1 2)
  have hp := countedBinaryFairStartup_work n (x.1 0) (x.1 3) (x.1 4) H hH hNH
    (h.1 0) (h.1 3) (h.1 4)
  refine ⟨h.1,?_⟩
  unfold binaryLearnerStartupBound
  change x.2+(countedBinaryFairStartup n (x.1 0) (x.1 1) (x.1 2)).work+
    (countedBinaryFairStartup n (x.1 0) (x.1 3) (x.1 4)).work+4≤_
  have hx := h.2
  change x.2≤binaryCalibrationQueryInputsWork m B at hx
  change x.2+_+_+4≤binaryCalibrationQueryInputsWork m B+2*binaryFairStartupWorkBound H+4
  exact Nat.add_le_add_right ((Nat.add_le_add (Nat.add_le_add hx ht) hp).trans_eq (by omega)) 4

end ProphetSecretary.Statistics.Calibration
