import ProphetSecretary.Statistics.CalibratedOuter.BinarySchedulePolynomial
import ProphetSecretary.Statistics.BinaryCalibrationPolynomial
import ProphetSecretary.Statistics.BinaryScalarPolynomial
import ProphetSecretary.Statistics.BinaryLearnerStartup
import ProphetSecretary.Statistics.BinaryBoundedRankExecution

/-!
# Uniform polynomial work of the binary learner

After the outer mesh, displayed values have a width depending on the mesh
parameter alone. Scalar output widths are bounded from the actual clock
and coefficient inputs before they are used in the calibration sums.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

namespace BinaryScheduleInput
variable {zlo : ℚ} {zInv : ℕ}

noncomputable def boundedPrepareBudgetAt (x : BinaryScheduleInput zlo zInv) (Y D : ℕ) : ℕ :=
  let a := x.parameters
  let A := binaryLearnerAccuracyWidth x.n x.m a.grid D
  binaryBoundedRankPrepareWork a.nativeTargetSchedule (a.nativeThresholdSchedule zlo x.coefficient_eq)
    x.n x.m a.grid a.clockBits a.coinBits Y x.m D x.m A A+2

noncomputable def boundedOnlineBudgetAt (x : BinaryScheduleInput zlo zInv) (Y D : ℕ) : ℕ :=
  let a := x.parameters
  binaryBoundedRankDecisionWork (a.nativeThresholdSchedule zlo x.coefficient_eq) x.n x.m a.grid
    a.clockBits Y x.m D x.m (binaryLearnerAccuracyWidth x.n x.m a.grid D)

noncomputable def boundedPrepareBudget (x : BinaryScheduleInput zlo zInv) (D : ℕ) : ℕ :=
  x.boundedPrepareBudgetAt (2*x.m) D

noncomputable def boundedOnlineBudget (x : BinaryScheduleInput zlo zInv) (D : ℕ) : ℕ :=
  x.boundedOnlineBudgetAt (2*x.m) D

noncomputable def publicStartupBudget (x : BinaryScheduleInput zlo zInv) (D : ℕ) : ℕ :=
  binaryLearnerStartupBound x.n x.m x.parameters.grid D

private lemma size_positive (x : BinaryScheduleInput zlo zInv) : 0<x.size := by simp [size]

private lemma add_work {F G : BinaryScheduleInput zlo zInv → ℕ}
    (hF : HasPolynomialWorkBound size F) (hG : HasPolynomialWorkBound size G) :
    HasPolynomialWorkBound size (fun x => F x+G x) :=
  HasPolynomialWorkBound.add size_positive hF hG

local infixl:65 " +ₚ " => add_work
local infixl:70 " *ₚ " => HasPolynomialWorkBound.mul
local infixr:80 " ^ₚ " => HasPolynomialWorkBound.pow

private def callSchedule (target : Bool) (x : BinaryScheduleInput zlo zInv) : FairCallSchedule :=
  if target then x.parameters.nativeTargetSchedule else
    x.parameters.nativeThresholdSchedule zlo x.coefficient_eq

private theorem callSchedule_poly (target : Bool) :
    HasPolynomialWorkBound (size (zlo := zlo) (zInv := zInv)) (fun x => (16:ℕ)^(callSchedule target x).level) ∧
    HasPolynomialWorkBound (size (zlo := zlo) (zInv := zInv)) (fun x => (callSchedule target x).bits) ∧
    HasPolynomialWorkBound (size (zlo := zlo) (zInv := zInv)) (fun x =>
      (countedConfidenceLevel (callSchedule target x).failure (callSchedule target x).confidence).1) := by
  constructor
  · apply HasPolynomialWorkBound.of_real_bound (finiteLevelConstant (zlo:ℝ)) 280
    intro x
    have h : (16:ℝ)^(callSchedule target x).level≤
        finiteLevelConstant x.parameters.zlo*((x.m:ℝ)+1)^280 := by
      cases target
      · exact finiteThresholdLevel_bound x.parameters zlo x.coefficient_eq
      · exact finiteTargetLevel_bound x.parameters
    have hN : (x.m:ℝ)+1≤(x.size:ℝ) := by
      exact_mod_cast (show x.m+1≤x.size by unfold size; omega)
    rw [Nat.cast_pow,Nat.cast_ofNat]
    rw [← x.coefficient_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hN _)
      (by unfold finiteLevelConstant; positivity))
  constructor
  · apply HasPolynomialWorkBound.of_real_bound (finiteQueryBitConstant (zlo:ℝ)) 36
    intro x
    have h : ((callSchedule target x).bits : ℝ)≤
        finiteQueryBitConstant x.parameters.zlo*((x.n:ℝ)+x.m+2)^36 := by
      cases target
      · exact finiteThresholdBits_bound x.parameters zlo x.coefficient_eq
      · exact finiteTargetBits_bound x.parameters
    have hN : (x.n : ℝ)+x.m+2≤(x.size : ℝ) := by
      exact_mod_cast (show x.n+x.m+2≤x.size by unfold size; omega)
    rw [← x.coefficient_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hN _)
      (by
        unfold finiteQueryBitConstant
        have h := x.parameters.coefficient_mem.1
        rw [← x.coefficient_eq] at h
        positivity))
  · refine ⟨12,4,fun x => ?_⟩
    let s := callSchedule target x
    have h : confidenceCopyCount s.failure s.confidence+1≤12*(x.n+x.m+2)^4 := by
      cases target
      · exact finiteThresholdCopies_bound x.parameters zlo x.coefficient_eq
      · exact finiteTargetCopies_bound x.parameters
    have h' : (countedConfidenceLevel s.failure s.confidence).1≤confidenceCopyCount s.failure s.confidence+1 := by
      unfold confidenceCopyCount
      omega
    exact h'.trans (h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold size; omega) _)))

theorem boundedWorkBudgets_polynomial (D : ℕ) (Y : BinaryScheduleInput zlo zInv → ℕ)
    (hY : HasPolynomialWorkBound size Y) :
    HasPolynomialWorkBound size (fun x => x.boundedPrepareBudgetAt (Y x) D) ∧
    HasPolynomialWorkBound size (fun x => x.boundedOnlineBudgetAt (Y x) D) ∧
    HasPolynomialWorkBound (size (zlo := zlo) (zInv := zInv)) (fun x => x.publicStartupBudget D) := by
  let N := size (zlo := zlo) (zInv := zInv)
  let c := HasPolynomialWorkBound.const N
  have hn : HasPolynomialWorkBound N (fun x => x.n) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hm : HasPolynomialWorkBound N (fun x => x.m) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hJ : HasPolynomialWorkBound N (fun x => x.parameters.grid) :=
    hm.of_le (fun x => familyGridSize_le (by linarith only [x.parameters.coefficient_mem.1]))
  have hClock : HasPolynomialWorkBound N (fun x => x.parameters.clockBits) := by
    refine ⟨400*(zInv+1),5,fun x => ?_⟩
    have h := finiteClockBits_polynomial x.parameters
    rw [x.inverse_eq] at h
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold N size; omega) _))
  have hCoin : HasPolynomialWorkBound N (fun x => x.parameters.coinBits) :=
    ⟨1,2,fun x => by
      simp only [one_mul]
      exact (finiteCoinBits_bound x.parameters).trans (Nat.pow_le_pow_left (by unfold N size; omega) _)⟩
  have hZT := c 2 *ₚ hm +ₚ c 2
  have hZP := c 3 *ₚ c D +ₚ c 2 *ₚ hm +ₚ c 2
  have hU := c 7 *ₚ (hClock +ₚ c 1)
  have hInput : HasPolynomialWorkBound N (fun x => binaryLearnerInputWidth x.n x.m x.parameters.grid D) :=
    c D +ₚ hn +ₚ hm +ₚ hJ +ₚ c 20
  have hA : HasPolynomialWorkBound N (fun x => binaryLearnerAccuracyWidth x.n x.m x.parameters.grid D) :=
    c 150 *ₚ (hInput +ₚ c 1)
  obtain ⟨hTe,hTb,hTa⟩ := callSchedule_poly (zlo := zlo) (zInv := zInv) true
  obtain ⟨hPe,hPb,hPa⟩ := callSchedule_poly (zlo := zlo) (zInv := zInv) false
  have hR (f : Bool) (hE : HasPolynomialWorkBound N (fun x => (16:ℕ)^(callSchedule f x).level)) :
      HasPolynomialWorkBound N (fun x => (callSchedule f x).level) :=
    hE.of_le (fun x => (Nat.lt_two_pow_self (n := (callSchedule f x).level)).le.trans
      (Nat.pow_le_pow_left (by decide) _))
  obtain ⟨_,hTWork,hTHeight⟩ :=
    binaryScalarBudgets_polynomial size_positive hn hm hY hm (c 0) hZT hTb (hR _ hTe) hTa hA hTe
  obtain ⟨_,hPWork,hPHeight⟩ :=
    binaryScalarBudgets_polynomial size_positive hn hm hY hm hU hZP hPb (hR _ hPe) hPa hA hPe
  have hTW := hTWork +ₚ hn +ₚ c 3
  have hPW := hPWork +ₚ c 1 +ₚ c 3 *ₚ hn +ₚ c 10 *ₚ (hn +ₚ c 1) ^ₚ 2
  have hNM := hn *ₚ hm
  have hMax : HasPolynomialWorkBound N (fun x => binaryEmpiricalMaximumWidth x.n (x.n*x.m) (Y x) x.m) :=
    hY +ₚ hm +ₚ c 4 *ₚ hm *ₚ hn +ₚ (hNM +ₚ c 2) *ₚ (hY +ₚ c 4 *ₚ hm *ₚ hn +ₚ c 2) +ₚ c 2
  have hWidth : HasPolynomialWorkBound N (fun x => finiteBinaryCalibrationWidth
      x.parameters.nativeTargetSchedule (x.parameters.nativeThresholdSchedule zlo x.coefficient_eq)
      x.n x.m (Y x) x.m x.parameters.clockBits D x.m x.parameters.coinBits) :=
    c 4 *ₚ (hm +ₚ c 1) +ₚ c 2 +ₚ hY +ₚ hClock +ₚ c D +ₚ hm +ₚ hCoin +ₚ hZT +ₚ hZP +ₚ
      hMax +ₚ (c 2 *ₚ hn +ₚ c 1) *ₚ (c 3 *ₚ hm +ₚ c 2) +ₚ hTHeight +ₚ hPHeight +ₚ c 8
  have hPrepare := (binaryCalibrationBudgets_polynomial size_positive hn hm hJ hY hm hWidth hPHeight hTW hPW).1
  have hOnline := (binaryCalibrationBudgets_polynomial size_positive hn hm hJ hY hm
    (hY +ₚ hClock +ₚ hZP) hPHeight hTW hPW).2
  have hRank : HasPolynomialWorkBound N (fun x => binaryRankOrderWorkBound x.n x.parameters.clockBits) :=
    hn *ₚ (c 110 *ₚ (hClock +ₚ c 2) ^ₚ 3 +ₚ c 3) +ₚ c 2 +ₚ
      (c 3400 *ₚ (hClock +ₚ c 2) ^ₚ 3 +ₚ c 7) *ₚ (hn +ₚ c 1) ^ₚ 2 +ₚ
      c 10 *ₚ (hn +ₚ c 1) ^ₚ 2
  have hInputs : HasPolynomialWorkBound N (fun x => binaryCalibrationQueryInputsWork x.m (binaryLearnerInputWidth x.n x.m x.parameters.grid D)) :=
    c 4 *ₚ (c 3 *ₚ (hInput +ₚ c 1) +ₚ c 3) +ₚ c 4 *ₚ hm +ₚ
      c 5 *ₚ (c 150 *ₚ (c 3600 *ₚ (c 150 *ₚ (hInput +ₚ c 1) +ₚ c 2) ^ₚ 3 +ₚ c 1) +ₚ c 2) +ₚ c 10
  have hSearchA := c 20 *ₚ (hA +ₚ c 1) +ₚ c 1
  have hSearch : HasPolynomialWorkBound N (fun x => binaryPublicSearchWorkBound
      (20*(binaryLearnerAccuracyWidth x.n x.m x.parameters.grid D+1))) :=
    c 3 *ₚ hSearchA *ₚ (c 7000 *ₚ (c 2 *ₚ hSearchA +ₚ c 4) ^ₚ 3 +ₚ c 5) +ₚ c 12 *ₚ hSearchA +ₚ c 35
  have hStartup : HasPolynomialWorkBound N (fun x => binaryFairStartupWorkBound (binaryLearnerAccuracyWidth x.n x.m x.parameters.grid D)) :=
    c 3 *ₚ (hA +ₚ c 1) +ₚ c 3 +ₚ c 20 *ₚ (c 3600 *ₚ (c 20 *ₚ (hA +ₚ c 1) +ₚ c 2) ^ₚ 3 +ₚ c 1) +ₚ
      c 5 *ₚ (c 3600 *ₚ (c 4 *ₚ hA +ₚ c 15) ^ₚ 3) +ₚ c 8 +ₚ hSearch +ₚ c 8
  refine ⟨?_,?_,?_⟩
  · exact hm *ₚ (c 2 *ₚ hRank +ₚ c 6) +ₚ hRank +ₚ c 110 *ₚ (hCoin +ₚ c 3) ^ₚ 3 +ₚ
        c 4 *ₚ hCoin +ₚ c 10 +ₚ hPrepare +ₚ c 4 +ₚ c 2
  · exact hOnline +ₚ hn +ₚ c 3
  · exact hInputs +ₚ c 2 *ₚ hStartup +ₚ c 4

theorem actualWorkBudget_polynomial (D : ℕ) :
    HasPolynomialWorkBound (size (zlo := zlo) (zInv := zInv))
      (fun x => x.workBudget (x.boundedPrepareBudget D) (x.boundedOnlineBudget D) (2*x.publicStartupBudget D)) := by
  let N := size (zlo := zlo) (zInv := zInv)
  have hm : HasPolynomialWorkBound N (fun x => x.m) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hY := HasPolynomialWorkBound.const N 2 *ₚ hm
  obtain ⟨hP,hO,hS⟩ := boundedWorkBudgets_polynomial D _ hY
  exact workBudget_polynomial hP hO (HasPolynomialWorkBound.const N 2 *ₚ hS)

end BinaryScheduleInput

end ProphetSecretary.Statistics.Calibration
