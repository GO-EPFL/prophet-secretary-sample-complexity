import ProphetSecretary.Statistics.CalibratedOuter.BinarySchedule
import ProphetSecretary.Statistics.BinaryCalibrationRandomness
import ProphetSecretary.Statistics.FiniteSchedulePolynomial
import ProphetSecretary.Analysis.PolynomialWorkBound
import ProphetSecretary.Statistics.CalibrationRankRandomness

/-!
# Polynomial composition of the binary outer and bounded work

The raw width bound is included in the size parameter. The public clock,
mark and query scales are fixed by the accuracy and instance size. The
bounded binary controller supplies its separate preparation, online and
startup work estimates.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

structure BinaryScheduleInput (zlo : ℚ) (zInv : ℕ) where
  n : ℕ
  m : ℕ
  width : ℕ
  parameters : FairCalibrationParameters n m
  coefficient_eq : (zlo : ℝ)=parameters.zlo
  inverse_eq : parameters.clockInverse=zInv

namespace BinaryScheduleInput

variable {zlo : ℚ} {zInv : ℕ}

def size (x : BinaryScheduleInput zlo zInv) : ℕ := x.n+x.m+x.width+2

def outerWidth (x : BinaryScheduleInput zlo zInv) : ℕ :=
  x.width+outerMarkBits x.n x.m

noncomputable def bitBudget (x : BinaryScheduleInput zlo zInv) : ℕ :=
  finiteScheduleFairBitsBound x.n x.m x.parameters.grid x.parameters.clockBits x.parameters.coinBits
    (outerMarkBits x.n x.m) x.parameters.nativeTargetSchedule
    (x.parameters.nativeThresholdSchedule zlo x.coefficient_eq)

noncomputable def allocationBudget (x : BinaryScheduleInput zlo zInv) : ℕ :=
  finiteScheduleArithmeticBound x.n x.m x.parameters.grid x.parameters.clockBits x.parameters.coinBits
    (outerMarkBits x.n x.m) x.parameters.nativeTargetSchedule
    (x.parameters.nativeThresholdSchedule zlo x.coefficient_eq)

def clockDecodeBudget (x : BinaryScheduleInput zlo zInv) : ℕ :=
  x.m*(2*binaryRankOrderWorkBound x.n x.parameters.clockBits+6)+
    binaryRankOrderWorkBound x.n x.parameters.clockBits+
    110*(x.parameters.coinBits+3)^3+4*x.parameters.coinBits+10

noncomputable def workBudget (x : BinaryScheduleInput zlo zInv) (Wprep Wonline Wstartup : ℕ) : ℕ :=
  binaryOuterStageWorkBound x.n x.m (outerMarkBits x.n x.m) x.m x.outerWidth Wprep+
    x.n*(Wonline+binaryOuterOnlineOverhead x.n x.m x.m x.outerWidth)+
    x.clockDecodeBudget+Wstartup+x.bitBudget+x.allocationBudget+
    rankAuxiliaryBitStorageWork x.n x.m x.parameters.clockBits x.parameters.coinBits+2+
    8*(outerMarkSlotCount x.n x.m+1)*(outerMarkBits x.n x.m+1)+
    8*(x.n+1)*(outerSampleBudget x.m+1)

private lemma size_pos (x : BinaryScheduleInput zlo zInv) : 0<x.size := by simp [size]

private lemma add_bound {F G : BinaryScheduleInput zlo zInv → ℕ}
    (hF : HasPolynomialWorkBound size F) (hG : HasPolynomialWorkBound size G) :
    HasPolynomialWorkBound size (fun x => F x+G x) :=
  HasPolynomialWorkBound.add size_pos hF hG

local infixl:65 " +ₚ " => add_bound
local infixl:70 " *ₚ " => HasPolynomialWorkBound.mul
local infixr:80 " ^ₚ " => HasPolynomialWorkBound.pow

/-- Explicit stage bounds compose uniformly when the bounded binary
controller's own budgets have polynomial growth. -/
theorem workBudget_polynomial {F G H : BinaryScheduleInput zlo zInv → ℕ}
    (hF : HasPolynomialWorkBound size F) (hG : HasPolynomialWorkBound size G)
    (hH : HasPolynomialWorkBound size H) :
    HasPolynomialWorkBound size (fun x => workBudget x (F x) (G x) (H x)) := by
  let N := size (zlo := zlo) (zInv := zInv)
  let c := HasPolynomialWorkBound.const N
  have hn : HasPolynomialWorkBound N (fun x => x.n) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hm : HasPolynomialWorkBound N (fun x => x.m) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hY : HasPolynomialWorkBound N (fun x => x.width) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hm1 := hm +ₚ c 1
  have hn1 := hn +ₚ c 1
  have hO : HasPolynomialWorkBound N (fun x => outerMarkBits x.n x.m) := by
    refine ⟨12004^2,6,fun x => (finiteOuterMarkBits_bound x.n x.m).trans ?_⟩
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold N size; omega) _)
  have hB : HasPolynomialWorkBound N outerWidth := hY +ₚ hO
  have hSlot : HasPolynomialWorkBound N (fun x => outerMarkSlotCount x.n x.m) := by
    refine ⟨12004,2,fun x => (finiteOuterMarkSlots_bound x.n x.m).trans ?_⟩
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold N size; omega) _)
  have hClock : HasPolynomialWorkBound N (fun x => x.parameters.clockBits) := by
    refine ⟨400*(zInv+1),5,fun x => ?_⟩
    have h := finiteClockBits_polynomial x.parameters
    rw [x.inverse_eq] at h
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold N size; omega) _))
  have hCoin : HasPolynomialWorkBound N (fun x => x.parameters.coinBits) := by
    refine ⟨1,2,fun x => ?_⟩
    simp only [one_mul]
    exact (finiteCoinBits_bound x.parameters).trans (Nat.pow_le_pow_left (by unfold N size; omega) _)
  have hPilot : HasPolynomialWorkBound N (fun x => outerPilotRounds x.m) := by
    refine ⟨12000,1,fun x => ?_⟩
    have hc := clog_two_le_self (2*x.m)
    unfold outerPilotRounds outerPilotRank N size
    simp only [pow_one]
    omega
  have hBudget : HasPolynomialWorkBound N (fun x => outerSampleBudget x.m) := by
    refine ⟨12003,1,fun x => ?_⟩
    dsimp only
    rw [outerSampleBudget_eq,pow_one]
    have hc := clog_two_le_self (2*x.m)
    unfold N size
    omega
  have hb2 := (hB +ₚ c 2) ^ₚ 3
  have hb12 := (hB +ₚ c 12) ^ₚ 3
  have hDisplay : HasPolynomialWorkBound N (fun x => binaryOuterDisplayBound x.m x.m x.outerWidth) :=
    c 52000 *ₚ hm1 *ₚ (hm +ₚ (hB +ₚ (c 10 +ₚ hB)) +ₚ c 2) ^ₚ 3
  have hPre : HasPolynomialWorkBound N (fun x => binaryOuterPreparationBound x.n x.m x.m x.outerWidth) :=
    c 32000 *ₚ hm1 *ₚ hn1 *ₚ hb2 +ₚ c 19000 *ₚ (hPilot +ₚ c 1) ^ₚ 2 *ₚ hn1 *ₚ hb2 +ₚ
      c 6810 *ₚ hb2 +ₚ c 3600 *ₚ hb12 +ₚ c 5 +ₚ hn *ₚ (c 2 *ₚ hm) *ₚ (hDisplay +ₚ c 3)
  have hOuter : HasPolynomialWorkBound N (fun x => binaryOuterStageWorkBound x.n x.m
      (outerMarkBits x.n x.m) x.m x.outerWidth (F x)) :=
    hSlot *ₚ (c 110 *ₚ (hO +ₚ c 2) ^ₚ 3 +ₚ c 3) +ₚ c 2 +ₚ hPre +ₚ c 6810 *ₚ hb2 +ₚ hF +ₚ c 4
  have hOn : HasPolynomialWorkBound N (fun x => binaryOuterOnlineOverhead x.n x.m x.m x.outerWidth) :=
    c 20430 *ₚ hb2 +ₚ c 3600 *ₚ hb12 +ₚ hn1 *ₚ (hDisplay +ₚ c 6) +ₚ c 9
  have hbc := (hClock +ₚ c 2) ^ₚ 3
  have hRank : HasPolynomialWorkBound N (fun x => binaryRankOrderWorkBound x.n x.parameters.clockBits) :=
    hn *ₚ (c 110 *ₚ hbc +ₚ c 3) +ₚ c 2 +ₚ (c 3400 *ₚ hbc +ₚ c 7) *ₚ hn1 ^ₚ 2 +ₚ c 10 *ₚ hn1 ^ₚ 2
  have hCD : HasPolynomialWorkBound N clockDecodeBudget :=
    hm *ₚ (c 2 *ₚ hRank +ₚ c 6) +ₚ hRank +ₚ c 110 *ₚ (hCoin +ₚ c 3) ^ₚ 3 +ₚ c 4 *ₚ hCoin +ₚ c 10
  obtain ⟨C,d,h⟩ := finiteScheduleBounds_polynomial zlo zInv
  have hNP (x : BinaryScheduleInput zlo zInv) : x.n+x.m+2≤N x := by unfold N size; omega
  have hBits : HasPolynomialWorkBound N bitBudget :=
    ⟨C,d,fun x => (h x.parameters x.coefficient_eq x.inverse_eq).1.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hNP x) _))⟩
  have hAlloc : HasPolynomialWorkBound N allocationBudget :=
    ⟨C,d,fun x => (h x.parameters x.coefficient_eq x.inverse_eq).2.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hNP x) _))⟩
  have hAux : HasPolynomialWorkBound N (fun x => rankAuxiliaryBitStorageWork
      x.n x.m x.parameters.clockBits x.parameters.coinBits) :=
    (c 2 *ₚ hm +ₚ c 1) *ₚ (hn *ₚ (c 5 *ₚ hClock +ₚ c 10) +ₚ c 5) +ₚ
      c 10 *ₚ hm1 +ₚ c 5 *ₚ hCoin +ₚ c 15
  exact hOuter +ₚ hn *ₚ (hG +ₚ hOn) +ₚ hCD +ₚ hH +ₚ hBits +ₚ hAlloc +ₚ hAux +ₚ c 2 +ₚ
    c 8 *ₚ (hSlot +ₚ c 1) *ₚ (hO +ₚ c 1) +ₚ c 8 *ₚ hn1 *ₚ (hBudget +ₚ c 1)

end BinaryScheduleInput

end ProphetSecretary.Statistics.Calibration
