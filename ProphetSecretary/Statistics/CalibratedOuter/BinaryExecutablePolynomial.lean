import ProphetSecretary.Statistics.CalibratedOuter.BinaryExecutable
import ProphetSecretary.Statistics.CalibratedOuter.BinaryLearnerPolynomial

/-!
# Polynomial cost of executable public setup

The grid has at most (m) subintervals, so its bit computation, the
descriptor repacking, and the public integer scales have a uniform
polynomial bound.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

namespace BinaryScheduleInput

variable {zlo : ℚ} {zInv : ℕ}

noncomputable def executableSetupBudget (x : BinaryScheduleInput zlo zInv) (D : ℕ) : ℕ :=
  FairCalibrationParameters.executablePublicSetupExtraBound x.n x.m x.parameters.grid D+
    binaryPublicIntegersWork x.n x.m zInv

private lemma size_pos' (x : BinaryScheduleInput zlo zInv) : 0<x.size := by
  unfold size
  omega

private lemma addPoly {F G : BinaryScheduleInput zlo zInv → ℕ}
    (hF : HasPolynomialWorkBound size F) (hG : HasPolynomialWorkBound size G) :
    HasPolynomialWorkBound size (fun x => F x+G x) :=
  HasPolynomialWorkBound.add size_pos' hF hG

local infixl:65 " +ₚ " => addPoly
local infixl:70 " *ₚ " => HasPolynomialWorkBound.mul
local infixr:80 " ^ₚ " => HasPolynomialWorkBound.pow

theorem executableSetupBudget_polynomial (D : ℕ) :
    HasPolynomialWorkBound (size (zlo := zlo) (zInv := zInv)) (fun x => x.executableSetupBudget D) := by
  let N := size (zlo := zlo) (zInv := zInv)
  let c := HasPolynomialWorkBound.const N
  have hn : HasPolynomialWorkBound N (fun x => x.n) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hm : HasPolynomialWorkBound N (fun x => x.m) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N size; omega)
  have hJ : HasPolynomialWorkBound N (fun x => x.parameters.grid) :=
    hm.of_le (fun x => familyGridSize_le (by linarith only [x.parameters.coefficient_mem.1]))
  have hA : HasPolynomialWorkBound N (fun x => binaryLearnerAccuracyWidth x.n x.m x.parameters.grid D) :=
    c 150 *ₚ (c D +ₚ hn +ₚ hm +ₚ hJ +ₚ c 20 +ₚ c 1)
  have hI : HasPolynomialWorkBound N (fun x => binaryPublicIntegersWork x.n x.m zInv) :=
    ⟨1000000000000*(zInv+501)^2,2,fun x =>
      (binaryPublicIntegersWork_polynomial x.n x.m zInv).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold N size; omega) _))⟩
  let hB := hm +ₚ c D +ₚ c 2
  have hGrid : HasPolynomialWorkBound N (fun x => binaryPublicGridWork (x.m+D+2)) :=
    c 6 *ₚ (hB +ₚ c 2) +ₚ c 5 *ₚ (c 3600 *ₚ (c 5 *ₚ (hB +ₚ c 1) +ₚ c 2) ^ₚ 3 +ₚ c 1) +ₚ
      c 60 *ₚ (c 5 *ₚ (hB +ₚ c 1) +ₚ c 3) ^ₚ 2 +ₚ c 3
  exact hGrid +ₚ c 60 *ₚ (hA +ₚ c 3) ^ₚ 2 +ₚ c 8 +ₚ hI

theorem executableBinaryWorkBudget_polynomial (D : ℕ) :
    HasPolynomialWorkBound (size (zlo := zlo) (zInv := zInv))
      (fun x => x.workBudget (x.boundedPrepareBudget D) (x.boundedOnlineBudget D)
        (2*x.publicStartupBudget D)+2*x.executableSetupBudget D) :=
  actualWorkBudget_polynomial D +ₚ HasPolynomialWorkBound.const size 2 *ₚ executableSetupBudget_polynomial D

end BinaryScheduleInput
end ProphetSecretary.Statistics.Calibration
