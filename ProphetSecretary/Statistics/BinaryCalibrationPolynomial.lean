import ProphetSecretary.Statistics.BinaryCalibrationPrepare
import ProphetSecretary.Analysis.PolynomialWorkBound

/-!
# Composing binary calibration cost bounds

Query work and operand widths enter as separate parameters. The explicit
stage formulas combine their polynomial bounds by sums and products.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

variable {α : Type*} {N : α → ℕ}

private lemma add_bound {F G : α → ℕ} [Fact (∀ x, 0<N x)]
    (hF : HasPolynomialWorkBound N F) (hG : HasPolynomialWorkBound N G) :
    HasPolynomialWorkBound N (fun x => F x+G x) :=
  HasPolynomialWorkBound.add Fact.out hF hG

local infixl:65 " +ₚ " => add_bound
local infixl:70 " *ₚ " => HasPolynomialWorkBound.mul
local infixr:80 " ^ₚ " => HasPolynomialWorkBound.pow

theorem binaryCalibrationBudgets_polynomial (hN : ∀ x, 0<N x)
    {n m J Y P B E WT WP : α → ℕ}
    (hn : HasPolynomialWorkBound N n) (hm : HasPolynomialWorkBound N m)
    (hJ : HasPolynomialWorkBound N J) (hY : HasPolynomialWorkBound N Y)
    (hP : HasPolynomialWorkBound N P) (hB : HasPolynomialWorkBound N B)
    (hE : HasPolynomialWorkBound N E) (hWT : HasPolynomialWorkBound N WT)
    (hWP : HasPolynomialWorkBound N WP) :
    HasPolynomialWorkBound N (fun x => binaryCalibrationPrepareWork
      (n x) (m x) (J x) (Y x) (P x) (B x) (E x) (WT x) (WP x)) ∧
    HasPolynomialWorkBound N (fun x => binaryCalibrationOnlineWork
      (n x) (J x) (B x) (E x) (WP x)) := by
  letI : Fact (∀ x, 0<N x) := ⟨hN⟩
  let c := HasPolynomialWorkBound.const N
  let op {D : α → ℕ} (hD : HasPolynomialWorkBound N D) :
      HasPolynomialWorkBound N (fun x => 3600*(D x+2)^3) :=
    c 3600 *ₚ (hD +ₚ c 2) ^ₚ 3
  let cmp {D : α → ℕ} (hD : HasPolynomialWorkBound N D) :
      HasPolynomialWorkBound N (fun x => calibrationComparisonWork (D x)) :=
    c 6800 *ₚ (hD +ₚ c 2) ^ₚ 3 +ₚ c 2
  let field {D : α → ℕ} (hD : HasPolynomialWorkBound N D) :
      HasPolynomialWorkBound N (fun x => calibrationFieldWork (D x)) :=
    cmp hD +ₚ op hD +ₚ c 4
  let unit {L D : α → ℕ} (hL : HasPolynomialWorkBound N L) (hD : HasPolynomialWorkBound N D) :
      HasPolynomialWorkBound N (fun x => CalibrationBinaryExpr.workUnit (L x) (D x)) :=
    op (hL *ₚ (hD +ₚ c 1)) +ₚ c 1
  have hn1 := hn +ₚ c 1
  have hm1 := hm +ₚ c 1
  have hJ1 := hJ +ₚ c 1
  have hNM := hn *ₚ hm
  have hTrainWidth : HasPolynomialWorkBound N (fun x => binaryEmpiricalMaximumWidth (n x) (n x*m x) (Y x) (P x)) :=
    hY +ₚ hP +ₚ c 4 *ₚ hP *ₚ hn +ₚ (hNM +ₚ c 2) *ₚ (hY +ₚ c 4 *ₚ hP *ₚ hn +ₚ c 2) +ₚ c 2
  have hMaximum : HasPolynomialWorkBound N (fun x => binaryEmpiricalMaximumWork (n x) (n x*m x) (Y x) (P x)) :=
    c 1 +ₚ c 2 *ₚ hn +ₚ c 2 *ₚ hNM +ₚ (c 1 +ₚ hNM *ₚ (cmp hTrainWidth +ₚ c 2)) +ₚ
      (hNM +ₚ c 2) ^ₚ 2 *ₚ (cmp hTrainWidth +ₚ c 4) +ₚ c 2 +ₚ
      (c 1 +ₚ (hNM +ₚ c 1) *ₚ (c 16 *ₚ (hn +ₚ hNM +ₚ c 1) +ₚ c 8) *ₚ field hTrainWidth) +ₚ c 1
  have hStats : HasPolynomialWorkBound N (fun x => binaryTrainingStatisticsWork (n x) (m x) (Y x) (P x)) :=
    hMaximum +ₚ (c 2 *ₚ hn +ₚ c 1) *ₚ unit (c 2 *ₚ hn +ₚ c 1) (c 3 *ₚ hP +ₚ c 1) +ₚ
      hn *ₚ (hm1 *ₚ c 12 *ₚ field (c 2 *ₚ (hY +ₚ hP) +ₚ c 1) +ₚ c 2) +ₚ
      hn *ₚ (cmp (c 3 *ₚ hP +ₚ c 1) +ₚ c 2) +ₚ c 6 *ₚ hn1 *ₚ hm1
  have hW := c 3 *ₚ (hB +ₚ c 1) +ₚ c 3
  have hCount := c 4 *ₚ hm +ₚ c 1
  have hPublic : HasPolynomialWorkBound N (fun x => binaryCalibrationPublicWork (m x) (J x) (B x)) :=
    c 3 *ₚ hW +ₚ c 2 *ₚ op hB +ₚ c 4 *ₚ (hB +ₚ c 1) +ₚ
      hCount *ₚ (hW +ₚ op hB +ₚ c 2) +ₚ hJ1 *ₚ (hW +ₚ c 9 *ₚ unit (c 9) hB +ₚ c 2) +ₚ c 10
  have hA := c 7 *ₚ (hB +ₚ c 1)
  have hTarget : HasPolynomialWorkBound N (fun x => binaryTargetScanWork (4*m x+1) (B x) (WT x)) :=
    c 2 +ₚ hCount *ₚ (hWT +ₚ c 7 *ₚ unit (c 7) hB +ₚ c 1 +ₚ op hA +ₚ c 2) +ₚ op hA
  have hAccept : HasPolynomialWorkBound N (fun x => binaryRankAcceptWork (B x)) :=
    c 3 *ₚ cmp (c 11 *ₚ (hB +ₚ c 1)) +ₚ c 11 *ₚ unit (c 11) hB +ₚ c 5
  have hValidation : HasPolynomialWorkBound N (fun x => binaryCalibrationValidationWork (n x) (J x) (B x) (E x) (WP x)) :=
    hn *ₚ (hn +ₚ c 7 *ₚ unit (c 7) hB +ₚ hJ1 *ₚ (hWP +ₚ op hE +ₚ c 3) +ₚ c 6) +ₚ
      hJ1 *ₚ (c 3 +ₚ hn *ₚ (hAccept +ₚ c 2)) +ₚ c 2
  have hU := (c 2 *ₚ hm +ₚ c 3) *ₚ (hA +ₚ c 1)
  have hV := c 7 *ₚ (hU +ₚ c 1)
  have hKnot : HasPolynomialWorkBound N (fun x => binaryCalibrationKnotWork (m x) (7*(B x+1))) :=
    (c 2 *ₚ hm +ₚ c 3) *ₚ unit (c 2 *ₚ hm +ₚ c 3) hA +ₚ c 2 *ₚ hm +ₚ c 3
  have hSelect : HasPolynomialWorkBound N (fun x => binaryCalibrationSelectionWork (m x) (J x) (7*(B x+1))) :=
    (hJ +ₚ c 3) *ₚ (hKnot +ₚ c 2) +ₚ c 1 +ₚ
      (c 1 +ₚ (hJ +ₚ c 2) *ₚ (cmp hU +ₚ c 4)) +ₚ c 7 *ₚ unit (c 7) hU +ₚ
      (op hV +ₚ c 60 *ₚ (c 2 *ₚ hV +ₚ c 2) ^ₚ 2 +ₚ
        c 2 *ₚ (c 16 *ₚ (c 2 *ₚ hV +ₚ c 1) +ₚ c 12) +ₚ c 4) +ₚ c 8
  have hOnlineA := c 11 *ₚ (hB +ₚ hE +ₚ c 1)
  exact ⟨hPublic +ₚ hStats +ₚ (c 2 *ₚ cmp hB +ₚ c 2) +ₚ
      (c 2 *ₚ cmp hB +ₚ hTarget +ₚ c 3) +ₚ hm *ₚ (hValidation +ₚ c 2) +ₚ hSelect +ₚ c 8,
    c 3 *ₚ cmp hOnlineA +ₚ hn *ₚ c 4 +ₚ c 7 *ₚ unit (c 7) hB +ₚ
      hJ1 *ₚ (hWP +ₚ op hE +ₚ c 2) +ₚ c 2 *ₚ op hOnlineA +ₚ c 13⟩

end ProphetSecretary.Statistics.Calibration
