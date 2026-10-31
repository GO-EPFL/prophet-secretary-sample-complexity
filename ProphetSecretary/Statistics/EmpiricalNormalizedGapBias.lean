import ProphetSecretary.Statistics.EmpiricalGapMoments
import ProphetSecretary.Statistics.EmpiricalOptimismRate

/-!
# Fixed-weight upward bias for the normalized empirical gap

The expected empirical maximum is exactly unbiased. Homogeneity converts the
proved scalar-value upward bias to normalized reward/duration coefficients.
The weight a is deterministic; the statement never centers a selected weight.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.empiricalNormalizedGap_bias (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {δ a : ℝ} (hδ : 0 < δ)
    (ha : a∈Icc δ (1-δ)) :
    0 ≤ (∫ y, normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a
        ∂P.trainingCoordinateLaw k)-normalizedScalarGap P a ∧
    (∫ y, normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a
        ∂P.trainingCoordinateLaw k)-normalizedScalarGap P a ≤
      empiricalCandidateRegretConstant δ δ⁻¹*P.totalFirstMoment*(1+P.totalFirstMoment)/(k : ℝ) := by
  let z := (1-a)/a
  have haP : 0 < a := hδ.trans_le ha.1
  have ha1 : a ≤ 1 := by linarith only [ha.2,hδ]
  have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr ha1) haP.le
  have haz : a*z = 1-a := by dsimp only [z]; field_simp [haP.ne']
  have hd1 : δ ≤ 1 := ha.1.trans ha1
  have hdhi : δ ≤ δ⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [hδ,hd1]
  have hz : z∈Icc δ δ⁻¹ := by
    constructor
    · apply (le_div_iff₀ haP).mpr
      have h := mul_le_mul_of_nonneg_left ha1 hδ.le
      linarith only [h,ha.2]
    · apply (div_le_iff₀ haP).mpr
      have h := mul_le_mul_of_nonneg_left ha.1 (inv_nonneg.mpr hδ.le)
      rw [inv_mul_cancel₀ hδ.ne'] at h
      linarith only [h,haP]
  let V := fun y : (Fin n × Fin k) → ℝ =>
    optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm y)) 1 z
  have hVI : Integrable V (P.trainingCoordinateLaw k) := integrable_empiricalScalarValue_unit P hcap hz0
  have hP := P.integrable_maximum_of_bounded hcap
  have hScale (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw) :
      optimalScalarValue Q a (1-a) = a*optimalScalarValue Q 1 z := by
    have h := optimalScalarValue_smul Q hQ haP.le zero_le_one hz0
    simpa only [mul_one,haz] using h
  have hMean : (∫ y, normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a
      ∂P.trainingCoordinateLaw k)-normalizedScalarGap P a =
      a*((∫ y, V y ∂P.trainingCoordinateLaw k)-optimalScalarValue P 1 z) := by
    have hExpr (y : (Fin n × Fin k) → ℝ) :
        normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a =
          a*V y-optimalCompetitiveRatio*(a*empiricalExpectedMaximum y+(1-a)) := by
      unfold normalizedScalarGap scalarGap
      rw [hScale _ (totalEmpiricalInstance_integrable _)]
      rfl
    have hMInt := (P.memLp_empiricalExpectedMaximum (k := k) 1 hcap 1).integrable (by norm_num)
    have hBInt : Integrable (fun y => optimalCompetitiveRatio*(a*empiricalExpectedMaximum y+(1-a)))
        (P.trainingCoordinateLaw k) := ((hMInt.const_mul a).add (integrable_const (1-a))).const_mul _
    simp_rw [hExpr]
    rw [integral_sub (hVI.const_mul a) hBInt,integral_const_mul,integral_const_mul,
      integral_add (hMInt.const_mul a) (integrable_const (1-a)),integral_const_mul,
      P.integral_empiricalExpectedMaximum 1 hcap]
    simp only [integral_const,probReal_univ,one_smul]
    unfold normalizedScalarGap scalarGap
    rw [hScale P hP]
    ring
  rw [hMean]
  have hBias := empiricalScalarValue_expected_optimism_bound (k := k) P hcap hδ hdhi hz
  have hNonnegative := mul_nonneg haP.le hBias.1
  refine ⟨hNonnegative,?_⟩
  calc
    _ ≤ (∫ y, V y ∂P.trainingCoordinateLaw k)-optimalScalarValue P 1 z :=
      mul_le_of_le_one_left hBias.1 ha1
    _ ≤ _ := hBias.2

end ProphetSecretary.Model
