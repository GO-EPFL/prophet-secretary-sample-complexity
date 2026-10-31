import ProphetSecretary.Model.UnitScalarGap
import ProphetSecretary.Model.MidpointRegret
import ProphetSecretary.Model.NumericalCompetitiveBound

/-!
# Unconditional lower-endpoint comparison for small-mean instances

For cap-one instances with M≤1/80, regret at 4/5 forces large duration. The
resulting fixed-policy gap bound is the lower-endpoint ingredient of
`cor:small-mean-clamp`. It uses the internally proved global constant bound.
No reward-boundary slack or upper projection endpoint is supplied here.
-/

open MeasureTheory Set
namespace ProphetSecretary.Model
variable {n : ℕ}

/-- The waiting policy and the true regret at 4/5 force duration at least
19/20−5r, for every admissible randomized competing policy. -/
lemma RandomizedPolicy.duration_ge_of_smallMean_endpoint_regret (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80) {r : ℝ}
    (hr : π.normalizedRegret P (4/5)≤r) : 19/20-5*r≤π.expectedDuration P := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hWait := durationWeight_le_optimalScalarValue P hP (w:=(4/5:ℝ)) (c:=(1-4/5:ℝ)) (by norm_num) (by norm_num)
  have hR := π.expectedReward_le_maximum P hP
  unfold RandomizedPolicy.normalizedRegret at hr
  rw [π.scalarObjective_eq P hP] at hr
  nlinarith only [hr,hWait,hR,hM]

/-- Source lower-endpoint constant 13/400. Boundary slack is not needed for this
finite statement, and the policy class remains unrestricted. -/
theorem RandomizedPolicy.smallMean_lowerClamp_comparison (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80) {lam r : ℝ}
    (hlam : lam∈Icc (0:ℝ) (4/5)) (hr : π.normalizedRegret P (4/5)≤r) :
    13/400-5*r≤π.scalarObjective P lam (1-lam)-
      optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam) := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hT := π.duration_ge_of_smallMean_endpoint_regret P hcap hM hr
  have hR0 := π.expectedReward_nonnegative P
  have hr0 : 0≤r := (π.normalizedRegret_nonnegative P hP (show (4/5:ℝ)∈Icc 0 1 by norm_num)).trans hr
  have hC : optimalCompetitiveRatio≤3/4 := by
    linarith only [optimalCompetitiveRatio_le_seventyThreeHundredths]
  have hCM : optimalCompetitiveRatio*P.expectedMaximum≤3/320 := by
    have h := mul_le_mul hC hM P.expectedMaximum_nonnegative (by norm_num : (0:ℝ)≤3/4)
    norm_num at h ⊢
    exact h
  have hTime : 0≤1-lam := by linarith only [hlam.2]
  have hTw := mul_le_mul_of_nonneg_left hT hTime
  have hRw := mul_nonneg hlam.1 hR0
  have hrw := mul_nonneg hlam.1 hr0
  have hCMw := mul_le_mul_of_nonneg_left hCM hlam.1
  have hCw := mul_le_mul_of_nonneg_left (show (1/5:ℝ)≤19/20-optimalCompetitiveRatio by linarith only [hC]) hTime
  rw [π.scalarObjective_eq P hP]
  nlinarith only [hTw,hRw,hrw,hCMw,hCw,hlam.2]

/-- The source F(lambda)/40 comparison follows from the already proved unit gap
bound. Paper correspondence: the lower-target estimate in `cor:small-mean-clamp`. -/
theorem RandomizedPolicy.smallMean_lowerClamp_gap (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80) {lam r : ℝ}
    (hlam : lam∈Icc (0:ℝ) (4/5)) (hr : π.normalizedRegret P (4/5)≤r) :
    normalizedScalarGap P lam/40-5*r≤π.scalarObjective P lam (1-lam)-
      optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam) := by
  have h := π.smallMean_lowerClamp_comparison P hcap hM hlam hr
  have hF := (P.normalizedScalarGap_mem_unit hcap (show lam∈Icc (0:ℝ) 1 from ⟨hlam.1,by linarith only [hlam.2]⟩)).2
  linarith only [h,hF]

end ProphetSecretary.Model
