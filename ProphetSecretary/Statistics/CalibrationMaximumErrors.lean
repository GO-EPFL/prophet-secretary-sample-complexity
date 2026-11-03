import ProphetSecretary.Statistics.EmpiricalMaximumVariance
import ProphetSecretary.Probability.ScorePayoffComparison

/-!
# Expected-maximum estimation for duration calibration

The product-empirical maximum is unbiased and has variance at most `M/m`.
Cauchy--Schwarz gives its first-moment error, and Chebyshev controls the
small empirical denominator event in `lem:calibration-target`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.empiricalMaximum_L1_error_le (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) :
    (∫ y, |empiricalExpectedMaximum (k := k) y-P.expectedMaximum| ∂P.trainingCoordinateLaw k) ≤
      Real.sqrt (P.expectedMaximum/(k : ℝ)) := by
  have hLP := P.memLp_empiricalExpectedMaximum (k := k) 1 hcap 2
  have hMean := P.integral_empiricalExpectedMaximum (k := k) 1 hcap
  have hVar := P.variance_empiricalExpectedMaximum_le_mean_div_samples (k := k) hcap
  rw [variance_eq_integral measurable_empiricalExpectedMaximum.aemeasurable, hMean] at hVar
  have hAbsVar : (∫ y, |empiricalExpectedMaximum (k := k) y-P.expectedMaximum|^2
      ∂P.trainingCoordinateLaw k) ≤ P.expectedMaximum/(k : ℝ) := by
    simpa only [sq_abs] using hVar
  have h := ProphetSecretary.Probability.abs_integral_le_sqrt_secondMoment (P.trainingCoordinateLaw k)
    (fun y => |empiricalExpectedMaximum (k := k) y-P.expectedMaximum|)
    (hLP.sub (memLp_const P.expectedMaximum)).abs hAbsVar
  rw [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at h
  exact h

lemma Instance.empiricalMaximum_small_probability (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {mu : ℝ} (hmu : 0 < mu)
    (hM : mu ≤ P.expectedMaximum) :
    (P.trainingCoordinateLaw k).real {y | empiricalExpectedMaximum (k := k) y < mu/2} ≤
      4/(mu*(k : ℝ)) := by
  have hMP : 0 < P.expectedMaximum := hmu.trans_le hM
  have hk : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  have hLP := P.memLp_empiricalExpectedMaximum (k := k) 1 hcap 2
  have hMean := P.integral_empiricalExpectedMaximum (k := k) 1 hcap
  have hSub : {y : (Fin n × Fin k) → ℝ | empiricalExpectedMaximum (k := k) y < mu/2} ⊆
      {y | P.expectedMaximum/2 ≤ |empiricalExpectedMaximum (k := k) y -
        (∫ a, empiricalExpectedMaximum (k := k) a ∂P.trainingCoordinateLaw k)|} := by
    intro y hy
    rw [hMean]
    have h := neg_le_abs (empiricalExpectedMaximum (k := k) y-P.expectedMaximum)
    change empiricalExpectedMaximum (k := k) y < mu/2 at hy
    change P.expectedMaximum/2 ≤ |empiricalExpectedMaximum (k := k) y-P.expectedMaximum|
    linarith
  have hCheb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (meas_ge_le_variance_div_sq hLP (div_pos hMP (by norm_num : (0 : ℝ) < 2)))
  have hNonneg : 0 ≤ variance (empiricalExpectedMaximum (k := k)) (P.trainingCoordinateLaw k) /
      (P.expectedMaximum/2)^2 := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hProb : (P.trainingCoordinateLaw k).real {y | empiricalExpectedMaximum (k := k) y < mu/2} ≤
      variance (empiricalExpectedMaximum (k := k)) (P.trainingCoordinateLaw k)/(P.expectedMaximum/2)^2 :=
    (measureReal_mono hSub).trans (by
      simpa only [measureReal_def, ENNReal.toReal_ofReal hNonneg] using hCheb)
  have hVar := P.variance_empiricalExpectedMaximum_le_mean_div_samples (k := k) hcap
  calc
    _ ≤ _ := hProb
    _ ≤ (P.expectedMaximum/(k : ℝ))/(P.expectedMaximum/2)^2 :=
      div_le_div_of_nonneg_right hVar (sq_nonneg _)
    _ = 4/(P.expectedMaximum*(k : ℝ)) := by field_simp [hMP.ne', hk.ne']; ring
    _ ≤ 4/(mu*(k : ℝ)) := div_le_div_of_nonneg_left (by norm_num) (mul_pos hmu hk)
      (mul_le_mul_of_nonneg_right hM hk.le)

end ProphetSecretary.Model
