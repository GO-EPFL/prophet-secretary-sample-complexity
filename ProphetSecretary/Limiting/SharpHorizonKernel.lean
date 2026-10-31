import ProphetSecretary.Limiting.HorizonKernel
import ProphetSecretary.Limiting.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The sharp integrated uniform-clock hazard constant

The primitive arcsin(√t)−√(t(1−t)) evaluates the integrable singular kernel
√(t/(1−t)) on [0,1]. Its endpoint difference is π/2, the constant in
`eq:tail-residual` and `lem:causal-poisson`.
-/

open MeasureTheory Set

namespace ProphetSecretary.Limiting

noncomputable def timeRatioKernel (t : ℝ) : ℝ := Real.sqrt (t / (1 - t))

lemma timeRatioKernel_integrable : Integrable timeRatioKernel Model.Instance.uniformClock := by
  have hm : Measurable timeRatioKernel := by unfold timeRatioKernel; fun_prop
  apply remainingSqrtEnvelope_integrable.mono' hm.aestronglyMeasurable
  filter_upwards [uniformClock_mem_Ioo] with t ht
  change ‖Real.sqrt (t / (1 - t))‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_timeRatio_le_envelope ht.1.le ht.2

lemma timeRatioKernel_primitive_deriv {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => Real.arcsin (Real.sqrt s) - Real.sqrt (s * (1 - s)))
      (timeRatioKernel t) t := by
  have hrem : 0 < 1 - t := by linarith [ht.2]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 hrem
  have hs1 : Real.sqrt t < 1 := by nlinarith [Real.sq_sqrt ht.1.le, ht.2]
  have hsq := Real.hasDerivAt_sqrt ht.1.ne'
  have harc := (Real.hasDerivAt_arcsin (by linarith : Real.sqrt t ≠ -1) (ne_of_lt hs1)).comp t hsq
  have hprod := (hasDerivAt_id t).mul ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  have hroot := (Real.hasDerivAt_sqrt (mul_pos ht.1 hrem).ne').comp t hprod
  have hd := harc.sub hroot
  have heq : 1 / Real.sqrt (1 - Real.sqrt t ^ 2) * (1 / (2 * Real.sqrt t)) -
      1 / (2 * Real.sqrt (t * (1 - t))) * (1 * (1 - t) + t * (0 - 1)) = timeRatioKernel t := by
    rw [Real.sq_sqrt ht.1.le, Real.sqrt_mul ht.1.le]
    unfold timeRatioKernel
    rw [Real.sqrt_div ht.1.le]
    field_simp
    nlinarith [Real.sq_sqrt ht.1.le]
  rw [← heq]
  exact hd

lemma integral_timeRatioKernel :
    (∫ t, timeRatioKernel t ∂Model.Instance.uniformClock) = Real.pi / 2 := by
  have hi : IntervalIntegrable timeRatioKernel volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mpr timeRatioKernel_integrable
  have hcont : ContinuousOn (fun s : ℝ => Real.arcsin (Real.sqrt s) - Real.sqrt (s * (1 - s))) (Icc 0 1) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.arcsin (Real.sqrt s) - Real.sqrt (s * (1 - s)))).continuousOn
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (0 : ℝ) ≤ 1 by norm_num)
    hcont (fun t ht => timeRatioKernel_primitive_deriv ht) hi
  rw [Model.Instance.uniformClock, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simpa only [Real.sqrt_one, Real.arcsin_one, sub_self, mul_zero, Real.sqrt_zero,
    sub_zero, zero_mul, Real.arcsin_zero] using h

end ProphetSecretary.Limiting
