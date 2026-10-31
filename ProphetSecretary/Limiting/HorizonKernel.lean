import ProphetSecretary.Model.Instance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# An integrable remaining-horizon envelope

The inverse square root of remaining time has integral two. This auxiliary
bound is sufficient for convergence of finite Bernoulli potentials; it does
not assert the sharper pi-over-two constant in the manuscript's comparison.
-/

open MeasureTheory Set

namespace ProphetSecretary.Limiting

noncomputable def remainingSqrtEnvelope (t : ℝ) : ℝ := 1 / Real.sqrt (1 - t)

lemma remainingSqrtEnvelope_eq_rpow {t : ℝ} (ht : t ≤ 1) :
    remainingSqrtEnvelope t = (1 - t) ^ (-(1 / 2 : ℝ)) := by
  rw [remainingSqrtEnvelope, one_div, Real.sqrt_eq_rpow, Real.rpow_neg (sub_nonneg.mpr ht)]

lemma remainingSqrtEnvelope_integrable : Integrable remainingSqrtEnvelope Model.Instance.uniformClock := by
  have hr : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hc := (hr.comp_sub_left 1).symm
  simp only [sub_zero, sub_self] at hc
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mp hc
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (remainingSqrtEnvelope_eq_rpow ht.2).symm

lemma integral_remainingSqrtEnvelope : (∫ t, remainingSqrtEnvelope t ∂Model.Instance.uniformClock) = 2 := by
  have he : remainingSqrtEnvelope =ᵐ[Model.Instance.uniformClock] (fun t => (1 - t) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact remainingSqrtEnvelope_eq_rpow ht.2
  rw [integral_congr_ae he, Model.Instance.uniformClock, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1]
  norm_num [integral_rpow (Or.inl (show (-1 : ℝ) < -(1 / 2 : ℝ) by norm_num))]

lemma sqrt_timeRatio_le_envelope {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.sqrt (t / (1 - t)) ≤ remainingSqrtEnvelope t := by
  rw [Real.sqrt_div ht0, remainingSqrtEnvelope]
  exact div_le_div_of_nonneg_right ((Real.sqrt_le_one).mpr ht1.le) (Real.sqrt_nonneg _)

end ProphetSecretary.Limiting
