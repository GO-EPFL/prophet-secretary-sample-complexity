import ProphetSecretary.Limiting.HazardFluctuation
import ProphetSecretary.Limiting.HorizonKernel

/-!
# Integrated unseen-clock intensity error

Fixed weights produce an integrable joint error, even at the terminal horizon.
The bound depends only on their square sum and remains uniform in the number
of individual distributions.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {N : ℕ}

lemma measurable_tailHazardError (a : Fin N → ℝ) :
    Measurable (fun q : ℝ × (Fin N → ℝ) => tailHazardError a q.1 q.2) := by
  have hs : Measurable (fun q : ℝ × (Fin N → ℝ) => ∑ i, if q.1 < q.2 i then a i else 0) := by
    apply Finset.measurable_fun_sum
    intro i _
    exact Measurable.ite (measurableSet_lt measurable_fst ((measurable_pi_apply i).comp measurable_snd))
      measurable_const measurable_const
  exact (hs.div (measurable_const.sub measurable_fst)).sub measurable_const

lemma integrable_abs_tailHazardError (a : Fin N → ℝ) (t : ℝ) :
    Integrable (fun u => |tailHazardError a t u|) (Model.Instance.clocksLaw N) := by
  have hs : Integrable (fun u : Fin N → ℝ => ∑ i, if t < u i then a i else 0) (Model.Instance.clocksLaw N) := by
    apply integrable_finsetSum
    intro i _
    apply Integrable.of_bound (Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
      measurable_const measurable_const).aestronglyMeasurable |a i|
    exact Filter.Eventually.of_forall (fun u => by split_ifs <;> simp)
  exact ((hs.div_const (1 - t)).sub (integrable_const _)).abs

lemma integrable_mean_abs_tailHazardError (a : Fin N → ℝ) :
    Integrable (fun t => ∫ u, |tailHazardError a t u| ∂Model.Instance.clocksLaw N) Model.Instance.uniformClock := by
  have hsm : StronglyMeasurable (fun q : ℝ × (Fin N → ℝ) => |tailHazardError a q.1 q.2|) :=
    (continuous_abs.measurable.comp (measurable_tailHazardError a)).stronglyMeasurable
  have hm : StronglyMeasurable (fun t => ∫ u, |tailHazardError a t u| ∂Model.Instance.clocksLaw N) :=
    hsm.integral_prod_right' 
  apply ((remainingSqrtEnvelope_integrable.const_mul (Real.sqrt (∑ i, (a i) ^ 2)))).mono' hm.aestronglyMeasurable
  filter_upwards [uniformClock_mem_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
  exact (tailHazardError_absoluteMean_le a ht.1.le ht.2).trans
    ((mul_le_mul_of_nonneg_right (sqrt_timeRatio_le_envelope ht.1.le ht.2) (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _))

lemma integral_mean_abs_tailHazardError_le (a : Fin N → ℝ) :
    (∫ t, ∫ u, |tailHazardError a t u| ∂Model.Instance.clocksLaw N ∂Model.Instance.uniformClock) ≤
      2 * Real.sqrt (∑ i, (a i) ^ 2) := by
  have h := integral_mono_ae (integrable_mean_abs_tailHazardError a)
    (remainingSqrtEnvelope_integrable.const_mul (Real.sqrt (∑ i, (a i) ^ 2)))
    (Filter.Eventually.mono uniformClock_mem_Ioo (fun t ht =>
      (tailHazardError_absoluteMean_le a ht.1.le ht.2).trans
        ((mul_le_mul_of_nonneg_right (sqrt_timeRatio_le_envelope ht.1.le ht.2) (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _))))
  rw [integral_const_mul, integral_remainingSqrtEnvelope] at h
  simpa only [mul_comm] using h

lemma integrable_tailHazardError_product (a : Fin N → ℝ) :
    Integrable (fun q : ℝ × (Fin N → ℝ) => |tailHazardError a q.1 q.2|)
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) := by
  have hm : Measurable (fun q : ℝ × (Fin N → ℝ) => |tailHazardError a q.1 q.2|) :=
    continuous_abs.measurable.comp (measurable_tailHazardError a)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (integrable_abs_tailHazardError a)
  · simpa only [Real.norm_eq_abs, abs_abs] using integrable_mean_abs_tailHazardError a

lemma mean_integral_abs_tailHazardError_le (a : Fin N → ℝ) :
    (∫ u, ∫ t, |tailHazardError a t u| ∂Model.Instance.uniformClock ∂Model.Instance.clocksLaw N) ≤
      2 * Real.sqrt (∑ i, (a i) ^ 2) := by
  rw [← integral_prod_symm _ (integrable_tailHazardError_product a),
    integral_prod _ (integrable_tailHazardError_product a)]
  exact integral_mean_abs_tailHazardError_le a

end ProphetSecretary.Limiting
