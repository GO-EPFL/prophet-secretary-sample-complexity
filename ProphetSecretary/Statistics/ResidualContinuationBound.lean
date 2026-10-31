import ProphetSecretary.Statistics.ResidualFutureSuffix
import ProphetSecretary.Model.FirstArrivalIntegral

/-!
# Value comparison after a fixed observed prefix

The complete-path residual envelope controls every continuation value error.
The future clocks are an actual independent uniform product; restriction to the
unseen identities is measure preserving. Prefix observations, including zeros,
are retained in the extended execution.
-/

open MeasureTheory Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.residualSuffixEnvelope_le_firstMoments (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (u : Fin n → ℝ) :
    Q.residualSuffixEnvelope P w c u ≤ w * (Q.totalFirstMoment + P.totalFirstMoment) := by
  apply (ProphetSecretary.Statistics.suffixEnvelope_le_sum_abs _ _).trans
  calc
    (∑ i, |Q.transitionResidual P w c u i|) ≤
        ∑ i, w * ((∫ x, x ∂Q.law i) + ∫ x, x ∂P.law i) :=
      Finset.sum_le_sum fun i _ => Q.abs_transitionResidual_le P hQ hP hw hc u i
    _ = _ := by simp only [Instance.totalFirstMoment, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma Instance.integrable_residualSuffixEnvelope_comp {Ω : Type*} [MeasurableSpace Ω]
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → Fin n → ℝ) (hf : Measurable f) :
    Integrable (fun v => Q.residualSuffixEnvelope P w c (f v)) μ := by
  apply Integrable.of_bound ((Q.measurable_residualSuffixEnvelope P hQ hP hw hc).comp hf).aestronglyMeasurable
    (w * (Q.totalFirstMoment + P.totalFirstMoment))
  exact Eventually.of_forall fun v => by
    change ‖Q.residualSuffixEnvelope P w c (f v)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Q.residualSuffixEnvelope P w c (f v) from
      ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)]
    exact Q.residualSuffixEnvelope_le_firstMoments P hQ hP hw.le hc (f v)

/-- An unrestricted continuation value difference is controlled by averaging
one original complete-path envelope over fresh normalized future clocks. -/
theorem Instance.abs_continuationValue_difference_le_extendedEnvelope (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (A : Finset (Fin n)) {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    |Q.continuationValue A (1-s) w c - P.continuationValue A (1-s) w c| ≤
      2 * ∫ v : Fin n → ℝ,
        Q.residualSuffixEnvelope P w c (extendClocks A s H (v ∘ stateEmbedding A)) ∂Instance.clocksLaw n := by
  have hQA := Q.restrictTo_integrable_maximum A hQ
  have hPA := P.restrictTo_integrable_maximum A hP
  have hcu : 0 ≤ c * (1-s) := mul_nonneg hc (sub_nonneg.mpr hs.le)
  have hb := (Q.restrictTo A).abs_value_difference_le_residualSuffix (P.restrictTo A) hQA hPA hw hcu
  have hp := Instance.restrictClocks_measurePreserving (stateEmbedding A)
  have hmean := integral_map (μ := Instance.clocksLaw n) hp.measurable.aemeasurable
    ((Q.restrictTo A).measurable_residualSuffixEnvelope (P.restrictTo A) hQA hPA hw hcu).aestronglyMeasurable
  rw [hp.map_eq] at hmean
  have hL : Integrable (fun v : Fin n → ℝ =>
      (Q.restrictTo A).residualSuffixEnvelope (P.restrictTo A) w (c*(1-s)) (v ∘ stateEmbedding A))
      (Instance.clocksLaw n) := hp.integrable_comp_of_integrable
        ((Q.restrictTo A).integrable_residualSuffixEnvelope (P.restrictTo A) hQA hPA hw hcu)
  have hR : Integrable (fun v : Fin n → ℝ =>
      Q.residualSuffixEnvelope P w c (extendClocks A s H (v ∘ stateEmbedding A))) (Instance.clocksLaw n) :=
    Q.integrable_residualSuffixEnvelope_comp P hQ hP hw hc _ _ (by
      apply measurable_pi_lambda
      intro i
      by_cases hi : i ∈ A
      · simp only [extendClocks, dif_pos hi, Function.comp_apply]
        fun_prop
      · simp only [extendClocks, dif_neg hi]
        exact measurable_const)
  have hineq := integral_mono_ae hL hR (by
    filter_upwards [Instance.clocks_positive (m := n)] with v hv
    exact Q.residualSuffixEnvelope_continuation_le P hQ A hs H hH hw hc
      (v ∘ stateEmbedding A) (fun j => hv _))
  change (∫ v, (Q.restrictTo A).residualSuffixEnvelope (P.restrictTo A) w (c*(1-s)) v
    ∂Instance.clocksLaw A.card) = _ at hmean
  rw [← hmean] at hineq
  exact hb.trans (mul_le_mul_of_nonneg_left hineq (by norm_num))

end ProphetSecretary.Model
