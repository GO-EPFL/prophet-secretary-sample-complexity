import ProphetSecretary.Limiting.CountableMaskTail
import ProphetSecretary.Limiting.CountableValueLimit
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform approximation of actual remaining-state scalar values

The omitted individual maximum is bounded by that of the original unmasked
instance. Consequently one retained-prefix/cutoff error controls every mask
and remaining horizon, including zero horizon and zero anonymous intensity.
Masks are deterministic arguments here; this does not assert a conditional
product-law statement at an observation-dependent random mask.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

lemma remainingState_truncation_value_error_le (B : CountableInstance) (keep : IndividualMask) (u : ℝ≥0)
    (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b) {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    |((B.remainingState keep u).truncation N b hb).optimalScalarValue w d-
      (B.remainingState keep u).optimalScalarValue w d| ≤
        w*(B.expectedIndividualTailExcessMaximum N+(b-(B.terminal : ℝ))) := by
  have h := (B.remainingState keep u).truncation_value_error_le N hb hw hd
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (B.expectedIndividualTailExcessMaximum_remainingState_le keep u N) le_rfl) hw)

noncomputable def continuationValue (B : CountableInstance) (keep : IndividualMask) (w c : ℝ) (u : ℝ≥0) : ℝ :=
  (B.remainingState keep u).optimalScalarValue w (c*(u : ℝ))

noncomputable def truncatedContinuationValue (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (keep : IndividualMask) (w c : ℝ) (u : ℝ≥0) : ℝ :=
  ((B.remainingState keep u).truncation N b hb).optimalScalarValue w (c*(u : ℝ))

lemma truncatedContinuationValue_error_le (B : CountableInstance) (N : ℕ) {b : ℝ}
    (hb : (B.terminal : ℝ) < b) (keep : IndividualMask) (u : ℝ≥0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |B.truncatedContinuationValue N b hb keep w c u-B.continuationValue keep w c u| ≤
      w*(B.expectedIndividualTailExcessMaximum N+(b-(B.terminal : ℝ))) :=
  B.remainingState_truncation_value_error_le keep u N hb hw (mul_nonneg hc u.property)

lemma truncatedContinuationValue_uniform_limit (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    TendstoUniformly (fun N (z : IndividualMask × ℝ≥0) =>
      B.truncatedContinuationValue N (B.markCutoff N) (B.terminal_lt_markCutoff N) z.1 w c z.2)
      (fun z => B.continuationValue z.1 w c z.2) atTop := by
  have hWidth : Tendsto (fun N => B.markCutoff N-(B.terminal : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using B.markCutoff_tendsto.sub_const (B.terminal : ℝ)
  have hError : Tendsto (fun N => w*(B.expectedIndividualTailExcessMaximum N+
      (B.markCutoff N-(B.terminal : ℝ)))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero,mul_zero] using (B.expectedIndividualTailExcessMaximum_tendsto.add hWidth).const_mul w
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hError).2 ε hε] with N hN
  intro z
  rw [dist_comm,Real.dist_eq]
  exact (B.truncatedContinuationValue_error_le (N := N) (B.terminal_lt_markCutoff N) z.1 z.2 hw hc).trans_lt hN

end ProphetSecretary.Limiting.CountableInstance
