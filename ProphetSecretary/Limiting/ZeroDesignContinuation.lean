import ProphetSecretary.Limiting.BernoulliClockPremium
import ProphetSecretary.Model.ZeroVariableValue

/-!
# A zero design identity has no effect on continuation value

This equality is about optimal values under a zero design marginal; it does
not erase the corresponding observed identity from a competing execution.
It is what lets the original rare-offer generator use a common current-state
premium in the causal Poisson comparison.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma zero_design_childContinuation_eq_current (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (i : Fin n)
    (hi : Q.law i = Measure.dirac 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (t : ℝ) :
    Q.continuationAtArrival w c (fun _ => 0) (Function.update u i t) i =
      poissonContinuation Q w c u t := by
  have h := Q.optimalScalarValue_restrictTo_erase_zero
    (Model.unseen (Model.history Finset.univ (fun _ => 0) u t)) i hQ hi hw
      (mul_nonneg hc (le_max_left 0 (1 - t)))
  unfold Model.Instance.continuationAtArrival
  rw [Function.update_self, unseen_updated_clock_erase]
  exact h.symm

lemma zero_design_lawResidual_eq_negative_currentPremium (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (i : Fin n)
    (hi : Q.law i = Measure.dirac 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (t : ℝ) :
    Q.lawResidual P i w (Q.continuationAtArrival w c (fun _ => 0) (Function.update u i t) i) =
      -Model.positivePremium (P.law i) w (poissonContinuation Q w c u t) := by
  rw [zero_design_childContinuation_eq_current Q hQ i hi hw hc]
  have hv := poissonContinuation_nonnegative Q hQ hw hc u t
  unfold Model.Instance.lawResidual
  rw [hi]
  simp only [Model.positivePremium, integral_dirac, mul_zero, zero_sub,
    max_eq_right (neg_nonpos.mpr hv)]

end ProphetSecretary.Limiting
