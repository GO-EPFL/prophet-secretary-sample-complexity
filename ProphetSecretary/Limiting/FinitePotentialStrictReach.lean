import ProphetSecretary.Limiting.HybridStrictReach
import ProphetSecretary.Limiting.FinitePotentialPolicy

/-!
# Strict retained reach for an actual finite-design hybrid potential policy

Both individual and anonymous threshold monotonicity follow from the proved
finite-instance continuation values. This is a concrete specialization of the
hybrid strict comparison. It is not a claim that this finite-design policy is
an optimizer for a general hybrid instance.
-/
open MeasureTheory Set
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def finitePotentialHybridThreshold (Q : Model.Instance n) (w c : ℝ)
    (_r : Unit) (A : Finset (Fin n)) (t : ℝ) (candidate : Option (Fin n)) : ℝ :=
  candidate.elim (poissonThreshold Q w c A t) (fun i => Q.valueThreshold w c A t i)

lemma finitePotentialRule_eq_hybridThresholdRule (Q : Model.Instance n) (w c : ℝ) :
    finitePotentialRule Q w c = hybridThresholdRule (finitePotentialHybridThreshold Q w c) := rfl

lemma finitePotentialHybridThreshold_monotone (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    MonotoneHybridThresholds (finitePotentialHybridThreshold Q w c) := by
  intro r t _ht
  constructor
  · intro i A B hi hAB
    exact Q.valueThreshold_monotone hQ hw hc r t i A B hi hAB
  · intro A B hAB
    have h := Q.optimalScalarValue_restrictTo_mono hQ hAB hw.le (mul_nonneg hc (le_max_left 0 (1-t)))
    exact div_le_div_of_nonneg_right h hw.le

/-- All threshold and measurability prerequisites are discharged for this
actual shared finite-design rule, under its explicit design hypotheses. -/
theorem finitePotentialRule_strict_retained_reach (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (i : Fin n) :
    (finitePotentialRule Q w c).individualReachProbability P μ (Measure.dirac ()) i -
      (finitePotentialRule Q w c).meanDuration P μ (Measure.dirac ()) ≥
      ((finitePotentialRule Q w c).individualSelectionProbability P μ (Measure.dirac ()) i) ^ 2 / 2 := by
  have hπ : (hybridThresholdRule (finitePotentialHybridThreshold Q w c)).IsMeasurable := by
    rw [← finitePotentialRule_eq_hybridThresholdRule]
    exact finitePotentialRule_isMeasurable Q hQ hw.le hc
  rw [finitePotentialRule_eq_hybridThresholdRule]
  exact hybridThresholdRule_strict_reach _ (finitePotentialHybridThreshold_monotone Q hQ hw hc) hπ P μ (Measure.dirac ()) i

end ProphetSecretary.Limiting
